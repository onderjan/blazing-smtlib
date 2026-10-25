//! Black-box tests of the lexer that recovers from errors: where it makes
//! the consumer abandon, how much of the input it skips, where it goes on,
//! and what the end of the input does.
//!
//! A run is written as a trace of what the consumer was called with, in
//! order: the tokens as their text, an abandon as `!` and a recovery as `>`,
//! both with the offset of their location, and the end-of-file token as `$`.
//!
//! The consumer is the one of the driver protocol that fails by what the
//! tokens are: on the symbol `bad`, on a closing parenthesis that closes
//! nothing, and on the end-of-file token inside a parenthesis. The symbol
//! `to-2.0` makes it set the version. The runs go through the lexing backend
//! of the tests, so they check the Lean port when its driver is selected; the
//! tests at the end use the Rust interface itself.

mod lex_backend;

use std::cell::RefCell;
use std::rc::Rc;

use blazing_smtlib::{
    SmtVersion,
    lexer::{SmtLexer, SmtRecovering},
    token::SmtTokenCategory,
};

use lex_backend::{
    Feed, Line, Loc, Options,
    driver::{Behaviour, Scripted},
};

/// What a consumer was called with.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Event {
    Token(SmtTokenCategory, Vec<u8>, Loc),
    Abandon(Loc),
    Recover(Loc),
}

/// What the consumer does beyond its fixed rules.
#[derive(Debug, Clone, Copy, Default)]
struct Rules {
    /// The end-of-file token is refused whatever came before it.
    refuse_every_end: bool,
}

/// Everything observable about a run.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Run {
    events: Vec<Event>,
    /// Every error returned, as its kind and the offset the input continues
    /// from, or `-` if it does not continue.
    errors: Vec<String>,
    /// The lexer's location after every feed.
    locations: Vec<Loc>,
}

impl Run {
    /// The events in the notation of the tests.
    fn trace(&self) -> String {
        let words: Vec<String> = self
            .events
            .iter()
            .map(|event| match event {
                Event::Abandon(location) => format!("!{}", location.0),
                Event::Recover(location) => format!(">{}", location.0),
                Event::Token(category, content, _) => {
                    let text = String::from_utf8_lossy(content);
                    match category {
                        SmtTokenCategory::EndOfFile => "$".to_string(),
                        SmtTokenCategory::String => format!("\"{text}\""),
                        SmtTokenCategory::QuotedSymbol => format!("|{text}|"),
                        SmtTokenCategory::Keyword => format!(":{text}"),
                        SmtTokenCategory::Hexadecimal => format!("#x{text}"),
                        SmtTokenCategory::Binary => format!("#b{text}"),
                        SmtTokenCategory::Whitespace => "_".to_string(),
                        SmtTokenCategory::Comment => format!(";{}", text.trim_end()),
                        _ => text.into_owned(),
                    }
                }
            })
            .collect();
        words.join(" ")
    }
}

/// An error as its kind and where the input continues from.
fn describe(what: String, continues: Option<Option<Loc>>, context: &str) -> String {
    match continues
        .unwrap_or_else(|| panic!("a recovering lexer says where it continues: {context}"))
    {
        Some(location) => format!("{what}@{}", location.0),
        None => format!("{what}@-"),
    }
}

/// The contract of the two calls: every abandon is followed by exactly one
/// recovery before the next token, and a recovery only follows an abandon.
fn assert_paired(events: &[Event], context: &str) {
    let mut abandoned = false;
    for event in events {
        match event {
            Event::Abandon(_) => {
                assert!(!abandoned, "two abandons without a recovery in {context}");
                abandoned = true;
            }
            Event::Recover(_) => {
                assert!(abandoned, "a recovery without an abandon in {context}");
                abandoned = false;
            }
            Event::Token(..) => {
                assert!(!abandoned, "a token before the recovery in {context}");
            }
        }
    }
    assert!(!abandoned, "an abandon without a recovery in {context}");
}

/// Runs a fresh recovering lexer over the feeds. After an error, the rest of
/// the failed feed is applied again from where the input continues, and the
/// end of the input is given again if the first time failed.
fn run_feeds<const WHITESPACE: bool>(
    version: SmtVersion,
    feeds: &[Feed<'_>],
    rules: Rules,
    context: &str,
) -> Run {
    let options = Options {
        whitespace: WHITESPACE,
        recover: true,
        behaviour: Behaviour::Rules {
            refuse_end: rules.refuse_every_end,
        },
    };
    let mut run = Run {
        events: Vec::new(),
        errors: Vec::new(),
        locations: Vec::new(),
    };
    for line in lex_backend::run(version, &options, feeds) {
        match line {
            Line::Token(token) => {
                run.events
                    .push(Event::Token(token.ty, token.content, token.start));
            }
            Line::Abandon(location) => run.events.push(Event::Abandon(location)),
            Line::Recover(location) => run.events.push(Event::Recover(location)),
            Line::LexicalError { error, continues } => {
                run.errors
                    .push(describe(format!("{:?}", error.kind), continues, context));
            }
            Line::ConsumerError { name, continues } => {
                run.errors.push(describe(name, continues, context));
            }
            Line::At(location) => run.locations.push(location),
            Line::Version(_) => {}
            Line::Handover { .. } | Line::Finish(_) => {
                panic!("the consumer has no plan and never finishes: {context}")
            }
            Line::Done { .. } | Line::NoResult | Line::IoError { .. } => {
                panic!("feeding slices reads no whole input: {context}")
            }
        }
    }
    assert_eq!(
        run.locations.len(),
        feeds.len(),
        "every feed is applied: {context}"
    );
    assert_paired(&run.events, context);
    run
}

/// Runs a fresh recovering lexer over the input, fed as the pieces between
/// the cuts and then its end.
fn run_as<const WHITESPACE: bool>(
    version: SmtVersion,
    input: &[u8],
    cuts: &[usize],
    rules: Rules,
) -> Run {
    let context = format!(
        "{:?} cut at {cuts:?} under {version:?}",
        String::from_utf8_lossy(input)
    );
    let mut feeds = Vec::new();
    let mut at = 0;
    for &end in cuts.iter().chain([&input.len()]) {
        feeds.push(Feed::Slice(&input[at..end]));
        at = end;
    }
    feeds.push(Feed::Eof);
    let mut run = run_feeds::<WHITESPACE>(version, &feeds, rules, &context);

    // after every piece the lexer is after everything it was fed, however
    // often it failed inside the piece, and the end of the input resets it
    let mut expected: Vec<u64> = cuts.iter().map(|&cut| cut as u64).collect();
    expected.push(input.len() as u64);
    expected.push(0);
    let offsets: Vec<u64> = run.locations.iter().map(|location| location.0).collect();
    assert_eq!(offsets, expected, "{context}");
    // the locations depend on the cuts, the rest of a run must not
    run.locations.clear();
    run
}

fn run(input: &[u8]) -> Run {
    run_as::<false>(SmtVersion::V2_7, input, &[], Rules::default())
}

/// Checks the trace and the errors of the input fed whole.
#[track_caller]
fn check(input: &[u8], trace: &str, errors: &[&str]) {
    let run = run(input);
    let context = String::from_utf8_lossy(input).into_owned();
    assert_eq!(run.trace(), trace, "trace of {context:?}");
    assert_eq!(run.errors, errors, "errors of {context:?}");
}

// --- Where the failure takes effect, for every kind of lexical error ---

#[test]
fn a_lexical_error_takes_effect_before_the_byte_that_raised_it() {
    // every input has the failing token alone with nothing open, followed by
    // a symbol: the token is abandoned before the byte that raised the
    // error, the rest of it is skipped up to its delimiter, and no part of it
    // is handed over
    check(b"a \x00b c", "a !2 >4 c $", &["UnexpectedByte@2"]);
    check(b"12abc x", "!2 >5 x $", &["MissingDelimiter@2"]);
    check(b"\"s\"t x", "!3 >4 x $", &["MissingDelimiter@3"]);
    check(b"|s|t x", "!3 >4 x $", &["MissingDelimiter@3"]);
    check(b"012 x", "!1 >3 x $", &["NumeralLeadingZero@1"]);
    check(b"7.y x", "!2 >3 x $", &["Expected(FractionDigit)@2"]);
    check(b"#xg x", "!2 >3 x $", &["Expected(HexadecimalDigit)@2"]);
    check(b"#b2 x", "!2 >3 x $", &["Expected(BinaryDigit)@2"]);
    check(b"#q x", "!1 >2 x $", &["Expected(Base)@1"]);
    check(b":\x00 x", "!1 >2 x $", &["EmptyKeyword@1"]);
    check(b"\"a\x00b c\" x", "!2 >7 x $", &["ForbiddenByteInString@2"]);
    check(b"|a\\b c| x", "!2 >7 x $", &["BackslashInQuotedSymbol@2"]);
    check(
        b"|a\x00b c| x",
        "!2 >7 x $",
        &["ForbiddenByteInQuotedSymbol@2"],
    );
}

#[test]
fn a_delimiter_that_raises_the_error_is_not_skipped() {
    // the failing token has ended where its delimiter stands, so the lexing
    // goes on at the very location of the failure
    check(b"7. x", "!2 >2 x $", &["Expected(FractionDigit)@2"]);
    check(b"#x x", "!2 >2 x $", &["Expected(HexadecimalDigit)@2"]);
    check(b"#b(x)", "!2 >2 ( x ) $", &["Expected(BinaryDigit)@2"]);
    check(b": x", "!1 >1 x $", &["EmptyKeyword@1"]);
    check(b"# x", "!1 >1 x $", &["Expected(Base)@1"]);
}

#[test]
fn an_error_raised_by_the_end_of_the_input_takes_effect_at_the_end() {
    // nothing is left to skip: the second end of the input recovers there
    // and hands over the end-of-file token
    check(b"#", "!1 >1 $", &["Expected(Base)@1"]);
    check(b"7.", "!2 >2 $", &["Expected(FractionDigit)@2"]);
    check(b"#x", "!2 >2 $", &["Expected(HexadecimalDigit)@2"]);
    check(b"#b", "!2 >2 $", &["Expected(BinaryDigit)@2"]);
    check(b":", "!1 >1 $", &["EmptyKeyword@1"]);
    check(b"\"ab", "!3 >3 $", &["UnclosedString@3"]);
    check(b"|ab", "!3 >3 $", &["UnclosedQuotedSymbol@3"]);
    // the tokens before the failing one were handed over
    check(b"(a \"bc", "( a !6 >6 $", &["UnclosedString@6"]);
}

// --- How much is skipped: the value the error is in, with nothing open ---

#[test]
fn with_nothing_open_the_failing_atom_is_skipped_to_its_delimiter() {
    // a closing parenthesis is a delimiter, and is handed over next
    check(
        b"#q)",
        "!1 >2 ) !3 >3 $",
        &["Expected(Base)@1", "unmatched@3"],
    );
    // what is written together with the failing token is a part of the atom
    check(b"#q\"str\"", "!1 >7 $", &["Expected(Base)@1"]);
    check(b"#q|a b|c x", "!1 >8 x $", &["Expected(Base)@1"]);
    check(b"#q:k x", "!1 >4 x $", &["Expected(Base)@1"]);
    check(b"12abc\"s t\" x", "!2 >10 x $", &["MissingDelimiter@2"]);
    // what a delimiter separates from it is the next value
    check(b"#q \"str\"", "!1 >2 \"str\" $", &["Expected(Base)@1"]);
    check(b"#q foo", "!1 >2 foo $", &["Expected(Base)@1"]);
    check(b"#q(a)", "!1 >2 ( a ) $", &["Expected(Base)@1"]);
    check(b"#q;note\nx", "!1 >2 x $", &["Expected(Base)@1"]);
    check(b"#q\tx", "!1 >2 x $", &["Expected(Base)@1"]);
    check(b"#q\rx", "!1 >2 x $", &["Expected(Base)@1"]);
    check(b"#q\nx", "!1 >2 x $", &["Expected(Base)@1"]);
}

#[test]
fn inside_parentheses_the_whole_parenthesised_value_is_skipped() {
    // the skipping ends right after the parenthesis that closes the
    // outermost one, whatever follows it
    check(
        b"(assert #q (f x)) y",
        "( assert !9 >17 y $",
        &["Expected(Base)@9"],
    );
    check(b"(a #q)b", "( a !4 >6 b $", &["Expected(Base)@4"]);
    check(b"(a #q)(b)", "( a !4 >6 ( b ) $", &["Expected(Base)@4"]);
    check(
        b"((a) (b #q (c)) d) e",
        "( ( a ) ( b !9 >18 e $",
        &["Expected(Base)@9"],
    );
    // a delimiter that raises the error is skipped like everything else
    check(
        b"(a 7. b) c",
        "( a !5 >8 c $",
        &["Expected(FractionDigit)@5"],
    );
    check(
        b"(a (b #x) c) d",
        "( a ( b !8 >12 d $",
        &["Expected(HexadecimalDigit)@8"],
    );
}

#[test]
fn strings_quoted_symbols_and_comments_hide_what_they_enclose() {
    // a parenthesis inside them closes nothing, and a quote in a comment
    // opens nothing
    check(
        b"(a #q \") \" |) | ; \") |\n b) c",
        "( a !4 >26 c $",
        &["Expected(Base)@4"],
    );
    // the failing token itself is one of them: the skipping starts inside it
    check(
        b"(a \"b\x00c ) d\" e) f",
        "( a !5 >15 f $",
        &["ForbiddenByteInString@5"],
    );
    check(
        b"(a |b\\c ) d| e) f",
        "( a !5 >15 f $",
        &["BackslashInQuotedSymbol@5"],
    );
    // a quote written together with a failing token opens a string
    check(
        b"(a 12\"b ) c\" d) e",
        "( a !5 >15 e $",
        &["MissingDelimiter@5"],
    );
    // no delimiter is needed after the closing quote or pipe
    check(
        b"(a #q \"b\"|c|d \"e\")f",
        "( a !4 >18 f $",
        &["Expected(Base)@4"],
    );
    // a carriage return ends a comment too
    check(b"(a #q ; )\r b) c", "( a !4 >13 c $", &["Expected(Base)@4"]);
}

#[test]
fn a_string_is_skipped_by_the_rule_of_the_version_in_force() {
    // under 2.0 a backslash escapes the quote after it, later it does not
    let input: &[u8] = b"(a #q \"x\\\" )\" b) c";
    let legacy = run_as::<false>(SmtVersion::V2_0, input, &[], Rules::default());
    assert_eq!(legacy.trace(), "( a !4 >16 c $");
    assert_eq!(legacy.errors, ["Expected(Base)@4"]);
    for version in [SmtVersion::V2_5, SmtVersion::V2_6, SmtVersion::V2_7] {
        // the parenthesis after the string closes the value, and the quote
        // after it opens a string that is never closed
        let run = run_as::<false>(version, input, &[], Rules::default());
        assert_eq!(run.trace(), "( a !4 >12 !18 >18 $", "{version:?}");
        assert_eq!(
            run.errors,
            ["Expected(Base)@4", "UnclosedString@18"],
            "{version:?}"
        );
    }
}

#[test]
fn the_version_set_by_the_consumer_survives_a_recovery() {
    // the string after the recovery is lexed under 2.0, as one token
    let run = run(b"to-2.0 (a #q) \"x\\\" y\" z");
    assert_eq!(run.trace(), "to-2.0 ( a !11 >13 \"x\" y\" z $");
    assert_eq!(run.errors, ["Expected(Base)@11"]);
}

// --- Errors of the consumer ---

#[test]
fn a_consumer_error_takes_effect_after_the_token_it_was_raised_on() {
    // with nothing open, the refused token is a whole value: nothing is
    // skipped, and the tokens lexed ahead of it are lexed again
    check(b"a bad b", "a bad !5 >5 b $", &["bad@5"]);
    check(b"a ) b", "a ) !3 >3 b $", &["unmatched@3"]);
    check(b"bad)x", "bad !3 >3 ) !4 >4 x $", &["bad@3", "unmatched@4"]);
    // inside parentheses, the rest of the parenthesised value is skipped
    check(b"(x bad y) z", "( x bad !6 >9 z $", &["bad@6"]);
    check(b"(x (bad) y) z", "( x ( bad !7 >11 z $", &["bad@7"]);
    // the parenthesis that closes the value may be the refused token itself
    check(b"(x) ) y", "( x ) ) !5 >5 y $", &["unmatched@5"]);
}

#[test]
fn the_open_parentheses_are_counted_over_many_hand_overs() {
    // more tokens than a hand-over holds on both sides of the failure
    let mut input = b"(((".to_vec();
    for _ in 0..300 {
        input.extend_from_slice(b"x ");
    }
    let failure = input.len() + 1;
    input.extend_from_slice(b"#q ");
    for _ in 0..300 {
        input.extend_from_slice(b"(y) ");
    }
    input.extend_from_slice(b"))) z");
    let closed = input.len() - 2;

    let first = run(&input);
    assert_eq!(first.errors, [format!("Expected(Base)@{failure}")]);
    let trace = first.trace();
    assert!(
        trace.ends_with(&format!("x !{failure} >{closed} z $")),
        "{}",
        &trace[trace.len() - 60..]
    );

    // and for a consumer error deep inside
    let mut input = b"((".to_vec();
    for _ in 0..300 {
        input.extend_from_slice(b"(x) ");
    }
    input.extend_from_slice(b"bad");
    let failure = input.len();
    for _ in 0..300 {
        input.extend_from_slice(b" (y)");
    }
    input.extend_from_slice(b")) z");
    let closed = input.len() - 2;
    let run = run(&input);
    assert_eq!(run.errors, [format!("bad@{failure}")]);
    assert!(
        run.trace()
            .ends_with(&format!("bad !{failure} >{closed} z $"))
    );
}

#[test]
fn the_open_parentheses_are_counted_anew_after_a_recovery() {
    // the first error is inside a parenthesis, the second with nothing open:
    // what was open at the first one must not count for the second, or the
    // rest of the input would be skipped
    check(
        b"(a #q) b #x c",
        "( a !4 >6 b !11 >11 c $",
        &["Expected(Base)@4", "Expected(HexadecimalDigit)@11"],
    );
    check(
        b"(x bad) y bad z",
        "( x bad !6 >7 y bad !13 >13 z $",
        &["bad@6", "bad@13"],
    );
    // and the other way round: nothing is left over from the first error
    // when the second one is inside a parenthesis
    check(
        b"#q (a #x b) c",
        "!1 >2 ( a !8 >11 c $",
        &["Expected(Base)@1", "Expected(HexadecimalDigit)@8"],
    );
}

// --- Locations ---

#[test]
fn the_two_locations_have_their_lines_and_columns() {
    let run = run(b"(a\n #q\n (b\n c))\nd");
    assert_eq!(
        run.events,
        [
            Event::Token(SmtTokenCategory::ParenOpen, b"(".to_vec(), (0, 0, 0)),
            Event::Token(SmtTokenCategory::UnquotedSymbol, b"a".to_vec(), (1, 0, 1)),
            Event::Abandon((5, 1, 2)),
            // the lines skipped are counted
            Event::Recover((15, 3, 4)),
            Event::Token(SmtTokenCategory::UnquotedSymbol, b"d".to_vec(), (16, 4, 0)),
            Event::Token(SmtTokenCategory::EndOfFile, b"".to_vec(), (17, 4, 1)),
        ]
    );
}

// --- The end of the input ---

#[test]
fn the_end_of_the_input_ends_the_skipping() {
    // the value is never closed: the recovery is reported at the end, and
    // the end-of-file token is handed over as usual
    check(b"(a #q (b", "( a !4 >8 $", &["Expected(Base)@4"]);
    check(b"(a \"b\x00c", "( a !5 >7 $", &["ForbiddenByteInString@5"]);
    check(b"(a #q ; c", "( a !4 >9 $", &["Expected(Base)@4"]);
}

#[test]
fn an_error_at_the_end_of_the_input_is_followed_by_a_second_end() {
    // the consumer refuses the end-of-file token inside a parenthesis; after
    // the abandon nothing is open, so it takes the token the second time
    check(b"(a b", "( a b $ !4 >4 $", &["unexpected-end@4"]);
    // a token that only the end of the input finishes is refused
    check(b"bad", "bad !3 >3 $", &["bad@3"]);
}

#[test]
fn an_error_on_the_second_end_of_the_input_is_final() {
    let rules = Rules {
        refuse_every_end: true,
    };
    // the consumer refuses the end-of-file token again with nothing to
    // abandon: the error does not continue the input, and no call follows it
    let run = run_as::<false>(SmtVersion::V2_7, b"a", &[], rules);
    assert_eq!(run.trace(), "a $ !1 >1 $");
    assert_eq!(run.errors, ["unexpected-end@1", "unexpected-end@-"]);
    // the same when the skipping was still going on at the end
    let run = run_as::<false>(SmtVersion::V2_7, b"(a #q", &[], rules);
    assert_eq!(run.trace(), "( a !4 >5 $");
    assert_eq!(run.errors, ["Expected(Base)@4", "unexpected-end@-"]);
}

#[test]
fn the_lexer_takes_a_new_input_after_a_final_error() {
    let rules = Rules {
        refuse_every_end: true,
    };
    // the end of the first input fails twice; what is fed then is a new
    // input, lexed from the origin
    let feeds = [Feed::Slice(b"a"), Feed::Eof, Feed::Slice(b"b c ")];
    let run = run_feeds::<false>(SmtVersion::V2_7, &feeds, rules, "two inputs");
    assert_eq!(run.trace(), "a $ !1 >1 $ b c");
    assert_eq!(run.errors, ["unexpected-end@1", "unexpected-end@-"]);
    assert_eq!(run.locations, [(1, 0, 1), (0, 0, 0), (4, 0, 4)]);
}

// --- A consumer that takes whitespace and comments ---

#[test]
fn whitespace_and_comments_are_handed_over_around_the_skipped_input() {
    let run = run_as::<true>(SmtVersion::V2_7, b"(a #q) ;c\n b", &[], Rules::default());
    // what is skipped is not handed over in any form
    assert_eq!(run.trace(), "( a _ !4 >6 _ ;c _ b $");
    assert_eq!(run.errors, ["Expected(Base)@4"]);
}

// --- The run does not depend on how the input is sliced ---

#[test]
fn the_run_is_the_same_for_every_slicing() {
    let inputs: [&[u8]; 16] = [
        b"#q)",
        b"#q\"str\" x",
        b"7. x",
        b"(assert #q (f x)) y",
        b"(a \"b\x00c ) d\" e) f",
        b"(a |b\\c ) d| e) f",
        b"(a #q \") \" |) | ; \") |\n b) c",
        b"(a\n #q\n (b\n c))\nd",
        b"a bad b",
        b"(x (bad) y) z",
        b"bad)x",
        b"(a #q (b",
        b"(a b",
        b"\"ab",
        b"12abc\"s t\" x",
        b"(a #q) (b 012 c) (d) #b e",
    ];
    for version in [SmtVersion::V2_0, SmtVersion::V2_7] {
        for whitespace in [false, true] {
            for input in inputs {
                let run_cut = |cuts: &[usize]| {
                    if whitespace {
                        run_as::<true>(version, input, cuts, Rules::default())
                    } else {
                        run_as::<false>(version, input, cuts, Rules::default())
                    }
                };
                let whole = run_cut(&[]);
                for first in 0..=input.len() {
                    for second in first..=input.len() {
                        assert_eq!(
                            run_cut(&[first, second]),
                            whole,
                            "{:?} cut at {first} and {second} under {version:?}",
                            String::from_utf8_lossy(input)
                        );
                    }
                }
                let every: Vec<usize> = (0..=input.len()).collect();
                assert_eq!(
                    run_cut(&every),
                    whole,
                    "{:?} byte by byte under {version:?}",
                    String::from_utf8_lossy(input)
                );
            }
        }
    }
}

// --- The Rust interface itself ---

/// A recovering lexer over the consumer of these tests, and what the
/// consumer writes.
fn rust_lexer() -> (
    SmtLexer<Scripted<false>, SmtRecovering>,
    Rc<RefCell<String>>,
) {
    let written = Rc::new(RefCell::new(String::new()));
    let consumer = Scripted::new(Behaviour::Rules { refuse_end: false }, written.clone());
    (
        SmtLexer::new_recovering(consumer, SmtVersion::V2_7),
        written,
    )
}

/// The number of lines the consumer wrote that start with the word.
fn count_lines(written: &RefCell<String>, word: &str) -> usize {
    written
        .borrow()
        .lines()
        .filter(|line| line.split(' ').next() == Some(word))
        .count()
}

#[test]
#[should_panic(expected = "cannot lex a slice after the end of the input")]
fn a_slice_after_a_failed_end_of_the_input_panics() {
    let (mut lexer, _written) = rust_lexer();
    assert!(lexer.lex_slice(b"(a").is_ok());
    assert!(lexer.lex_eof().is_err());
    let _ = lexer.lex_slice(b"b");
}

#[test]
fn an_empty_slice_after_a_failed_end_of_the_input_is_allowed() {
    // an empty slice feeds nothing, as everywhere else
    let (mut lexer, written) = rust_lexer();
    assert!(lexer.lex_slice(b"(a").is_ok());
    let err = lexer.lex_eof().expect_err("the end is refused");
    assert_eq!(
        err.continues_from().map(|location| location.offset()),
        Some(2)
    );
    assert!(lexer.lex_slice(b"").is_ok());
    // the recovery only comes with the second end of the input
    assert_eq!(count_lines(&written, "rc"), 0);
    assert!(lexer.lex_eof().is_ok());
    assert_eq!(count_lines(&written, "ab"), 1);
    assert_eq!(count_lines(&written, "rc"), 1);
}

#[test]
fn a_mutable_reference_to_a_consumer_that_can_recover_can_recover() {
    let written = Rc::new(RefCell::new(String::new()));
    let mut consumer =
        Scripted::<false>::new(Behaviour::Rules { refuse_end: false }, written.clone());
    let mut lexer = SmtLexer::new_recovering(&mut consumer, SmtVersion::V2_7);
    assert!(lexer.lex_slice(b"(a #q) b").is_err());
    assert!(lexer.lex_slice(b"q) b").is_ok());
    assert!(lexer.lex_eof().is_ok());
    assert_eq!(count_lines(&written, "ab"), 1);
    assert_eq!(count_lines(&written, "rc"), 1);
}

#[test]
fn a_lexer_that_stops_at_its_first_error_does_not_abandon() {
    // the same consumer serves a lexer that stops at its first error, which
    // calls neither of the two and does not continue the input
    let written = Rc::new(RefCell::new(String::new()));
    let consumer = Scripted::<false>::new(Behaviour::Rules { refuse_end: false }, written.clone());
    let mut lexer = SmtLexer::new(consumer, SmtVersion::V2_7);
    let err = lexer.lex_all(b"(a #q) b").expect_err("a lexical error");
    assert_eq!(err.continues_from(), None);
    assert_eq!(count_lines(&written, "t"), 2);
    assert_eq!(count_lines(&written, "ab"), 0);
    assert_eq!(count_lines(&written, "rc"), 0);
}

#[test]
fn well_formed_input_is_lexed_without_abandoning() {
    check(
        b"(assert x)\n(check-sat)",
        "( assert x ) ( check-sat ) $",
        &[],
    );
}
