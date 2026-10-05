//! Black-box tests of the lexer that recovers from errors: where it makes
//! the consumer abandon, how much of the input it skips, where it goes on,
//! and what the end of the input does.
//!
//! A run is written as a trace of what the consumer was called with, in
//! order: the tokens as their text, an abandon as `!` and a recovery as `>`,
//! both with the offset of their location, and the end-of-file token as `$`.

use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtLocation,
    lexer::{SmtLexError, SmtLexErrorCause, SmtLexer, SmtRecovering},
    token::{SmtBatchCursor, SmtConsume, SmtRecover, SmtTokenCategory, SmtVersion},
};

/// A location as `(offset, line, column)`, all zero-based.
type Loc = (u64, u64, u64);

fn loc(location: SmtLocation) -> Loc {
    (location.offset(), location.line(), location.column())
}

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

/// Records every call and refuses some tokens, after consuming them:
/// the symbol `bad`, a closing parenthesis that closes nothing, and the
/// end-of-file token inside a parenthesis. The symbol `to-2.0` makes it set
/// the version. `WHITESPACE` says whether it takes whitespace and comments.
struct Checker<'r, const WHITESPACE: bool> {
    events: &'r mut Vec<Event>,
    open: u64,
    rules: Rules,
}

impl<const WHITESPACE: bool> SmtConsume for Checker<'_, WHITESPACE> {
    type Result = ();
    type Error = &'static str;
    const CONSUMES_WHITESPACE_AND_COMMENTS: bool = WHITESPACE;

    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        while let Some(token) = cursor.next() {
            self.events.push(Event::Token(
                token.category(),
                token.content().to_vec(),
                loc(token.span().start()),
            ));
            match token.category() {
                SmtTokenCategory::ParenOpen => self.open += 1,
                SmtTokenCategory::ParenClose => {
                    if self.open == 0 {
                        return Err("unmatched");
                    }
                    self.open -= 1;
                }
                SmtTokenCategory::EndOfFile => {
                    if self.rules.refuse_every_end || self.open > 0 {
                        return Err("unexpected-end");
                    }
                }
                SmtTokenCategory::UnquotedSymbol if token.content() == b"bad" => {
                    return Err("bad");
                }
                SmtTokenCategory::UnquotedSymbol if token.content() == b"to-2.0" => {
                    cursor.set_version(SmtVersion::V2_0);
                }
                _ => {}
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

impl<const WHITESPACE: bool> SmtRecover for Checker<'_, WHITESPACE> {
    fn abandon(&mut self, location: SmtLocation) {
        self.events.push(Event::Abandon(loc(location)));
        self.open = 0;
    }

    fn recover(&mut self, location: SmtLocation) {
        self.events.push(Event::Recover(loc(location)));
    }
}

/// Everything observable about a run.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Run {
    events: Vec<Event>,
    /// Every error returned, as its kind and the offset the input continues
    /// from, or `-` if it does not continue.
    errors: Vec<String>,
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

fn describe(err: &SmtLexError<&'static str>) -> String {
    let what = match err.cause() {
        SmtLexErrorCause::Lexical(err) => format!("{:?}", err.kind()),
        SmtLexErrorCause::Consumer(err) => err.to_string(),
    };
    match err.continues_from() {
        Some(location) => format!("{what}@{}", location.offset()),
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

/// Runs a fresh recovering lexer over the input, fed as the pieces between
/// the cuts, the way a driver does: after an error, the rest of the piece
/// is fed again from where the input continues, and the end of the input
/// is given again if the first time failed.
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
    let mut events = Vec::new();
    let mut errors = Vec::new();
    {
        let mut lexer: SmtLexer<_, SmtRecovering> = SmtLexer::new_recovering(
            Checker::<WHITESPACE> {
                events: &mut events,
                open: 0,
                rules,
            },
            version,
        );
        let mut at = 0;
        for &end in cuts.iter().chain([&input.len()]) {
            // every failed call makes progress, or the loop would not end
            let mut calls = 0;
            loop {
                calls += 1;
                assert!(calls <= 2 * input.len() + 2, "no progress in {context}");
                match lexer.lex_slice(&input[at..end]) {
                    Ok(ControlFlow::Continue(())) => {
                        at = end;
                        break;
                    }
                    Ok(ControlFlow::Break(_)) => panic!("the consumer never finishes"),
                    Err(err) => {
                        errors.push(describe(&err));
                        let from = err
                            .continues_from()
                            .unwrap_or_else(|| panic!("a recovering lexer continues in {context}"));
                        // the failure is inside the piece, and the lexer is there
                        assert!(
                            (at..=end).contains(&(from.offset() as usize)),
                            "the input continues outside of the piece in {context}"
                        );
                        assert_eq!(loc(lexer.current_location()), loc(from), "{context}");
                        at = from.offset() as usize;
                    }
                }
            }
            assert_eq!(lexer.current_location().offset() as usize, at, "{context}");
        }
        match lexer.lex_eof() {
            Ok(ControlFlow::Continue(())) => {}
            Ok(ControlFlow::Break(_)) => panic!("the consumer never finishes"),
            Err(err) => {
                errors.push(describe(&err));
                // an error at the end either is final, or continues at the end
                if let Some(from) = err.continues_from() {
                    assert_eq!(from.offset() as usize, input.len(), "{context}");
                    // nothing is left of the input, so its end is given again
                    match lexer.lex_eof() {
                        Ok(ControlFlow::Continue(())) => {}
                        Ok(ControlFlow::Break(_)) => panic!("the consumer never finishes"),
                        Err(err) => {
                            errors.push(describe(&err));
                            assert_eq!(err.continues_from(), None, "{context}");
                        }
                    }
                }
            }
        }
        // the input has ended, whatever happened in it
        assert_eq!(loc(lexer.current_location()), (0, 0, 0), "{context}");
    }
    assert_paired(&events, &context);
    Run { events, errors }
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
    check(b"a \x00b c", "a !2 >4 c $", &["UnexpectedCharacter@2"]);
    check(b"12abc x", "!2 >5 x $", &["MissingDelimiter@2"]);
    check(b"\"s\"t x", "!3 >4 x $", &["MissingDelimiter@3"]);
    check(b"|s|t x", "!3 >4 x $", &["MissingDelimiter@3"]);
    check(b"012 x", "!1 >3 x $", &["NumeralLeadingZero@1"]);
    check(b"7.y x", "!2 >3 x $", &["FractionDigitExpected@2"]);
    check(b"#xg x", "!2 >3 x $", &["HexadecimalDigitExpected@2"]);
    check(b"#b2 x", "!2 >3 x $", &["BinaryDigitExpected@2"]);
    check(b"#q x", "!1 >2 x $", &["BaseSelectionExpected@1"]);
    check(b":\x00 x", "!1 >2 x $", &["ForbiddenKeywordName@1"]);
    check(b"\"a\x00b c\" x", "!2 >7 x $", &["ForbiddenCharInString@2"]);
    check(b"|a\\b c| x", "!2 >7 x $", &["BackslashInQuotedSymbol@2"]);
    check(
        b"|a\x00b c| x",
        "!2 >7 x $",
        &["ForbiddenCharInQuotedSymbol@2"],
    );
}

#[test]
fn a_delimiter_that_raises_the_error_is_not_skipped() {
    // the failing token has ended where its delimiter stands, so the lexing
    // goes on at the very location of the failure
    check(b"7. x", "!2 >2 x $", &["FractionDigitExpected@2"]);
    check(b"#x x", "!2 >2 x $", &["HexadecimalDigitExpected@2"]);
    check(b"#b(x)", "!2 >2 ( x ) $", &["BinaryDigitExpected@2"]);
    check(b": x", "!1 >1 x $", &["ForbiddenKeywordName@1"]);
    check(b"# x", "!1 >1 x $", &["BaseSelectionExpected@1"]);
}

#[test]
fn an_error_raised_by_the_end_of_the_input_takes_effect_at_the_end() {
    // nothing is left to skip: the second end of the input recovers there
    // and hands over the end-of-file token
    check(b"#", "!1 >1 $", &["BaseSelectionExpected@1"]);
    check(b"7.", "!2 >2 $", &["FractionDigitExpected@2"]);
    check(b"#x", "!2 >2 $", &["HexadecimalDigitExpected@2"]);
    check(b"#b", "!2 >2 $", &["BinaryDigitExpected@2"]);
    check(b":", "!1 >1 $", &["ForbiddenKeywordName@1"]);
    check(b"\"ab", "!3 >3 $", &["UnclosedStringLiteral@3"]);
    check(b"|ab", "!3 >3 $", &["UnclosedQuotedSymbol@3"]);
    // the tokens before the failing one were handed over
    check(b"(a \"bc", "( a !6 >6 $", &["UnclosedStringLiteral@6"]);
}

// --- How much is skipped: the value the error is in, with nothing open ---

#[test]
fn with_nothing_open_the_failing_atom_is_skipped_to_its_delimiter() {
    // a closing parenthesis is a delimiter, and is handed over next
    check(
        b"#q)",
        "!1 >2 ) !3 >3 $",
        &["BaseSelectionExpected@1", "unmatched@3"],
    );
    // what is written together with the failing token is a part of the atom
    check(b"#q\"str\"", "!1 >7 $", &["BaseSelectionExpected@1"]);
    check(b"#q|a b|c x", "!1 >8 x $", &["BaseSelectionExpected@1"]);
    check(b"#q:k x", "!1 >4 x $", &["BaseSelectionExpected@1"]);
    check(b"12abc\"s t\" x", "!2 >10 x $", &["MissingDelimiter@2"]);
    // what a delimiter separates from it is the next value
    check(
        b"#q \"str\"",
        "!1 >2 \"str\" $",
        &["BaseSelectionExpected@1"],
    );
    check(b"#q foo", "!1 >2 foo $", &["BaseSelectionExpected@1"]);
    check(b"#q(a)", "!1 >2 ( a ) $", &["BaseSelectionExpected@1"]);
    check(b"#q;note\nx", "!1 >2 x $", &["BaseSelectionExpected@1"]);
    check(b"#q\tx", "!1 >2 x $", &["BaseSelectionExpected@1"]);
    check(b"#q\rx", "!1 >2 x $", &["BaseSelectionExpected@1"]);
    check(b"#q\nx", "!1 >2 x $", &["BaseSelectionExpected@1"]);
}

#[test]
fn inside_parentheses_the_whole_parenthesised_value_is_skipped() {
    // the skipping ends right after the parenthesis that closes the
    // outermost one, whatever follows it
    check(
        b"(assert #q (f x)) y",
        "( assert !9 >17 y $",
        &["BaseSelectionExpected@9"],
    );
    check(b"(a #q)b", "( a !4 >6 b $", &["BaseSelectionExpected@4"]);
    check(
        b"(a #q)(b)",
        "( a !4 >6 ( b ) $",
        &["BaseSelectionExpected@4"],
    );
    check(
        b"((a) (b #q (c)) d) e",
        "( ( a ) ( b !9 >18 e $",
        &["BaseSelectionExpected@9"],
    );
    // a delimiter that raises the error is skipped like everything else
    check(b"(a 7. b) c", "( a !5 >8 c $", &["FractionDigitExpected@5"]);
    check(
        b"(a (b #x) c) d",
        "( a ( b !8 >12 d $",
        &["HexadecimalDigitExpected@8"],
    );
}

#[test]
fn strings_quoted_symbols_and_comments_hide_what_they_enclose() {
    // a parenthesis inside them closes nothing, and a quote in a comment
    // opens nothing
    check(
        b"(a #q \") \" |) | ; \") |\n b) c",
        "( a !4 >26 c $",
        &["BaseSelectionExpected@4"],
    );
    // the failing token itself is one of them: the skipping starts inside it
    check(
        b"(a \"b\x00c ) d\" e) f",
        "( a !5 >15 f $",
        &["ForbiddenCharInString@5"],
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
        &["BaseSelectionExpected@4"],
    );
    // a carriage return ends a comment too
    check(
        b"(a #q ; )\r b) c",
        "( a !4 >13 c $",
        &["BaseSelectionExpected@4"],
    );
}

#[test]
fn a_string_is_skipped_by_the_rule_of_the_version_in_force() {
    // under 2.0 a backslash escapes the quote after it, later it does not
    let input: &[u8] = b"(a #q \"x\\\" )\" b) c";
    let legacy = run_as::<false>(SmtVersion::V2_0, input, &[], Rules::default());
    assert_eq!(legacy.trace(), "( a !4 >16 c $");
    assert_eq!(legacy.errors, ["BaseSelectionExpected@4"]);
    for version in [SmtVersion::V2_5, SmtVersion::V2_6, SmtVersion::V2_7] {
        // the parenthesis after the string closes the value, and the quote
        // after it opens a string that is never closed
        let run = run_as::<false>(version, input, &[], Rules::default());
        assert_eq!(run.trace(), "( a !4 >12 !18 >18 $", "{version:?}");
        assert_eq!(
            run.errors,
            ["BaseSelectionExpected@4", "UnclosedStringLiteral@18"],
            "{version:?}"
        );
    }
}

#[test]
fn the_version_set_by_the_consumer_survives_a_recovery() {
    // the string after the recovery is lexed under 2.0, as one token
    let run = run(b"to-2.0 (a #q) \"x\\\" y\" z");
    assert_eq!(run.trace(), "to-2.0 ( a !11 >13 \"x\" y\" z $");
    assert_eq!(run.errors, ["BaseSelectionExpected@11"]);
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
    assert_eq!(first.errors, [format!("BaseSelectionExpected@{failure}")]);
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
    check(b"(a #q (b", "( a !4 >8 $", &["BaseSelectionExpected@4"]);
    check(b"(a \"b\x00c", "( a !5 >7 $", &["ForbiddenCharInString@5"]);
    check(b"(a #q ; c", "( a !4 >9 $", &["BaseSelectionExpected@4"]);
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
    assert_eq!(run.errors, ["BaseSelectionExpected@4", "unexpected-end@-"]);
}

#[test]
fn the_lexer_takes_a_new_input_after_a_final_error() {
    let mut events = Vec::new();
    {
        let mut lexer = SmtLexer::new_recovering(
            Checker::<false> {
                events: &mut events,
                open: 0,
                rules: Rules {
                    refuse_every_end: true,
                },
            },
            SmtVersion::V2_7,
        );
        assert!(matches!(
            lexer.lex_slice(b"a"),
            Ok(ControlFlow::Continue(()))
        ));
        assert!(lexer.lex_eof().is_err());
        assert!(lexer.lex_eof().is_err());
        // the next input is lexed from the origin
        assert!(matches!(
            lexer.lex_slice(b"b c "),
            Ok(ControlFlow::Continue(()))
        ));
        assert_eq!(loc(lexer.current_location()), (4, 0, 4));
    }
    let run = Run {
        events,
        errors: Vec::new(),
    };
    assert_eq!(run.trace(), "a $ !1 >1 $ b c");
}

#[test]
#[should_panic(expected = "cannot lex a slice after the end of the input")]
fn a_slice_after_a_failed_end_of_the_input_panics() {
    let mut events = Vec::new();
    let mut lexer = SmtLexer::new_recovering(
        Checker::<false> {
            events: &mut events,
            open: 0,
            rules: Rules::default(),
        },
        SmtVersion::V2_7,
    );
    assert!(matches!(
        lexer.lex_slice(b"(a"),
        Ok(ControlFlow::Continue(()))
    ));
    assert!(lexer.lex_eof().is_err());
    let _ = lexer.lex_slice(b"b");
}

#[test]
fn an_empty_slice_after_a_failed_end_of_the_input_is_allowed() {
    // a driver that gives the rest of the input again gives nothing here
    let mut events = Vec::new();
    {
        let mut lexer = SmtLexer::new_recovering(
            Checker::<false> {
                events: &mut events,
                open: 0,
                rules: Rules::default(),
            },
            SmtVersion::V2_7,
        );
        assert!(matches!(
            lexer.lex_slice(b"(a"),
            Ok(ControlFlow::Continue(()))
        ));
        let err = lexer.lex_eof().expect_err("the end is refused");
        assert_eq!(err.continues_from().map(loc), Some((2, 0, 2)));
        assert!(matches!(
            lexer.lex_slice(b""),
            Ok(ControlFlow::Continue(()))
        ));
        assert!(matches!(lexer.lex_eof(), Ok(ControlFlow::Continue(()))));
    }
    let run = Run {
        events,
        errors: Vec::new(),
    };
    assert_eq!(run.trace(), "( a $ !2 >2 $");
}

// --- A consumer that takes whitespace and comments ---

#[test]
fn whitespace_and_comments_are_handed_over_around_the_skipped_input() {
    let run = run_as::<true>(SmtVersion::V2_7, b"(a #q) ;c\n b", &[], Rules::default());
    // what is skipped is not handed over in any form
    assert_eq!(run.trace(), "( a _ !4 >6 _ ;c _ b $");
    assert_eq!(run.errors, ["BaseSelectionExpected@4"]);
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

// --- A lexer that stops at its first error is not affected ---

#[test]
fn well_formed_input_is_lexed_without_abandoning() {
    check(
        b"(assert x)\n(check-sat)",
        "( assert x ) ( check-sat ) $",
        &[],
    );

    // a mutable reference to a consumer that can recover can recover
    let mut events = Vec::new();
    {
        let mut consumer = Checker::<false> {
            events: &mut events,
            open: 0,
            rules: Rules::default(),
        };
        let mut lexer = SmtLexer::new_recovering(&mut consumer, SmtVersion::V2_7);
        assert!(lexer.lex_slice(b"(a #q) b").is_err());
        assert!(matches!(
            lexer.lex_slice(b"q) b"),
            Ok(ControlFlow::Continue(()))
        ));
        assert!(matches!(lexer.lex_eof(), Ok(ControlFlow::Continue(()))));
    }
    let run = Run {
        events,
        errors: Vec::new(),
    };
    assert_eq!(run.trace(), "( a !4 >6 b $");

    // the same consumer serves a lexer that stops at its first error, which
    // calls neither of the two and does not continue the input
    let mut events = Vec::new();
    {
        let mut lexer = SmtLexer::new(
            Checker::<false> {
                events: &mut events,
                open: 0,
                rules: Rules::default(),
            },
            SmtVersion::V2_7,
        );
        let err = lexer.lex_all(b"(a #q) b").expect_err("a lexical error");
        assert_eq!(err.continues_from(), None);
    }
    let run = Run {
        events,
        errors: Vec::new(),
    };
    assert_eq!(run.trace(), "( a");
}
