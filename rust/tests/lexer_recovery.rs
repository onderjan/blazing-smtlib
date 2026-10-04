//! Black-box tests of the lexer that recovers from errors.

use std::convert::Infallible;
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtLocation,
    lexer::{SmtLexer, SmtRecovering},
    token::{SmtBatchCursor, SmtConsume, SmtRecover, SmtTokenCategory, SmtVersion},
};

/// A location as `(offset, line, column)`, all zero-based.
type Loc = (u64, u64, u64);

fn loc(location: SmtLocation) -> Loc {
    (location.offset(), location.line(), location.column())
}

/// What a consumer was called with, in order.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Event {
    Token(SmtTokenCategory, Vec<u8>),
    Abandon(Loc),
    Recover(Loc),
}

/// Takes every token and records every call.
struct Record<'r>(&'r mut Vec<Event>);

impl SmtConsume for Record<'_> {
    type Result = ();
    type Error = Infallible;
    const CONSUMES_WHITESPACE_AND_COMMENTS: bool = false;

    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        while let Some(token) = cursor.next() {
            self.0
                .push(Event::Token(token.category(), token.content().to_vec()));
        }
        Ok(ControlFlow::Continue(()))
    }
}

impl SmtRecover for Record<'_> {
    fn abandon(&mut self, location: SmtLocation) {
        self.0.push(Event::Abandon(loc(location)));
    }

    fn recover(&mut self, location: SmtLocation) {
        self.0.push(Event::Recover(loc(location)));
    }
}

fn token(category: SmtTokenCategory, content: &[u8]) -> Event {
    Event::Token(category, content.to_vec())
}

#[test]
fn well_formed_input_is_lexed_without_abandoning() {
    let input: &[u8] = b"(assert x)\n(check-sat)";
    let expected = [
        token(SmtTokenCategory::ParenOpen, b"("),
        token(SmtTokenCategory::UnquotedSymbol, b"assert"),
        token(SmtTokenCategory::UnquotedSymbol, b"x"),
        token(SmtTokenCategory::ParenClose, b")"),
        token(SmtTokenCategory::ParenOpen, b"("),
        token(SmtTokenCategory::UnquotedSymbol, b"check-sat"),
        token(SmtTokenCategory::ParenClose, b")"),
        token(SmtTokenCategory::EndOfFile, b""),
    ];

    // the kind of lexer is a part of its type, with its own constructor
    let mut events = Vec::new();
    {
        let mut lexer: SmtLexer<Record<'_>, SmtRecovering> =
            SmtLexer::new_recovering(Record(&mut events), SmtVersion::V2_7);
        assert!(matches!(
            lexer.lex_all(input),
            Ok(ControlFlow::Continue(()))
        ));
    }
    assert_eq!(events, expected);

    // a mutable reference to a consumer that can abandon can abandon
    let mut events = Vec::new();
    {
        let mut consumer = Record(&mut events);
        let mut lexer = SmtLexer::new_recovering(&mut consumer, SmtVersion::V2_7);
        assert!(matches!(
            lexer.lex_all(input),
            Ok(ControlFlow::Continue(()))
        ));
    }
    assert_eq!(events, expected);

    // the same consumer serves a lexer that stops at its first error
    let mut events = Vec::new();
    {
        let mut lexer = SmtLexer::new(Record(&mut events), SmtVersion::V2_7);
        assert!(matches!(
            lexer.lex_all(input),
            Ok(ControlFlow::Continue(()))
        ));
    }
    assert_eq!(events, expected);
}
