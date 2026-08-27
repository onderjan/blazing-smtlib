use std::ops::ControlFlow;

use crate::{
    SmtApplication, SmtHandler, SmtIdent, SmtQualifiedIdent, SmtSpecialConstant, SmtSymbol,
    SmtTerm,
    read::parser::{
        CategoryParserError, ParserError,
        category::{CategoryParser, ident::IdentParser},
    },
    token::{Reserved, Token, TokenKind},
};

pub enum TermLevel<H: SmtHandler> {
    Application(SmtQualifiedIdent, Vec<H::Term>),
    LetBinding(Vec<(SmtSymbol, H::Term)>, SmtSymbol),
    LetInner,
}

pub enum TermParserState<H: SmtHandler> {
    Start,
    Open,
    IndexedIdent(IdentParser),
    ApplicationIdent(IdentParser),
    ApplicationTerm(SmtQualifiedIdent, Vec<H::Term>),
    LetBeforeBindingsOpen,
    LetBeforeBindingOpen(Vec<(SmtSymbol, H::Term)>),
    LetBeforeBindingSymbol(Vec<(SmtSymbol, H::Term)>),
    LetBeforeBindingClose(Vec<(SmtSymbol, H::Term)>),
    LetAfterInnerTerm(H::Term),
}

pub struct TermParser<H: SmtHandler> {
    state: TermParserState<H>,
    levels: Vec<TermLevel<H>>,
}

impl<H: SmtHandler> CategoryParser<H> for TermParser<H> {
    type Result = H::Term;

    fn init() -> Self {
        TermParser {
            state: TermParserState::Start,
            levels: Vec::new(),
        }
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Term, Self>, ParserError<H>> {
        let (mut levels, term) = match self.progress_last_level(handler, token)? {
            ControlFlow::Continue(parser) => return Ok(ControlFlow::Continue(parser)),
            ControlFlow::Break((levels, term)) => (levels, term),
        };
        let Some(last_level) = levels.pop() else {
            // this is the root term level, we are done
            return Ok(ControlFlow::Break(term));
        };

        // we need to progress the last level
        let state = match last_level {
            TermLevel::Application(function, mut args) => {
                // add argument and go back to term state
                args.push(term);
                TermParserState::ApplicationTerm(function, args)
            }
            TermLevel::LetBinding(mut bindings, binding_name) => {
                // add binding, should be followed by parenthesis closing the bindings
                bindings.push((binding_name, term));
                TermParserState::LetBeforeBindingClose(bindings)
            }
            TermLevel::LetInner => {
                // end let, should be followed by closing parenthesis
                let term = handler
                    .end_let(term)
                    .map_err(ParserError::HandlerError)?;
                TermParserState::LetAfterInnerTerm(term)
            }
        };

        Ok(ControlFlow::Continue(Self { state, levels }))
    }
}

type TermProgressOk<H, P> = ControlFlow<(Vec<TermLevel<H>>, <H as SmtHandler>::Term), P>;

impl<H: SmtHandler> TermParser<H> {
    fn progress_last_level(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<TermProgressOk<H, Self>, ParserError<H>> {
        let mut levels = self.levels;
        let state = match self.state {
            TermParserState::Start => return Self::parse_term_start(levels, handler, token),
            TermParserState::Open => {
                return Ok(ControlFlow::Continue(Self::parse_term_open(levels, token)?));
            }
            TermParserState::IndexedIdent(parser) => {
                match parser.progress(handler, token)? {
                    ControlFlow::Continue(parser) => TermParserState::IndexedIdent(parser),
                    ControlFlow::Break(ident) => {
                        // TODO: actual qualified ident
                        let term = SmtTerm::QualifiedIdent(SmtQualifiedIdent::Ident(ident));
                        let term = handler
                            .handle_term(term)
                            .map_err(ParserError::HandlerError)?;
                        return Ok(ControlFlow::Break((levels, term)));
                    }
                }
            }
            TermParserState::ApplicationIdent(parser) => {
                match parser.progress(handler, token)? {
                    ControlFlow::Continue(parser) => TermParserState::ApplicationIdent(parser),
                    ControlFlow::Break(ident) => {
                        // TODO: actual qualified ident
                        let ident = SmtQualifiedIdent::Ident(ident);
                        TermParserState::ApplicationTerm(ident, Vec::new())
                    }
                }
            }
            TermParserState::ApplicationTerm(function, args) => {
                if matches!(token.kind(), TokenKind::ParenClose) {
                    // this ends the application term
                    // it must have at least one argument
                    if args.is_empty() {
                        return Err(CategoryParserError::EmptyApplication.into());
                    }
                    let term = SmtTerm::Application(SmtApplication { function, args });
                    let term = handler
                        .handle_term(term)
                        .map_err(ParserError::HandlerError)?;
                    return Ok(ControlFlow::Break((levels, term)));
                } else {
                    // add the application to the level stack and parse the argument
                    levels.push(TermLevel::Application(function, args));
                    return Self::parse_term_start(levels, handler, token);
                }
            }
            TermParserState::LetBeforeBindingsOpen => {
                expect_open_paren(token)?;
                TermParserState::LetBeforeBindingOpen(Vec::new())
            }
            TermParserState::LetBeforeBindingOpen(bindings) => {
                match token.kind() {
                    TokenKind::ParenOpen => {
                        // new binding
                        TermParserState::LetBeforeBindingSymbol(bindings)
                    }
                    TokenKind::ParenClose => {
                        // bindings are closed, inner term will be next
                        // check that there is at least one binding
                        if bindings.is_empty() {
                            return Err(CategoryParserError::EmptyLetBindings.into());
                        }

                        handler
                            .start_let(bindings)
                            .map_err(ParserError::HandlerError)?;

                        levels.push(TermLevel::LetInner);
                        TermParserState::Start
                    }
                    _ => return Err(CategoryParserError::ExpectedOpenOrCloseParen.into()),
                }
            }
            TermParserState::LetBeforeBindingSymbol(bindings) => {
                let symbol = expect_symbol(token)?;
                levels.push(TermLevel::LetBinding(bindings, symbol));
                TermParserState::Start
            }
            TermParserState::LetBeforeBindingClose(bindings) => {
                expect_close_paren(token)?;
                TermParserState::LetBeforeBindingOpen(bindings)
            }
            TermParserState::LetAfterInnerTerm(term) => {
                expect_close_paren(token)?;
                return Ok(ControlFlow::Break((levels, term)));
            }
        };
        Ok(ControlFlow::Continue(Self { state, levels }))
    }

    fn parse_term_start(
        levels: Vec<TermLevel<H>>,
        handler: &mut H,
        token: Token,
    ) -> Result<TermProgressOk<H, Self>, ParserError<H>> {
        let span = token.span();
        match token.into_kind() {
            TokenKind::ParenOpen => {
                // application, binder, or annotation
                // move to operator parsing
                Ok(ControlFlow::Continue(Self {
                    state: TermParserState::Open,
                    levels,
                }))
            }
            TokenKind::Symbol(symbol) => {
                // a qualified identifier that is just a symbol
                let qualified_ident = SmtQualifiedIdent::Ident(SmtIdent {
                    name: symbol,
                    indices: Vec::new(),
                });
                let term = handler
                    .handle_term(SmtTerm::QualifiedIdent(qualified_ident))
                    .map_err(ParserError::HandlerError)?;

                Ok(ControlFlow::Break((levels, term)))
            }

            kind => {
                // handle special constants
                match parse_special_constant(Token::new(kind, span)) {
                    Ok(special_constant) => {
                        let term = handler
                            .handle_term(SmtTerm::SpecialConstant(special_constant))
                            .map_err(ParserError::HandlerError)?;
                        Ok(ControlFlow::Break((levels, term)))
                    }
                    Err(_token) => Err(CategoryParserError::ExpectedTerm.into()),
                }
            }
        }
    }

    fn parse_term_open(
        levels: Vec<TermLevel<H>>,
        token: Token,
    ) -> Result<Self, ParserError<H>> {
        let state = match token.into_kind() {
            TokenKind::Symbol(fn_name) => {
                // this is an application where the function identifier is just a symbol
                let fn_ident = SmtQualifiedIdent::Ident(SmtIdent {
                    name: fn_name,
                    indices: Vec::new(),
                });
                TermParserState::ApplicationTerm(fn_ident, Vec::new())
            }
            TokenKind::Reserved(Reserved::Let) => TermParserState::LetBeforeBindingsOpen,
            TokenKind::Reserved(Reserved::Lambda) => todo!("Lambda"),
            TokenKind::Reserved(Reserved::Forall) => todo!("Forall"),
            TokenKind::Reserved(Reserved::Exists) => todo!("Exists"),
            TokenKind::Reserved(Reserved::Match) => todo!("Match"),
            TokenKind::Reserved(Reserved::ExclamationMark) => todo!("Annotation"),
            TokenKind::Reserved(Reserved::Underscore) => {
                // this is actually a term composed of an indexed identifier
                // start an indexed ident parser after the undescore
                let parser = IdentParser::after_underscore();
                TermParserState::IndexedIdent(parser)
            }
            TokenKind::ParenOpen => {
                // this is an application where the function identifier is qualified or indexed
                // start a qualified ident parser after the parenthesis open
                let parser = IdentParser::after_open_paren();
                TermParserState::ApplicationIdent(parser)
            }
            _ => return Err(CategoryParserError::ExpectedOperator.into()),
        };
        Ok(Self { state, levels })
    }
}

fn parse_special_constant(token: Token) -> Result<SmtSpecialConstant, Token> {
    let span = token.span();
    let constant = match token.into_kind() {
        TokenKind::Numeral(value) => SmtSpecialConstant::Numeral(value),
        TokenKind::Decimal(decimal) => SmtSpecialConstant::Decimal(decimal),
        TokenKind::Hexadecimal(value) => SmtSpecialConstant::Hexadecimal(value),
        TokenKind::Binary(value) => SmtSpecialConstant::Binary(value),
        TokenKind::String(string) => SmtSpecialConstant::String(string),
        kind => return Err(Token::new(kind, span)),
    };
    Ok(constant)
}

fn expect_open_paren<H: SmtHandler>(token: Token) -> Result<(), ParserError<H>> {
    if matches!(token.kind(), TokenKind::ParenOpen) {
        Ok(())
    } else {
        Err(CategoryParserError::ExpectedToken(TokenKind::ParenOpen).into())
    }
}

fn expect_close_paren<H: SmtHandler>(token: Token) -> Result<(), ParserError<H>> {
    if matches!(token.kind(), TokenKind::ParenClose) {
        Ok(())
    } else {
        Err(CategoryParserError::ExpectedToken(TokenKind::ParenClose).into())
    }
}

fn expect_symbol<H: SmtHandler>(token: Token) -> Result<SmtSymbol, ParserError<H>> {
    if let TokenKind::Symbol(symbol) = token.into_kind() {
        Ok(symbol)
    } else {
        Err(CategoryParserError::ExpectedSymbol.into())
    }
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use super::*;
    use crate::{
        SmtAttributeValue, SmtKeyword, SmtSExpr, SmtSort,
        read::{
            lexer::Lexer,
            parser::category::tests::{Printing, assert_error, parse_all, run},
        },
    };

    #[test]
    fn special_constants() {
        assert_eq!(parse_all::<TermParser<Printing>>(b"42"), "42");
        assert_eq!(parse_all::<TermParser<Printing>>(b"0"), "0");
        assert_eq!(parse_all::<TermParser<Printing>>(b"3.25"), "3.25");
        assert_eq!(parse_all::<TermParser<Printing>>(b"#xdead"), "#xdead");
        assert_eq!(parse_all::<TermParser<Printing>>(b"#b101"), "#b101");
        assert_eq!(parse_all::<TermParser<Printing>>(b"\"str\""), "\"str\"");
    }

    #[test]
    fn identifiers() {
        assert_eq!(parse_all::<TermParser<Printing>>(b"x"), "x");
        assert_eq!(parse_all::<TermParser<Printing>>(b"|x y|"), "x y");
        assert_eq!(parse_all::<TermParser<Printing>>(b"(_ bv5 8)"), "(_ bv5 8)");
    }

    #[test]
    fn term_consumes_exactly_one_term() {
        let (term, left) = run::<TermParser<Printing>>(b"x y").expect("valid");
        assert_eq!(term, "x");
        assert_eq!(left, 1);

        let (term, left) = run::<TermParser<Printing>>(b"(f x) )").expect("valid");
        assert_eq!(term, "(f x)");
        assert_eq!(left, 1);
    }

    #[test]
    fn applications() {
        assert_eq!(parse_all::<TermParser<Printing>>(b"(f x)"), "(f x)");
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(f x 1 \"s\")"),
            "(f x 1 \"s\")"
        );
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(f (g x) (h y z))"),
            "(f (g x) (h y z))"
        );
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(+ (* 2 x) (- y))"),
            "(+ (* 2 x) (- y))"
        );
    }

    #[test]
    fn application_of_indexed_function() {
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"((_ extract 7 0) x)"),
            "((_ extract 7 0) x)"
        );
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(f ((_ zero_extend 8) y) (_ bv1 8))"),
            "(f ((_ zero_extend 8) y) (_ bv1 8))"
        );
    }

    #[test]
    fn empty_application_is_rejected() {
        // an application must have at least one argument
        let err = assert_error::<TermParser<Printing>>(b"(f)", 2, 3);
        assert!(matches!(err, CategoryParserError::EmptyApplication), "{err:?}");
    }

    #[test]
    fn lets() {
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(let ((x 1)) x)"),
            "(let ((x 1)) x)"
        );
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(let ((x 1) (y (f 2))) (g x y))"),
            "(let ((x 1) (y (f 2))) (g x y))"
        );
        // nested lets in the bindings and in the body
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(let ((x (let ((z 0)) z))) (let ((y x)) (f x y)))"),
            "(let ((x (let ((z 0)) z))) (let ((y x)) (f x y)))"
        );
        // let as an application argument
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(f (let ((x 1)) x) 2)"),
            "(f (let ((x 1)) x) 2)"
        );
    }

    #[test]
    fn let_errors() {
        let err = assert_error::<TermParser<Printing>>(b"(let () x)", 6, 7);
        assert!(matches!(err, CategoryParserError::EmptyLetBindings), "{err:?}");

        let err = assert_error::<TermParser<Printing>>(b"(let x x)", 5, 6);
        assert!(
            matches!(err, CategoryParserError::ExpectedToken(TokenKind::ParenOpen)),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"(let (x) x)", 6, 7);
        assert!(
            matches!(err, CategoryParserError::ExpectedOpenOrCloseParen),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"(let ((1 x)) x)", 7, 8);
        assert!(matches!(err, CategoryParserError::ExpectedSymbol), "{err:?}");

        let err = assert_error::<TermParser<Printing>>(b"(let ((x 1 2)) x)", 11, 12);
        assert!(
            matches!(err, CategoryParserError::ExpectedToken(TokenKind::ParenClose)),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"(let ((x 1)) x y)", 15, 16);
        assert!(
            matches!(err, CategoryParserError::ExpectedToken(TokenKind::ParenClose)),
            "{err:?}"
        );
    }

    #[test]
    fn errors() {
        let err = assert_error::<TermParser<Printing>>(b")", 0, 1);
        assert!(matches!(err, CategoryParserError::ExpectedTerm), "{err:?}");

        let err = assert_error::<TermParser<Printing>>(b":kw", 0, 3);
        assert!(matches!(err, CategoryParserError::ExpectedTerm), "{err:?}");

        let err = assert_error::<TermParser<Printing>>(b"", 0, 0);
        assert!(matches!(err, CategoryParserError::ExpectedTerm), "{err:?}");

        // the operator position takes a symbol, a reserved binder, `_` or `(`
        let err = assert_error::<TermParser<Printing>>(b"(1 x)", 1, 2);
        assert!(matches!(err, CategoryParserError::ExpectedOperator), "{err:?}");

        let err = assert_error::<TermParser<Printing>>(b"()", 1, 2);
        assert!(matches!(err, CategoryParserError::ExpectedOperator), "{err:?}");

        // bad argument
        let err = assert_error::<TermParser<Printing>>(b"(f x :kw)", 5, 8);
        assert!(matches!(err, CategoryParserError::ExpectedTerm), "{err:?}");

        // EOF inside an application is a missing term
        let err = assert_error::<TermParser<Printing>>(b"(f x", 4, 4);
        assert!(matches!(err, CategoryParserError::ExpectedTerm), "{err:?}");

        // bad indexed identifier in a term
        let err = assert_error::<TermParser<Printing>>(b"(_ f)", 4, 5);
        assert!(matches!(err, CategoryParserError::RequiredIndices), "{err:?}");
    }

    /// Handler that only counts terms, so deep nesting does not build huge strings.
    #[derive(Default)]
    struct Counting {
        terms: usize,
    }

    impl SmtHandler for Counting {
        type Error = Infallible;
        type SExpr = ();
        type Attribute = ();
        type Sort = ();
        type Term = ();

        fn handle_sort(&mut self, _sort: SmtSort) -> Result<(), Infallible> {
            Ok(())
        }
        fn handle_term(&mut self, _term: SmtTerm<Self>) -> Result<(), Infallible> {
            self.terms += 1;
            Ok(())
        }
        fn start_let(&mut self, _bindings: Vec<(SmtSymbol, ())>) -> Result<(), Infallible> {
            Ok(())
        }
        fn end_let(&mut self, _term: ()) -> Result<(), Infallible> {
            Ok(())
        }
        fn handle_s_expr(&mut self, _expr: SmtSExpr<()>) -> Result<(), Infallible> {
            Ok(())
        }
        fn handle_attribute(
            &mut self,
            _name: SmtKeyword,
            _value: Option<SmtAttributeValue<Self>>,
        ) -> Result<(), Infallible> {
            Ok(())
        }
    }

    #[test]
    fn deep_nesting_does_not_overflow_the_stack() {
        // (f (f (f ... x ...))) with a depth far beyond what recursion would survive
        const DEPTH: usize = 200_000;
        let mut input = Vec::with_capacity(DEPTH * 4);
        for _ in 0..DEPTH {
            input.extend_from_slice(b"(f ");
        }
        input.push(b'x');
        input.extend(std::iter::repeat_n(b')', DEPTH));

        let mut handler = Counting::default();
        let mut parser = TermParser::<Counting>::init();
        let mut finished = false;
        for token in Lexer::lex_all(&input).expect("valid input") {
            match parser.progress(&mut handler, token) {
                Ok(ControlFlow::Continue(next)) => parser = next,
                Ok(ControlFlow::Break(())) => {
                    finished = true;
                    break;
                }
                Err(ParserError::ParserError(err)) => panic!("{err:?}"),
                Err(ParserError::HandlerError(err)) => match err {},
            }
        }
        assert!(finished);
        // every application plus the innermost x
        assert_eq!(handler.terms, DEPTH + 1);
    }
}
