use std::ops::ControlFlow;

use crate::{
    SmtApplication, SmtHandler, SmtQualifiedIdent, SmtSpecialConstant, SmtSymbol, SmtTerm,
    parser::{
        category::{CategoryParserErrorKind, handle_err},
        qualified_ident::QualifiedIdentParser,
    },
    read::parser::{ParserError, category::CategoryParser},
    token::{Reserved, Token, TokenKind, TokenType},
};

pub enum TermLevel<H: SmtHandler> {
    Application(SmtQualifiedIdent<H>, Vec<H::Term>),
    LetBinding(Vec<(SmtSymbol, H::Term)>, SmtSymbol),
    LetInner,
}

pub enum TermParserState<H: SmtHandler> {
    Start,
    Open,
    QualifiedIdent(QualifiedIdentParser<H>),
    ApplicationQualifiedIdent(QualifiedIdentParser<H>),
    ApplicationTerm(SmtQualifiedIdent<H>, Vec<H::Term>),
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

impl<H: SmtHandler> TermParser<H> {
    fn new() -> Self {
        TermParser {
            state: TermParserState::Start,
            levels: Vec::new(),
        }
    }
}

impl<H: SmtHandler> Default for TermParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for TermParser<H> {
    type Result = H::Term;

    fn init() -> Self {
        Self::new()
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Term, Self>, ParserError<H>> {
        let span = token.span();

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
                let term = handle_err(handler.end_let(term), span)?;
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
        let span = token.span();
        let mut levels = self.levels;
        let state = match self.state {
            TermParserState::Start => return Self::parse_term_start(levels, handler, token),
            TermParserState::Open => {
                return Ok(ControlFlow::Continue(Self::parse_term_open(levels, token)?));
            }
            TermParserState::QualifiedIdent(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => TermParserState::QualifiedIdent(parser),
                ControlFlow::Break(qualified_ident) => {
                    let term = SmtTerm::QualifiedIdent(qualified_ident);

                    let term = handle_err(handler.handle_term(term), span)?;
                    return Ok(ControlFlow::Break((levels, term)));
                }
            },
            TermParserState::ApplicationQualifiedIdent(parser) => {
                match parser.progress(handler, token)? {
                    ControlFlow::Continue(parser) => {
                        TermParserState::ApplicationQualifiedIdent(parser)
                    }
                    ControlFlow::Break(ident) => {
                        TermParserState::ApplicationTerm(ident, Vec::new())
                    }
                }
            }
            TermParserState::ApplicationTerm(function, args) => {
                if matches!(token.kind(), TokenKind::ParenClose) {
                    // this ends the application term
                    // it must have at least one argument
                    if args.is_empty() {
                        return Err(ParserError::category_error(
                            CategoryParserErrorKind::EmptyTermApplication,
                            span,
                        ));
                    }
                    let term = SmtTerm::Application(SmtApplication { function, args });

                    let term = handle_err(handler.handle_term(term), span)?;
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
                            return Err(ParserError::category_error(
                                CategoryParserErrorKind::EmptyLetBindings,
                                span,
                            ));
                        }

                        handle_err(handler.start_let(bindings), span)?;

                        levels.push(TermLevel::LetInner);
                        TermParserState::Start
                    }
                    _ => {
                        // expected open or close parenthesis
                        return Err(ParserError::category_error(
                            CategoryParserErrorKind::ExpectedToken(&[
                                TokenType::ParenOpen,
                                TokenType::ParenClose,
                            ]),
                            span,
                        ));
                    }
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
            TokenKind::Symbol(name) => {
                // a qualified identifier that is just a symbol
                let qualified_ident = SmtQualifiedIdent::new_simple(name);
                let term = handle_err(
                    handler.handle_term(SmtTerm::QualifiedIdent(qualified_ident)),
                    span,
                )?;

                Ok(ControlFlow::Break((levels, term)))
            }

            kind => {
                // handle special constants
                match parse_special_constant(Token::new(kind, span)) {
                    Ok(special_constant) => {
                        let term = handle_err(
                            handler.handle_term(SmtTerm::SpecialConstant(special_constant)),
                            span,
                        )?;
                        Ok(ControlFlow::Break((levels, term)))
                    }
                    Err(_token) => Err(ParserError::category_error(
                        CategoryParserErrorKind::ExpectedTerm,
                        span,
                    )),
                }
            }
        }
    }

    fn parse_term_open(levels: Vec<TermLevel<H>>, token: Token) -> Result<Self, ParserError<H>> {
        let span = token.span();
        let state = match token.into_kind() {
            TokenKind::Symbol(fn_name) => {
                // this is an application where the function identifier is just a symbol
                let fn_ident = SmtQualifiedIdent::new_simple(fn_name);
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
                // start a qualified ident parser after the underscore
                // (meaning the ident will be unqualified but indexed)
                TermParserState::QualifiedIdent(QualifiedIdentParser::after_underscore())
            }
            TokenKind::Reserved(Reserved::As) => {
                // this is actually a term composed of a qualified identifier
                // start a qualified ident parser after the 'as' reserved word
                // (meaning the ident will be qualified)
                TermParserState::QualifiedIdent(QualifiedIdentParser::after_as())
            }
            TokenKind::ParenOpen => {
                // this is an application where the function identifier is qualified or indexed
                // start a qualified ident parser after the parenthesis open
                TermParserState::ApplicationQualifiedIdent(QualifiedIdentParser::after_open_paren())
            }
            _ => {
                return Err(ParserError::category_error(
                    CategoryParserErrorKind::ExpectedOperator,
                    span,
                ));
            }
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
        Err(ParserError::category_error(
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen]),
            token.span(),
        ))
    }
}

fn expect_close_paren<H: SmtHandler>(token: Token) -> Result<(), ParserError<H>> {
    if matches!(token.kind(), TokenKind::ParenClose) {
        Ok(())
    } else {
        Err(ParserError::category_error(
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose]),
            token.span(),
        ))
    }
}

fn expect_symbol<H: SmtHandler>(token: Token) -> Result<SmtSymbol, ParserError<H>> {
    let span = token.span();
    if let TokenKind::Symbol(symbol) = token.into_kind() {
        Ok(symbol)
    } else {
        Err(ParserError::category_error(
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol]),
            span,
        ))
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
            parser::{
                ParserErrorKind,
                category::tests::{Printing, assert_error, parse_all, run},
            },
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
    fn qualified_identifiers() {
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(as x Bool)"),
            "(as x Bool)"
        );
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(as (_ bv5 8) (_ BitVec 8))"),
            "(as (_ bv5 8) (_ BitVec 8))"
        );
        // qualified identifier as an application argument
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(f (as x Bool) 1)"),
            "(f (as x Bool) 1)"
        );
    }

    #[test]
    fn application_of_qualified_function() {
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"((as f Bool) x)"),
            "((as f Bool) x)"
        );
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"((as (_ f 2) (_ BitVec 8)) x y)"),
            "((as (_ f 2) (_ BitVec 8)) x y)"
        );
    }

    #[test]
    fn empty_application_is_rejected() {
        // an application must have at least one argument
        let err = assert_error::<TermParser<Printing>>(b"(f)", 2, 3);
        assert!(
            matches!(err, CategoryParserErrorKind::EmptyTermApplication),
            "{err:?}"
        );
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
        assert!(
            matches!(err, CategoryParserErrorKind::EmptyLetBindings),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"(let x x)", 5, 6);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
            ),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"(let (x) x)", 6, 7);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[
                    TokenType::ParenOpen,
                    TokenType::ParenClose
                ])
            ),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"(let ((1 x)) x)", 7, 8);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
            ),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"(let ((x 1 2)) x)", 11, 12);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"(let ((x 1)) x y)", 15, 16);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
    }

    #[test]
    fn errors() {
        let err = assert_error::<TermParser<Printing>>(b")", 0, 1);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedTerm),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b":kw", 0, 3);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedTerm),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"", 0, 0);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedTerm),
            "{err:?}"
        );

        // the operator position takes a symbol, a reserved binder, `_` or `(`
        let err = assert_error::<TermParser<Printing>>(b"(1 x)", 1, 2);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedOperator),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"()", 1, 2);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedOperator),
            "{err:?}"
        );

        // bad argument
        let err = assert_error::<TermParser<Printing>>(b"(f x :kw)", 5, 8);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedTerm),
            "{err:?}"
        );

        // EOF inside an application is a missing term
        let err = assert_error::<TermParser<Printing>>(b"(f x", 4, 4);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedTerm),
            "{err:?}"
        );

        // bad indexed identifier in a term
        let err = assert_error::<TermParser<Printing>>(b"(_ f)", 4, 5);
        assert!(
            matches!(err, CategoryParserErrorKind::RequiredIndices),
            "{err:?}"
        );
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

        fn handle_sort(&mut self, _sort: SmtSort<Self>) -> Result<(), Infallible> {
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
                Err(err) => {
                    let span = err.span();
                    match err.into_kind() {
                        ParserErrorKind::Category(kind) => panic!("{kind:?} at {span:?}"),
                        // the `Counting` handler never fails
                        ParserErrorKind::Handler(err) => match err {},
                    }
                }
            }
        }
        assert!(finished);
        // every application plus the innermost x
        assert_eq!(handler.terms, DEPTH + 1);
    }
}
