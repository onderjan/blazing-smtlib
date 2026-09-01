use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtFunctionSignature,
    read::parser::{
        CategoryParser, CloseParenParser, KeywordParser, ParserError, StringParser, SymbolParser,
        category::{
            ClosedAttributeParser, ClosedParser, MultipleParser, OpenClosedParser, PairParser,
            SortParser, TermParser,
        },
        command::StandardCommand,
        handle_err,
    },
    token::Token,
};

macro_rules! standard_command {
    ($command:ident, $parser:ty, |$handler:ident, $result:pat_param| $handle:expr) => {
        pub struct $command;

        impl<H: CommandHandler> StandardCommand<H> for $command {
            type Parser = $parser;

            fn handle(
                $handler: &mut H,
                $result: <$parser as CategoryParser<H>>::Result,
            ) -> Result<(), H::Error> {
                $handle
            }
        }
    };
}

// standard parsers used, handler called at the end
standard_command!(CommandSetLogic, ClosedParser<H, SymbolParser>,
    |handler, logic| handler.command_set_logic(logic));
standard_command!(CommandDeclareConst,
    ClosedParser<H, PairParser<H, SymbolParser, SortParser<H>>>,
    |handler, (name,sort)| handler.command_declare_const(name, sort)
);
standard_command!(CommandDeclareFun,
    ClosedParser<H, PairParser<H, SymbolParser,
        PairParser<H, MultipleParser<H, SortParser<H>>, SortParser<H>>>>,
    |handler, (name, (param_sorts, result_sort))|
        handler.command_declare_fun(name, param_sorts, result_sort));
standard_command!(CommandAssert, ClosedParser<H, TermParser<H>>,
    |handler, term| handler.command_assert(term)
);
standard_command!(CommandCheckSat, CloseParenParser, |handler, ()| handler
    .command_check_sat());
standard_command!(
    CommandSetInfo,
    ClosedAttributeParser<H>,
    |handler, attribute| handler.command_set_info(attribute)
);
standard_command!(CommandEcho, ClosedParser<H, StringParser>,
    |handler, value| handler.command_echo(value));
standard_command!(CommandGetOption, ClosedParser<H, KeywordParser>,
    |handler, option| handler.command_get_option(option));
standard_command!(
    CommandSetOption,
    ClosedAttributeParser<H>,
    |handler, option| handler.command_set_option(option)
);
standard_command!(CommandGetInfo, ClosedParser<H, KeywordParser>,
    |handler, keyword| handler.command_get_info(keyword));
standard_command!(CommandReset, CloseParenParser, |handler, ()| handler
    .command_reset());
standard_command!(CommandResetAssertions, CloseParenParser, |handler, ()| {
    handler.command_reset_assertions()
});

// the handler is called by the custom parser
standard_command!(CommandDefineFun, ClosedParser<H, DefineFunParser<H>>,
    |_handler, ()| Ok(()));

type SortedVarParser<H> = OpenClosedParser<H, PairParser<H, SymbolParser, SortParser<H>>>;
type DefineFunSignatureParser<H> = PairParser<
    H,
    SymbolParser,
    PairParser<H, MultipleParser<H, SortedVarParser<H>>, SortParser<H>>,
>;

pub enum DefineFunParser<H: CommandHandler> {
    Signature(DefineFunSignatureParser<H>),
    Body(TermParser<H>),
}

impl<H: CommandHandler> DefineFunParser<H> {
    pub fn new() -> Self {
        Self::Signature(DefineFunSignatureParser::new())
    }
}

impl<H: CommandHandler> Default for DefineFunParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler> CategoryParser<H> for DefineFunParser<H> {
    type Result = ();

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserError<H>> {
        let span = token.span();
        let result = match self {
            DefineFunParser::Signature(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => DefineFunParser::Signature(parser),
                ControlFlow::Break((name, (params, result_sort))) => {
                    let signature = SmtFunctionSignature {
                        name,
                        params,
                        result_sort,
                    };

                    handle_err(handler.start_define_fun(signature), span)?;
                    DefineFunParser::Body(TermParser::new())
                }
            },
            DefineFunParser::Body(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => DefineFunParser::Body(parser),
                ControlFlow::Break(term) => {
                    handle_err(handler.end_define_fun(term), span)?;
                    return Ok(ControlFlow::Break(()));
                }
            },
        };
        Ok(ControlFlow::Continue(result))
    }
}

pub struct CommandExit;

impl<H: CommandHandler> StandardCommand<H> for CommandExit {
    type Parser = CloseParenParser;

    fn handle(_handler: &mut H, _unit: ()) -> Result<(), <H>::Error> {
        // do not call anything, exit is handled within parsing
        Ok(())
    }

    fn is_exit() -> bool {
        true
    }
}

// TODO: fix tests
/*
#[cfg(test)]
mod tests {
    use crate::{
        SmtAttributeValue, SmtFunctionSignature, SmtHandler, SmtKeyword, SmtSExpr, SmtSort,
        SmtSpecialConstant, SmtStringContent, SmtSymbol, SmtTerm,
        read::parser::{
            CategoryParserErrorKind, NoCommandParser, ParserErrorKind,
            tests::{assert_error_span, assert_parser_error, parse_with},
        },
        token::TokenType,
    };

    use super::*;

    /// Handler that resolves body identifiers against the parameters of the
    /// define-fun currently in progress, marking resolved ones as `[name]`.
    /// The resolution succeeding proves that `start_define_fun` delivers the
    /// signature before the body terms are constructed.
    #[derive(Default)]
    struct Resolving {
        /// Callbacks received, in order.
        events: Vec<String>,
        /// Parameter names of the define-fun in progress, empty outside one.
        params: Vec<String>,
    }

    fn text(bytes: &[u8]) -> String {
        String::from_utf8(bytes.to_vec()).expect("test inputs are ASCII")
    }

    impl SmtHandler for Resolving {
        type Error = String;
        type SExpr = ();
        type Attribute = ();
        type Sort = String;
        type Term = String;

        fn handle_sort(&mut self, sort: SmtSort<Self>) -> Result<String, String> {
            let name = text(sort.ident.name.as_slice());
            Ok(if sort.applied.is_empty() {
                name
            } else {
                format!("({} {})", name, sort.applied.join(" "))
            })
        }

        fn handle_term(&mut self, term: SmtTerm<Self>) -> Result<String, String> {
            Ok(match term {
                SmtTerm::SpecialConstant(constant) => match constant {
                    SmtSpecialConstant::Numeral(numeral) => text(numeral.as_slice()),
                    _ => "<constant>".into(),
                },
                SmtTerm::QualifiedIdent(qualified_ident) => {
                    let name = text(qualified_ident.ident.name.as_slice());
                    if self.params.contains(&name) {
                        format!("[{name}]")
                    } else {
                        name
                    }
                }
                SmtTerm::Application(application) => {
                    let function = text(application.function.ident.name.as_slice());
                    format!("({} {})", function, application.args.join(" "))
                }
            })
        }

        fn start_let(&mut self, _bindings: Vec<(SmtSymbol, String)>) -> Result<(), String> {
            Ok(())
        }

        fn end_let(&mut self, term: String) -> Result<String, String> {
            Ok(term)
        }

        fn handle_s_expr(&mut self, _expr: SmtSExpr<Self>) -> Result<(), String> {
            Ok(())
        }

        fn handle_attribute(
            &mut self,
            _name: SmtKeyword,
            _value: Option<SmtAttributeValue<Self>>,
        ) -> Result<(), String> {
            Ok(())
        }
    }

    impl CommandHandler for Resolving {
        type NonstandardParser = NoCommandParser;

        fn nonstandard_command(
            &mut self,
            name: SmtSymbol,
        ) -> Result<Self::NonstandardParser, String> {
            Err(format!("nonstandard command {:?}", text(name.as_slice())))
        }

        fn command_echo(&mut self, _value: SmtStringContent) -> Result<(), String> {
            Ok(())
        }
        fn command_get_option(&mut self, _option: SmtKeyword) -> Result<(), String> {
            Ok(())
        }
        fn command_set_option(&mut self, _option: ()) -> Result<(), String> {
            Ok(())
        }
        fn command_get_info(&mut self, _keyword: SmtKeyword) -> Result<(), String> {
            Ok(())
        }
        fn command_set_info(&mut self, _attribute: ()) -> Result<(), String> {
            Ok(())
        }
        fn command_set_logic(&mut self, _logic: SmtSymbol) -> Result<(), String> {
            Ok(())
        }
        fn command_declare_const(&mut self, _name: SmtSymbol, _sort: String) -> Result<(), String> {
            Ok(())
        }
        fn command_declare_fun(
            &mut self,
            _name: SmtSymbol,
            _param_sorts: Vec<String>,
            _result_sort: String,
        ) -> Result<(), String> {
            Ok(())
        }

        fn command_assert(&mut self, term: String) -> Result<(), String> {
            self.events.push(format!("assert {term}"));
            Ok(())
        }

        fn command_check_sat(&mut self) -> Result<(), String> {
            self.events.push("check-sat".into());
            Ok(())
        }

        fn command_reset(&mut self) -> Result<(), String> {
            Ok(())
        }
        fn command_reset_assertions(&mut self) -> Result<(), String> {
            Ok(())
        }
        fn command_exit(&mut self) -> Result<(), String> {
            Ok(())
        }

        fn start_define_fun(
            &mut self,
            signature: SmtFunctionSignature<Self>,
        ) -> Result<(), String> {
            let name = text(signature.name.as_slice());
            if name == "forbidden" {
                return Err("forbidden function name".into());
            }
            let params: Vec<String> = signature
                .params
                .iter()
                .map(|(param, sort)| format!("({} {})", text(param.as_slice()), sort))
                .collect();
            self.events.push(format!(
                "start {name} ({}) {}",
                params.join(" "),
                signature.result_sort
            ));
            self.params = signature
                .params
                .iter()
                .map(|(param, _)| text(param.as_slice()))
                .collect();
            Ok(())
        }

        fn end_define_fun(&mut self, term: String) -> Result<(), String> {
            if term == "boom" {
                return Err("exploding body".into());
            }
            self.events.push(format!("end {term}"));
            self.params.clear();
            Ok(())
        }
    }

    #[track_caller]
    fn parse_resolving(handler: &mut Resolving, input: &[u8]) {
        parse_with(handler, input)
            .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    }

    #[test]
    fn params_resolve_while_body_is_parsed() {
        let mut handler = Resolving::default();
        parse_resolving(
            &mut handler,
            b"(define-fun inc ((x Int)) Int (+ x 1)) (assert x) (check-sat)",
        );
        assert_eq!(
            handler.events,
            [
                // the signature arrives before any body term
                "start inc ((x Int)) Int",
                // `x` was resolved as a parameter while the body was constructed
                "end (+ [x] 1)",
                // the parameter scope ended with the define-fun
                "assert x",
                "check-sat",
            ]
        );
    }

    #[test]
    fn zero_params_and_applied_result_sort() {
        let mut handler = Resolving::default();
        parse_resolving(&mut handler, b"(define-fun c () (Array Int Bool) zero)");
        assert_eq!(handler.events, ["start c () (Array Int Bool)", "end zero"]);
    }

    #[test]
    fn signature_errors_point_at_offending_token() {
        // the function name must be a symbol
        let err = assert_parser_error(b"(define-fun 1 () Int 5)", 12, 13);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
            ),
            "{err:?}"
        );
        // each sorted var must be parenthesized
        let err = assert_parser_error(b"(define-fun f (x Int) Int x)", 15, 16);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
            ),
            "{err:?}"
        );
        // the body term is required
        let err = assert_parser_error(b"(define-fun f () Int)", 20, 21);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedTerm),
            "{err:?}"
        );
        // exactly one body term is allowed
        let err = assert_parser_error(b"(define-fun f () Int 5 6)", 23, 24);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
    }

    #[track_caller]
    fn assert_handler_error(input: &[u8], message: &str, start: u64, end: u64) -> Resolving {
        let mut handler = Resolving::default();
        let err = parse_with(&mut handler, input).expect_err("expected a handler error");
        assert_error_span(&err, start, end);
        match err.into_kind() {
            ParserErrorKind::Handler(handler_message) => assert_eq!(handler_message, message),
            ParserErrorKind::Category(kind) => panic!("expected handler error, got {kind:?}"),
        }
        handler
    }

    #[test]
    fn start_define_fun_error_points_at_last_signature_token() {
        let handler = assert_handler_error(
            b"(define-fun forbidden () Int 5)",
            "forbidden function name",
            25,
            28,
        );
        assert!(handler.events.is_empty());
    }

    #[test]
    fn end_define_fun_error_points_at_last_body_token() {
        let handler = assert_handler_error(b"(define-fun f () Int boom)", "exploding body", 21, 25);
        assert_eq!(handler.events, ["start f () Int"]);
    }

    #[test]
    fn trivial_command_errors_point_at_offending_token() {
        // echo takes a string literal
        let err = assert_parser_error(b"(echo 1)", 6, 7);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::String])
            ),
            "{err:?}"
        );
        // exactly one string literal
        let err = assert_parser_error(b"(echo \"hi\" \"there\")", 11, 18);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
        // get-option and get-info take a keyword, not a symbol or string
        let err = assert_parser_error(b"(get-option opt)", 12, 15);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword])
            ),
            "{err:?}"
        );
        let err = assert_parser_error(b"(get-info \"x\")", 10, 13);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword])
            ),
            "{err:?}"
        );
        // set-option requires an attribute, which starts with a keyword
        let err = assert_parser_error(b"(set-option)", 11, 12);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword])
            ),
            "{err:?}"
        );
        // reset and reset-assertions take no arguments
        let err = assert_parser_error(b"(reset x)", 7, 8);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
        let err = assert_parser_error(b"(reset-assertions x)", 18, 19);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
    }
}
*/
