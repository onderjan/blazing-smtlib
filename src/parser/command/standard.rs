use std::{marker::PhantomData, ops::ControlFlow};

use crate::{
    CommandHandler, SmtHandler,
    parser::{
        ParserError, ParserOrHandlerError,
        category::{
            CategoryParser, ClosedParser, MultipleParser, PairParser, SymbolParser,
            attribute::AttributeParser, sort::SortParser, term::TermParser,
        },
    },
    token::Token,
};

pub trait Command<H: CommandHandler>
where
    Self: std::marker::Sized,
{
    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>>;
}

pub struct CommandSetLogic<H: SmtHandler>(ClosedParser<H, SymbolParser>);

impl<H: CommandHandler> CommandSetLogic<H> {
    pub fn init() -> Self {
        Self(ClosedParser::init())
    }
}

impl<H: CommandHandler> Command<H> for CommandSetLogic<H> {
    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>> {
        Ok(self
            .0
            .progress_with_callback(handler, token, |handler, logic| {
                handler.command_set_logic(logic)
            })?
            .map_continue(Self))
    }
}

pub struct CommandDeclareConst<H: SmtHandler>(
    ClosedParser<H, PairParser<H, SymbolParser, SortParser>>,
);

impl<H: CommandHandler> CommandDeclareConst<H> {
    pub fn init() -> Self {
        Self(ClosedParser::init())
    }
}

impl<H: CommandHandler> Command<H> for CommandDeclareConst<H> {
    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>> {
        Ok(self
            .0
            .progress_with_callback(handler, token, |handler, (name, sort)| {
                handler.command_declare_const(name, sort)
            })?
            .map_continue(Self))
    }
}

#[allow(clippy::type_complexity)]
pub struct CommandDeclareFun<H: SmtHandler>(
    ClosedParser<
        H,
        PairParser<H, SymbolParser, PairParser<H, MultipleParser<H, SortParser>, SortParser>>,
    >,
);

impl<H: CommandHandler> CommandDeclareFun<H> {
    pub fn init() -> Self {
        Self(ClosedParser::init())
    }
}

impl<H: CommandHandler> Command<H> for CommandDeclareFun<H> {
    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>> {
        Ok(self
            .0
            .progress_with_callback(
                handler,
                token,
                |handler, (name, (param_sorts, result_sort))| {
                    handler.command_declare_fun(name, param_sorts, result_sort)
                },
            )?
            .map_continue(Self))
    }
}

pub enum CommandAssert<H: SmtHandler> {
    Start,
    ParsingTerm(TermParser<H>),
    End(H::Term),
}

impl<H: CommandHandler> CommandAssert<H> {
    pub fn init() -> Self {
        Self::Start
    }
}
impl<H: CommandHandler> Command<H> for CommandAssert<H> {
    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>> {
        match self {
            CommandAssert::Start => {
                let term_parser = TermParser::init();
                let result = match term_parser.progress(handler, token)? {
                    ControlFlow::Continue(term_parser) => CommandAssert::ParsingTerm(term_parser),
                    ControlFlow::Break(term) => CommandAssert::End(term),
                };
                Ok(ControlFlow::Continue(result))
            }
            CommandAssert::ParsingTerm(term_parser) => {
                let result = match term_parser.progress(handler, token)? {
                    ControlFlow::Continue(term_parser) => CommandAssert::ParsingTerm(term_parser),
                    ControlFlow::Break(term) => CommandAssert::End(term),
                };
                Ok(ControlFlow::Continue(result))
            }
            CommandAssert::End(term) => {
                if matches!(token, Token::ParenClose) {
                    handler
                        .command_assert(term)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    Ok(ControlFlow::Break(()))
                } else {
                    Err(ParserError::ExpectedToken(Token::ParenClose).into())
                }
            }
        }
    }
}

pub struct CommandCheckSat<H: SmtHandler> {
    phantom: PhantomData<H>,
}

impl<H: CommandHandler> CommandCheckSat<H> {
    pub fn init() -> Self {
        Self {
            phantom: PhantomData,
        }
    }
}

impl<H: CommandHandler> Command<H> for CommandCheckSat<H> {
    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>> {
        if matches!(token, Token::ParenClose) {
            handler
                .command_check_sat()
                .map_err(ParserOrHandlerError::HandlerError)?;
            Ok(ControlFlow::Break(()))
        } else {
            Err(ParserError::ExpectedToken(Token::ParenClose).into())
        }
    }
}

pub struct CommandExit<H: SmtHandler> {
    phantom: PhantomData<H>,
}

impl<H: CommandHandler> CommandExit<H> {
    pub fn init() -> Self {
        Self {
            phantom: PhantomData,
        }
    }
}

impl<H: CommandHandler> Command<H> for CommandExit<H> {
    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>> {
        if matches!(token, Token::ParenClose) {
            handler
                .command_exit()
                .map_err(ParserOrHandlerError::HandlerError)?;
            Ok(ControlFlow::Break(()))
        } else {
            Err(ParserError::ExpectedToken(Token::ParenClose).into())
        }
    }
}

pub enum CommandSetInfo<H: SmtHandler> {
    Start,
    ParsingAttribute(AttributeParser<H>),
    End(H::Attribute),
}

impl<H: CommandHandler> CommandSetInfo<H> {
    pub fn init() -> Self {
        Self::Start
    }
}

impl<H: CommandHandler> Command<H> for CommandSetInfo<H> {
    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>> {
        enum Progress<H: SmtHandler> {
            Parser(AttributeParser<H>),
            CloseParen(H::Attribute),
        }

        let progress = match self {
            CommandSetInfo::Start => Progress::Parser(AttributeParser::init()),
            CommandSetInfo::ParsingAttribute(attribute_parser) => {
                Progress::Parser(attribute_parser)
            }
            CommandSetInfo::End(attribute) => Progress::CloseParen(attribute),
        };

        let (token, attribute) = match progress {
            Progress::Parser(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => {
                    return Ok(ControlFlow::Continue(Self::ParsingAttribute(parser)));
                }
                ControlFlow::Break(parser_result) => match parser_result.returned_token {
                    Some(token) => (token, parser_result.attribute),
                    None => {
                        return Ok(ControlFlow::Continue(Self::End(parser_result.attribute)));
                    }
                },
            },
            Progress::CloseParen(attribute) => (token, attribute),
        };

        // process close parenthesis
        expect_close_parenthesis::<H>(token)?;
        handler
            .command_set_info(attribute)
            .map_err(ParserOrHandlerError::HandlerError)?;
        Ok(ControlFlow::Break(()))
    }
}

fn expect_close_parenthesis<H: SmtHandler>(token: Token) -> Result<(), ParserOrHandlerError<H>> {
    if matches!(token, Token::ParenClose) {
        Ok(())
    } else {
        Err(ParserError::ExpectedToken(Token::ParenClose).into())
    }
}
