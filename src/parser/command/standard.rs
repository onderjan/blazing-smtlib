use std::{marker::PhantomData, ops::ControlFlow};

use crate::{
    CommandHandler, SmtHandler, String8,
    parser::{
        ParserError, ParserOrHandlerError,
        category::{
            CategoryParser, attribute::AttributeParser, sort::SortParser, term::TermParser,
        },
    },
    token::Token,
};

pub trait Command<H: CommandHandler>
where
    Self: std::marker::Sized,
{
    fn init() -> Self;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>>;
}

pub enum CommandSetLogic<H: SmtHandler> {
    Start(PhantomData<H>),
    End(String8),
}

impl<H: CommandHandler> Command<H> for CommandSetLogic<H> {
    fn init() -> Self {
        Self::Start(PhantomData)
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>> {
        match self {
            CommandSetLogic::Start(_) => {
                if let Token::Symbol(logic) = token {
                    Ok(ControlFlow::Continue(Self::End(logic)))
                } else {
                    Err(ParserError::ExpectedSymbol.into())
                }
            }
            CommandSetLogic::End(logic) => {
                if matches!(token, Token::ParenClose) {
                    handler
                        .command_set_logic(logic.as_str())
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    Ok(ControlFlow::Break(()))
                } else {
                    Err(ParserError::ExpectedToken(Token::ParenClose).into())
                }
            }
        }
    }
}

pub enum CommandDeclareConst<H: SmtHandler> {
    Start,
    Name(String8),
    ParsingSort(String8, SortParser<H>),
    End(String8, H::Sort),
}

impl<H: CommandHandler> Command<H> for CommandDeclareConst<H> {
    fn init() -> Self {
        Self::Start
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>> {
        let result = match self {
            CommandDeclareConst::Start => {
                if let Token::Symbol(name) = token {
                    Self::Name(name)
                } else {
                    return Err(ParserError::ExpectedSymbol.into());
                }
            }
            CommandDeclareConst::Name(name) => {
                CommandDeclareConst::ParsingSort(name, SortParser::init())
            }

            CommandDeclareConst::ParsingSort(name, sort_parser) => {
                match sort_parser.progress(handler, token)? {
                    ControlFlow::Continue(sort_parser) => {
                        CommandDeclareConst::ParsingSort(name, sort_parser)
                    }

                    ControlFlow::Break(sort) => CommandDeclareConst::End(name, sort),
                }
            }
            CommandDeclareConst::End(name, sort) => {
                if matches!(token, Token::ParenClose) {
                    handler
                        .command_declare_const(name.as_str(), sort)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    return Ok(ControlFlow::Break(()));
                } else {
                    return Err(ParserError::ExpectedToken(Token::ParenClose).into());
                }
            }
        };
        Ok(ControlFlow::Continue(result))
    }
}

pub enum CommandAssert<H: SmtHandler> {
    Start,
    ParsingTerm(TermParser<H>),
    End(H::Term),
}

impl<H: CommandHandler> Command<H> for CommandAssert<H> {
    fn init() -> Self {
        Self::Start
    }

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

impl<H: CommandHandler> Command<H> for CommandCheckSat<H> {
    fn init() -> Self {
        Self {
            phantom: PhantomData,
        }
    }

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

impl<H: CommandHandler> Command<H> for CommandExit<H> {
    fn init() -> Self {
        Self {
            phantom: PhantomData,
        }
    }

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

impl<H: CommandHandler> Command<H> for CommandSetInfo<H> {
    fn init() -> Self {
        Self::Start
    }

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
