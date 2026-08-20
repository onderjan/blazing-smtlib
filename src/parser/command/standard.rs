use std::{marker::PhantomData, ops::ControlFlow};

use crate::{
    CommandHandler, SmtHandler, String8,
    parser::{
        ParserError, ParserOrHandlerError,
        category::{sort::SortParser, term::TermParser},
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
                CommandDeclareConst::ParsingSort(name, SortParser::new())
            }

            CommandDeclareConst::ParsingSort(name, mut sort_parser) => {
                match sort_parser.progress(handler, token)? {
                    ControlFlow::Continue(()) => {
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
                let mut term_parser = TermParser::new();
                let result = term_parser.progress(handler, token)?;
                let result = match result {
                    ControlFlow::Continue(()) => CommandAssert::ParsingTerm(term_parser),
                    ControlFlow::Break(term) => CommandAssert::End(term),
                };
                Ok(ControlFlow::Continue(result))
            }
            CommandAssert::ParsingTerm(mut term_parser) => {
                let result = term_parser.progress(handler, token)?;
                let result = match result {
                    ControlFlow::Continue(()) => CommandAssert::ParsingTerm(term_parser),
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
        match self {
            CommandSetInfo::Start => {
                todo!("Parse attribute")
            }
            CommandSetInfo::End(attribute) => {
                todo!("Handle attribute")
                /*if matches!(token, Token::ParenClose) {
                    handler.command_set_info(attribute);
                    Ok(ControlFlow::Break(()))
                } else {
                    Err(ParserError::ExpectedToken(Token::ParenClose).into())
                }*/
            }
        }
    }
}
