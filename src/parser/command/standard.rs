use std::{marker::PhantomData, ops::ControlFlow};

use crate::{
    CommandHandler, SmtHandler, String8,
    parser::{ParserError, ParserOrHandlerError},
    token::Token,
};

pub trait Command<H: CommandHandler> {
    fn init() -> Self;

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<()>, ParserOrHandlerError<H>>;
}

pub enum CommandSetLogic<H: SmtHandler> {
    Start(PhantomData<H>),
    Logic(String8),
}

impl<H: CommandHandler> Command<H> for CommandSetLogic<H> {
    fn init() -> Self {
        Self::Start(PhantomData)
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<()>, ParserOrHandlerError<H>> {
        match self {
            CommandSetLogic::Start(_) => {
                if let Token::Symbol(logic) = token {
                    *self = Self::Logic(logic);
                    Ok(ControlFlow::Continue(()))
                } else {
                    Err(ParserError::ExpectedSymbol.into())
                }
            }
            CommandSetLogic::Logic(logic) => {
                if matches!(token, Token::ParenClose) {
                    handler.command_set_logic(logic.as_str());
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
    Full(String8, H::Sort),
}

impl<H: CommandHandler> Command<H> for CommandDeclareConst<H> {
    fn init() -> Self {
        Self::Start
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<()>, ParserOrHandlerError<H>> {
        match self {
            CommandDeclareConst::Start => {
                if let Token::Symbol(name) = token {
                    *self = Self::Name(name);
                    Ok(ControlFlow::Continue(()))
                } else {
                    Err(ParserError::ExpectedSymbol.into())
                }
            }
            CommandDeclareConst::Name(name) => {
                todo!("Parse sort")
            }
            CommandDeclareConst::Full(name, sort) => {
                if matches!(token, Token::ParenClose) {
                    todo!("Handle sort")
                    /*
                    handler.command_declare_const(name.as_str(), sort);
                    Ok(ControlFlow::Break(()))
                    */
                } else {
                    Err(ParserError::ExpectedToken(Token::ParenClose).into())
                }
            }
        }
    }
}

pub enum CommandAssert<H: SmtHandler> {
    Start,
    Term(H::Term),
}

impl<H: CommandHandler> Command<H> for CommandAssert<H> {
    fn init() -> Self {
        Self::Start
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<()>, ParserOrHandlerError<H>> {
        match self {
            CommandAssert::Start => {
                todo!("Parse sort")
                /*
                if let Token::Symbol(logic) = token {
                    *self = Self::Term(term);
                    Ok(ControlFlow::Continue(()))
                } else {
                    Err(ParserError::ExpectedSymbol.into())
                }*/
            }
            CommandAssert::Term(term) => {
                todo!("Handle term")
                /*if matches!(token, Token::ParenClose) {
                    handler.command_assert(term);
                    Ok(ControlFlow::Break(()))
                } else {
                    Err(ParserError::ExpectedToken(Token::ParenClose).into())
                }*/
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
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<()>, ParserOrHandlerError<H>> {
        if matches!(token, Token::ParenClose) {
            handler.command_check_sat();
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
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<()>, ParserOrHandlerError<H>> {
        if matches!(token, Token::ParenClose) {
            handler.command_exit();
            Ok(ControlFlow::Break(()))
        } else {
            Err(ParserError::ExpectedToken(Token::ParenClose).into())
        }
    }
}

pub enum CommandSetInfo<H: SmtHandler> {
    Start,
    Attribute(H::Attribute),
}

impl<H: CommandHandler> Command<H> for CommandSetInfo<H> {
    fn init() -> Self {
        Self::Start
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<()>, ParserOrHandlerError<H>> {
        match self {
            CommandSetInfo::Start => {
                todo!("Parse attribute")
                /*
                  if let Token::Symbol(logic) = token {
                    *self = Self::Logic(logic);
                    Ok(ControlFlow::Continue(()))
                } else {
                    Err(ParserError::ExpectedSymbol.into())
                }
                */
            }
            CommandSetInfo::Attribute(attribute) => {
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
