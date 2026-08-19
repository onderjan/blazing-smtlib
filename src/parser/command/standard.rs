use crate::{
    CommandHandler, SmtHandler,
    parser::command::{CommandAction, CommandProgress, CommandStage},
};

pub struct CommandSetLogic<H: SmtHandler> {
    logic: Option<H::Symbol>,
}

impl<H: SmtHandler> CommandSetLogic<H> {
    pub fn new() -> Self {
        Self { logic: None }
    }
}

impl<H: CommandHandler> CommandStage<H> for CommandSetLogic<H> {
    fn action(self: Box<Self>) -> CommandAction<H> {
        match self.logic {
            None => {
                // read logic
                CommandAction::Symbol(Box::new(|_handler, symbol| {
                    Ok(CommandProgress::Continuation(Box::new(CommandSetLogic {
                        logic: Some(symbol),
                    })))
                }))
            }
            Some(logic) => {
                // done on close paren
                CommandAction::CloseParen(Box::new(|handler, ()| {
                    handler.command_set_logic(logic)?;
                    Ok(CommandProgress::EndCommand)
                }))
            }
        }
    }
}

pub enum CommandDeclareConst<H: SmtHandler> {
    Start,
    Name(H::Symbol),
    Full(H::Symbol, H::Sort),
}

impl<H: SmtHandler> CommandDeclareConst<H> {
    pub fn new() -> Self {
        Self::Start
    }
}

impl<H: CommandHandler> CommandStage<H> for CommandDeclareConst<H> {
    fn action(self: Box<Self>) -> CommandAction<H> {
        match *self {
            CommandDeclareConst::Start => {
                // read name symbol
                CommandAction::Symbol(Box::new(|_handler, symbol| {
                    Ok(CommandProgress::Continuation(Box::new(
                        CommandDeclareConst::Name(symbol),
                    )))
                }))
            }
            CommandDeclareConst::Name(name) => {
                // read sort
                CommandAction::Sort(Box::new(|_handler, sort| {
                    Ok(CommandProgress::Continuation(Box::new(
                        CommandDeclareConst::Full(name, sort),
                    )))
                }))
            }
            CommandDeclareConst::Full(name, sort) => {
                // done on close paren
                CommandAction::CloseParen(Box::new(|handler, ()| {
                    handler.command_declare_const(name, sort)?;
                    Ok(CommandProgress::EndCommand)
                }))
            }
        }
    }
}

pub enum CommandAssert<H: SmtHandler> {
    Start,
    Term(H::Term),
}

impl<H: SmtHandler> CommandAssert<H> {
    pub fn new() -> Self {
        Self::Start
    }
}

impl<H: CommandHandler> CommandStage<H> for CommandAssert<H> {
    fn action(self: Box<Self>) -> CommandAction<H> {
        match *self {
            CommandAssert::Start => {
                // read assert term
                CommandAction::Term(Box::new(|_handler, term| {
                    Ok(CommandProgress::Continuation(Box::new(
                        CommandAssert::Term(term),
                    )))
                }))
            }
            CommandAssert::Term(term) => {
                // done on close paren
                CommandAction::CloseParen(Box::new(|handler, ()| {
                    handler.command_assert(term)?;
                    Ok(CommandProgress::EndCommand)
                }))
            }
        }
    }
}

pub struct CommandCheckSat;

impl<H: CommandHandler> CommandStage<H> for CommandCheckSat {
    fn action(self: Box<Self>) -> CommandAction<H> {
        // done on close paren
        CommandAction::CloseParen(Box::new(|handler, ()| {
            handler.command_check_sat()?;
            Ok(CommandProgress::EndCommand)
        }))
    }
}

pub struct CommandExit;

impl<H: CommandHandler> CommandStage<H> for CommandExit {
    fn action(self: Box<Self>) -> CommandAction<H> {
        // done on close paren
        CommandAction::CloseParen(Box::new(|handler, ()| {
            handler.command_exit()?;
            Ok(CommandProgress::Exit)
        }))
    }
}

pub enum CommandSetInfo<H: SmtHandler> {
    Start,
    Attribute(H::Attribute),
}

impl<H: SmtHandler> CommandSetInfo<H> {
    pub fn new() -> Self {
        Self::Start
    }
}

impl<H: CommandHandler> CommandStage<H> for CommandSetInfo<H> {
    fn action(self: Box<Self>) -> CommandAction<H> {
        match *self {
            CommandSetInfo::Start => {
                // read assert term
                CommandAction::Attribute(Box::new(|_handler, term| {
                    Ok(CommandProgress::Continuation(Box::new(
                        CommandSetInfo::Attribute(term),
                    )))
                }))
            }
            CommandSetInfo::Attribute(attribute) => {
                // done on close paren
                CommandAction::CloseParen(Box::new(|handler, ()| {
                    handler.command_set_info(attribute)?;
                    Ok(CommandProgress::EndCommand)
                }))
            }
        }
    }
}
