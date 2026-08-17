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
                CommandAction::CloseParen(Box::new(|handler| {
                    handler.command_set_logic(logic)?;
                    Ok(CommandProgress::End)
                }))
            }
        }
    }
}
