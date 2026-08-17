use crate::{
    CommandHandler, SmtHandler, Str8,
    parser::{
        ParserError, ParserOrHandlerError,
        command::standard::{CommandDeclareConst, CommandSetLogic},
    },
    token::Token,
};

mod standard;

pub enum CommandProgress<H> {
    Continuation(Box<dyn CommandStage<H>>),
    End,
}

pub type CommandActionCloseParen<H> =
    Box<dyn FnOnce(&mut H) -> Result<CommandProgress<H>, <H as SmtHandler>::Error>>;

pub type CommandActionSymbol<H> = Box<
    dyn FnOnce(
        &mut H,
        <H as SmtHandler>::Symbol,
    ) -> Result<CommandProgress<H>, <H as SmtHandler>::Error>,
>;

pub type CommandActionSort<H> = Box<
    dyn FnOnce(
        &mut H,
        <H as SmtHandler>::Sort,
    ) -> Result<CommandProgress<H>, <H as SmtHandler>::Error>,
>;

pub enum CommandAction<H: CommandHandler> {
    CloseParen(CommandActionCloseParen<H>),
    Symbol(CommandActionSymbol<H>),
    Sort(CommandActionSort<H>),
}

pub trait CommandStage<H: CommandHandler> {
    fn action(self: Box<Self>) -> CommandAction<H>;
}

impl<H: CommandHandler> super::Parser<'_, H> {
    pub fn start_command(
        &mut self,
        command_name: Str8,
    ) -> Result<Box<dyn CommandStage<H>>, ParserOrHandlerError<H>> {
        Ok(match command_name.bytes() {
            b"set-logic" => Box::new(CommandSetLogic::new()),
            b"declare-const" => Box::new(CommandDeclareConst::new()),
            _ => todo!("Unknown command {:?}", command_name),
        })
    }

    pub fn progress_command(
        &mut self,
        stage: Box<dyn CommandStage<H> + 'static>,
        token: Token,
    ) -> Result<CommandProgress<H>, ParserOrHandlerError<H>> {
        match stage.action() {
            CommandAction::CloseParen(callback) => {
                if !matches!(token, Token::ParenClose) {
                    return Err(ParserOrHandlerError::ParserError(
                        ParserError::ExpectedToken(Token::ParenClose),
                    ));
                }
                callback(self.handler)
            }
            CommandAction::Symbol(callback) => {
                let Token::Symbol(symbol) = token else {
                    return Err(ParserError::ExpectedSymbol.into());
                };
                let symbol = self
                    .handler
                    .handle_symbol(symbol.as_str())
                    .map_err(ParserOrHandlerError::HandlerError)?;
                callback(self.handler, symbol)
            }
            CommandAction::Sort(callback) => todo!("Parse sort"),
        }
        .map_err(ParserOrHandlerError::HandlerError)
    }
}
