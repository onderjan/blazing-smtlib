use crate::{
    CommandHandler, SmtHandler, Str8,
    parser::{
        ParserError, ParserOrHandlerError, ParserState,
        command::standard::{CommandAssert, CommandDeclareConst, CommandSetLogic},
        progress_state,
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

pub type CommandActionTerm<H> = Box<
    dyn FnOnce(
        &mut H,
        <H as SmtHandler>::Term,
    ) -> Result<CommandProgress<H>, <H as SmtHandler>::Error>,
>;

pub enum CommandAction<H: CommandHandler> {
    CloseParen(CommandActionCloseParen<H>),
    Symbol(CommandActionSymbol<H>),
    Sort(CommandActionSort<H>),
    Term(CommandActionTerm<H>),
}

pub trait CommandStage<H: CommandHandler> {
    fn action(self: Box<Self>) -> CommandAction<H>;
}

impl<H: CommandHandler> super::Parser<'_, H> {
    pub(super) fn start_command(
        &mut self,
        command_name: Str8,
    ) -> Result<Box<dyn CommandStage<H>>, ParserOrHandlerError<H>> {
        Ok(match command_name.bytes() {
            b"set-logic" => Box::new(CommandSetLogic::new()),
            b"declare-const" => Box::new(CommandDeclareConst::new()),
            b"assert" => Box::new(CommandAssert::new()),
            _ => todo!("Unknown command {:?}", command_name),
        })
    }

    pub(super) fn progress_command(
        &mut self,
        stage: Box<dyn CommandStage<H> + 'static>,
        token: Token,
    ) -> Result<ParserState<H>, ParserOrHandlerError<H>> {
        let progress = match stage.action() {
            CommandAction::CloseParen(callback) => {
                if !matches!(token, Token::ParenClose) {
                    return Err(ParserOrHandlerError::ParserError(
                        ParserError::ExpectedToken(Token::ParenClose),
                    ));
                }
                callback(self.handler).map_err(ParserOrHandlerError::HandlerError)?
            }
            CommandAction::Symbol(callback) => {
                let symbol = self.parse_symbol(token)?;
                callback(self.handler, symbol).map_err(ParserOrHandlerError::HandlerError)?
            }
            CommandAction::Sort(callback) => return self.parse_sort(callback, token),
            CommandAction::Term(callback) => return self.parse_term(callback, token),
        };

        Ok(progress_state(progress))
    }
}
