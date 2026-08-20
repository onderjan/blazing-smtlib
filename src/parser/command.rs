use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtHandler, Str8,
    parser::{
        ParserOrHandlerError,
        command::standard::{
            Command, CommandAssert, CommandCheckSat, CommandDeclareConst, CommandExit,
            CommandSetInfo, CommandSetLogic,
        },
    },
    token::Token,
};

mod standard;

pub enum StandardCommand<H: CommandHandler> {
    SetLogic(CommandSetLogic<H>),
    DeclareConst(CommandDeclareConst<H>),
    Assert(CommandAssert<H>),
    CheckSat(CommandCheckSat<H>),
    SetInfo(CommandSetInfo<H>),
    Exit(CommandExit<H>),
}

pub enum CommandBreak {
    EndCommand,
    Exit,
}

impl<H: CommandHandler> super::Parser<'_, H> {
    pub(super) fn start_command(
        &mut self,
        command_name: Str8,
    ) -> Result<StandardCommand<H>, ParserOrHandlerError<H>> {
        Ok(match command_name.bytes() {
            b"set-logic" => StandardCommand::SetLogic(CommandSetLogic::init()),
            b"declare-const" => StandardCommand::DeclareConst(CommandDeclareConst::init()),
            b"assert" => StandardCommand::Assert(CommandAssert::init()),
            b"check-sat" => StandardCommand::CheckSat(CommandCheckSat::init()),
            b"exit" => StandardCommand::Exit(CommandExit::init()),
            b"set-info" => StandardCommand::SetInfo(CommandSetInfo::init()),
            _ => todo!("Unknown command {:?}", command_name),
        })
    }
}

impl<H: CommandHandler> StandardCommand<H> {
    pub fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<CommandBreak, Self>, ParserOrHandlerError<H>> {
        let result = match self {
            StandardCommand::SetLogic(command) => command
                .progress(handler, token)?
                .map_continue(StandardCommand::SetLogic),
            StandardCommand::DeclareConst(command) => command
                .progress(handler, token)?
                .map_continue(StandardCommand::DeclareConst),
            StandardCommand::Assert(command) => command
                .progress(handler, token)?
                .map_continue(StandardCommand::Assert),
            StandardCommand::CheckSat(command) => command
                .progress(handler, token)?
                .map_continue(StandardCommand::CheckSat),
            StandardCommand::SetInfo(command) => command
                .progress(handler, token)?
                .map_continue(StandardCommand::SetInfo),
            StandardCommand::Exit(command) => {
                return Ok(command
                    .progress(handler, token)?
                    .map_continue(StandardCommand::Exit)
                    .map_break(|()| CommandBreak::Exit));
            }
        };

        Ok(result.map_break(|()| CommandBreak::EndCommand))
    }
}

/*
pub enum CommandProgress<H> {
    Continuation(Box<dyn CommandStage<H>>),
    EndCommand,
    Exit,
}

pub type CommandCallback<H, Y> =
    Box<dyn FnOnce(&mut H, Y) -> Result<CommandProgress<H>, <H as SmtHandler>::Error>>;

pub enum CommandAction<H: CommandHandler> {
    CloseParen(CommandCallback<H, ()>),
    Symbol(CommandCallback<H, H::Symbol>),
    Sort(CommandCallback<H, H::Sort>),
    Term(CommandCallback<H, H::Term>),
    Attribute(CommandCallback<H, H::Attribute>),
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
            b"check-sat" => Box::new(CommandCheckSat),
            b"exit" => Box::new(CommandExit),
            b"set-info" => Box::new(CommandSetInfo::new()),
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
                callback(self.handler, ()).map_err(ParserOrHandlerError::HandlerError)?
            }
            CommandAction::Symbol(callback) => {
                let symbol = self.parse_symbol(token)?;
                callback(self.handler, symbol).map_err(ParserOrHandlerError::HandlerError)?
            }
            CommandAction::Sort(callback) => return parse_sort(self.handler, callback, token),
            CommandAction::Term(callback) => return parse_term(self.handler, callback, token),
            CommandAction::Attribute(callback) => {
                return parse_attribute(self.handler, callback, token);
            }
        };

        Ok(progress_state(progress))
    }
}
*/
