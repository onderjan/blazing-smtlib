use std::ops::ControlFlow;

use crate::{
    CommandHandler, Str8,
    parser::{
        ParserOrHandlerError,
        command::standard::{
            CommandAssert, CommandCheckSat, CommandDeclareConst, CommandDeclareFun, CommandExit,
            CommandParser, CommandSetInfo, CommandSetLogic,
        },
    },
    token::Token,
};

mod standard;

pub enum StandardCommand<H: CommandHandler> {
    SetLogic(CommandParser<H, CommandSetLogic>),
    DeclareConst(CommandParser<H, CommandDeclareConst>),
    DeclareFun(CommandParser<H, CommandDeclareFun>),
    Assert(CommandParser<H, CommandAssert>),
    CheckSat(CommandParser<H, CommandCheckSat>),
    SetInfo(CommandParser<H, CommandSetInfo>),
    Exit(CommandParser<H, CommandExit>),
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
            b"set-logic" => StandardCommand::SetLogic(CommandParser::new()),
            b"declare-const" => StandardCommand::DeclareConst(CommandParser::new()),
            b"declare-fun" => StandardCommand::DeclareFun(CommandParser::new()),
            b"assert" => StandardCommand::Assert(CommandParser::new()),
            b"check-sat" => StandardCommand::CheckSat(CommandParser::new()),
            b"exit" => StandardCommand::Exit(CommandParser::new()),
            b"set-info" => StandardCommand::SetInfo(CommandParser::new()),
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
            StandardCommand::DeclareFun(command) => command
                .progress(handler, token)?
                .map_continue(StandardCommand::DeclareFun),
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
