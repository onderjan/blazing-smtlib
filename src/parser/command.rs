use std::ops::ControlFlow;

use crate::{
    CommandHandler, Str8,
    parser::{
        ParserOrHandlerError,
        command::standard::{
            Command, CommandAssert, CommandCheckSat, CommandDeclareConst, CommandDeclareFun,
            CommandDefineFun, CommandExit, CommandParser, CommandSetInfo, CommandSetLogic,
        },
    },
    token::Token,
};

mod standard;

pub enum StandardCommand<H: CommandHandler> {
    SetLogic(CommandParser<H, CommandSetLogic>),
    DeclareConst(CommandParser<H, CommandDeclareConst>),
    DeclareFun(CommandParser<H, CommandDeclareFun>),
    DefineFun(CommandParser<H, CommandDefineFun>),
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
            b"define-fun" => StandardCommand::DefineFun(CommandParser::new()),
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
        match self {
            StandardCommand::SetLogic(command) => {
                progress(command, handler, token, StandardCommand::SetLogic)
            }
            StandardCommand::DeclareConst(command) => {
                progress(command, handler, token, StandardCommand::DeclareConst)
            }
            StandardCommand::DeclareFun(command) => {
                progress(command, handler, token, StandardCommand::DeclareFun)
            }
            StandardCommand::DefineFun(command) => {
                progress(command, handler, token, StandardCommand::DefineFun)
            }
            StandardCommand::Assert(command) => {
                progress(command, handler, token, StandardCommand::Assert)
            }
            StandardCommand::CheckSat(command) => {
                progress(command, handler, token, StandardCommand::CheckSat)
            }
            StandardCommand::SetInfo(command) => {
                progress(command, handler, token, StandardCommand::SetInfo)
            }
            StandardCommand::Exit(command) => {
                Ok(progress(command, handler, token, StandardCommand::Exit)?
                    .map_break(|_| CommandBreak::Exit))
            }
        }
    }
}

fn progress<H: CommandHandler, C: Command<H>>(
    command: CommandParser<H, C>,
    handler: &mut H,
    token: Token,
    map: fn(CommandParser<H, C>) -> StandardCommand<H>,
) -> Result<ControlFlow<CommandBreak, StandardCommand<H>>, ParserOrHandlerError<H>> {
    Ok(command
        .progress(handler, token)?
        .map_continue(map)
        .map_break(|()| CommandBreak::EndCommand))
}
