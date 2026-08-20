use std::ops::ControlFlow;

use crate::{
    CommandHandler, Str8,
    parser::{
        ParserOrHandlerError,
        command::standard::{
            Command, CommandAssert, CommandCheckSat, CommandDeclareConst, CommandDeclareFun,
            CommandExit, CommandSetInfo, CommandSetLogic,
        },
    },
    token::Token,
};

mod standard;

pub enum StandardCommand<H: CommandHandler> {
    SetLogic(CommandSetLogic<H>),
    DeclareConst(CommandDeclareConst<H>),
    DeclareFun(CommandDeclareFun<H>),
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
            b"declare-fun" => StandardCommand::DeclareFun(CommandDeclareFun::init()),
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
