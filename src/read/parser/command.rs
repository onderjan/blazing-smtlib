use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtSymbol,
    read::parser::{
        ParserOrHandlerError,
        category::CategoryParser,
        command::standard::{
            CommandAssert, CommandCheckSat, CommandDeclareConst, CommandDeclareFun,
            CommandDefineFun, CommandExit, CommandSetInfo, CommandSetLogic,
        },
    },
    token::Token,
};

mod standard;

pub trait ParseCommand<H: CommandHandler + ?Sized> {
    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<CommandResult, ()>, ParserOrHandlerError<H>>;
}

pub enum NoCommandParser {}

impl<H: CommandHandler> ParseCommand<H> for NoCommandParser {
    fn progress(
        &mut self,
        _handler: &mut H,
        _token: Token,
    ) -> Result<ControlFlow<CommandResult, ()>, ParserOrHandlerError<H>> {
        match *self {}
    }
}

pub(crate) trait StandardCommand<H: CommandHandler> {
    type Parser: CategoryParser<H>;

    fn handle(
        handler: &mut H,
        result: <Self::Parser as CategoryParser<H>>::Result,
    ) -> Result<(), H::Error>;

    fn is_exit() -> bool {
        false
    }
}

pub(crate) enum CommandParser<H: CommandHandler> {
    SetLogic(StaticCommandParser<H, CommandSetLogic>),
    DeclareConst(StaticCommandParser<H, CommandDeclareConst>),
    DeclareFun(StaticCommandParser<H, CommandDeclareFun>),
    DefineFun(StaticCommandParser<H, CommandDefineFun>),
    Assert(StaticCommandParser<H, CommandAssert>),
    CheckSat(StaticCommandParser<H, CommandCheckSat>),
    Exit(StaticCommandParser<H, CommandExit>),
    SetInfo(StaticCommandParser<H, CommandSetInfo>),
    Nonstandard(H::NonstandardParser),
}

impl<H: CommandHandler> ParseCommand<H> for CommandParser<H> {
    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<CommandResult, ()>, ParserOrHandlerError<H>> {
        match self {
            Self::SetLogic(p) => p.progress(handler, token),
            Self::DeclareConst(p) => p.progress(handler, token),
            Self::DeclareFun(p) => p.progress(handler, token),
            Self::DefineFun(p) => p.progress(handler, token),
            Self::Assert(p) => p.progress(handler, token),
            Self::CheckSat(p) => p.progress(handler, token),
            Self::Exit(p) => p.progress(handler, token),
            Self::SetInfo(p) => p.progress(handler, token),
            Self::Nonstandard(p) => p.progress(handler, token),
        }
    }
}

pub(crate) struct StaticCommandParser<H: CommandHandler, C: StandardCommand<H>>(Option<C::Parser>);

impl<H: CommandHandler, C: StandardCommand<H>> StaticCommandParser<H, C> {
    pub fn new() -> Self {
        Self(Some(C::Parser::init()))
    }
}

impl<H: CommandHandler, C: StandardCommand<H>> ParseCommand<H> for StaticCommandParser<H, C> {
    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<CommandResult, ()>, ParserOrHandlerError<H>> {
        match self.0.take() {
            Some(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => {
                    self.0 = Some(parser);
                    Ok(ControlFlow::Continue(()))
                }
                ControlFlow::Break(result) => {
                    C::handle(handler, result).map_err(ParserOrHandlerError::HandlerError)?;
                    let command_result = if C::is_exit() {
                        CommandResult::Exit
                    } else {
                        CommandResult::EndCommand
                    };
                    Ok(ControlFlow::Break(command_result))
                }
            },
            None => panic!("Parser already consumed"),
        }
    }
}

pub enum CommandResult {
    EndCommand,
    Exit,
}

impl<H: CommandHandler> super::Parser<'_, H> {
    pub(super) fn start_command(
        &mut self,
        name: SmtSymbol,
    ) -> Result<CommandParser<H>, ParserOrHandlerError<H>> {
        Ok(match name.as_slice() {
            b"set-logic" => CommandParser::SetLogic(StaticCommandParser::new()),
            b"declare-const" => CommandParser::DeclareConst(StaticCommandParser::new()),
            b"declare-fun" => CommandParser::DeclareFun(StaticCommandParser::new()),
            b"define-fun" => CommandParser::DefineFun(StaticCommandParser::new()),
            b"assert" => CommandParser::Assert(StaticCommandParser::new()),
            b"check-sat" => CommandParser::CheckSat(StaticCommandParser::new()),
            b"exit" => CommandParser::Exit(StaticCommandParser::new()),
            b"set-info" => CommandParser::SetInfo(StaticCommandParser::new()),
            _ => CommandParser::Nonstandard(
                self.handler
                    .nonstandard_command(name)
                    .map_err(ParserOrHandlerError::HandlerError)?,
            ),
        })
    }
}
