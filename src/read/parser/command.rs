use std::ops::ControlFlow;

use crate::{
    CommandHandler, String8View,
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

pub trait Command<H: CommandHandler> {
    type Parser: CategoryParser<H>;

    fn handle(
        handler: &mut H,
        result: <Self::Parser as CategoryParser<H>>::Result,
    ) -> Result<(), H::Error>;

    fn is_exit() -> bool {
        false
    }
}

pub trait ParseCommand<H: CommandHandler> {
    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<CommandResult, ()>, ParserOrHandlerError<H>>;
}

pub struct StaticCommandParser<H: CommandHandler, C: Command<H>>(Option<C::Parser>);

impl<H: CommandHandler, C: Command<H>> StaticCommandParser<H, C> {
    pub fn new() -> Self {
        Self(Some(C::Parser::init()))
    }
}

impl<H: CommandHandler, C: Command<H>> ParseCommand<H> for StaticCommandParser<H, C> {
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

pub struct DynamicCommandParser<H: CommandHandler>(Box<dyn ParseCommand<H>>);

impl<H: CommandHandler> DynamicCommandParser<H> {
    pub fn new<C: Command<H> + 'static>() -> Self {
        Self(Box::new(StaticCommandParser::<H, C>::new()))
    }
}

impl<H: CommandHandler> ParseCommand<H> for DynamicCommandParser<H> {
    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<CommandResult, ()>, ParserOrHandlerError<H>> {
        self.0.progress(handler, token)
    }
}

pub enum CommandResult {
    EndCommand,
    Exit,
}

impl<H: CommandHandler> super::Parser<'_, H> {
    pub(super) fn start_command(
        &mut self,
        command_name: String8View,
    ) -> Result<DynamicCommandParser<H>, ParserOrHandlerError<H>> {
        Ok(match command_name.as_slice() {
            b"set-logic" => DynamicCommandParser::new::<CommandSetLogic>(),
            b"declare-const" => DynamicCommandParser::new::<CommandDeclareConst>(),
            b"declare-fun" => DynamicCommandParser::new::<CommandDeclareFun>(),
            b"define-fun" => DynamicCommandParser::new::<CommandDefineFun>(),
            b"assert" => DynamicCommandParser::new::<CommandAssert>(),
            b"check-sat" => DynamicCommandParser::new::<CommandCheckSat>(),
            b"exit" => DynamicCommandParser::new::<CommandExit>(),
            b"set-info" => DynamicCommandParser::new::<CommandSetInfo>(),
            _ => todo!("Unknown command {:?}", command_name),
        })
    }
}
