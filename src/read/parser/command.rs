use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtSpan, SmtSymbolView,
    read::parser::{
        ParserError,
        category::CategoryParser,
        command::standard::{
            CommandAssert, CommandCheckSat, CommandDeclareConst, CommandDeclareFun,
            CommandDefineFun, CommandEcho, CommandExit, CommandGetInfo, CommandGetOption,
            CommandReset, CommandResetAssertions, CommandSetInfo, CommandSetLogic,
            CommandSetOption,
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
    ) -> Result<ControlFlow<CommandResult, ()>, ParserError<H::Error>>;
}

pub enum NoCommandParser {}

impl<H: CommandHandler> ParseCommand<H> for NoCommandParser {
    fn progress(
        &mut self,
        _handler: &mut H,
        _token: Token,
    ) -> Result<ControlFlow<CommandResult, ()>, ParserError<H::Error>> {
        match *self {}
    }
}

pub trait StandardCommand<H: CommandHandler> {
    type Parser: CategoryParser<H>;

    fn handle(
        handler: &mut H,
        result: <Self::Parser as CategoryParser<H>>::Result,
    ) -> Result<(), H::Error>;

    fn is_exit() -> bool {
        false
    }
}

pub enum CommandParser<H: CommandHandler> {
    SetLogic(StaticCommandParser<H, CommandSetLogic>),
    DeclareConst(StaticCommandParser<H, CommandDeclareConst>),
    DeclareFun(StaticCommandParser<H, CommandDeclareFun>),
    DefineFun(StaticCommandParser<H, CommandDefineFun>),
    Assert(StaticCommandParser<H, CommandAssert>),
    CheckSat(StaticCommandParser<H, CommandCheckSat>),
    Exit(StaticCommandParser<H, CommandExit>),
    SetInfo(StaticCommandParser<H, CommandSetInfo>),
    Echo(StaticCommandParser<H, CommandEcho>),
    GetOption(StaticCommandParser<H, CommandGetOption>),
    SetOption(StaticCommandParser<H, CommandSetOption>),
    GetInfo(StaticCommandParser<H, CommandGetInfo>),
    Reset(StaticCommandParser<H, CommandReset>),
    ResetAssertions(StaticCommandParser<H, CommandResetAssertions>),
    Nonstandard(H::NonstandardParser),
}

impl<H: CommandHandler> ParseCommand<H> for CommandParser<H> {
    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<CommandResult, ()>, ParserError<H::Error>> {
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
            Self::Echo(p) => p.progress(handler, token),
            Self::GetOption(p) => p.progress(handler, token),
            Self::SetOption(p) => p.progress(handler, token),
            Self::GetInfo(p) => p.progress(handler, token),
            Self::Reset(p) => p.progress(handler, token),
            Self::ResetAssertions(p) => p.progress(handler, token),
        }
    }
}

pub struct StaticCommandParser<H: CommandHandler, C: StandardCommand<H>> {
    parser: C::Parser,
    finished: bool,
}

impl<H: CommandHandler, C: StandardCommand<H>> StaticCommandParser<H, C> {
    pub fn new() -> Self {
        Self {
            parser: C::Parser::default(),
            finished: false,
        }
    }
}

impl<H: CommandHandler, C: StandardCommand<H>> Default for StaticCommandParser<H, C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler, C: StandardCommand<H>> ParseCommand<H> for StaticCommandParser<H, C> {
    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<CommandResult, ()>, ParserError<H::Error>> {
        if self.finished {
            panic!("cannot progress command parser that already finished");
        }

        let span = token.span();
        let ControlFlow::Break(result) = self.parser.progress(handler, token)? else {
            return Ok(ControlFlow::Continue(()));
        };

        match C::handle(handler, result) {
            Ok(()) => {
                self.finished = true;
                let command_result = if C::is_exit() {
                    CommandResult::Exit
                } else {
                    CommandResult::EndCommand
                };
                Ok(ControlFlow::Break(command_result))
            }
            Err(err) => Err(ParserError::handler_error(err, span)),
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
        name: SmtSymbolView<'_>,
        span: SmtSpan,
    ) -> Result<CommandParser<H>, ParserError<H::Error>> {
        Ok(match name.as_slice() {
            b"set-logic" => CommandParser::SetLogic(StaticCommandParser::new()),
            b"declare-const" => CommandParser::DeclareConst(StaticCommandParser::new()),
            b"declare-fun" => CommandParser::DeclareFun(StaticCommandParser::new()),
            b"define-fun" => CommandParser::DefineFun(StaticCommandParser::new()),
            b"assert" => CommandParser::Assert(StaticCommandParser::new()),
            b"check-sat" => CommandParser::CheckSat(StaticCommandParser::new()),
            b"exit" => CommandParser::Exit(StaticCommandParser::new()),
            b"set-info" => CommandParser::SetInfo(StaticCommandParser::new()),
            b"echo" => CommandParser::Echo(StaticCommandParser::new()),
            b"get-option" => CommandParser::GetOption(StaticCommandParser::new()),
            b"set-option" => CommandParser::SetOption(StaticCommandParser::new()),
            b"get-info" => CommandParser::GetInfo(StaticCommandParser::new()),
            b"reset" => CommandParser::Reset(StaticCommandParser::new()),
            b"reset-assertions" => CommandParser::ResetAssertions(StaticCommandParser::new()),
            _ => match self.handler.nonstandard_command(name) {
                Ok(parser) => CommandParser::Nonstandard(parser),
                Err(err) => return Err(ParserError::handler_error(err, span)),
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckStandardSyntax, SmtSpan, token::TokenKind};

    #[test]
    #[should_panic(expected = "cannot progress command parser that already finished")]
    fn progressing_a_finished_command_parser_panics() {
        let mut handler = CheckStandardSyntax;
        let mut parser: StaticCommandParser<CheckStandardSyntax, CommandCheckSat> =
            StaticCommandParser::new();

        // a check-sat command body is just the closing parenthesis,
        // so one token finishes the command
        let close = Token::new(TokenKind::ParenClose, SmtSpan::new_zero());
        let flow = parser
            .progress(&mut handler, close)
            .expect("check-sat closing parenthesis must parse");
        assert!(matches!(
            flow,
            ControlFlow::Break(CommandResult::EndCommand)
        ));

        // the command has finished; progressing the parser again is a usage error
        let close = Token::new(TokenKind::ParenClose, SmtSpan::new_zero());
        let _ = parser.progress(&mut handler, close);
    }
}
