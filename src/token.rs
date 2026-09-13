use crate::{
    SmtBinDigitsView, SmtDecimalView, SmtHexDigitsView, SmtKeywordView, SmtNumeralView, SmtSpan,
    SmtStringContentView, SmtSymbolView, string::String8,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenType {
    ParenOpen,
    ParenClose,
    Numeral,
    Decimal,
    Hexadecimal,
    Binary,
    String,
    Keyword,
    UnquotedSymbol,
    QuotedSymbol,
    // PERFORMANCE: leave EOF last for easy construction
    // from a similar enum without EOF in the lexer
    EndOfFile,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind<'a> {
    ParenOpen,
    ParenClose,
    Numeral(SmtNumeralView<'a>),
    Decimal(SmtDecimalView<'a>),
    Hexadecimal(SmtHexDigitsView<'a>),
    Binary(SmtBinDigitsView<'a>),
    String(SmtStringContentView<'a>),
    Keyword(SmtKeywordView<'a>),
    Symbol(SmtSymbolView<'a>),
    Reserved(Reserved),
    EndOfFile,
}

/// Version of the SMT-LIB standard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtVersion {
    V2_7,
}

impl<'a> TokenKind<'a> {
    /// Construct the token kind from the token and version.
    #[inline]
    pub fn from_token(token: &Token<'a>, version: SmtVersion) -> Self {
        let content = token.content();
        match token.ty() {
            TokenType::ParenOpen => TokenKind::ParenOpen,
            TokenType::ParenClose => TokenKind::ParenClose,
            TokenType::Numeral => TokenKind::Numeral(SmtNumeralView::new_unchecked(content)),
            TokenType::Decimal => TokenKind::Decimal(SmtDecimalView::new_unchecked(content)),
            TokenType::Hexadecimal => {
                TokenKind::Hexadecimal(SmtHexDigitsView::new_unchecked(content))
            }
            TokenType::Binary => TokenKind::Binary(SmtBinDigitsView::new_unchecked(content)),
            TokenType::UnquotedSymbol => {
                // process reserved words
                // TODO: multiple versions
                match version {
                    SmtVersion::V2_7 => {
                        match Reserved::from_bytes_opt(content) {
                            Some(reserved) => {
                                // reserved word, not a symbol
                                TokenKind::Reserved(reserved)
                            }
                            None => TokenKind::Symbol(SmtSymbolView::new_unchecked(content)),
                        }
                    }
                }
            }
            TokenType::QuotedSymbol => TokenKind::Symbol(SmtSymbolView::new_unchecked(content)),
            TokenType::String => TokenKind::String(SmtStringContentView::new_unchecked(content)),
            TokenType::Keyword => TokenKind::Keyword(SmtKeywordView::new_unchecked(content)),
            TokenType::EndOfFile => TokenKind::EndOfFile,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token<'a> {
    ty: TokenType,
    content: &'a [u8],
    span: SmtSpan,
}

impl<'a> Token<'a> {
    #[inline]
    pub(crate) fn new(ty: TokenType, content: &'a [u8], span: SmtSpan) -> Token<'a> {
        Self { ty, content, span }
    }

    #[inline]
    pub fn ty(&self) -> TokenType {
        self.ty
    }

    #[inline]
    pub fn content(&self) -> &'a [u8] {
        self.content
    }

    #[inline]
    pub fn span(&self) -> SmtSpan {
        self.span
    }
}

/// Reserved words in SMT-LIB2, including standard command names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reserved {
    General(GeneralReserved),
    CommandName(CommandNameReserved),
}

impl Reserved {
    #[inline]
    pub fn from_symbol_opt(symbol: &String8) -> Option<Reserved> {
        Self::from_bytes_opt(symbol.as_slice())
    }

    #[inline]
    pub fn from_bytes_opt(symbol: &[u8]) -> Option<Reserved> {
        match GeneralReserved::from_bytes_opt(symbol) {
            Some(general) => Some(Reserved::General(general)),
            None => CommandNameReserved::from_bytes_opt(symbol).map(Reserved::CommandName),
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            Reserved::General(general) => general.as_str(),
            Reserved::CommandName(command_name) => command_name.as_str(),
        }
    }

    /// Whether the reserved word is the name of a standard command.
    #[inline]
    pub fn is_command_name(&self) -> bool {
        matches!(self, Reserved::CommandName(_))
    }
}

/// General reserved words of the SMT-LIB2 grammar.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeneralReserved {
    Binary,
    Decimal,
    Hexadecimal,
    Numeral,
    String,
    Underscore,
    ExclamationMark,
    As,
    Lambda,
    Let,
    Exists,
    Forall,
    Match,
    Par,
}

impl GeneralReserved {
    #[inline]
    pub fn from_bytes_opt(symbol: &[u8]) -> Option<GeneralReserved> {
        Some(match symbol {
            b"BINARY" => GeneralReserved::Binary,
            b"DECIMAL" => GeneralReserved::Decimal,
            b"HEXADECIMAL" => GeneralReserved::Hexadecimal,
            b"NUMERAL" => GeneralReserved::Numeral,
            b"STRING" => GeneralReserved::String,
            b"_" => GeneralReserved::Underscore,
            b"!" => GeneralReserved::ExclamationMark,
            b"as" => GeneralReserved::As,
            b"lambda" => GeneralReserved::Lambda,
            b"let" => GeneralReserved::Let,
            b"exists" => GeneralReserved::Exists,
            b"forall" => GeneralReserved::Forall,
            b"match" => GeneralReserved::Match,
            b"par" => GeneralReserved::Par,
            _ => return None,
        })
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            GeneralReserved::Binary => "BINARY",
            GeneralReserved::Decimal => "DECIMAL",
            GeneralReserved::Hexadecimal => "HEXADECIMAL",
            GeneralReserved::Numeral => "NUMERAL",
            GeneralReserved::String => "STRING",
            GeneralReserved::Underscore => "_",
            GeneralReserved::ExclamationMark => "!",
            GeneralReserved::As => "as",
            GeneralReserved::Lambda => "lambda",
            GeneralReserved::Let => "let",
            GeneralReserved::Exists => "exists",
            GeneralReserved::Forall => "forall",
            GeneralReserved::Match => "match",
            GeneralReserved::Par => "par",
        }
    }
}

/// Reserved words naming standard SMT-LIB2 commands.
///
/// Standard SMT-LIB2 commands are reserved words.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommandNameReserved {
    Assert,
    CheckSat,
    CheckSatAssuming,
    DeclareConst,
    DeclareDatatype,
    DeclareDatatypes,
    DeclareFun,
    DeclareSort,
    DeclareSortParameter,
    DefineConst,
    DefineFun,
    DefineFunRec,
    DefineFunsRec,
    DefineSort,
    Echo,
    Exit,
    GetAssertions,
    GetAssignment,
    GetInfo,
    GetModel,
    GetOption,
    GetProof,
    GetUnsatAssumptions,
    GetUnsatCore,
    GetValue,
    Pop,
    Push,
    Reset,
    ResetAssertions,
    SetInfo,
    SetLogic,
    SetOption,
}

impl CommandNameReserved {
    #[inline]
    pub fn from_bytes_opt(symbol: &[u8]) -> Option<CommandNameReserved> {
        Some(match symbol {
            b"assert" => CommandNameReserved::Assert,
            b"check-sat" => CommandNameReserved::CheckSat,
            b"check-sat-assuming" => CommandNameReserved::CheckSatAssuming,
            b"declare-const" => CommandNameReserved::DeclareConst,
            b"declare-datatype" => CommandNameReserved::DeclareDatatype,
            b"declare-datatypes" => CommandNameReserved::DeclareDatatypes,
            b"declare-fun" => CommandNameReserved::DeclareFun,
            b"declare-sort" => CommandNameReserved::DeclareSort,
            b"declare-sort-parameter" => CommandNameReserved::DeclareSortParameter,
            b"define-const" => CommandNameReserved::DefineConst,
            b"define-fun" => CommandNameReserved::DefineFun,
            b"define-fun-rec" => CommandNameReserved::DefineFunRec,
            b"define-funs-rec" => CommandNameReserved::DefineFunsRec,
            b"define-sort" => CommandNameReserved::DefineSort,
            b"echo" => CommandNameReserved::Echo,
            b"exit" => CommandNameReserved::Exit,
            b"get-assertions" => CommandNameReserved::GetAssertions,
            b"get-assignment" => CommandNameReserved::GetAssignment,
            b"get-info" => CommandNameReserved::GetInfo,
            b"get-model" => CommandNameReserved::GetModel,
            b"get-option" => CommandNameReserved::GetOption,
            b"get-proof" => CommandNameReserved::GetProof,
            b"get-unsat-assumptions" => CommandNameReserved::GetUnsatAssumptions,
            b"get-unsat-core" => CommandNameReserved::GetUnsatCore,
            b"get-value" => CommandNameReserved::GetValue,
            b"pop" => CommandNameReserved::Pop,
            b"push" => CommandNameReserved::Push,
            b"reset" => CommandNameReserved::Reset,
            b"reset-assertions" => CommandNameReserved::ResetAssertions,
            b"set-info" => CommandNameReserved::SetInfo,
            b"set-logic" => CommandNameReserved::SetLogic,
            b"set-option" => CommandNameReserved::SetOption,
            _ => return None,
        })
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            CommandNameReserved::Assert => "assert",
            CommandNameReserved::CheckSat => "check-sat",
            CommandNameReserved::CheckSatAssuming => "check-sat-assuming",
            CommandNameReserved::DeclareConst => "declare-const",
            CommandNameReserved::DeclareDatatype => "declare-datatype",
            CommandNameReserved::DeclareDatatypes => "declare-datatypes",
            CommandNameReserved::DeclareFun => "declare-fun",
            CommandNameReserved::DeclareSort => "declare-sort",
            CommandNameReserved::DeclareSortParameter => "declare-sort-parameter",
            CommandNameReserved::DefineConst => "define-const",
            CommandNameReserved::DefineFun => "define-fun",
            CommandNameReserved::DefineFunRec => "define-fun-rec",
            CommandNameReserved::DefineFunsRec => "define-funs-rec",
            CommandNameReserved::DefineSort => "define-sort",
            CommandNameReserved::Echo => "echo",
            CommandNameReserved::Exit => "exit",
            CommandNameReserved::GetAssertions => "get-assertions",
            CommandNameReserved::GetAssignment => "get-assignment",
            CommandNameReserved::GetInfo => "get-info",
            CommandNameReserved::GetModel => "get-model",
            CommandNameReserved::GetOption => "get-option",
            CommandNameReserved::GetProof => "get-proof",
            CommandNameReserved::GetUnsatAssumptions => "get-unsat-assumptions",
            CommandNameReserved::GetUnsatCore => "get-unsat-core",
            CommandNameReserved::GetValue => "get-value",
            CommandNameReserved::Pop => "pop",
            CommandNameReserved::Push => "push",
            CommandNameReserved::Reset => "reset",
            CommandNameReserved::ResetAssertions => "reset-assertions",
            CommandNameReserved::SetInfo => "set-info",
            CommandNameReserved::SetLogic => "set-logic",
            CommandNameReserved::SetOption => "set-option",
        }
    }
}

/// A sequential handler of tokens.
pub trait TokenHandler {
    type Error;

    /// Sequentially handles one token.
    fn handle_token(&mut self, token: &Token) -> Result<(), Self::Error>;
}

/// Mutable references over token handlers are token handlers.
impl<T: TokenHandler + ?Sized> TokenHandler for &mut T {
    type Error = T::Error;

    #[inline]
    fn handle_token(&mut self, token: &Token) -> Result<(), Self::Error> {
        (**self).handle_token(token)
    }
}
