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
    // from InnerType in the lexer
    EndOfFile,
}

/// TokenType but without End of File.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InnerType {
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
}

impl InnerType {
    fn into_type(self) -> TokenType {
        match self {
            InnerType::ParenOpen => TokenType::ParenOpen,
            InnerType::ParenClose => TokenType::ParenClose,
            InnerType::Numeral => TokenType::Numeral,
            InnerType::Decimal => TokenType::Decimal,
            InnerType::Hexadecimal => TokenType::Hexadecimal,
            InnerType::Binary => TokenType::Binary,
            InnerType::String => TokenType::String,
            InnerType::Keyword => TokenType::Keyword,
            InnerType::UnquotedSymbol => TokenType::UnquotedSymbol,
            InnerType::QuotedSymbol => TokenType::QuotedSymbol,
        }
    }
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
    pub fn from_token(token: Token<'a>, version: SmtVersion) -> Self {
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
    /// Entry where End of File is kept as None.
    ///
    /// This is for performance reasons: instead of having to
    /// overwrite the whole token when the referenced buffer
    /// is no longer available, we have to only overwrite
    /// the Option variant byte to None.
    entry: &'a Option<(InnerType, &'a [u8])>,
    span: &'a SmtSpan,
}

impl<'a> Token<'a> {
    #[inline]
    pub(crate) fn new(entry: &'a Option<(InnerType, &'a [u8])>, span: &'a SmtSpan) -> Token<'a> {
        Self { entry, span }
    }

    #[inline]
    pub fn ty(&self) -> TokenType {
        match self.entry {
            Some((ty, _)) => ty.into_type(),
            None => TokenType::EndOfFile,
        }
    }

    #[inline]
    pub fn content(&self) -> &'a [u8] {
        match self.entry {
            Some((_, content)) => content,
            None => &[],
        }
    }

    #[inline]
    pub fn span(&self) -> SmtSpan {
        *self.span
    }
}

/// A cursor into a batch of tokens, from which elements are consumed sequentially.
///
/// A parser reads a batch through a cursor: it can look at the
/// tokens ahead, consume them one at a time or several at once, look back at
/// what it consumed last, and tell how many tokens it has taken. However,
/// it is not guaranteed how many elements the batch will actually have,
/// so the lookahead is only useful for fast paths that fall back to
/// slow paths with the same behaviour if the lookahead is not available.
#[derive(Clone, Copy)]
pub struct TokenCursor<'a> {
    entries: &'a [Option<(InnerType, &'a [u8])>],
    spans: &'a [SmtSpan],
    next: usize,
}

impl<'a> TokenCursor<'a> {
    /// Returns a cursor at the start of the batch given as its entries and
    /// their spans, of equal length.
    #[inline]
    pub(crate) fn new(entries: &'a [Option<(InnerType, &'a [u8])>], spans: &'a [SmtSpan]) -> Self {
        debug_assert_eq!(entries.len(), spans.len());
        Self {
            entries,
            spans,
            next: 0,
        }
    }

    /// The token at `index` of the batch, if any.
    #[inline]
    fn at(&self, index: usize) -> Option<Token<'a>> {
        match (self.entries.get(index), self.spans.get(index)) {
            (Some(entry), Some(span)) => Some(Token::new(entry, span)),
            _ => None,
        }
    }

    /// Returns a cursor over a single token.
    ///
    /// This can be used for parsing one token using a cursor-parsing function.
    #[inline]
    pub fn single(token: Token<'a>) -> Self {
        Self::new(
            std::slice::from_ref(token.entry),
            std::slice::from_ref(token.span),
        )
    }

    /// Returns the next token (if any) without consuming it.
    #[inline]
    pub fn peek(&self) -> Option<Token<'a>> {
        self.at(self.next)
    }

    /// Returns the token `ahead` positions after the next one without consuming anything.
    ///
    /// `get(0)` is the next token, also available through `peek`.
    #[inline]
    pub fn get(&self, ahead: usize) -> Option<Token<'a>> {
        self.at(self.next + ahead)
    }

    /// Consumes the next token (if any).
    #[inline]
    pub fn take(&mut self) -> Option<Token<'a>> {
        let token = self.at(self.next)?;
        self.next += 1;
        Some(token)
    }

    /// Consumes the next `count` tokens.
    ///
    /// Behaves as if [`TokenCursor::take`] was called `count` times
    /// with the results discarded, stopping at the end of the cursor.
    #[inline]
    pub fn advance(&mut self, count: usize) {
        self.next = self.next.saturating_add(count).min(self.entries.len());
    }

    /// Returns the most recently consumed token, if any was consumed through
    /// this cursor.
    #[inline]
    pub fn last_consumed(&self) -> Option<Token<'a>> {
        self.at(self.next.checked_sub(1)?)
    }

    /// How many tokens have been consumed.
    #[inline]
    pub fn consumed(&self) -> usize {
        self.next
    }

    /// Whether every token has been consumed.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.next >= self.entries.len()
    }
}

/// Reserved words in SMT-LIB2, including standard command names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reserved {
    General(GeneralReserved),
    CommandName(CommandNameReserved),
}

/// Every reserved word with its classification.
const RESERVED_WORDS: [(&[u8], Reserved); 46] = [
    (b"as", Reserved::General(GeneralReserved::As)),
    (
        b"assert",
        Reserved::CommandName(CommandNameReserved::Assert),
    ),
    (b"BINARY", Reserved::General(GeneralReserved::Binary)),
    (
        b"check-sat-assuming",
        Reserved::CommandName(CommandNameReserved::CheckSatAssuming),
    ),
    (
        b"check-sat",
        Reserved::CommandName(CommandNameReserved::CheckSat),
    ),
    (b"DECIMAL", Reserved::General(GeneralReserved::Decimal)),
    (
        b"declare-const",
        Reserved::CommandName(CommandNameReserved::DeclareConst),
    ),
    (
        b"declare-datatype",
        Reserved::CommandName(CommandNameReserved::DeclareDatatype),
    ),
    (
        b"declare-datatypes",
        Reserved::CommandName(CommandNameReserved::DeclareDatatypes),
    ),
    (
        b"declare-fun",
        Reserved::CommandName(CommandNameReserved::DeclareFun),
    ),
    (
        b"declare-sort",
        Reserved::CommandName(CommandNameReserved::DeclareSort),
    ),
    (
        b"declare-sort-parameter",
        Reserved::CommandName(CommandNameReserved::DeclareSortParameter),
    ),
    (
        b"define-const",
        Reserved::CommandName(CommandNameReserved::DefineConst),
    ),
    (
        b"define-fun",
        Reserved::CommandName(CommandNameReserved::DefineFun),
    ),
    (
        b"define-fun-rec",
        Reserved::CommandName(CommandNameReserved::DefineFunRec),
    ),
    (
        b"define-funs-rec",
        Reserved::CommandName(CommandNameReserved::DefineFunsRec),
    ),
    (
        b"define-sort",
        Reserved::CommandName(CommandNameReserved::DefineSort),
    ),
    (b"echo", Reserved::CommandName(CommandNameReserved::Echo)),
    (b"exists", Reserved::General(GeneralReserved::Exists)),
    (b"exit", Reserved::CommandName(CommandNameReserved::Exit)),
    (b"forall", Reserved::General(GeneralReserved::Forall)),
    (b"!", Reserved::General(GeneralReserved::ExclamationMark)),
    (b"_", Reserved::General(GeneralReserved::Underscore)),
    (
        b"get-assertions",
        Reserved::CommandName(CommandNameReserved::GetAssertions),
    ),
    (
        b"get-assignment",
        Reserved::CommandName(CommandNameReserved::GetAssignment),
    ),
    (
        b"get-info",
        Reserved::CommandName(CommandNameReserved::GetInfo),
    ),
    (
        b"get-model",
        Reserved::CommandName(CommandNameReserved::GetModel),
    ),
    (
        b"get-option",
        Reserved::CommandName(CommandNameReserved::GetOption),
    ),
    (
        b"get-proof",
        Reserved::CommandName(CommandNameReserved::GetProof),
    ),
    (
        b"get-unsat-assumptions",
        Reserved::CommandName(CommandNameReserved::GetUnsatAssumptions),
    ),
    (
        b"get-unsat-core",
        Reserved::CommandName(CommandNameReserved::GetUnsatCore),
    ),
    (
        b"get-value",
        Reserved::CommandName(CommandNameReserved::GetValue),
    ),
    (
        b"HEXADECIMAL",
        Reserved::General(GeneralReserved::Hexadecimal),
    ),
    (b"lambda", Reserved::General(GeneralReserved::Lambda)),
    (b"let", Reserved::General(GeneralReserved::Let)),
    (b"match", Reserved::General(GeneralReserved::Match)),
    (b"NUMERAL", Reserved::General(GeneralReserved::Numeral)),
    (b"par", Reserved::General(GeneralReserved::Par)),
    (b"pop", Reserved::CommandName(CommandNameReserved::Pop)),
    (b"push", Reserved::CommandName(CommandNameReserved::Push)),
    (
        b"reset-assertions",
        Reserved::CommandName(CommandNameReserved::ResetAssertions),
    ),
    (b"reset", Reserved::CommandName(CommandNameReserved::Reset)),
    (
        b"set-info",
        Reserved::CommandName(CommandNameReserved::SetInfo),
    ),
    (
        b"set-logic",
        Reserved::CommandName(CommandNameReserved::SetLogic),
    ),
    (
        b"set-option",
        Reserved::CommandName(CommandNameReserved::SetOption),
    ),
    (b"STRING", Reserved::General(GeneralReserved::String)),
];

/// Number of slots of the reserved-word table.
const RESERVED_SLOTS: usize = 128;

/// Returns the slot in the reserved-word table corresponding to the symbol.
///
/// A perfect hash of the reserved words over their length and their first, last, and
/// middle byte: no two reserved words share a slot, which the construction of
/// [`RESERVED_TABLE`] checks at compile time. The multipliers were found by the
/// ignored test `search_reserved_hash_multipliers` in this module; if a reserved
/// word is added and the check fails, run it again for new ones.
#[inline(always)]
const fn reserved_slot(symbol: &[u8]) -> usize {
    let len = symbol.len();
    let (first, last, mid) = (
        symbol[0] as usize,
        symbol[len - 1] as usize,
        symbol[len / 2] as usize,
    );
    (first + last * 4 + len * 34 + mid * 54) % RESERVED_SLOTS
}

/// The empty word is used as a sentinel value for empty reserved-word table slots.
const EMPTY_WORD: &[u8] = &[];

/// The reserved words by slot.
static RESERVED_TABLE: [(&[u8], Reserved); RESERVED_SLOTS] = {
    let mut table = [(EMPTY_WORD, Reserved::General(GeneralReserved::Underscore)); RESERVED_SLOTS];
    let mut i = 0;
    while i < RESERVED_WORDS.len() {
        let (word, reserved) = RESERVED_WORDS[i];
        let slot = reserved_slot(word);
        assert!(
            table[slot].0.is_empty(),
            "the reserved-word hash must be perfect"
        );
        table[slot] = (word, reserved);
        i += 1;
    }
    table
};

impl Reserved {
    #[inline]
    pub fn from_symbol_opt(symbol: &String8) -> Option<Reserved> {
        Self::from_bytes_opt(symbol.as_slice())
    }

    #[inline]
    pub fn from_bytes_opt(symbol: &[u8]) -> Option<Reserved> {
        // make sure that the symbol is not an empty word,
        // which is a sentinel
        if symbol.is_empty() {
            return None;
        }
        // the slot holds a reserved word or a sentinel
        let (word, reserved) = RESERVED_TABLE[reserved_slot(symbol)];
        // if the symbol is equal to the reserved word, return it
        if word == symbol { Some(reserved) } else { None }
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
    fn handle_token(&mut self, token: Token) -> Result<(), TokenStop<Self::Error>>;

    /// Handles the tokens in a batch.
    ///
    /// Default implementation forwards to [`TokenHandler::handle_token`].
    /// Implementations that have to be fast should instead implement this
    /// function and call it from [`TokenHandler::handle_token`].
    #[inline]
    fn handle_tokens(
        &mut self,
        cursor: &mut TokenCursor<'_>,
    ) -> Result<(), TokenStop<Self::Error>> {
        while let Some(token) = cursor.take() {
            self.handle_token(token)?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokenStop<E> {
    /// Lex again from the end of the last consumed token.
    Relex,
    /// The handler failed at the token after the consumed ones.
    Error(E),
}

/// Mutable references over token handlers are token handlers.
impl<T: TokenHandler + ?Sized> TokenHandler for &mut T {
    type Error = T::Error;

    #[inline]
    fn handle_token(&mut self, token: Token) -> Result<(), TokenStop<Self::Error>> {
        (**self).handle_token(token)
    }

    #[inline]
    fn handle_tokens(
        &mut self,
        cursor: &mut TokenCursor<'_>,
    ) -> Result<(), TokenStop<Self::Error>> {
        (**self).handle_tokens(cursor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Multipliers of a candidate reserved-word hash, see `reserved_slot`.
    type Multipliers = (usize, usize, usize, usize);

    fn candidate_slot(word: &[u8], (a, b, c, d): Multipliers, slots: usize) -> usize {
        let len = word.len();
        let (first, last, mid) = (
            word[0] as usize,
            word[len - 1] as usize,
            word[len / 2] as usize,
        );
        (first * a + last * b + len * c + mid * d) % slots
    }

    /// Whether the multipliers give every reserved word its own slot.
    fn is_perfect(multipliers: Multipliers, slots: usize) -> bool {
        let mut used = vec![false; slots];
        RESERVED_WORDS.iter().all(|(word, _)| {
            let slot = candidate_slot(word, multipliers, slots);
            !std::mem::replace(&mut used[slot], true)
        })
    }

    /// Finds multipliers for `reserved_slot`, to be run when a reserved word is added
    /// and the compile-time check of `RESERVED_TABLE` fails:
    ///
    /// ```text
    /// cargo test --release --lib -- --ignored search_reserved_hash_multipliers --nocapture
    /// ```
    ///
    /// For each table size it prints the smallest multipliers (up to 63 each) under
    /// which no two reserved words share a slot, or that there are none.
    #[test]
    #[ignore]
    fn search_reserved_hash_multipliers() {
        const MAX_MULTIPLIER: usize = 63;
        println!("{} reserved words", RESERVED_WORDS.len());
        for slots in [64usize, 128, 256] {
            let range = 1..=MAX_MULTIPLIER;
            let found = range.clone().find_map(|a| {
                range.clone().find_map(|b| {
                    range.clone().find_map(|c| {
                        range
                            .clone()
                            .find(|&d| is_perfect((a, b, c, d), slots))
                            .map(|d| (a, b, c, d))
                    })
                })
            });
            match found {
                Some((a, b, c, d)) => {
                    println!(
                        "{slots} slots: (first * {a} + last * {b} + len * {c} + mid * {d}) % {slots}"
                    )
                }
                None => println!(
                    "{slots} slots: no perfect hash with multipliers up to {MAX_MULTIPLIER}"
                ),
            }
        }
    }

    #[test]
    fn the_landed_multipliers_are_perfect_and_match_the_search_form() {
        // the table's construction proves this at compile time; the test ties the
        // search's formula to the landed one, so the two cannot drift apart
        assert!(is_perfect((1, 4, 34, 54), RESERVED_SLOTS));
        for (word, _) in RESERVED_WORDS {
            assert_eq!(
                candidate_slot(word, (1, 4, 34, 54), RESERVED_SLOTS),
                reserved_slot(word),
                "slot of {:?}",
                String::from_utf8_lossy(word)
            );
        }
    }
}
