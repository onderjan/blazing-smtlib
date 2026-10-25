//! The 1:1 check: a handler that prints every call back as SMT-LIB text,
//! and a comparison of the token sequences of the input and the printed text.
//!
//! The handler calls are meant to determine the input apart from whitespace
//! and comments. If they do, printing what the calls describe gives the same
//! tokens as the input, up to and including a top-level `(exit)`, after which
//! the input is discarded. Both sides are folded into a digest token by token,
//! so no file is held in memory as a whole; on a mismatch the file is lexed
//! again to find the first differing token.

use std::{
    convert::Infallible,
    fs::File,
    hash::{DefaultHasher, Hasher},
    io::{BufRead, BufReader},
    ops::ControlFlow,
    path::Path,
    sync::mpsc::{Receiver, SyncSender, sync_channel},
};

use blazing_smtlib::{
    SmtCommandHandler, SmtHandler, SmtNonstandardCommandError, SmtReadError, SmtVersion,
    grammar::{
        SmtAttributeValue, SmtConstructors, SmtFunctionSignature, SmtFunctionSignatures, SmtIdent,
        SmtIndex, SmtMatchCases, SmtMultiple, SmtNamedValues, SmtPattern, SmtQuantifierKind,
        SmtSExpr, SmtSimplePattern, SmtSort, SmtSortArities, SmtSpecialConstant, SmtSymbols,
        SmtTerm,
    },
    lexer::{SmtLexer, SmtLexerCursor},
    lexicon::{SmtKeyword, SmtNumeral, SmtStringContent, SmtSymbol},
    read_smt_file,
    token::{SmtConsume, SmtConsumeFrom, SmtCursor, SmtSyntaxToken},
};

/// Printed text is lexed in pieces of about this size, cut between commands.
const FLUSH_SIZE: usize = 1 << 20;

// --- token digests ---

/// Writes the text of a token as it appears in SMT-LIB, nothing for the end of input.
fn token_text(token: &SmtSyntaxToken<'_>, out: &mut Vec<u8>) {
    match token {
        SmtSyntaxToken::ParenOpen => out.push(b'('),
        SmtSyntaxToken::ParenClose => out.push(b')'),
        SmtSyntaxToken::Numeral(numeral) => out.extend_from_slice(numeral.as_slice()),
        SmtSyntaxToken::Decimal(decimal) => out.extend_from_slice(decimal.as_slice()),
        SmtSyntaxToken::Hexadecimal(digits) => {
            out.extend_from_slice(b"#x");
            out.extend_from_slice(digits.as_slice());
        }
        SmtSyntaxToken::Binary(digits) => {
            out.extend_from_slice(b"#b");
            out.extend_from_slice(digits.as_slice());
        }
        SmtSyntaxToken::String(content) => string(out, *content),
        SmtSyntaxToken::Keyword(keyword) => self::keyword(out, *keyword),
        SmtSyntaxToken::Symbol(symbol) => self::symbol(out, *symbol),
        SmtSyntaxToken::Reserved(reserved) => out.extend_from_slice(reserved.as_str().as_bytes()),
        SmtSyntaxToken::Whitespace(_) | SmtSyntaxToken::Comment(_) => {
            unreachable!("a plain consumer is not handed whitespace or comments")
        }
        SmtSyntaxToken::EndOfFile => {}
    }
}

/// Where a token stream stands with respect to a top-level `(exit)`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ExitState {
    /// Not inside the opening of a top-level command.
    Outside,
    /// Right after a top-level `(`.
    AfterOpen,
    /// Inside a top-level `(exit`.
    InExit,
    /// After the `)` of a top-level `(exit)`: the rest is discarded.
    Done,
}

/// Token consumer folding the texts of the tokens into a digest,
/// optionally keeping them, and stopping after a top-level `(exit)`.
struct TokenDigest {
    hasher: DefaultHasher,
    count: u64,
    depth: u64,
    exit: ExitState,
    stops_at_exit: bool,
    kept: Option<Vec<Vec<u8>>>,
    text: Vec<u8>,
}

impl TokenDigest {
    fn new(stops_at_exit: bool, keeps: bool) -> Self {
        Self {
            hasher: DefaultHasher::new(),
            count: 0,
            depth: 0,
            exit: ExitState::Outside,
            stops_at_exit,
            kept: keeps.then(Vec::new),
            text: Vec::new(),
        }
    }

    fn add(&mut self, token: &SmtSyntaxToken<'_>) {
        if self.exit == ExitState::Done {
            return;
        }
        self.text.clear();
        token_text(token, &mut self.text);
        if self.text.is_empty() {
            return;
        }
        self.hasher.write_u64(self.text.len() as u64);
        self.hasher.write(&self.text);
        self.count += 1;
        if let Some(kept) = &mut self.kept {
            kept.push(self.text.clone());
        }

        // follow the depth to find a top-level `(exit)`
        let at_top = self.depth == 0;
        match token {
            SmtSyntaxToken::ParenOpen => self.depth += 1,
            SmtSyntaxToken::ParenClose => self.depth = self.depth.saturating_sub(1),
            _ => {}
        }
        if self.stops_at_exit {
            self.exit = match (self.exit, token) {
                (_, SmtSyntaxToken::ParenOpen) if at_top => ExitState::AfterOpen,
                (ExitState::AfterOpen, _) if self.text == b"exit" => ExitState::InExit,
                (ExitState::InExit, SmtSyntaxToken::ParenClose) if self.depth == 0 => {
                    ExitState::Done
                }
                (ExitState::InExit, _) => ExitState::InExit,
                _ => ExitState::Outside,
            };
        }
    }

    fn digest(&self) -> (u64, u64) {
        (self.count, self.hasher.finish())
    }
}

impl SmtConsume for TokenDigest {
    type Result = ();
    type Error = Infallible;
    const IS_CONCRETE: bool = false;
}

impl<'a> SmtConsumeFrom<SmtLexerCursor<'a>> for TokenDigest {
    fn consume(&mut self, cursor: &mut SmtLexerCursor<'a>) -> Result<ControlFlow<()>, Infallible> {
        let mut at_end = false;
        while let Some(token) = cursor.next() {
            let syntax = cursor.syntax(&token);
            if matches!(syntax, SmtSyntaxToken::EndOfFile) {
                at_end = true;
            }
            self.add(&syntax);
        }
        // every consumer breaks at the end of the input at the latest
        Ok(if at_end {
            ControlFlow::Break(())
        } else {
            ControlFlow::Continue(())
        })
    }
}

/// Lexes `input`, read through `reader`, into a token digest.
fn lex_reader(reader: impl BufRead, digest: &mut TokenDigest) -> Result<(), String> {
    let mut reader = reader;
    let mut lexer = SmtLexer::new(digest, SmtVersion::V2_7);
    loop {
        let buffer = reader
            .fill_buf()
            .map_err(|err| format!("Read error: {err}"))?;
        if buffer.is_empty() {
            break;
        }
        let len = buffer.len();
        lexer
            .lex_slice(buffer)
            .map_err(|err| format!("Lexer error: {:?}", err.span()))?;
        reader.consume(len);
    }
    lexer
        .lex_eof()
        .map_err(|err| format!("Lexer error: {:?}", err.span()))?;
    Ok(())
}

/// Lexes printed text into a token digest; the pieces end between commands.
fn lex_printed(text: &[u8], digest: &mut TokenDigest) {
    let mut lexer = SmtLexer::new(digest, SmtVersion::V2_7);
    if let Err(err) = lexer.lex_all(text) {
        let span = err.span();
        let start = span.start().offset() as usize;
        let from = start.saturating_sub(40);
        let to = (span.end().offset() as usize + 40).min(text.len());
        panic!(
            "printed text must lex, got an error at {span:?} in `{}`",
            String::from_utf8_lossy(&text[from..to])
        );
    }
}

// --- the printing handler ---

fn symbol(out: &mut Vec<u8>, symbol: SmtSymbol<'_>) {
    if symbol.is_quoted() {
        out.push(b'|');
        out.extend_from_slice(symbol.as_slice());
        out.push(b'|');
    } else {
        out.extend_from_slice(symbol.as_slice());
    }
}

fn keyword(out: &mut Vec<u8>, keyword: SmtKeyword<'_>) {
    out.push(b':');
    out.extend_from_slice(keyword.as_slice());
}

/// Writes a string literal; the content is decoded, so a double quote is escaped again
/// as two (the escape of SMT-LIB 2.5 on, the only one the inputs use).
fn string(out: &mut Vec<u8>, content: SmtStringContent<'_>) {
    out.push(b'"');
    for &byte in content.as_slice() {
        if byte == b'"' {
            out.push(b'"');
        }
        out.push(byte);
    }
    out.push(b'"');
}

fn numeral(out: &mut Vec<u8>, numeral: SmtNumeral<'_>) {
    out.extend_from_slice(numeral.as_slice());
}

fn special_constant(out: &mut Vec<u8>, constant: SmtSpecialConstant<'_>) {
    let token = match constant {
        SmtSpecialConstant::Numeral(numeral) => SmtSyntaxToken::Numeral(numeral),
        SmtSpecialConstant::Decimal(decimal) => SmtSyntaxToken::Decimal(decimal),
        SmtSpecialConstant::Hexadecimal(digits) => SmtSyntaxToken::Hexadecimal(digits),
        SmtSpecialConstant::Binary(digits) => SmtSyntaxToken::Binary(digits),
        SmtSpecialConstant::String(content) => SmtSyntaxToken::String(content),
    };
    token_text(&token, out);
}

fn ident(out: &mut Vec<u8>, ident: SmtIdent<'_>) {
    if ident.indices.is_empty() {
        symbol(out, ident.name);
        return;
    }
    out.extend_from_slice(b"(_ ");
    symbol(out, ident.name);
    for index in ident.indices.iter() {
        out.push(b' ');
        match index {
            SmtIndex::Numeral(index) => numeral(out, index),
            SmtIndex::Symbol(index) => symbol(out, index),
        }
    }
    out.push(b')');
}

/// Writes `(` the items separated by spaces `)`.
fn list<'v>(out: &mut Vec<u8>, items: impl IntoIterator<Item = &'v Vec<u8>>) {
    out.push(b'(');
    for (i, item) in items.into_iter().enumerate() {
        if i > 0 {
            out.push(b' ');
        }
        out.extend_from_slice(item);
    }
    out.push(b')');
}

fn symbols(out: &mut Vec<u8>, symbols: SmtSymbols<'_>) {
    out.push(b'(');
    for (i, name) in symbols.iter().enumerate() {
        if i > 0 {
            out.push(b' ');
        }
        symbol(out, name);
    }
    out.push(b')');
}

/// Writes sorted variables, or selectors, as `((x S) (y T))`.
fn sorted_vars<'v>(
    out: &mut Vec<u8>,
    vars: impl IntoIterator<Item = (SmtSymbol<'v>, &'v Vec<u8>)>,
) {
    out.push(b'(');
    for (i, (name, sort)) in vars.into_iter().enumerate() {
        if i > 0 {
            out.push(b' ');
        }
        out.push(b'(');
        symbol(out, name);
        out.push(b' ');
        out.extend_from_slice(sort);
        out.push(b')');
    }
    out.push(b')');
}

/// Writes a signature as `f ((x S)) R`.
fn signature(out: &mut Vec<u8>, signature: SmtFunctionSignature<'_, Vec<u8>>) {
    symbol(out, signature.name());
    out.push(b' ');
    sorted_vars(out, signature.params());
    out.push(b' ');
    out.extend_from_slice(signature.result_sort());
}

/// Writes constructors as `(c (s S)) (d)`, separated by spaces.
fn constructors(out: &mut Vec<u8>, constructors: SmtConstructors<'_, Vec<u8>>) {
    for (i, (name, selectors)) in constructors.into_iter().enumerate() {
        if i > 0 {
            out.push(b' ');
        }
        out.push(b'(');
        symbol(out, name);
        for (selector, sort) in selectors.iter() {
            out.extend_from_slice(b" (");
            symbol(out, selector);
            out.push(b' ');
            out.extend_from_slice(sort);
            out.push(b')');
        }
        out.push(b')');
    }
}

fn simple_pattern(out: &mut Vec<u8>, pattern: SmtSimplePattern<'_>) {
    match pattern {
        SmtSimplePattern::Symbol(name) => symbol(out, name),
        SmtSimplePattern::Wildcard => out.push(b'_'),
    }
}

fn pattern(out: &mut Vec<u8>, pattern: SmtPattern<'_>) {
    match pattern {
        SmtPattern::Simple(simple) => simple_pattern(out, simple),
        SmtPattern::Application(application) => {
            out.push(b'(');
            symbol(out, application.constructor());
            for arg in application.args().iter() {
                out.push(b' ');
                simple_pattern(out, arg);
            }
            out.push(b')');
        }
    }
}

/// Where the printed text goes.
enum Sink {
    /// Lexed into a token digest.
    Digest(TokenDigest),
    /// Sent on in pieces that end between commands.
    Channel(SyncSender<Vec<u8>>),
}

/// Handler that prints every call back as SMT-LIB text, with handled values
/// that are their own text, and hands the printed text to its sink.
struct Reprint {
    /// Printed commands not yet handed on.
    out: Vec<u8>,
    /// The command in progress, when it is made of several calls.
    open: Vec<u8>,
    /// Whether the datatype declaration in progress is parametric.
    parametric: bool,
    sink: Sink,
}

impl Reprint {
    fn new(keeps: bool) -> Self {
        Self {
            out: Vec::new(),
            open: Vec::new(),
            parametric: false,
            sink: Sink::Digest(TokenDigest::new(false, keeps)),
        }
    }

    fn sending(sender: SyncSender<Vec<u8>>) -> Self {
        Self {
            out: Vec::new(),
            open: Vec::new(),
            parametric: false,
            sink: Sink::Channel(sender),
        }
    }

    fn digest(&self) -> &TokenDigest {
        match &self.sink {
            Sink::Digest(digest) => digest,
            Sink::Channel(_) => panic!("a sending printer keeps no digest"),
        }
    }

    fn into_digest(self) -> TokenDigest {
        match self.sink {
            Sink::Digest(digest) => digest,
            Sink::Channel(_) => panic!("a sending printer keeps no digest"),
        }
    }

    /// Ends a command: appends it and lexes the printed text when enough has gathered.
    fn command(&mut self, text: &[u8]) {
        self.out.extend_from_slice(text);
        self.out.push(b'\n');
        if self.out.len() >= FLUSH_SIZE {
            self.flush();
        }
    }

    fn command_with<F: FnOnce(&mut Vec<u8>)>(
        &mut self,
        write: F,
    ) -> Result<(), SmtNonstandardCommandError> {
        let mut text = Vec::new();
        write(&mut text);
        self.command(&text);
        Ok(())
    }

    /// Ends the command in progress with `tail`.
    fn close_open(&mut self, tail: &[u8]) -> Result<(), SmtNonstandardCommandError> {
        let mut text = std::mem::take(&mut self.open);
        text.extend_from_slice(tail);
        self.command(&text);
        Ok(())
    }

    fn flush(&mut self) {
        let out = std::mem::take(&mut self.out);
        match &mut self.sink {
            Sink::Digest(digest) => lex_printed(&out, digest),
            // the receiver stops listening at the first mismatch, the rest is not needed
            Sink::Channel(sender) => {
                let _ = sender.send(out);
            }
        }
    }
}

type Text = Vec<u8>;
type Res<T> = Result<T, SmtNonstandardCommandError>;

impl SmtHandler for Reprint {
    type Error = SmtNonstandardCommandError;
    type SExpr = Text;
    type Attribute = Text;
    type Sort = Text;
    type Term = Text;
    type Scope = Text;

    fn set_version(&mut self, _version: SmtVersion) {}

    fn handle_sort(&mut self, sort: SmtSort<'_, Self>) -> Res<Text> {
        let mut out = Vec::new();
        if sort.args.is_empty() {
            ident(&mut out, sort.ident);
        } else {
            out.push(b'(');
            ident(&mut out, sort.ident);
            for arg in sort.args.iter() {
                out.push(b' ');
                out.extend_from_slice(arg);
            }
            out.push(b')');
        }
        Ok(out)
    }

    fn handle_term(&mut self, term: SmtTerm<'_, Self>) -> Res<Text> {
        let mut out = Vec::new();
        let qualified =
            |out: &mut Vec<u8>, function: &blazing_smtlib::grammar::SmtQualifiedIdent<'_, Self>| {
                match &function.sort {
                    None => ident(out, function.ident),
                    Some(sort) => {
                        out.extend_from_slice(b"(as ");
                        ident(out, function.ident);
                        out.push(b' ');
                        out.extend_from_slice(sort);
                        out.push(b')');
                    }
                }
            };
        match term {
            SmtTerm::SpecialConstant(constant) => special_constant(&mut out, constant),
            SmtTerm::QualifiedIdent(qualified_ident) => qualified(&mut out, &qualified_ident),
            SmtTerm::Application(application) => {
                out.push(b'(');
                qualified(&mut out, application.function());
                for arg in application.args().iter() {
                    out.push(b' ');
                    out.extend_from_slice(arg);
                }
                out.push(b')');
            }
        }
        Ok(out)
    }

    fn handle_s_expr(&mut self, expr: SmtSExpr<'_, Self>) -> Res<Text> {
        let mut out = Vec::new();
        match expr {
            SmtSExpr::SpecialConstant(constant) => special_constant(&mut out, constant),
            SmtSExpr::Symbol(name) => symbol(&mut out, name),
            SmtSExpr::Reserved(reserved) => out.extend_from_slice(reserved.as_str().as_bytes()),
            SmtSExpr::Keyword(word) => keyword(&mut out, word),
            SmtSExpr::SExprs(exprs) => list(&mut out, exprs.iter()),
        }
        Ok(out)
    }

    fn handle_attribute(
        &mut self,
        name: SmtKeyword<'_>,
        value: Option<SmtAttributeValue<'_, Self>>,
    ) -> Res<Text> {
        let mut out = Vec::new();
        keyword(&mut out, name);
        match value {
            None => {}
            Some(SmtAttributeValue::SpecialConstant(constant)) => {
                out.push(b' ');
                special_constant(&mut out, constant);
            }
            Some(SmtAttributeValue::Symbol(value)) => {
                out.push(b' ');
                symbol(&mut out, value);
            }
            Some(SmtAttributeValue::SExprs(exprs)) => {
                out.push(b' ');
                list(&mut out, exprs.iter());
            }
        }
        Ok(out)
    }

    fn annotate_term(
        &mut self,
        term: Text,
        attributes: SmtMultiple<'_, Self::Attribute>,
    ) -> Res<Text> {
        let mut out = b"(! ".to_vec();
        out.extend_from_slice(&term);
        for attribute in attributes.iter() {
            out.push(b' ');
            out.extend_from_slice(attribute);
        }
        out.push(b')');
        Ok(out)
    }

    fn start_let(&mut self, bindings: SmtNamedValues<'_, Text>) -> Res<Text> {
        let mut out = b"(let ".to_vec();
        sorted_vars(&mut out, bindings.iter());
        Ok(out)
    }

    fn end_let(&mut self, scope: Text, body: Text) -> Res<Text> {
        let mut out = scope;
        out.push(b' ');
        out.extend_from_slice(&body);
        out.push(b')');
        Ok(out)
    }

    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        vars: SmtNamedValues<'_, Text>,
    ) -> Res<Text> {
        let mut out = Vec::new();
        sorted_vars(&mut out, vars.iter());
        Ok(out)
    }

    fn end_quantifier(&mut self, kind: SmtQuantifierKind, scope: Text, body: Text) -> Res<Text> {
        let mut out = match kind {
            SmtQuantifierKind::Forall => b"(forall ".to_vec(),
            SmtQuantifierKind::Exists => b"(exists ".to_vec(),
        };
        out.extend_from_slice(&scope);
        out.push(b' ');
        out.extend_from_slice(&body);
        out.push(b')');
        Ok(out)
    }

    fn start_lambda(&mut self, vars: SmtNamedValues<'_, Text>) -> Res<Text> {
        let mut out = b"(lambda ".to_vec();
        sorted_vars(&mut out, vars.iter());
        Ok(out)
    }

    fn end_lambda(&mut self, scope: Text, body: Text) -> Res<Text> {
        let mut out = scope;
        out.push(b' ');
        out.extend_from_slice(&body);
        out.push(b')');
        Ok(out)
    }

    fn start_match(&mut self, _scrutinee: &Text) -> Res<()> {
        Ok(())
    }

    fn start_match_case(&mut self, _scrutinee: &Text, case: SmtPattern<'_>) -> Res<Text> {
        let mut out = Vec::new();
        pattern(&mut out, case);
        Ok(out)
    }

    fn end_match_case(&mut self, scope: Text, _scrutinee: &Text, body: Text) -> Res<Text> {
        let mut out = b"(".to_vec();
        out.extend_from_slice(&scope);
        out.push(b' ');
        out.extend_from_slice(&body);
        out.push(b')');
        Ok(out)
    }

    fn end_match(&mut self, scrutinee: Text, cases: SmtMatchCases<'_, Self>) -> Res<Text> {
        let mut out = b"(match ".to_vec();
        out.extend_from_slice(&scrutinee);
        out.push(b' ');
        list(&mut out, cases.iter().map(|(_, case)| case));
        out.push(b')');
        Ok(out)
    }
}

impl SmtCommandHandler for Reprint {
    type NonstandardParser = Infallible;

    fn nonstandard_command(&mut self, name: SmtSymbol<'_>) -> Res<Infallible> {
        Err(SmtNonstandardCommandError::new(name.into_owned()))
    }

    fn command_echo(&mut self, value: SmtStringContent<'_>) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(echo ");
            string(out, value);
            out.push(b')');
        })
    }

    fn command_get_option(&mut self, option: SmtKeyword<'_>) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(get-option ");
            keyword(out, option);
            out.push(b')');
        })
    }

    fn command_set_option(&mut self, option: Text) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(set-option ");
            out.extend_from_slice(&option);
            out.push(b')');
        })
    }

    fn command_get_info(&mut self, flag: SmtKeyword<'_>) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(get-info ");
            keyword(out, flag);
            out.push(b')');
        })
    }

    fn command_set_info(&mut self, attribute: Text) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(set-info ");
            out.extend_from_slice(&attribute);
            out.push(b')');
        })
    }

    fn command_set_logic(&mut self, logic: SmtSymbol<'_>) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(set-logic ");
            symbol(out, logic);
            out.push(b')');
        })
    }

    fn command_get_value(&mut self, terms: SmtMultiple<'_, Text>) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(get-value ");
            list(out, terms.iter());
            out.push(b')');
        })
    }

    fn command_get_assertions(&mut self) -> Res<()> {
        self.command_with(|out| out.extend_from_slice(b"(get-assertions)"))
    }

    fn command_get_assignment(&mut self) -> Res<()> {
        self.command_with(|out| out.extend_from_slice(b"(get-assignment)"))
    }

    fn command_get_model(&mut self) -> Res<()> {
        self.command_with(|out| out.extend_from_slice(b"(get-model)"))
    }

    fn command_get_proof(&mut self) -> Res<()> {
        self.command_with(|out| out.extend_from_slice(b"(get-proof)"))
    }

    fn command_get_unsat_assumptions(&mut self) -> Res<()> {
        self.command_with(|out| out.extend_from_slice(b"(get-unsat-assumptions)"))
    }

    fn command_get_unsat_core(&mut self) -> Res<()> {
        self.command_with(|out| out.extend_from_slice(b"(get-unsat-core)"))
    }

    fn command_declare_sort(&mut self, name: SmtSymbol<'_>, arity: SmtNumeral<'_>) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(declare-sort ");
            symbol(out, name);
            out.push(b' ');
            numeral(out, arity);
            out.push(b')');
        })
    }

    fn command_declare_sort_parameter(&mut self, name: SmtSymbol<'_>) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(declare-sort-parameter ");
            symbol(out, name);
            out.push(b')');
        })
    }

    fn command_declare_const(&mut self, name: SmtSymbol<'_>, sort: Text) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(declare-const ");
            symbol(out, name);
            out.push(b' ');
            out.extend_from_slice(&sort);
            out.push(b')');
        })
    }

    fn command_declare_fun(
        &mut self,
        name: SmtSymbol<'_>,
        param_sorts: SmtMultiple<'_, Text>,
        result_sort: Text,
    ) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(declare-fun ");
            symbol(out, name);
            out.push(b' ');
            list(out, param_sorts.iter());
            out.push(b' ');
            out.extend_from_slice(&result_sort);
            out.push(b')');
        })
    }

    fn command_assert(&mut self, term: Text) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(assert ");
            out.extend_from_slice(&term);
            out.push(b')');
        })
    }

    fn command_check_sat(&mut self) -> Res<()> {
        self.command_with(|out| out.extend_from_slice(b"(check-sat)"))
    }

    fn command_check_sat_assuming(&mut self, assumptions: SmtMultiple<'_, Text>) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(check-sat-assuming ");
            list(out, assumptions.iter());
            out.push(b')');
        })
    }

    fn command_reset(&mut self) -> Res<()> {
        self.command_with(|out| out.extend_from_slice(b"(reset)"))
    }

    fn command_reset_assertions(&mut self) -> Res<()> {
        self.command_with(|out| out.extend_from_slice(b"(reset-assertions)"))
    }

    fn command_exit(&mut self) -> Res<()> {
        self.command_with(|out| out.extend_from_slice(b"(exit)"))
    }

    fn command_push(&mut self, amount: SmtNumeral<'_>) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(push ");
            numeral(out, amount);
            out.push(b')');
        })
    }

    fn command_pop(&mut self, amount: SmtNumeral<'_>) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(pop ");
            numeral(out, amount);
            out.push(b')');
        })
    }

    fn start_define_sort(&mut self, name: SmtSymbol<'_>, params: SmtSymbols<'_>) -> Res<()> {
        let open = &mut self.open;
        open.extend_from_slice(b"(define-sort ");
        symbol(open, name);
        open.push(b' ');
        symbols(open, params);
        open.push(b' ');
        Ok(())
    }

    fn end_define_sort(&mut self, sort: Text) -> Res<()> {
        let mut tail = sort;
        tail.push(b')');
        self.close_open(&tail)
    }

    fn start_define_fun(&mut self, sig: SmtFunctionSignature<'_, Text>) -> Res<()> {
        self.open.extend_from_slice(b"(define-fun ");
        signature(&mut self.open, sig);
        self.open.push(b' ');
        Ok(())
    }

    fn end_define_fun(&mut self, body: Text) -> Res<()> {
        let mut tail = body;
        tail.push(b')');
        self.close_open(&tail)
    }

    fn command_define_const(&mut self, name: SmtSymbol<'_>, sort: Text, body: Text) -> Res<()> {
        self.command_with(|out| {
            out.extend_from_slice(b"(define-const ");
            symbol(out, name);
            out.push(b' ');
            out.extend_from_slice(&sort);
            out.push(b' ');
            out.extend_from_slice(&body);
            out.push(b')');
        })
    }

    fn start_define_fun_rec(&mut self, sig: SmtFunctionSignature<'_, Text>) -> Res<()> {
        self.open.extend_from_slice(b"(define-fun-rec ");
        signature(&mut self.open, sig);
        self.open.push(b' ');
        Ok(())
    }

    fn end_define_fun_rec(&mut self, body: Text) -> Res<()> {
        let mut tail = body;
        tail.push(b')');
        self.close_open(&tail)
    }

    fn start_define_funs_rec(&mut self, signatures: SmtFunctionSignatures<'_, Text>) -> Res<()> {
        let open = &mut self.open;
        open.extend_from_slice(b"(define-funs-rec (");
        for (i, sig) in signatures.iter().enumerate() {
            if i > 0 {
                open.push(b' ');
            }
            open.push(b'(');
            signature(open, sig);
            open.push(b')');
        }
        open.extend_from_slice(b") (");
        Ok(())
    }

    fn start_recursive_body(&mut self, _signature: SmtFunctionSignature<'_, Text>) -> Res<()> {
        Ok(())
    }

    fn end_recursive_body(&mut self, body: Text) -> Res<()> {
        self.open.extend_from_slice(&body);
        self.open.push(b' ');
        Ok(())
    }

    fn end_define_funs_rec(&mut self) -> Res<()> {
        self.close_open(b"))")
    }

    fn start_declare_datatype(&mut self, name: SmtSymbol<'_>, params: SmtSymbols<'_>) -> Res<()> {
        let open = &mut self.open;
        open.extend_from_slice(b"(declare-datatype ");
        symbol(open, name);
        open.push(b' ');
        self.parametric = !params.is_empty();
        if self.parametric {
            open.extend_from_slice(b"(par ");
            symbols(open, params);
            open.push(b' ');
        }
        open.push(b'(');
        Ok(())
    }

    fn end_declare_datatype(&mut self, list: SmtConstructors<'_, Text>) -> Res<()> {
        constructors(&mut self.open, list);
        let tail: &[u8] = if self.parametric { b")))" } else { b"))" };
        self.close_open(tail)
    }

    fn start_declare_datatypes(&mut self, arities: SmtSortArities<'_>) -> Res<()> {
        let open = &mut self.open;
        open.extend_from_slice(b"(declare-datatypes (");
        for (i, (name, arity)) in arities.iter().enumerate() {
            if i > 0 {
                open.push(b' ');
            }
            open.push(b'(');
            symbol(open, name);
            open.push(b' ');
            numeral(open, arity);
            open.push(b')');
        }
        open.extend_from_slice(b") (");
        Ok(())
    }

    fn end_declare_datatypes(&mut self) -> Res<()> {
        self.close_open(b"))")
    }

    fn start_datatype_declaration(&mut self, params: SmtSymbols<'_>) -> Res<()> {
        let open = &mut self.open;
        self.parametric = !params.is_empty();
        if self.parametric {
            open.extend_from_slice(b"(par ");
            symbols(open, params);
            open.push(b' ');
        }
        open.push(b'(');
        Ok(())
    }

    fn end_datatype_declaration(&mut self, list: SmtConstructors<'_, Text>) -> Res<()> {
        let open = &mut self.open;
        constructors(open, list);
        open.extend_from_slice(if self.parametric { b")) " } else { b") " });
        Ok(())
    }
}

// --- the check ---

/// Checks that printing the calls of the file gives the tokens of the file.
pub fn roundtrip_file(path: &Path) -> Result<(), String> {
    let mut input = TokenDigest::new(true, false);
    let file = File::open(path).map_err(|err| format!("Read error: {err}"))?;
    lex_reader(BufReader::with_capacity(1 << 20, file), &mut input)?;

    let mut printer = Reprint::new(false);
    read_smt_file(&mut printer, path).map_err(read_error)?;
    printer.flush();

    if input.digest() == printer.digest().digest() {
        return Ok(());
    }
    Err(first_difference(path))
}

fn read_error(err: SmtReadError<SmtNonstandardCommandError>) -> String {
    format!("Read error at {:?}: {:?}", err.span(), err.cause())
}

/// Describes where the printed tokens first differ from the input's.
fn first_difference(path: &Path) -> String {
    let mut input = TokenDigest::new(true, true);
    let read = File::open(path).map(|file| lex_reader(BufReader::new(file), &mut input));
    if !matches!(read, Ok(Ok(()))) {
        return "Mismatch, and the input could not be lexed again".into();
    }
    let mut printer = Reprint::new(true);
    if read_smt_file(&mut printer, path).is_err() {
        return "Mismatch, and the input could not be read again".into();
    }
    printer.flush();
    let left = input.kept.unwrap_or_default();
    let right = printer.into_digest().kept.unwrap_or_default();
    let index = left
        .iter()
        .zip(&right)
        .position(|(a, b)| a != b)
        .unwrap_or(left.len().min(right.len()));
    let show = |tokens: &[Vec<u8>]| {
        let from = index.saturating_sub(3);
        let to = (index + 3).min(tokens.len());
        tokens[from..to]
            .iter()
            .map(|token| String::from_utf8_lossy(token).into_owned())
            .collect::<Vec<_>>()
            .join(" ")
    };
    format!(
        "Mismatch at token {index} of {} (input) and {} (printed): input `{}`, printed `{}`",
        left.len(),
        right.len(),
        show(&left),
        show(&right)
    )
}

// --- the bytes-to-bytes check ---

/// The printed tokens, lexed from the pieces the printing thread sends.
struct PrintedTokens {
    receiver: Receiver<Vec<u8>>,
    tokens: std::collections::VecDeque<Vec<u8>>,
}

impl PrintedTokens {
    /// The next printed token, or `None` once the printer has finished.
    fn next(&mut self) -> Option<Vec<u8>> {
        while self.tokens.is_empty() {
            let piece = self.receiver.recv().ok()?;
            let mut digest = TokenDigest::new(false, true);
            lex_printed(&piece, &mut digest);
            self.tokens.extend(digest.kept.unwrap_or_default());
        }
        self.tokens.pop_front()
    }
}

/// Concrete token consumer that rebuilds the input from its own whitespace
/// and comments and the printed tokens, comparing with the input as it goes.
struct Rebuild<'i> {
    input: &'i [u8],
    printed: PrintedTokens,
    /// Follows the input's tokens to stop after a top-level `(exit)`.
    exit: TokenDigest,
    /// The first difference found, if any.
    mismatch: Option<String>,
    /// How many input bytes were rebuilt and compared.
    compared: u64,
}

impl SmtConsume for Rebuild<'_> {
    type Result = ();
    type Error = Infallible;
    const IS_CONCRETE: bool = true;
}

impl<'a> SmtConsumeFrom<SmtLexerCursor<'a>> for Rebuild<'_> {
    fn consume(&mut self, cursor: &mut SmtLexerCursor<'a>) -> Result<ControlFlow<()>, Infallible> {
        let mut at_end = false;
        while let Some(token) = cursor.next() {
            let syntax = cursor.syntax(&token);
            match syntax {
                SmtSyntaxToken::EndOfFile => at_end = true,
                // after a top-level `(exit)` the input is discarded, nothing is rebuilt
                _ if self.mismatch.is_some() || self.exit.exit == ExitState::Done => {}
                // layout is copied from the input, so it matches by construction
                SmtSyntaxToken::Whitespace(_) | SmtSyntaxToken::Comment(_) => {
                    let span = token.span();
                    self.compared += span.end().offset() - span.start().offset();
                }
                _ => {
                    let span = token.span();
                    let start = span.start().offset() as usize;
                    let raw = &self.input[start..span.end().offset() as usize];
                    match self.printed.next() {
                        Some(printed) if printed == raw => self.compared += raw.len() as u64,
                        Some(printed) => {
                            self.mismatch = Some(format!(
                                "Bytes differ at offset {start}: input `{}`, printed `{}`",
                                String::from_utf8_lossy(raw),
                                String::from_utf8_lossy(&printed)
                            ))
                        }
                        None => {
                            self.mismatch = Some(format!(
                                "Printed text ends before the input at offset {start}, at `{}`",
                                String::from_utf8_lossy(raw)
                            ))
                        }
                    }
                    self.exit.add(&syntax);
                }
            }
        }
        // every consumer breaks at the end of the input at the latest
        Ok(if at_end {
            ControlFlow::Break(())
        } else {
            ControlFlow::Continue(())
        })
    }
}

/// Checks that the input is rebuilt byte for byte from its own whitespace
/// and comments and the printed tokens, up to a top-level `(exit)`.
pub fn bytes_file(path: &Path) -> Result<(), String> {
    let input = std::fs::read(path).map_err(|err| format!("Read error: {err}"))?;
    let (sender, receiver) = sync_channel(4);

    std::thread::scope(|scope| {
        let printing = scope.spawn(move || {
            let mut printer = Reprint::sending(sender);
            let read = read_smt_file(&mut printer, path).map_err(read_error);
            printer.flush();
            read
        });

        let mut rebuild = Rebuild {
            input: &input,
            printed: PrintedTokens {
                receiver,
                tokens: Default::default(),
            },
            exit: TokenDigest::new(true, false),
            mismatch: None,
            compared: 0,
        };
        {
            let mut lexer = SmtLexer::new(&mut rebuild, SmtVersion::V2_7);
            lexer
                .lex_all(&input)
                .map_err(|err| format!("Lexer error: {:?}", err.span()))?;
        }
        // the printed tokens must end where the rebuilt input does
        if rebuild.mismatch.is_none()
            && let Some(extra) = rebuild.printed.next()
        {
            rebuild.mismatch = Some(format!(
                "Printed text goes on after the input, with `{}`",
                String::from_utf8_lossy(&extra)
            ));
        }
        // stop the printer if it is still sending, then collect its result
        drop(rebuild.printed);
        printing
            .join()
            .expect("the printing thread does not panic")?;
        match rebuild.mismatch {
            None => Ok(()),
            Some(mismatch) => Err(mismatch),
        }
    })
}
