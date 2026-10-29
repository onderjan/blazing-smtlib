use std::{
    error::Error,
    fmt,
    io::{self, Write},
    ops::ControlFlow,
};

use crate::{
    SmtVersion,
    lexicon::SmtReserved,
    token::{SmtAppendTokens, SmtConsume, SmtConsumeFrom, SmtCursor, SmtToken, SmtTokensCursor},
};

/// Why writing failed (I/O error or a reserved word not in the version).
#[derive(Debug)]
pub enum SmtWriteErrorKind {
    /// Writing to the writer failed.
    Io(io::Error),
    /// The reserved word is not reserved in the version written in.
    ///
    /// There is no way to write the reserved word, as its text would be read as a symbol,
    /// e.g. the reserved word `lambda` in SMT-LIB 2.6.
    NotInVersion(SmtReserved),
}

/// Error that forced writing to stop.
#[derive(Debug)]
pub struct SmtWriteError(SmtWriteErrorKind);

impl SmtWriteError {
    #[inline]
    pub(crate) fn new(kind: SmtWriteErrorKind) -> Self {
        Self(kind)
    }

    /// Returns the kind of the error.
    pub fn kind(&self) -> &SmtWriteErrorKind {
        &self.0
    }

    /// Converts into the kind of the error.
    pub fn into_kind(self) -> SmtWriteErrorKind {
        self.0
    }
}

impl From<io::Error> for SmtWriteError {
    fn from(err: io::Error) -> Self {
        Self(SmtWriteErrorKind::Io(err))
    }
}

impl fmt::Display for SmtWriteErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(err) => write!(f, "I/O: {err}"),
            Self::NotInVersion(reserved) => {
                write!(
                    f,
                    "`{}` is not reserved in written version",
                    reserved.as_str()
                )
            }
        }
    }
}

impl fmt::Display for SmtWriteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Error for SmtWriteError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.0 {
            SmtWriteErrorKind::Io(err) => err.source(),
            SmtWriteErrorKind::NotInVersion(_) => None,
        }
    }
}

/// How tokens are laid out by the writer (single line, compact, or as handed over).
///
/// Independently of the style chosen, new input started after EOF is separated by
/// a line feed (LF). LF is not added if nothing has been written or the previous input
/// ended with LF.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum SmtWriteStyle {
    /// Writes tokens separated by spaces, without unnecessary line breaks.
    ///
    /// Tokens are separated by spaces. As conventional, no space follows an opening or precedes
    /// a closing parenthesis. Unnecessary whitespace is dropped. A comment is separated by a space
    /// at its start and is terminated by LF only if another token follows it.
    ///
    /// ```text
    /// (assert x) (assert y) ; comment
    /// (check-sat) junk ; no line ending at the end
    /// ```
    Line,
    /// Writes each top-level item and comment on a line of its own.
    ///
    /// Within an item, tokens are separated as in [`Line`](Self::Line). A line feed follows each
    /// top-level item.
    /// Whitespace is fully reformatted, and each comment is written on a line of
    /// its own, ended by a line feed.
    ///
    /// ```text
    /// (assert x)
    /// (assert y)
    /// ; comment
    /// (check-sat)
    /// junk
    /// ; LF at the end
    ///
    /// ```
    Compact,
    /// Writes tokens in the layout they are handed over in.
    ///
    /// Whitespace and comments are written as they are. A space is added only between two tokens
    /// that would otherwise run together, and a line feed only after a comment without a line
    /// ending followed by a token. A script lexed and written in the version it was read in is
    /// thus written back as it was, except that in SMT-LIB 2.0, every backslash in a string is
    /// written escaped: `"a\q"` is written back as `"a\\q"`, which is read as the same string.
    #[default]
    Layout,
}

/// Writer configuration (version in force and writing style).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SmtWriterConfig {
    version: SmtVersion,
    style: SmtWriteStyle,
}

impl SmtWriterConfig {
    /// Creates a writer configuration with the given version
    /// the [default style](SmtWriteStyle::Layout).
    pub fn new(version: SmtVersion) -> Self {
        Self {
            version,
            style: SmtWriteStyle::default(),
        }
    }

    /// Returns the configuration with the style replaced.
    pub fn with_style(self, style: SmtWriteStyle) -> Self {
        Self { style, ..self }
    }

    /// Returns the version written in.
    pub fn version(&self) -> SmtVersion {
        self.version
    }

    /// Returns the style written in.
    pub fn style(&self) -> SmtWriteStyle {
        self.style
    }
}

/// Writes nodes or tokens as SMT-LIB text.
///
/// The writer can write any value that implements [`SmtAppendTokens`] in its SMT-LIB
/// text representation.
///
/// For example, writing a token, a reserved word, a term and a slice of tokens:
///
/// ```
/// # use blazing_smtlib::{
/// #     SmtNodeTypes, SmtVersion, SmtWriteStyle, SmtWriter, SmtWriterConfig,
/// #     grammar::{SmtApplicationBuf, SmtQualifiedIdentBuf, SmtTermBuf},
/// #     lexicon::{SmtCommandNameReserved, SmtNumeralBuf, SmtReserved, SmtSymbolBuf},
/// #     token::SmtToken,
/// # };
/// #
/// // node types whose children are written as single tokens
/// struct Flat;
/// impl SmtNodeTypes for Flat {
///     type SExpr = ();
///     type Sort = SmtSymbolBuf;
///     type Term = SmtNumeralBuf;
/// }
///
/// let config = SmtWriterConfig::new(SmtVersion::V2_7).with_style(SmtWriteStyle::Line);
/// let mut writer = SmtWriter::new(Vec::new(), config);
/// writer.write(&SmtToken::ParenOpen).unwrap();
/// writer.write(&SmtReserved::CommandName(SmtCommandNameReserved::Assert)).unwrap();
///
/// let f = SmtQualifiedIdentBuf::new_simple(SmtSymbolBuf::new_unquoted(b"f".to_vec()).unwrap());
/// let args = vec![SmtNumeralBuf::from_u32(42)];
/// let term: SmtTermBuf<Flat> = SmtTermBuf::Application(SmtApplicationBuf::new(f, args).unwrap());
/// writer.write(&term).unwrap();
///
/// writer.write(&[SmtToken::ParenClose]).unwrap();
/// assert_eq!(writer.into_inner(), b"(assert (f 42))");
/// ```
///
/// The writer also implements [`SmtConsume`] and [`SmtConsumeFrom`] for any [`SmtCursor`],
/// so it can e.g. rewrite tokens from a lexer in a given [`SmtWriteStyle`].
///
/// For example, reformatting a script in the compact style:
///
/// ```
/// # use blazing_smtlib::{
/// #     SmtVersion, SmtWriteStyle, SmtWriter, SmtWriterConfig, lexer::SmtLexer,
/// # };
/// #
/// let config = SmtWriterConfig::new(SmtVersion::V2_7).with_style(SmtWriteStyle::Compact);
/// let mut lexer = SmtLexer::new(SmtWriter::new(Vec::new(), config), SmtVersion::V2_7);
/// lexer.lex_all(b"(assert  (> x 0)) ; positive\n(check-sat)").unwrap();
/// assert_eq!(
///     lexer.consumer().get_ref().as_slice(),
///     b"(assert (> x 0))\n; positive\n(check-sat)\n"
/// );
/// ```
///
/// The writer writes to the underlying byte writer immediately, without a buffer of its own,
/// and does not flush it. It writes under its SMT-LIB version in force, which is not affected
/// by the cursor version. To change the version in force, [`set_version`](Self::set_version)
/// can be used.
///
/// On encountering an unquoted symbol that is a reserved word in the version in force,
/// the writer recovers gracefully by quoting it. On encountering a reserved word which
/// is not reserved in the version in force, the writer fails with
/// [`SmtWriteErrorKind::NotInVersion`] as the reserved word cannot be represented
/// in the version.
///
/// ```
/// # use blazing_smtlib::{
/// #     SmtVersion, SmtWriteErrorKind, SmtWriter, SmtWriterConfig,
/// #     lexicon::{SmtGeneralReserved, SmtReserved, SmtSymbolBuf},
/// #     token::SmtToken,
/// # };
/// #
/// let mut writer = SmtWriter::new(Vec::new(), SmtWriterConfig::new(SmtVersion::V2_7));
/// // the symbol `lambda` of SMT-LIB 2.6 is written quoted in 2.7
/// let lambda = SmtSymbolBuf::new_unquoted(b"lambda".to_vec()).unwrap();
/// let tokens = [SmtToken::ParenOpen, SmtToken::Symbol(lambda.view()), SmtToken::ParenClose];
/// writer.write(&tokens).unwrap();
///
/// // the reserved word `lambda` of SMT-LIB 2.7 cannot be written in 2.6
/// writer.set_version(SmtVersion::V2_6);
/// let reserved = SmtToken::Reserved(SmtReserved::General(SmtGeneralReserved::Lambda));
/// let err = writer.write(&[SmtToken::ParenOpen, reserved]).unwrap_err();
/// assert!(matches!(err.kind(), SmtWriteErrorKind::NotInVersion(_)));
///
/// // the tokens before the failing one have been written
/// assert_eq!(writer.into_inner(), b"(|lambda|)(");
/// ```
#[derive(Debug)]
pub struct SmtWriter<W: Write> {
    writer: W,
    version: SmtVersion,
    position: Position,
    /// Kept for [`write`](Self::write) to reuse its allocation, empty between calls.
    cursor: SmtTokensCursor<'static>,
}

impl<W: Write> SmtWriter<W> {
    /// Creates a writer into `writer` that writes as configured.
    pub fn new(writer: W, config: SmtWriterConfig) -> Self {
        let position = match config.style {
            SmtWriteStyle::Line => Position::Line(LinePosition::new()),
            SmtWriteStyle::Layout => Position::Layout(LayoutPosition::new()),
            SmtWriteStyle::Compact => Position::Compact(CompactPosition::new()),
        };
        Self {
            writer,
            version: config.version,
            position,
            cursor: SmtTokensCursor::new(config.version),
        }
    }

    /// Returns the configuration the writer writes in.
    pub fn config(&self) -> SmtWriterConfig {
        let style = match self.position {
            Position::Line(_) => SmtWriteStyle::Line,
            Position::Layout(_) => SmtWriteStyle::Layout,
            Position::Compact(_) => SmtWriteStyle::Compact,
        };
        SmtWriterConfig::new(self.version).with_style(style)
    }

    /// Returns the version the writer writes in.
    pub fn version(&self) -> SmtVersion {
        self.version
    }

    /// Sets the version the writer writes the following tokens in.
    ///
    /// This is the only way the version in force can be changed:
    /// the writer does not follow the version of [`SmtCursor`].
    pub fn set_version(&mut self, version: SmtVersion) {
        self.version = version;
    }

    /// Returns a reference to the underlying writer.
    pub fn get_ref(&self) -> &W {
        &self.writer
    }

    /// Returns a mutable reference to the underlying writer.
    pub fn get_mut(&mut self) -> &mut W {
        &mut self.writer
    }

    /// Destructures into the underlying writer.
    pub fn into_inner(self) -> W {
        self.writer
    }

    /// Writes the tokens of the value.
    ///
    /// The value does not end an input: values written one after another are laid out as
    /// consecutive tokens, e.g. `(a)(b)` in the [`Layout`](SmtWriteStyle::Layout) style. An
    /// [`SmtToken::EndOfFile`] among the tokens ends an input.
    ///
    /// Returns an error if a reserved word is not reserved in the version written in, or if
    /// writing to the underlying writer fails. The tokens before the failing one have been
    /// written.
    pub fn write<V: SmtAppendTokens + ?Sized>(&mut self, value: &V) -> Result<(), SmtWriteError> {
        let kept = std::mem::replace(&mut self.cursor, SmtTokensCursor::new(self.version));
        let mut cursor = kept.recycle(self.version);
        value.append_tokens(&mut cursor);
        let mut result = Ok(());
        while let Some(token) = cursor.next() {
            if let Err(err) = self.write_token(token) {
                result = Err(err);
                break;
            }
        }
        self.cursor = cursor.recycle(self.version);
        result
    }

    /// Writes the token, returning whether it ended the input.
    #[inline]
    fn write_token(&mut self, token: SmtToken<'_>) -> Result<bool, SmtWriteError> {
        match &mut self.position {
            Position::Line(position) => position.write_token(&mut self.writer, self.version, token),
            Position::Layout(position) => {
                position.write_token(&mut self.writer, self.version, token)
            }
            Position::Compact(position) => {
                position.write_token(&mut self.writer, self.version, token)
            }
        }
    }
}

impl<W: Write> SmtConsume for SmtWriter<W> {
    type Result = ();
    type Error = SmtWriteError;
    const IS_CONCRETE: bool = true;
}

impl<W: Write, Z: SmtCursor> SmtConsumeFrom<Z> for SmtWriter<W> {
    fn consume(&mut self, cursor: &mut Z) -> Result<ControlFlow<()>, SmtWriteError> {
        while let Some(token) = cursor.next() {
            if self.write_token(cursor.syntax(&token))? {
                return Ok(ControlFlow::Break(()));
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Where a writer is in what it writes, in its style.
#[derive(Debug)]
enum Position {
    Line(LinePosition),
    Layout(LayoutPosition),
    Compact(CompactPosition),
}

/// Where a writer in the line style is on the line it writes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LinePosition {
    /// At the start of a line.
    Start,
    /// After an opening parenthesis.
    AfterOpen,
    /// After any other token.
    AfterToken,
    /// After a comment, written without its line ending.
    AfterComment,
    /// After the end of an input, not at the start of a line.
    AfterInput,
}

impl LinePosition {
    fn new() -> Self {
        Self::Start
    }

    /// Writes the token, returning whether it ended the input.
    #[inline]
    fn write_token<W: Write>(
        &mut self,
        writer: &mut W,
        version: SmtVersion,
        token: SmtToken<'_>,
    ) -> Result<bool, SmtWriteError> {
        match token {
            SmtToken::Whitespace(_) => return Ok(false),
            SmtToken::EndOfFile => {
                // the line is ended only if another input follows
                if *self != Self::Start {
                    *self = Self::AfterInput;
                }
                return Ok(true);
            }
            _ => {}
        }
        match (*self, token) {
            // anything after a comment would be a part of it,
            // and each input starts on a line of its own
            (Self::AfterComment | Self::AfterInput, _) => writer.write_all(b"\n")?,
            (Self::AfterToken, SmtToken::ParenClose) => {}
            (Self::AfterToken, _) => writer.write_all(b" ")?,
            _ => {}
        }
        *self = match token {
            SmtToken::Comment(comment) => {
                // the comment is ended by a line feed only if a token follows
                let content = comment.as_slice();
                let content = match content.last() {
                    Some(b'\r' | b'\n') => &content[..content.len() - 1],
                    _ => content,
                };
                writer.write_all(b";")?;
                writer.write_all(content)?;
                Self::AfterComment
            }
            SmtToken::ParenOpen => {
                writer.write_all(b"(")?;
                Self::AfterOpen
            }
            _ => {
                token.write_smt(writer, version)?;
                Self::AfterToken
            }
        };
        Ok(false)
    }
}

/// Where a writer in the layout style is.
#[derive(Debug)]
struct LayoutPosition {
    last: LayoutLast,
    /// Whether an input ended since the last token was written.
    input_ended: bool,
}

/// What the layout writer wrote last, as far as the next token cares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LayoutLast {
    /// Nothing, or a line feed.
    LineStart,
    /// A parenthesis, or whitespace or a comment ending otherwise.
    Delimiter,
    /// A token other than a parenthesis, whitespace or a comment.
    Atom,
    /// A comment without its line ending.
    OpenComment,
}

impl LayoutPosition {
    fn new() -> Self {
        Self {
            last: LayoutLast::LineStart,
            input_ended: false,
        }
    }

    /// Writes the token, returning whether it ended the input.
    #[inline]
    fn write_token<W: Write>(
        &mut self,
        writer: &mut W,
        version: SmtVersion,
        token: SmtToken<'_>,
    ) -> Result<bool, SmtWriteError> {
        let is_atom = !matches!(
            token,
            SmtToken::ParenOpen
                | SmtToken::ParenClose
                | SmtToken::Whitespace(_)
                | SmtToken::Comment(_)
                | SmtToken::EndOfFile
        );
        if matches!(token, SmtToken::EndOfFile) {
            self.input_ended = true;
            return Ok(true);
        }
        if self.input_ended {
            // each input starts on a line of its own
            self.input_ended = false;
            if self.last != LayoutLast::LineStart {
                writer.write_all(b"\n")?;
                self.last = LayoutLast::LineStart;
            }
        }
        match self.last {
            // anything after an open comment would be a part of it
            LayoutLast::OpenComment => writer.write_all(b"\n")?,
            // two atoms in a row would be read as one, or not at all
            LayoutLast::Atom if is_atom => writer.write_all(b" ")?,
            _ => {}
        }
        token.write_smt(writer, version)?;
        self.last = match token {
            SmtToken::Whitespace(whitespace) => match whitespace.as_slice().last() {
                Some(b'\n') => LayoutLast::LineStart,
                _ => LayoutLast::Delimiter,
            },
            SmtToken::Comment(comment) => match comment.as_slice().last() {
                Some(b'\n') => LayoutLast::LineStart,
                Some(b'\r') => LayoutLast::Delimiter,
                _ => LayoutLast::OpenComment,
            },
            _ if is_atom => LayoutLast::Atom,
            _ => LayoutLast::Delimiter,
        };
        Ok(false)
    }
}

/// Where a writer in the compact style is.
#[derive(Debug)]
struct CompactPosition {
    depth: u64,
    line: CompactLine,
}

/// Where the compact writer is on the line it writes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompactLine {
    /// At the start of a line.
    Start,
    /// After an opening parenthesis.
    AfterOpen,
    /// After any other token.
    AfterToken,
}

impl CompactPosition {
    fn new() -> Self {
        Self {
            depth: 0,
            line: CompactLine::Start,
        }
    }

    /// Writes the token, returning whether it ended the input.
    #[inline]
    fn write_token<W: Write>(
        &mut self,
        writer: &mut W,
        version: SmtVersion,
        token: SmtToken<'_>,
    ) -> Result<bool, SmtWriteError> {
        match token {
            SmtToken::Whitespace(_) => {}
            SmtToken::Comment(comment) => {
                if self.line != CompactLine::Start {
                    writer.write_all(b"\n")?;
                }
                // the line feed below ends the comment in place of its own ending
                let content = comment.as_slice();
                let content = match content.last() {
                    Some(b'\r' | b'\n') => &content[..content.len() - 1],
                    _ => content,
                };
                writer.write_all(b";")?;
                writer.write_all(content)?;
                writer.write_all(b"\n")?;
                self.line = CompactLine::Start;
            }
            SmtToken::EndOfFile => {
                if self.line != CompactLine::Start {
                    writer.write_all(b"\n")?;
                }
                self.depth = 0;
                self.line = CompactLine::Start;
                return Ok(true);
            }
            SmtToken::ParenOpen => {
                if self.line == CompactLine::AfterToken {
                    writer.write_all(b" ")?;
                }
                writer.write_all(b"(")?;
                self.depth += 1;
                self.line = CompactLine::AfterOpen;
            }
            SmtToken::ParenClose => {
                writer.write_all(b")")?;
                // a closing parenthesis outside of parentheses ends an item too
                self.depth = self.depth.saturating_sub(1);
                self.end_token(writer)?;
            }
            _ => {
                if self.line == CompactLine::AfterToken {
                    writer.write_all(b" ")?;
                }
                token.write_smt(writer, version)?;
                self.end_token(writer)?;
            }
        }
        Ok(false)
    }

    /// Ends the line after a token that ends a top-level item.
    #[inline]
    fn end_token<W: Write>(&mut self, writer: &mut W) -> Result<(), SmtWriteError> {
        if self.depth == 0 {
            writer.write_all(b"\n")?;
            self.line = CompactLine::Start;
        } else {
            self.line = CompactLine::AfterToken;
        }
        Ok(())
    }
}
