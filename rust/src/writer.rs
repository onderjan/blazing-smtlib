use std::{
    error::Error,
    fmt,
    io::{self, Write},
    ops::ControlFlow,
};

use crate::{
    SmtVersion,
    token::{
        SmtAppendTokens, SmtConsume, SmtConsumeFrom, SmtCursor, SmtReserved, SmtSyntaxToken,
        SmtTokensCursor,
    },
};

/// Determines why writing a token has failed.
#[derive(Debug)]
pub enum SmtWriteErrorCause {
    /// Writing to the writer failed.
    Io(io::Error),
    /// The reserved word is not reserved in the version, so no text in it is the token.
    NotInVersion(SmtReserved),
}

/// An error that ended writing a token.
#[derive(Debug)]
pub struct SmtWriteError(SmtWriteErrorCause);

impl SmtWriteError {
    #[inline]
    pub(crate) fn new(cause: SmtWriteErrorCause) -> Self {
        Self(cause)
    }

    /// Determines why writing has failed.
    pub fn cause(&self) -> &SmtWriteErrorCause {
        &self.0
    }

    /// Convert into the enumeration that determines why writing has failed.
    pub fn into_cause(self) -> SmtWriteErrorCause {
        self.0
    }
}

impl From<io::Error> for SmtWriteError {
    fn from(err: io::Error) -> Self {
        Self(SmtWriteErrorCause::Io(err))
    }
}

impl fmt::Display for SmtWriteErrorCause {
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
            SmtWriteErrorCause::Io(err) => err.source(),
            SmtWriteErrorCause::NotInVersion(_) => None,
        }
    }
}

/// How a writer lays out the tokens it writes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum SmtWriteStyle {
    /// Writes tokens on a single line, as far as comments allow.
    ///
    /// Tokens are written with one space between two tokens, except after an
    /// opening and before a closing parenthesis, top-level items included.
    /// Whitespace is not written. A comment is written after a space, without
    /// its line ending; a line feed ends it only if a token follows it.
    ///
    /// The writer can be handed tokens without their whitespace and comments;
    /// it then writes them all on one line, with no line feed at the end.
    ///
    /// At the end of an input, the writer ends the line it is on, so that the
    /// next input starts on a line of its own.
    Line,
    /// Writes tokens in the compact form.
    ///
    /// The canonical form of tokens is their text with one space between two
    /// tokens, except after an opening and before a closing parenthesis, and
    /// a line feed after each top-level item, that is, after the closing
    /// parenthesis that closes every open one and after a token outside of
    /// parentheses. The compact form is the canonical form with the comments:
    /// each comment is written on a line of its own, ended by a line feed.
    /// Whitespace is not written.
    ///
    /// The writer can be handed tokens without their whitespace and comments;
    /// it then writes the canonical form.
    ///
    /// At the end of the input, the writer ends the line it is on and starts
    /// anew, as if no parenthesis were open.
    Compact,
    /// Writes tokens in the layout they are handed over in.
    ///
    /// Whitespace and comments are written as they are. A space is written
    /// only between two tokens that would otherwise run together, and a line
    /// feed only after a comment without a line ending that is followed by a
    /// token. Tokens read from a script and written in the version they were
    /// read in are written back as the script was, except that in SMT-LIB 2.0,
    /// every backslash in a string is written escaped: `"a\q"` is written back
    /// as `"a\\q"`, which is read as the same string.
    ///
    /// The writer can be handed tokens without their whitespace and comments;
    /// it then writes only the spaces that keep the tokens apart.
    ///
    /// At the end of an input, the writer starts the next input on a new
    /// line: it writes a line feed before the next token unless what it wrote
    /// ends with one.
    #[default]
    Layout,
}

/// How a writer writes: the version it writes in and its style.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SmtWriterConfig {
    version: SmtVersion,
    style: SmtWriteStyle,
}

impl SmtWriterConfig {
    /// Constructs the configuration of writing in the version, in the default style.
    pub fn new(version: SmtVersion) -> Self {
        Self {
            version,
            style: SmtWriteStyle::default(),
        }
    }

    /// The configuration with the style replaced.
    pub fn with_style(self, style: SmtWriteStyle) -> Self {
        Self { style, ..self }
    }

    /// The version written in.
    pub fn version(&self) -> SmtVersion {
        self.version
    }

    /// The style written in.
    pub fn style(&self) -> SmtWriteStyle {
        self.style
    }
}

/// Writes tokens as SMT-LIB text, in the version and the style of its configuration.
#[derive(Debug)]
pub struct SmtWriter<W: Write> {
    writer: W,
    version: SmtVersion,
    position: Position,
    /// Kept for [`Self::write`] to reuse its allocation, empty between calls.
    cursor: SmtTokensCursor<'static>,
}

impl<W: Write> SmtWriter<W> {
    /// Constructs a writer into `writer` that writes as configured.
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

    /// The configuration the writer writes in.
    pub fn config(&self) -> SmtWriterConfig {
        let style = match self.position {
            Position::Line(_) => SmtWriteStyle::Line,
            Position::Layout(_) => SmtWriteStyle::Layout,
            Position::Compact(_) => SmtWriteStyle::Compact,
        };
        SmtWriterConfig::new(self.version).with_style(style)
    }

    /// The version the writer writes in.
    pub fn version(&self) -> SmtVersion {
        self.version
    }

    /// Sets the version the writer writes the following tokens in.
    pub fn set_version(&mut self, version: SmtVersion) {
        self.version = version;
    }

    pub fn get_ref(&self) -> &W {
        &self.writer
    }

    pub fn get_mut(&mut self) -> &mut W {
        &mut self.writer
    }

    pub fn into_inner(self) -> W {
        self.writer
    }

    /// Writes the tokens of the value.
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
    fn write_token(&mut self, token: SmtSyntaxToken<'_>) -> Result<bool, SmtWriteError> {
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
        token: SmtSyntaxToken<'_>,
    ) -> Result<bool, SmtWriteError> {
        match token {
            SmtSyntaxToken::Whitespace(_) => return Ok(false),
            SmtSyntaxToken::EndOfFile => {
                if *self != Self::Start {
                    writer.write_all(b"\n")?;
                }
                *self = Self::Start;
                return Ok(true);
            }
            _ => {}
        }
        match (*self, token) {
            // anything after a comment would be a part of it
            (Self::AfterComment, _) => writer.write_all(b"\n")?,
            (Self::AfterToken, SmtSyntaxToken::ParenClose) => {}
            (Self::AfterToken, _) => writer.write_all(b" ")?,
            _ => {}
        }
        *self = match token {
            SmtSyntaxToken::Comment(comment) => {
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
            SmtSyntaxToken::ParenOpen => {
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
        token: SmtSyntaxToken<'_>,
    ) -> Result<bool, SmtWriteError> {
        let is_atom = !matches!(
            token,
            SmtSyntaxToken::ParenOpen
                | SmtSyntaxToken::ParenClose
                | SmtSyntaxToken::Whitespace(_)
                | SmtSyntaxToken::Comment(_)
                | SmtSyntaxToken::EndOfFile
        );
        if matches!(token, SmtSyntaxToken::EndOfFile) {
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
            SmtSyntaxToken::Whitespace(whitespace) => match whitespace.as_slice().last() {
                Some(b'\n') => LayoutLast::LineStart,
                _ => LayoutLast::Delimiter,
            },
            SmtSyntaxToken::Comment(comment) => match comment.as_slice().last() {
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
        token: SmtSyntaxToken<'_>,
    ) -> Result<bool, SmtWriteError> {
        match token {
            SmtSyntaxToken::Whitespace(_) => {}
            SmtSyntaxToken::Comment(comment) => {
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
            SmtSyntaxToken::EndOfFile => {
                if self.line != CompactLine::Start {
                    writer.write_all(b"\n")?;
                }
                self.depth = 0;
                self.line = CompactLine::Start;
                return Ok(true);
            }
            SmtSyntaxToken::ParenOpen => {
                if self.line == CompactLine::AfterToken {
                    writer.write_all(b" ")?;
                }
                writer.write_all(b"(")?;
                self.depth += 1;
                self.line = CompactLine::AfterOpen;
            }
            SmtSyntaxToken::ParenClose => {
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
