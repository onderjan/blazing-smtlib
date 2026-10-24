use std::{collections::VecDeque, io::Write, ops::ControlFlow};

use super::{
    SmtAppendTokens, SmtConsume, SmtConsumeFrom, SmtCursor, SmtSyntaxToken, SmtTokensCursor,
    SmtVersion, SmtWriteError,
};

/// Writes tokens as SMT-LIB text in the compact form.
///
/// The canonical form of tokens is their text with one space between two
/// tokens, except after an opening and before a closing parenthesis, and a
/// line feed after each top-level item, that is, after the closing
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
#[derive(Debug)]
pub struct SmtCompactTokenWriter<W: Write> {
    writer: W,
    version: SmtVersion,
    depth: u64,
    line: CompactLine,
    /// Kept for [`Self::write`] to reuse its allocation, empty between calls.
    cursor: SmtTokensCursor<'static>,
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

impl<W: Write> SmtCompactTokenWriter<W> {
    /// Constructs a writer into `writer` that writes in the version.
    pub fn new(writer: W, version: SmtVersion) -> Self {
        Self {
            writer,
            version,
            depth: 0,
            line: CompactLine::Start,
            cursor: SmtTokensCursor::new(version),
        }
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
        let mut cursor = recycle(kept);
        cursor.version = self.version;
        value.append_tokens(&mut cursor);
        let mut result = Ok(());
        while let Some(token) = cursor.next() {
            if let Err(err) = self.write_token(token) {
                result = Err(err);
                break;
            }
        }
        self.cursor = recycle(cursor);
        result
    }

    /// Writes the token, returning whether it ended the input.
    #[inline]
    fn write_token(&mut self, token: SmtSyntaxToken<'_>) -> Result<bool, SmtWriteError> {
        match token {
            SmtSyntaxToken::Whitespace(_) => {}
            SmtSyntaxToken::Comment(comment) => {
                if self.line != CompactLine::Start {
                    self.writer.write_all(b"\n")?;
                }
                // the line feed below ends the comment in place of its own ending
                let content = comment.as_slice();
                let content = match content.last() {
                    Some(b'\r' | b'\n') => &content[..content.len() - 1],
                    _ => content,
                };
                self.writer.write_all(b";")?;
                self.writer.write_all(content)?;
                self.writer.write_all(b"\n")?;
                self.line = CompactLine::Start;
            }
            SmtSyntaxToken::EndOfFile => {
                if self.line != CompactLine::Start {
                    self.writer.write_all(b"\n")?;
                }
                self.depth = 0;
                self.line = CompactLine::Start;
                return Ok(true);
            }
            SmtSyntaxToken::ParenOpen => {
                if self.line == CompactLine::AfterToken {
                    self.writer.write_all(b" ")?;
                }
                self.writer.write_all(b"(")?;
                self.depth += 1;
                self.line = CompactLine::AfterOpen;
            }
            SmtSyntaxToken::ParenClose => {
                self.writer.write_all(b")")?;
                // a closing parenthesis outside of parentheses ends an item too
                self.depth = self.depth.saturating_sub(1);
                self.end_token()?;
            }
            _ => {
                if self.line == CompactLine::AfterToken {
                    self.writer.write_all(b" ")?;
                }
                token.write_smt(&mut self.writer, self.version)?;
                self.end_token()?;
            }
        }
        Ok(false)
    }

    /// Ends the line after a token that ends a top-level item.
    #[inline]
    fn end_token(&mut self) -> Result<(), SmtWriteError> {
        if self.depth == 0 {
            self.writer.write_all(b"\n")?;
            self.line = CompactLine::Start;
        } else {
            self.line = CompactLine::AfterToken;
        }
        Ok(())
    }
}

impl<W: Write> SmtConsume for SmtCompactTokenWriter<W> {
    type Result = ();
    type Error = SmtWriteError;
    const IS_CONCRETE: bool = true;
}

impl<W: Write, Z: SmtCursor> SmtConsumeFrom<Z> for SmtCompactTokenWriter<W> {
    fn consume(&mut self, cursor: &mut Z) -> Result<ControlFlow<()>, SmtWriteError> {
        while let Some(token) = cursor.next() {
            if self.write_token(cursor.syntax(&token))? {
                return Ok(ControlFlow::Break(()));
            }
        }
        Ok(ControlFlow::Continue(()))
    }
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

/// Writes tokens as SMT-LIB text in the layout they are handed over in.
///
/// Whitespace and comments are written as they are. A space is written only
/// between two tokens that would otherwise run together, and a line feed
/// only after a comment without a line ending that is followed by a token.
/// Tokens read from a script and written in the version they were read in
/// are written back as the script was, except that in SMT-LIB 2.0, every
/// backslash in a string is written escaped: `"a\q"` is written back as
/// `"a\\q"`, which is read as the same string.
///
/// The writer can be handed tokens without their whitespace and comments;
/// it then writes only the spaces that keep the tokens apart.
///
/// At the end of an input, the writer starts the next input on a new line:
/// it writes a line feed before the next token unless what it wrote ends
/// with one.
#[derive(Debug)]
pub struct SmtLayoutTokenWriter<W: Write> {
    writer: W,
    version: SmtVersion,
    last: LayoutLast,
    /// Whether an input ended since the last token was written.
    input_ended: bool,
    /// Kept for [`Self::write`] to reuse its allocation, empty between calls.
    cursor: SmtTokensCursor<'static>,
}

impl<W: Write> SmtLayoutTokenWriter<W> {
    /// Constructs a writer into `writer` that writes in the version.
    pub fn new(writer: W, version: SmtVersion) -> Self {
        Self {
            writer,
            version,
            last: LayoutLast::LineStart,
            input_ended: false,
            cursor: SmtTokensCursor::new(version),
        }
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
        let mut cursor = recycle(kept);
        cursor.version = self.version;
        value.append_tokens(&mut cursor);
        let mut result = Ok(());
        while let Some(token) = cursor.next() {
            if let Err(err) = self.write_token(token) {
                result = Err(err);
                break;
            }
        }
        self.cursor = recycle(cursor);
        result
    }

    /// Writes the token, returning whether it ended the input.
    #[inline]
    fn write_token(&mut self, token: SmtSyntaxToken<'_>) -> Result<bool, SmtWriteError> {
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
                self.writer.write_all(b"\n")?;
                self.last = LayoutLast::LineStart;
            }
        }
        match self.last {
            // anything after an open comment would be a part of it
            LayoutLast::OpenComment => self.writer.write_all(b"\n")?,
            // two atoms in a row would be read as one, or not at all
            LayoutLast::Atom if is_atom => self.writer.write_all(b" ")?,
            _ => {}
        }
        token.write_smt(&mut self.writer, self.version)?;
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

impl<W: Write> SmtConsume for SmtLayoutTokenWriter<W> {
    type Result = ();
    type Error = SmtWriteError;
    const IS_CONCRETE: bool = true;
}

impl<W: Write, Z: SmtCursor> SmtConsumeFrom<Z> for SmtLayoutTokenWriter<W> {
    fn consume(&mut self, cursor: &mut Z) -> Result<ControlFlow<()>, SmtWriteError> {
        while let Some(token) = cursor.next() {
            if self.write_token(cursor.syntax(&token))? {
                return Ok(ControlFlow::Break(()));
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Empties the cursor for tokens of another lifetime, keeping its allocation.
fn recycle<'b>(cursor: SmtTokensCursor<'_>) -> SmtTokensCursor<'b> {
    let SmtTokensCursor {
        mut tokens,
        version,
        ..
    } = cursor;
    tokens.clear();
    // an empty deque becomes a vector without moving or reallocating, and an
    // empty vector mapped and collected keeps its allocation in the new type
    let tokens: Vec<SmtSyntaxToken<'b>> = Vec::from(tokens)
        .into_iter()
        .map(|_| SmtSyntaxToken::EndOfFile)
        .collect();
    SmtTokensCursor {
        tokens: VecDeque::from(tokens),
        discarding: false,
        version,
    }
}
