module

public import BSmtLib.Token.AppendTokens
public import BSmtLib.Token.ConsumeFrom

public section

/- LEAN: Rust's module `token::writer`; the root module `BSmtLib` imports it, and the writers are
re-exported into `BSmtLib.Token`, as Rust's `pub use writer::*` in `token.rs` does. Rust's
`writer` is any `Write`; here an `IO.FS.Stream`, as for `SyntaxToken.writeSmt`. A writer writes
the bytes of a token in one call of the stream's `write`, where Rust writes them in pieces; the
bytes written are the same. Rust's writers keep a cursor for `write` to reuse its allocation;
here `write` makes its own. -/

open BSmtLib.Plain

namespace BSmtLib.Token.Writer

/-- Writes the bytes, catching an error of the stream. -/
@[inline]
private def emit {n : Type → Type} [Monad n] [MonadLiftT IO n] (writer : IO.FS.Stream)
    (bytes : ByteArray) : n (Except WriteError Unit) := do
  if bytes.isEmpty then return .ok ()
  let written : IO (Except IO.Error Unit) := (writer.write bytes).toBaseIO
  match ← written with
  | .error err => return .error (WriteError.Internal.new (.io err))
  | .ok () => return .ok ()

/-- The bytes of the slice appended. -/
@[inline]
private def appendSlice (out : ByteArray) (bytes : ByteSlice) : ByteArray :=
  bytes.byteArray.copySlice bytes.start out out.size bytes.size false

/--
Writes `before`, then the token as SMT-LIB text in the version, with `after` after it; if the
token is a reserved word not in the version, writes `before` and fails.
-/
@[inline]
private def emitToken {n : Type → Type} [Monad n] [MonadLiftT IO n] (writer : IO.FS.Stream)
    (before : ByteArray) (token : SyntaxToken) (version : Version) (after : ByteArray) :
    n (Except WriteError Unit) := do
  match SyntaxToken.Internal.appendSmt token before version with
  | .ok bytes => emit writer (bytes ++ after)
  | .error word =>
    match ← emit writer before with
    | .error err => return .error err
    | .ok () => return .error (WriteError.Internal.new (.notInVersion word))

/- LEAN: Rust's private `CompactLine`. -/
/-- Where the compact writer is on the line it writes. -/
inductive Internal.CompactLine where
  /-- At the start of a line. -/
  | start
  /-- After an opening parenthesis. -/
  | afterOpen
  /-- After any other token. -/
  | afterToken
  deriving BEq

/--
Writes tokens as SMT-LIB text in the compact form.

The canonical form of tokens is their text with one space between two
tokens, except after an opening and before a closing parenthesis, and a
line feed after each top-level item, that is, after the closing
parenthesis that closes every open one and after a token outside of
parentheses. The compact form is the canonical form with the comments:
each comment is written on a line of its own, ended by a line feed.
Whitespace is not written.

The writer can be handed tokens without their whitespace and comments;
it then writes the canonical form.

At the end of the input, the writer ends the line it is on and starts
anew, as if no parenthesis were open.
-/
structure CompactTokenWriter where
  private mk ::
  private writer : IO.FS.Stream
  private versionInForce : Version
  private depth : Nat
  private line : Internal.CompactLine

namespace CompactTokenWriter

/-- Constructs a writer into `writer` that writes in the version. -/
def new (writer : IO.FS.Stream) (version : Version) : CompactTokenWriter :=
  ⟨writer, version, 0, .start⟩

/-- The version the writer writes in. -/
def version (self : CompactTokenWriter) : Version := self.versionInForce

/-- Sets the version the writer writes the following tokens in. -/
def setVersion (self : CompactTokenWriter) (version : Version) : CompactTokenWriter :=
  { self with versionInForce := version }

def getRef (self : CompactTokenWriter) : IO.FS.Stream := self.writer

def intoInner (self : CompactTokenWriter) : IO.FS.Stream := self.writer

/- LEAN: Rust's private `write_token`, which returns the writer as it is after the token. -/
/-- Writes the token, returning whether it ended the input. -/
@[inline]
def Internal.writeToken {n : Type → Type} [Monad n] [MonadLiftT IO n]
    (self : CompactTokenWriter) (token : SyntaxToken) :
    n (Except WriteError Bool × CompactTokenWriter) := do
  -- the line feed that ends a line not at its start
  let lineEnd : ByteArray := if self.line != .start then ByteArray.empty.push (byte! '\n')
    else .empty
  -- the space before a token after a token
  let space : ByteArray := if self.line == .afterToken then ByteArray.empty.push (byte! ' ')
    else .empty
  match token with
  | .whitespace _ => return (.ok false, self)
  | .comment comment =>
    let content := comment.asSlice
    -- the line feed below ends the comment in place of its own ending
    let content := match content[content.size - 1]? with
      | some byte => if byte == byte! '\r' || byte == byte! '\n' then
          content.slice 0 (content.size - 1) else content
      | none => content
    let bytes := (appendSlice (lineEnd.push (byte! ';')) content).push (byte! '\n')
    match ← emit self.writer bytes with
    | .error err => return (.error err, self)
    | .ok () => return (.ok false, { self with line := .start })
  | .endOfFile =>
    match ← emit self.writer lineEnd with
    | .error err => return (.error err, self)
    | .ok () => return (.ok true, { self with depth := 0, line := .start })
  | .parenOpen =>
    match ← emit self.writer (space.push (byte! '(')) with
    | .error err => return (.error err, self)
    | .ok () => return (.ok false, { self with depth := self.depth + 1, line := .afterOpen })
  | .parenClose =>
    -- a closing parenthesis outside of parentheses ends an item too
    let depth := self.depth - 1
    -- the line ends after a token that ends a top-level item
    let after := if depth == 0 then ByteArray.empty.push (byte! '\n') else .empty
    match ← emit self.writer ((ByteArray.empty.push (byte! ')')) ++ after) with
    | .error err => return (.error err, self)
    | .ok () =>
      return (.ok false, { self with depth, line := if depth == 0 then .start else .afterToken })
  | _ =>
    let after := if self.depth == 0 then ByteArray.empty.push (byte! '\n') else .empty
    match ← emitToken self.writer space token self.versionInForce after with
    | .error err => return (.error err, self)
    | .ok () =>
      return (.ok false, { self with line := if self.depth == 0 then .start else .afterToken })

/-- Writes the tokens of the cursor from the first on, until none is left, one ends the input
or writing fails. -/
private def writeTokens {n : Type → Type} [Monad n] [MonadLiftT IO n]
    (self : CompactTokenWriter) (cursor : TokensCursor) :
    n (Except WriteError Unit × CompactTokenWriter) := do
  match Cursor.next? cursor with
  | none => return (.ok (), self)
  | some (token, ⟨next, _⟩) =>
    match ← Internal.writeToken self token with
    | (.error err, self) => return (.error err, self)
    | (.ok _, self) => writeTokens self next
termination_by (⟨cursor⟩ :
  Cursor.Internal.Draining (Z := TokensCursor) Cursor.Consumed Cursor.consumed_wf)
decreasing_by assumption

/-- Writes the tokens of the value. -/
def write {n : Type → Type} [Monad n] [MonadLiftT IO n] {V : Type} [AppendTokens V]
    (self : CompactTokenWriter) (value : V) : n (Except WriteError Unit × CompactTokenWriter) :=
  writeTokens self (AppendTokens.appendTokens value (TokensCursor.new self.versionInForce))

end CompactTokenWriter

/- LEAN: Rust's private `LayoutLast`. -/
/-- What the layout writer wrote last, as far as the next token cares. -/
inductive Internal.LayoutLast where
  /-- Nothing, or a line feed. -/
  | lineStart
  /-- A parenthesis, or whitespace or a comment ending otherwise. -/
  | delimiter
  /-- A token other than a parenthesis, whitespace or a comment. -/
  | atom
  /-- A comment without its line ending. -/
  | openComment
  deriving BEq

/--
Writes tokens as SMT-LIB text in the layout they are handed over in.

Whitespace and comments are written as they are. A space is written only
between two tokens that would otherwise run together, and a line feed
only after a comment without a line ending that is followed by a token.
Tokens read from a script and written in the version they were read in
are written back as the script was, except that in SMT-LIB 2.0, every
backslash in a string is written escaped: `"a\q"` is written back as
`"a\\q"`, which is read as the same string.

The writer can be handed tokens without their whitespace and comments;
it then writes only the spaces that keep the tokens apart.

At the end of an input, the writer starts the next input on a new line:
it writes a line feed before the next token unless what it wrote ends
with one.
-/
structure LayoutTokenWriter where
  private mk ::
  private writer : IO.FS.Stream
  private versionInForce : Version
  private last : Internal.LayoutLast
  /-- Whether an input ended since the last token was written. -/
  private inputEnded : Bool

namespace LayoutTokenWriter

/-- Constructs a writer into `writer` that writes in the version. -/
def new (writer : IO.FS.Stream) (version : Version) : LayoutTokenWriter :=
  ⟨writer, version, .lineStart, false⟩

/-- The version the writer writes in. -/
def version (self : LayoutTokenWriter) : Version := self.versionInForce

/-- Sets the version the writer writes the following tokens in. -/
def setVersion (self : LayoutTokenWriter) (version : Version) : LayoutTokenWriter :=
  { self with versionInForce := version }

def getRef (self : LayoutTokenWriter) : IO.FS.Stream := self.writer

def intoInner (self : LayoutTokenWriter) : IO.FS.Stream := self.writer

/-- What the writer wrote last after the token. -/
private def lastAfter (token : SyntaxToken) : Internal.LayoutLast :=
  match token with
  | .whitespace whitespace =>
    let bytes := whitespace.asSlice
    if bytes[bytes.size - 1]? == some (byte! '\n') then .lineStart else .delimiter
  | .comment comment =>
    let bytes := comment.asSlice
    match bytes[bytes.size - 1]? with
    | some byte =>
      if byte == byte! '\n' then .lineStart
      else if byte == byte! '\r' then .delimiter
      else .openComment
    | none => .openComment
  | .parenOpen | .parenClose | .endOfFile => .delimiter
  | _ => .atom

/- LEAN: Rust's private `write_token`, which returns the writer as it is after the token. -/
/-- Writes the token, returning whether it ended the input. -/
@[inline]
def Internal.writeToken {n : Type → Type} [Monad n] [MonadLiftT IO n]
    (self : LayoutTokenWriter) (token : SyntaxToken) :
    n (Except WriteError Bool × LayoutTokenWriter) := do
  let isAtom := match token with
    | .parenOpen | .parenClose | .whitespace _ | .comment _ | .endOfFile => false
    | _ => true
  if let .endOfFile := token then
    return (.ok true, { self with inputEnded := true })
  let mut self := self
  let mut before := ByteArray.empty
  if self.inputEnded then
    -- each input starts on a line of its own
    self := { self with inputEnded := false }
    if self.last != .lineStart then
      before := before.push (byte! '\n')
      self := { self with last := .lineStart }
  match self.last with
  -- anything after an open comment would be a part of it
  | .openComment => before := before.push (byte! '\n')
  -- two atoms in a row would be read as one, or not at all
  | .atom => if isAtom then before := before.push (byte! ' ')
  | _ => pure ()
  match ← emitToken self.writer before token self.versionInForce .empty with
  | .error err => return (.error err, self)
  | .ok () => return (.ok false, { self with last := lastAfter token })

/-- Writes the tokens of the cursor from the first on, until none is left, one ends the input
or writing fails. -/
private def writeTokens {n : Type → Type} [Monad n] [MonadLiftT IO n]
    (self : LayoutTokenWriter) (cursor : TokensCursor) :
    n (Except WriteError Unit × LayoutTokenWriter) := do
  match Cursor.next? cursor with
  | none => return (.ok (), self)
  | some (token, ⟨next, _⟩) =>
    match ← Internal.writeToken self token with
    | (.error err, self) => return (.error err, self)
    | (.ok _, self) => writeTokens self next
termination_by (⟨cursor⟩ :
  Cursor.Internal.Draining (Z := TokensCursor) Cursor.Consumed Cursor.consumed_wf)
decreasing_by assumption

/-- Writes the tokens of the value. -/
def write {n : Type → Type} [Monad n] [MonadLiftT IO n] {V : Type} [AppendTokens V]
    (self : LayoutTokenWriter) (value : V) : n (Except WriteError Unit × LayoutTokenWriter) :=
  writeTokens self (AppendTokens.appendTokens value (TokensCursor.new self.versionInForce))

end LayoutTokenWriter

/- LEAN: the writers' `consume`, Rust's loop over the cursor's tokens, as one function over the
writer's `writeToken`. -/
/-- Writes the tokens of the cursor until none is left or one ends the input. -/
private def consumeTokens {W Z : Type} [Cursor Z]
    (writeToken : W → SyntaxToken → IO (Except WriteError Bool × W))
    (origin cursor : Z) (consumed : Cursor.Consumed cursor origin) :
    StateT W IO
      (Except WriteError (ControlFlow Unit) × { next : Z // Cursor.Consumed next origin }) := do
  match Cursor.next? cursor with
  | none => return (.ok .continue, ⟨cursor, consumed⟩)
  | some (token, ⟨next, hnext⟩) =>
    let (result, writer) ← writeToken (← get) (Cursor.syntax cursor token)
    set writer
    match result with
    | .error err => return (.error err, ⟨next, Cursor.consumed_trans hnext consumed⟩)
    | .ok true => return (.ok (.break ()), ⟨next, Cursor.consumed_trans hnext consumed⟩)
    | .ok false => consumeTokens writeToken origin next (Cursor.consumed_trans hnext consumed)
termination_by (⟨cursor⟩ : Cursor.Internal.Draining (Z := Z) Cursor.Consumed Cursor.consumed_wf)
decreasing_by exact hnext

/-- Writes the tokens of the cursor, which has one, until none is left or one ends the input. -/
private def consumeFrom {W Z : Type} [Cursor Z]
    (writeToken : W → SyntaxToken → IO (Except WriteError Bool × W))
    (cursor : Z) (has : Cursor.HasNext cursor) :
    StateT W IO
      (Except WriteError (ControlFlow Unit) × { next : Z // Cursor.Consumed next cursor }) := do
  match h : Cursor.next? cursor with
  | none => absurd (Cursor.next?_isSome has) (by simp [h])
  | some (token, ⟨next, hnext⟩) =>
    let (result, writer) ← writeToken (← get) (Cursor.syntax cursor token)
    set writer
    match result with
    | .error err => return (.error err, ⟨next, hnext⟩)
    | .ok true => return (.ok (.break ()), ⟨next, hnext⟩)
    | .ok false => consumeTokens writeToken cursor next hnext

@[no_expose] instance : Consume CompactTokenWriter Unit WriteError where
  isConcrete := true

@[no_expose] instance {Z : Type} [Cursor Z] : ConsumeFrom CompactTokenWriter Z IO where
  consume := consumeFrom CompactTokenWriter.Internal.writeToken

@[no_expose] instance : Consume LayoutTokenWriter Unit WriteError where
  isConcrete := true

@[no_expose] instance {Z : Type} [Cursor Z] : ConsumeFrom LayoutTokenWriter Z IO where
  consume := consumeFrom LayoutTokenWriter.Internal.writeToken

end BSmtLib.Token.Writer
