module

public import BSmtLib.Token.AppendTokens
public import BSmtLib.Token.ConsumeFrom

public section

/- LEAN: Rust's module `writer`, whose items `lib.rs` re-exports at the root. `SmtWriter` is named
like the module, so it is the module's own name, `BSmtLib.Writer`, and the other items are in its
namespace; `WriteError` and its cause are declared with `Token.writeSmt`, which fails with them.
Rust's `writer` is any `Write`; here an `IO.FS.Stream`, as for `Token.writeSmt`. A writer writes
the bytes of a token in one call of the stream's `write`, where Rust writes them in pieces; the
bytes written are the same. Rust's writer keeps a cursor for `write` to reuse its allocation;
here `write` makes its own. -/

open BSmtLib.Token

namespace BSmtLib.Writer

/--
How tokens are laid out by the writer (single line, compact, or as handed over).

Independently of the style chosen, new input started after EOF is separated by
a line feed (LF). LF is not added if nothing has been written or the previous input
ended with LF.
-/
inductive WriteStyle where
  /--
  Writes tokens separated by spaces, without unnecessary line breaks.

  Tokens are separated by spaces. As conventional, no space follows an opening or precedes
  a closing parenthesis. Unnecessary whitespace is dropped. A comment is separated by a space
  at its start and is terminated by LF only if another token follows it.

  ```text
  (assert x) (assert y) ; comment
  (check-sat) junk ; no line ending at the end
  ```
  -/
  | line
  /--
  Writes each top-level item and comment on a line of its own.

  Within an item, tokens are separated as in `line`. A line feed follows each
  top-level item.
  Whitespace is fully reformatted, and each comment is written on a line of
  its own, ended by a line feed.

  ```text
  (assert x)
  (assert y)
  ; comment
  (check-sat)
  junk
  ; LF at the end

  ```
  -/
  | compact
  /--
  Writes tokens in the layout they are handed over in.

  Whitespace and comments are written as they are. A space is added only between two tokens
  that would otherwise run together, and a line feed only after a comment without a line
  ending followed by a token. A script lexed and written in the version it was read in is
  thus written back as it was, except that in SMT-LIB 2.0, every backslash in a string is
  written escaped: `"a\q"` is written back as `"a\\q"`, which is read as the same string.
  -/
  | layout
  deriving BEq, Hashable, Repr

/- LEAN: `Inhabited` gives the default value, the Rust `#[default]`. -/
instance : Inhabited WriteStyle := ⟨.layout⟩

/- LEAN: Rust's fields are private and read through the getters `version()` and `style()`. Here
the constructor is private, so a configuration is made only by `new` and `withStyle`, and the
fields are read-only: their projections are the getters. -/
/-- Writer configuration (version in force and writing style). -/
structure WriterConfig where
  private mk ::
  /-- Returns the version written in. -/
  version : Version
  /-- Returns the style written in. -/
  style : WriteStyle
  deriving BEq, Hashable, Repr

namespace WriterConfig

/--
Creates a writer configuration with the given version and the default style
(`WriteStyle.layout`).
-/
def new (version : Version) : WriterConfig :=
  { version, style := default }

/-- Returns the configuration with the style replaced. -/
def withStyle (self : WriterConfig) (style : WriteStyle) : WriterConfig :=
  { self with style }

end WriterConfig

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
    (before : ByteArray) (token : Token) (version : Version) (after : ByteArray) :
    n (Except WriteError Unit) := do
  match Token.Internal.appendSmt token before version with
  | .ok bytes => emit writer (bytes ++ after)
  | .error word =>
    match ← emit writer before with
    | .error err => return .error err
    | .ok () => return .error (WriteError.Internal.new (.notInVersion word))

/-- The content of the comment without its line ending, if it has one. -/
@[inline]
private def commentText (comment : Lexicon.Value.Comment) : ByteSlice :=
  let content := comment.asSlice
  match content[content.size - 1]? with
  | some byte => if byte == byte! '\r' || byte == byte! '\n' then
      content.slice 0 (content.size - 1) else content
  | none => content

/- LEAN: Rust's private `LinePosition`. -/
/-- Where a writer in the line style is on the line it writes. -/
inductive Internal.LinePosition where
  /-- At the start of a line. -/
  | start
  /-- After an opening parenthesis. -/
  | afterOpen
  /-- After any other token. -/
  | afterToken
  /-- After a comment, written without its line ending. -/
  | afterComment
  /-- After the end of an input, not at the start of a line. -/
  | afterInput
  deriving BEq

/- LEAN: Rust's private `LinePosition::write_token`, which returns the position after the
token. -/
/-- Writes the token, returning whether it ended the input. -/
@[inline]
def Internal.LinePosition.writeToken {n : Type → Type} [Monad n] [MonadLiftT IO n]
    (self : Internal.LinePosition) (writer : IO.FS.Stream) (version : Version) (token : Token) :
    n (Except WriteError Bool × Internal.LinePosition) := do
  match token with
  | .whitespace _ => return (.ok false, self)
  | .endOfFile =>
    -- the line is ended only if another input follows
    return (.ok true, if self != .start then .afterInput else self)
  | _ =>
    let before : ByteArray := match self, token with
      -- anything after a comment would be a part of it,
      -- and each input starts on a line of its own
      | .afterComment, _ | .afterInput, _ => ByteArray.empty.push (byte! '\n')
      | .afterToken, .parenClose => .empty
      | .afterToken, _ => ByteArray.empty.push (byte! ' ')
      | _, _ => .empty
    match token with
    | .comment text =>
      -- the comment is ended by a line feed only if a token follows
      match ← emit writer (appendSlice (before.push (byte! ';')) (commentText text)) with
      | .error err => return (.error err, self)
      | .ok () => return (.ok false, .afterComment)
    | .parenOpen =>
      match ← emit writer (before.push (byte! '(')) with
      | .error err => return (.error err, self)
      | .ok () => return (.ok false, .afterOpen)
    | _ =>
      match ← emitToken writer before token version .empty with
      | .error err => return (.error err, self)
      | .ok () => return (.ok false, .afterToken)

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

/- LEAN: Rust's private `LayoutPosition`. -/
/-- Where a writer in the layout style is. -/
structure Internal.LayoutPosition where
  last : Internal.LayoutLast
  /-- Whether an input ended since the last token was written. -/
  inputEnded : Bool

/-- What the writer wrote last after the token. -/
private def lastAfter (token : Token) : Internal.LayoutLast :=
  match token with
  | .whitespace text =>
    let bytes := text.asSlice
    if bytes[bytes.size - 1]? == some (byte! '\n') then .lineStart else .delimiter
  | .comment text =>
    let bytes := text.asSlice
    match bytes[bytes.size - 1]? with
    | some byte =>
      if byte == byte! '\n' then .lineStart
      else if byte == byte! '\r' then .delimiter
      else .openComment
    | none => .openComment
  | .parenOpen | .parenClose | .endOfFile => .delimiter
  | _ => .atom

/- LEAN: Rust's private `LayoutPosition::write_token`, which returns the position after the
token. -/
/-- Writes the token, returning whether it ended the input. -/
@[inline]
def Internal.LayoutPosition.writeToken {n : Type → Type} [Monad n] [MonadLiftT IO n]
    (self : Internal.LayoutPosition) (writer : IO.FS.Stream) (version : Version) (token : Token) :
    n (Except WriteError Bool × Internal.LayoutPosition) := do
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
  match ← emitToken writer before token version .empty with
  | .error err => return (.error err, self)
  | .ok () => return (.ok false, { self with last := lastAfter token })

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

/- LEAN: Rust's private `CompactPosition`. The depth is a `Nat`, where Rust's is a `u64`. -/
/-- Where a writer in the compact style is. -/
structure Internal.CompactPosition where
  depth : Nat
  line : Internal.CompactLine

/- LEAN: Rust's private `CompactPosition::write_token`, which returns the position after the
token. Rust's `end_token` is the line feed written after a token that ends a top-level item. -/
/-- Writes the token, returning whether it ended the input. -/
@[inline]
def Internal.CompactPosition.writeToken {n : Type → Type} [Monad n] [MonadLiftT IO n]
    (self : Internal.CompactPosition) (writer : IO.FS.Stream) (version : Version) (token : Token) :
    n (Except WriteError Bool × Internal.CompactPosition) := do
  -- the line feed that ends a line not at its start
  let lineEnd : ByteArray := if self.line != .start then ByteArray.empty.push (byte! '\n')
    else .empty
  -- the space before a token after a token
  let space : ByteArray := if self.line == .afterToken then ByteArray.empty.push (byte! ' ')
    else .empty
  match token with
  | .whitespace _ => return (.ok false, self)
  | .comment text =>
    -- the line feed below ends the comment in place of its own ending
    let bytes := (appendSlice (lineEnd.push (byte! ';')) (commentText text)).push (byte! '\n')
    match ← emit writer bytes with
    | .error err => return (.error err, self)
    | .ok () => return (.ok false, { self with line := .start })
  | .endOfFile =>
    match ← emit writer lineEnd with
    | .error err => return (.error err, self)
    | .ok () => return (.ok true, { depth := 0, line := .start })
  | .parenOpen =>
    match ← emit writer (space.push (byte! '(')) with
    | .error err => return (.error err, self)
    | .ok () => return (.ok false, { depth := self.depth + 1, line := .afterOpen })
  | .parenClose =>
    -- a closing parenthesis outside of parentheses ends an item too
    let depth := self.depth - 1
    -- the line ends after a token that ends a top-level item
    let after := if depth == 0 then ByteArray.empty.push (byte! '\n') else .empty
    match ← emit writer ((ByteArray.empty.push (byte! ')')) ++ after) with
    | .error err => return (.error err, self)
    | .ok () => return (.ok false, { depth, line := if depth == 0 then .start else .afterToken })
  | _ =>
    let after := if self.depth == 0 then ByteArray.empty.push (byte! '\n') else .empty
    match ← emitToken writer space token version after with
    | .error err => return (.error err, self)
    | .ok () =>
      return (.ok false, { self with line := if self.depth == 0 then .start else .afterToken })

/- LEAN: Rust's private `Position`. -/
/-- Where a writer is in what it writes, in its style. -/
inductive Internal.Position where
  | line (position : Internal.LinePosition)
  | layout (position : Internal.LayoutPosition)
  | compact (position : Internal.CompactPosition)

end BSmtLib.Writer

namespace BSmtLib

/--
Writes nodes or tokens as SMT-LIB text.

The writer can write any value that implements `Token.AppendTokens` in its SMT-LIB
text representation.

The writer also implements `Token.Consume` and `Token.ConsumeFrom` for any `Token.Cursor`,
so it can e.g. rewrite tokens from a lexer in a given `Writer.WriteStyle`.

The writer writes to the underlying byte writer immediately, without a buffer of its own,
and does not flush it. It writes under its SMT-LIB version in force, which is not affected
by the cursor version. To change the version in force, `Writer.setVersion`
can be used.

On encountering an unquoted symbol that is a reserved word in the version in force,
the writer recovers gracefully by quoting it. On encountering a reserved word which
is not reserved in the version in force, the writer fails with
`Writer.WriteErrorKind.notInVersion` as the reserved word cannot be represented
in the version.
-/
structure Writer where
  private mk ::
  private writer : IO.FS.Stream
  private versionInForce : Version
  private position : Writer.Internal.Position

end BSmtLib

namespace BSmtLib.Writer

/-- Creates a writer into `writer` that writes as configured. -/
def new (writer : IO.FS.Stream) (config : WriterConfig) : Writer :=
  let position : Internal.Position := match config.style with
    | .line => .line .start
    | .layout => .layout { last := .lineStart, inputEnded := false }
    | .compact => .compact { depth := 0, line := .start }
  ⟨writer, config.version, position⟩

/-- Returns the configuration the writer writes in. -/
def config (self : Writer) : WriterConfig :=
  let style : WriteStyle := match self.position with
    | .line _ => .line
    | .layout _ => .layout
    | .compact _ => .compact
  (WriterConfig.new self.versionInForce).withStyle style

/-- Returns the version the writer writes in. -/
def version (self : Writer) : Version := self.versionInForce

/--
Sets the version the writer writes the following tokens in.

This is the only way the version in force can be changed:
the writer does not follow the version of `Token.Cursor`.
-/
def setVersion (self : Writer) (version : Version) : Writer :=
  { self with versionInForce := version }

/-- Returns the underlying writer. -/
def getRef (self : Writer) : IO.FS.Stream := self.writer

/-- Destructures into the underlying writer. -/
def intoInner (self : Writer) : IO.FS.Stream := self.writer

/- LEAN: Rust's private `write_token`, which returns the writer as it is after the token. -/
/-- Writes the token, returning whether it ended the input. -/
@[inline]
def Internal.writeToken {n : Type → Type} [Monad n] [MonadLiftT IO n]
    (self : Writer) (token : Token) : n (Except WriteError Bool × Writer) := do
  match self.position with
  | .line position =>
    let (result, position) ← position.writeToken self.writer self.versionInForce token
    return (result, { self with position := .line position })
  | .layout position =>
    let (result, position) ← position.writeToken self.writer self.versionInForce token
    return (result, { self with position := .layout position })
  | .compact position =>
    let (result, position) ← position.writeToken self.writer self.versionInForce token
    return (result, { self with position := .compact position })

/-- Writes the tokens of the cursor from the first on, until none is left or writing fails. -/
private def writeTokens {n : Type → Type} [Monad n] [MonadLiftT IO n]
    (self : Writer) (cursor : TokensCursor) : n (Except WriteError Unit × Writer) := do
  match Cursor.next? cursor with
  | none => return (.ok (), self)
  | some (token, ⟨next, _⟩) =>
    match ← Internal.writeToken self token with
    | (.error err, self) => return (.error err, self)
    | (.ok _, self) => writeTokens self next
termination_by (⟨cursor⟩ :
  Cursor.Internal.Draining (Z := TokensCursor) Cursor.Consumed Cursor.consumed_wf)
decreasing_by assumption

/--
Writes the tokens of the value.

The value does not end an input: values written one after another are laid out as
consecutive tokens, e.g. `(a)(b)` in the `WriteStyle.layout` style. A
`Token.endOfFile` among the tokens ends an input.

Returns an error if a reserved word is not reserved in the version written in, or if
writing to the underlying writer fails. The tokens before the failing one have been
written.
-/
def write {n : Type → Type} [Monad n] [MonadLiftT IO n] {V : Type} [AppendTokens V]
    (self : Writer) (value : V) : n (Except WriteError Unit × Writer) :=
  writeTokens self (AppendTokens.appendTokens value (TokensCursor.new self.versionInForce))

/- LEAN: the writer's `consume`, Rust's loop over the cursor's tokens. -/
/-- Writes the tokens of the cursor until none is left or one ends the input. -/
private def consumeTokens {Z : Type} [Cursor Z] (origin cursor : Z)
    (consumed : Cursor.Consumed cursor origin) :
    StateT Writer IO
      (Except WriteError (ControlFlow Unit) × { next : Z // Cursor.Consumed next origin }) := do
  match Cursor.next? cursor with
  | none => return (.ok .continue, ⟨cursor, consumed⟩)
  | some (token, ⟨next, hnext⟩) =>
    let (result, writer) ← Internal.writeToken (← get) (Cursor.syntax cursor token)
    set writer
    match result with
    | .error err => return (.error err, ⟨next, Cursor.consumed_trans hnext consumed⟩)
    | .ok true => return (.ok (.break ()), ⟨next, Cursor.consumed_trans hnext consumed⟩)
    | .ok false => consumeTokens origin next (Cursor.consumed_trans hnext consumed)
termination_by (⟨cursor⟩ : Cursor.Internal.Draining (Z := Z) Cursor.Consumed Cursor.consumed_wf)
decreasing_by exact hnext

/-- Writes the tokens of the cursor, which has one, until none is left or one ends the input. -/
private def consumeFrom {Z : Type} [Cursor Z] (cursor : Z) (has : Cursor.HasNext cursor) :
    StateT Writer IO
      (Except WriteError (ControlFlow Unit) × { next : Z // Cursor.Consumed next cursor }) := do
  match h : Cursor.next? cursor with
  | none => absurd (Cursor.next?_isSome has) (by simp [h])
  | some (token, ⟨next, hnext⟩) =>
    let (result, writer) ← Internal.writeToken (← get) (Cursor.syntax cursor token)
    set writer
    match result with
    | .error err => return (.error err, ⟨next, hnext⟩)
    | .ok true => return (.ok (.break ()), ⟨next, hnext⟩)
    | .ok false => consumeTokens cursor next hnext

@[no_expose] instance : Consume Writer Unit WriteError where
  isConcrete := true

@[no_expose] instance {Z : Type} [Cursor Z] : ConsumeFrom Writer Z IO where
  consume := consumeFrom

end BSmtLib.Writer
