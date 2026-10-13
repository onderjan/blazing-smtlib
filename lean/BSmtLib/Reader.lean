import BSmtLib.Lexer
import BSmtLib.Parser

/-!
# Reading SMT-LIB input: lexing and parsing

Reading turns bytes into tokens (the lexer) and tokens into the syntactic categories and
commands of SMT-LIB (the parser), which are delivered to a command handler in streaming
fashion: the input is processed piece by piece and every category or command to be handled
reaches the handler before the next one is read.

For simple usage, use `readSmt` and `readSmtFile`.

`Reader` reads the same way from any sequence of buffers and keeps the parser's resources
under the caller's control, so it is the entry point when the input does not arrive as one
buffered reader or when the resources should serve several reads. The lexer and the parser can
also be used on their own.
-/

namespace BSmtLib

open Parser

/-- Determines why reading has failed. -/
inductive ReadErrorCause (E : Type) where
  /-- Reading from a file or a buffered reader failed. -/
  | io (error : IO.Error)
  /-- The input is not a valid sequence of SMT-LIB tokens. -/
  | lexical (kind : LexicalErrorKind)
  /--
  The tokens do not form valid SMT-LIB syntactic categories or commands.

  Commands with non-standard names are routed to the handler for processing, so they are
  rejected with a `ReadErrorCause.handler` error cause instead.
  -/
  | syntax (kind : SyntaxErrorKind)
  /-- The handler rejected a command or a syntactic category. -/
  | handler (error : E)

/- LEAN: the fields are readable as `error.cause` and `error.span`, replacing the getters
`cause`, `span` and `into_cause`. -/
/-- An error that ended reading, including its span. -/
structure ReadError (E : Type) where
  /-- Determines why reading has failed. -/
  cause : ReadErrorCause E
  /--
  Span where the error occurred.

  For I/O errors, the span is empty, indicating the position where the reading failed.
  -/
  span : Span

instance {E : Type} : Inhabited (ReadError E) :=
  ⟨{ cause := .io (IO.userError "reading failed"), span := Span.newZero }⟩

/-- Converts the error of a parser, located at `span`, into a read error. -/
def ReadError.ofParse {E : Type} (err : ParseErrorCause E) (span : Span) : ReadError E :=
  let cause := match err with
    | .syntax err => ReadErrorCause.syntax err
    | .handler err => ReadErrorCause.handler err
  { cause, span }

/-- Converts the error of a lexer over a parser into a read error. -/
def ReadError.ofLex {E : Type} (err : LexError (ParseErrorCause E)) : ReadError E :=
  let span := err.span
  match err.cause with
  | .lexical kind => { cause := .lexical kind, span }
  | .consumer err => ReadError.ofParse err span

/- LEAN: not in Rust, whose reader takes `&mut self` and survives the error. The failure will
carry the reader when recovery is added. -/
/-- The failure of a read by a `Reader H P`, carrying the error that ended reading. -/
structure ReadFailure (H P : Type) {m : Type → Type} [Monad m] {E R : Type} [Parse P H m E R]
    where
  /-- The error that ended reading. -/
  error : ReadError E

instance {H P : Type} {m : Type → Type} [Monad m] {E R : Type} [Parse P H m E R] :
    Inhabited (ReadFailure H P) :=
  ⟨{ error := default }⟩

/- LEAN: Rust's `std::io::BufRead`, which Lean's standard library does not have. Methods taking
`&mut self` return the updated reader; an I/O error is returned rather than thrown, as Rust
returns it. -/
/--
A source of bytes read through a buffer, in the monad `n`.

`fillBuf` returns the bytes buffered and not consumed yet, filling the buffer from the source
first if none are left; it returns no bytes at the end of the input. `consume` marks the given
number of bytes at the start of the buffer as consumed, so that `fillBuf` does not return them
again.
-/
class BufRead (B : Type) (n : Type → Type) where
  /--
  Returns the bytes buffered and not consumed yet, filling the buffer from the source if none
  are left. No bytes are returned at the end of the input.
  -/
  fillBuf : B → n (Except IO.Error (ByteSlice × B))
  /--
  Marks the first `amount` bytes of the buffer as consumed.

  The amount must not be more than `fillBuf` returned last.
  -/
  consume : B → Nat → B

/- LEAN: Rust's `impl BufRead for &[u8]`. -/
/-- Bytes in memory read as a whole: the buffer is the bytes not consumed yet. -/
instance {n : Type → Type} [Monad n] : BufRead ByteSlice n where
  fillBuf slice := pure (.ok (slice, slice))
  consume slice amount := slice.slice amount

/- LEAN: Rust's `std::io::BufReader`, over a stream, which Lean's file handles and in-memory
buffers both give (`IO.FS.Stream.ofHandle`, `IO.FS.Stream.ofBuffer`). -/
/-- A stream read through a buffer of a fixed capacity. -/
structure BufReader where
  private mk ::
  private stream : IO.FS.Stream
  private capacity : Nat
  /-- The bytes read from the stream last. -/
  private buffer : ByteArray
  /-- The number of bytes of the buffer consumed. -/
  private position : Nat

/-- Creates a reader of `stream` through a buffer of `capacity` bytes. -/
def BufReader.new (stream : IO.FS.Stream) (capacity : Nat) : BufReader :=
  { stream, capacity, buffer := ByteArray.empty, position := 0 }

instance {n : Type → Type} [Monad n] [MonadLiftT IO n] : BufRead BufReader n where
  fillBuf self := do
    if self.position < self.buffer.size then
      return .ok (self.buffer.toByteSlice self.position, self)
    -- the buffer has been consumed, fill it from the stream
    let read : IO (Except IO.Error ByteArray) := (self.stream.read self.capacity.toUSize).toBaseIO
    match ← read with
    | .ok buffer => return .ok (buffer.toByteSlice, { self with buffer, position := 0 })
    | .error err => return .error err
  consume self amount := { self with position := self.position + amount }

/- LEAN: Rust's reader holds a lexer over `SmtParseAdapter<'a, H, P>`, which borrows the
handler. Here the reader owns the handler, which `handler` and `modifyHandler` reach. -/
/--
Streams SMT-LIB input from bytes to a command handler.

A reader owns its lexer, its parser, the parser resources, and the handler. Any parser can be
used, and a convenience constructor `Reader.script` is provided for the common case of reading
SMT-LIB scripts.

The input is read either whole, through `readFile` or `readAll`, or in pieces, using
`readSlice` sequentially, followed by `readEof` once the input has ended. A piece may end
anywhere, even inside a token.

After a call of `readAll` or `readEof` that does not return an error, the reader is reset and
can be reused. A call that returns an error gives no reader back.

For whole inputs, consider `readSmtFile` and `readSmt`.
-/
structure Reader (H P : Type) {m : Type → Type} [Monad m] {E R : Type} [Parse P H m E R] where
  private mk ::
  private lexer : Lexer (ParseAdapter H P)

namespace Reader

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/--
Creates a reader of an SMT-LIB script, whose commands are delivered to `handler`.

The version under which the script is read can be changed by `set-info` commands. Therefore,
the version-change posture and the initial version used before any commands are read must be
provided.
-/
def script (handler : H) (posture : VersionPosture) (initialVersion : Version) :
    Reader H (ScriptParser H) :=
  { lexer := Lexer.new (ParseAdapter.new handler (ScriptParser.new posture)) initialVersion }

end

section

variable {H P : Type} {m : Type → Type} [Monad m] {E R : Type} [Parse P H m E R]

/--
Creates a reader of the input `parser` accepts, over `handler`.

The version passed is the initial one. Parsers may request the lexer to change versions, and the
lexer will always comply. No standard parser changes versions except for `ScriptParser`.
-/
def new (handler : H) (parser : P) (version : Version) : Reader H P :=
  { lexer := Lexer.new (ParseAdapter.new handler parser) version }

/--
The SMT-LIB version currently in force.

The version can change if the token consumer asks for it from the cursor. The end of the input
resets the version to the initial one.
-/
def version (self : Reader H P) : Version :=
  self.lexer.version

/--
The location from which the input has been discarded, if set.

`ScriptParser` discards input after the `(exit)` command. No other standard parsers discard.
-/
def discardedFrom (self : Reader H P) : Option Location :=
  self.lexer.discardedFrom

/-- Returns the handler. -/
def handler (self : Reader H P) : H :=
  self.lexer.consumer.handler

/- LEAN: Rust's `handler_mut`. The adapter is taken apart so that the handler is held once and
changed in place, if the caller does not keep the old reader. -/
/-- Returns the reader with its handler changed by `f`. -/
def modifyHandler (self : Reader H P) (f : H → H) : Reader H P :=
  { lexer := self.lexer.modifyConsumer fun adapter =>
      let { handler, parser, versionSet } := adapter
      { handler := f handler, parser, versionSet } }

namespace Internal

/- LEAN: not in Rust: the reader's lexer, which the proofs read, also where a call failed and
the reader is not given back. -/
/-- The lexer of the reader. -/
def lexer (self : Reader H P) : Lexer (ParseAdapter H P) :=
  self.lexer

/-- The reader with the lexer. -/
def ofLexer (lexer : Lexer (ParseAdapter H P)) : Reader H P :=
  { lexer }

end Internal

variable [Handler H m]

/--
Processes a byte slice as one piece of the input.

The piece may end anywhere, even inside a token: whatever is unfinished carries over to the next
call.

If an error occurs, the reader is not given back.
-/
def readSlice (self : Reader H P) (slice : ByteSlice) :
    m (Except (ReadFailure H P) (Reader H P)) := do
  -- parsing goes through lexing, so just call the lexer
  match ← self.lexer.lexSlice slice with
  | .ok lexer => return .ok ⟨lexer⟩
  | .error (err, ()) => return .error { error := ReadError.ofLex err }

/- LEAN: Rust's `read_eof` panics where the parser continues on the end of the input, a broken
contract; here it is an obligation on the caller, answered by `none`, as `Lexer.lexEof` does. -/
/--
Processes the end of the input.

Returns the located parser result if successful, and the reader, reset. A parser that continues
on the end of the input breaks its contract; the result is then `none`.

Call this once after the last `readSlice`; `readFile` and `readAll` call it themselves.

If an error occurs, the reader is not given back.
-/
def readEof (self : Reader H P) :
    m (Except (ReadFailure H P) (Option (Located R) × Reader H P)) := do
  -- parsing goes through lexing, so just call the lexer
  match ← self.lexer.lexEof with
  | .ok (result, lexer) => return .ok (result, ⟨lexer⟩)
  | .error (err, ()) => return .error { error := ReadError.ofLex err }

/- LEAN: Rust's `read_all` takes `&mut self` and the buffered reader; this takes the reader and
the buffered reader and gives both back, the buffered reader also after an error. The loop is the
recursion, a tail call; it is `partial`, as a buffered reader may give bytes without end. -/
/--
Reads the content of the buffered reader.

Returns the parser result if successful, `none` if the parser broke its contract (see
`readEof`), and the reader, reset; and, in any case, the buffered reader.

The input is considered to end when the buffered reader returns no bytes. A failure while
reading is reported as an I/O error with an empty span at the position reached.

The buffer content is consumed up to where the parser requests discarding the rest or fully if
no such request was made. Once the parser has requested discarding, the end of the input is
processed without reading further.

If an error occurs, the reader is not given back.
-/
@[specialize]
partial def readAll {B : Type} {n : Type → Type} [Monad n] [MonadLiftT m n] [BufRead B n]
    (self : Reader H P) (bufReader : B) :
    n (Except (ReadFailure H P) (Option R × Reader H P) × B) := do
  if self.discardedFrom.isSome then
    -- the lexer does not care about any subsequent bytes, break
    return (← readRest self, bufReader)

  match ← BufRead.fillBuf bufReader with
  | .error err =>
    -- I/O error
    -- return an empty span on the current lexer location
    let location := self.lexer.currentLocation
    let span := Span.newEmpty location
    let cause := ReadErrorCause.io err
    return (.error { error := { cause, span } }, bufReader)
  | .ok (buffer, bufReader) =>
    if buffer.size == 0 then
      -- end of file reached
      return (← readRest self, bufReader)

    -- remember the current offset and process the buffer
    let startOffset := self.lexer.currentLocation.offset
    match ← (self.readSlice buffer : m _) with
    | .error err => return (.error err, bufReader)
    | .ok self =>
      -- we need to consume the bytes read
      -- this might not be all bytes when discarding is set
      -- use the current lexer location offset minus our start offset
      let len := self.lexer.currentLocation.offset - startOffset
      readAll self (BufRead.consume (n := n) bufReader len)
where
  /-- Processes the end of the input, returning the result without its location. -/
  readRest (self : Reader H P) : n (Except (ReadFailure H P) (Option R × Reader H P)) := do
    -- end of stream, process EOF
    -- this will reset the lexer and return the break value
    match ← (self.readEof : m _) with
    | .error err => return .error err
    | .ok (result, self) =>
      -- do not return the result location as most callers will not want it
      return .ok (result.map fun located => located.value, self)

/- LEAN: Rust's `BufReader::with_capacity`, 1 MiB. -/
/-- The capacity of the buffer through which `readFile` reads a file. -/
def BUF_READER_CAPACITY : Nat := 1024 * 1024

/--
Opens the file at `path` and reads it.

Returns the parser result if successful, `none` if the parser broke its contract (see
`readEof`), and the reader, reset.

A failure to open the file is reported as an I/O error with an empty span at the start of the
input. An I/O read error is reported as an empty span at the respective position.

If an error occurs, the reader is not given back.
-/
def readFile {n : Type → Type} [Monad n] [MonadLiftT IO n] [MonadLiftT m n] (self : Reader H P)
    (path : System.FilePath) : n (Except (ReadFailure H P) (Option R × Reader H P)) := do
  let opened : IO (Except IO.Error IO.FS.Handle) := (IO.FS.Handle.mk path .read).toBaseIO
  match ← opened with
  | .error err => return .error { error := { cause := .io err, span := Span.newZero } }
  | .ok file =>
    -- make the buffered reader use a 1 MiB buffer so that we can
    -- lex/parse more efficiently with larger batches
    let bufReader := BufReader.new (IO.FS.Stream.ofHandle file) BUF_READER_CAPACITY
    let (result, _) ← self.readAll bufReader
    return result

end

end Reader

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/- LEAN: Rust's `read_smt_file` lends the handler; here it is given and given back. -/
/--
Reads the SMT-LIB file at `path`, delivering its content to `handler`, and returns the handler.

This is a convenience function over `Reader`: the parser is dropped after reading, so its
resources cannot be preserved for future use. Use `Reader` directly to keep the resources across
reads or to feed the input in pieces.

A failure to open the file is reported as an I/O error with an empty span at the start of the
input.
-/
def readSmtFile {n : Type → Type} [Monad n] [MonadLiftT IO n] [MonadLiftT m n] (handler : H)
    (path : System.FilePath) : n (Except (ReadFailure H (ScriptParser H)) H) := do
  let reader := Reader.script handler VersionPosture.default default
  match ← reader.readFile path with
  | .ok (_, reader) => return .ok reader.handler
  | .error err => return .error err

/- LEAN: Rust's `read_smt` lends the handler; here it is given and given back. -/
/--
Reads SMT-LIB input from `bufReader`, delivering its content to `handler`, and returns the
handler.

The input is considered to end when the buffered reader returns no bytes.

The buffer content is consumed up to where the parser requests discarding the rest or fully if
no such request was made.

This is a convenience function over `Reader`: the parser is dropped after reading, so its
resources cannot be preserved for future use. Use `Reader` directly to keep the resources across
reads or to feed the input in pieces.
-/
def readSmt {B : Type} {n : Type → Type} [Monad n] [MonadLiftT m n] [BufRead B n] (handler : H)
    (bufReader : B) : n (Except (ReadFailure H (ScriptParser H)) H) := do
  let reader := Reader.script handler VersionPosture.default default
  match ← reader.readAll bufReader with
  | (.ok (_, reader), _) => return .ok reader.handler
  | (.error err, _) => return .error err

end

end BSmtLib
