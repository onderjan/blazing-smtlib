import BSmtLib.Lexer

/-!
The naive lexer: the first of the chain of lexers that leads from the specification to the
library's lexer.

It has the contract of the library's lexer `BSmtLib.Lexer` and reuses its types: the consumer
classes `Consume` and `Recover`, the cursor and the batch, the tokens, the errors and the
recovery. It behaves as that lexer does in everything a consumer can observe, except where the
hand-overs are cut: it hands every token over as soon as the token is finished, alone in a
cursor of its own.

It is written to be proved, not to be fast. The lexing is a pure step over a state and one
byte (`start`, `advance`, `finish`, `scan`); the hand-overs to the consumer and its monad are
kept apart from it (`lexByte` and below). It reads one byte at a time and lexes nothing ahead
of what it hands over, so a version set by the consumer applies to the input from the end of
the token the consumer answered for, and nothing is ever lexed again.
-/

namespace BSmtLib.Proofs.Lexer.V1Naive

/-! ## Bytes -/

/--
Whether the byte delimits a token: whitespace, a parenthesis, or the start of a comment.
Every token but a parenthesis and a comment must be followed by such a byte or by the end of
the input.
-/
def isDelimiter (c : UInt8) : Bool :=
  c == byte! ' ' || c == byte! '\t' || c == byte! '\n' || c == byte! '\r'
    || c == byte! '(' || c == byte! ')' || c == byte! ';'

/-- Whether the byte is whitespace: tab, line feed, carriage return or space. -/
def isWhitespace (c : UInt8) : Bool :=
  c == byte! ' ' || c == byte! '\t' || c == byte! '\n' || c == byte! '\r'

def isDigit (c : UInt8) : Bool :=
  byte! '0' ≤ c && c ≤ byte! '9'

def isHexDigit (c : UInt8) : Bool :=
  isDigit c || (byte! 'a' ≤ c && c ≤ byte! 'f') || (byte! 'A' ≤ c && c ≤ byte! 'F')

def isBinaryDigit (c : UInt8) : Bool :=
  c == byte! '0' || c == byte! '1'

/-- Whether the byte is a letter: `A` to `Z` or `a` to `z`. -/
def isLetter (c : UInt8) : Bool :=
  (byte! 'A' ≤ c && c ≤ byte! 'Z') || (byte! 'a' ≤ c && c ≤ byte! 'z')

/-- Whether the byte is one of the punctuation characters allowed in a simple symbol:
`~!@$%^&*_-+=<>.?/`. -/
def isSymbolPunctuation (c : UInt8) : Bool :=
  c == byte! '~' || c == byte! '!' || c == byte! '@' || c == byte! '$' || c == byte! '%'
    || c == byte! '^' || c == byte! '&' || c == byte! '*' || c == byte! '_' || c == byte! '-'
    || c == byte! '+' || c == byte! '=' || c == byte! '<' || c == byte! '>' || c == byte! '.'
    || c == byte! '?' || c == byte! '/'

/-- Whether the byte may be in a simple symbol or a keyword: a letter, a digit, or a punctuation
character of `isSymbolPunctuation`. -/
def isSymbolByte (c : UInt8) : Bool :=
  isLetter c || isDigit c || isSymbolPunctuation c

/--
Whether the byte may be in a string literal or a quoted symbol, apart from the bytes that
close or escape them: a printable character or whitespace, that is, any byte but DEL and the
control characters other than tab, line feed and carriage return.
-/
def isTextByte (c : UInt8) : Bool :=
  (32 ≤ c.toNat && c.toNat ≤ 126) || 128 ≤ c.toNat || isWhitespace c

/-! ## The pure step -/

/-- The base of a hexadecimal or binary literal. -/
inductive Radix where
  | hexadecimal
  | binary
  deriving BEq, Repr

namespace Radix

/-- Whether the byte is a digit of the base. -/
def allows : Radix → UInt8 → Bool
  | .hexadecimal => isHexDigit
  | .binary => isBinaryDigit

def category : Radix → TokenCategory
  | .hexadecimal => .hexadecimal
  | .binary => .binary

/-- The error of a literal without digits. -/
def emptyError : Radix → LexicalErrorKind
  | .hexadecimal => .hexadecimalDigitExpected
  | .binary => .binaryDigitExpected

end Radix

/--
What the token in progress is, as far as its bytes so far tell. The content is kept beside it,
in `Pending`.
-/
inductive Mode where
  /-- Digits; `zero` if they are the single digit `0`, which no digit may follow. -/
  | numeral (zero : Bool)
  /-- Digits, a dot and digits; `digits` if there is a digit after the dot. -/
  | fraction (digits : Bool)
  /-- A `#`, which the base must follow. -/
  | hash
  /-- A `#x` or `#b` and digits of the base. The content is the digits. -/
  | digits (radix : Radix)
  /-- A `:` and symbol bytes. The content is the bytes after the colon. -/
  | keyword
  /-- Symbol bytes, the first of them not a digit. -/
  | simpleSymbol
  /-- An opening `|` and the bytes after it. The content is the bytes after the pipe. -/
  | quotedSymbol
  /-- A quoted symbol and its closing `|`, which a delimiter must follow. -/
  | quotedSymbolClosed
  /-- A `"` and the bytes after it, from version 2.5 on. The content is the bytes after the
  quote, with each `""` as one quote. -/
  | string
  /-- A string from version 2.5 on and a `"`, which closes it unless another `"` follows. -/
  | stringQuote
  /-- A `"` and the bytes after it, under version 2.0. The content is the bytes after the
  quote, with `\"` as a quote and `\\` as a backslash. -/
  | legacyString
  /-- A string under version 2.0 and a backslash, which escapes a following `"` or `\`. The
  content does not have the backslash yet. -/
  | legacyEscape
  /-- A string under version 2.0 and the `"` that closes it, which a delimiter must follow. -/
  | legacyQuote
  /-- A `;` and the bytes after it. The content is the bytes after the semicolon. -/
  | comment
  /-- Whitespace, taken by the consumer as a token. -/
  | whitespace
  deriving BEq, Repr

/-- The token in progress. -/
structure Pending where
  mode : Mode
  /-- Where the token starts. -/
  start : Location
  /-- The content of the token so far. -/
  content : ByteArray

/-- A finished token, to be handed over. -/
structure Lexeme where
  category : TokenCategory
  content : ByteArray
  start : Location
  «end» : Location

/-- A lexical error and its failure point: where the error takes effect. -/
structure LexFailure where
  error : LexicalError
  location : Location

/-- What a byte does when no token is in progress. -/
inductive Started where
  /-- Nothing: it is whitespace that the consumer does not take. -/
  | idle
  /-- It starts a token. -/
  | pending (pending : Pending)
  /-- It is a token by itself: a parenthesis. -/
  | token (lexeme : Lexeme)
  | error (failure : LexFailure)

/-- What a byte does to the token in progress. -/
inductive Advanced where
  /-- It is a part of the token, which goes on. -/
  | pending (pending : Pending)
  /-- It ends the token, which the consumer does not take: a comment. -/
  | idle
  /-- It is the last byte of the token: the line break that ends a comment. -/
  | tokenWith (lexeme : Lexeme)
  /-- It delimits the token, which ends before it. -/
  | tokenBefore (lexeme : Lexeme)
  | error (failure : LexFailure)

/-- What the end of the input does to the token in progress. -/
inductive Finished where
  /-- It ends the token, which the consumer does not take: a comment. -/
  | none
  /-- It ends the token. -/
  | token (lexeme : Lexeme)
  | error (failure : LexFailure)

/--
The failure on an offending byte at `location`, for the token from `start`: the error spans the
token and the byte, and takes effect just before the byte.
-/
def failAtByte (kind : LexicalErrorKind) (start location : Location) : LexFailure :=
  -- the end of the span counts the byte as a column, also a line feed
  { error := { kind, span := Span.newUnchecked start location.afterColumn }, location }

/--
The failure at the end of the input at `location`, for the token from `start`: the error spans
the token, and takes effect at the end.
-/
def failAtEnd (kind : LexicalErrorKind) (start location : Location) : LexFailure :=
  { error := { kind, span := Span.newUnchecked start location }, location }

/--
Lexes the byte `c` at `location` with no token in progress, under `version`. `whitespace` says
whether the consumer takes whitespace and comments.
-/
def start (version : Version) (whitespace : Bool) (location : Location) (c : UInt8) : Started :=
  let pending (mode : Mode) (content : ByteArray) : Started :=
    .pending { mode, start := location, content }
  let paren (category : TokenCategory) : Started :=
    .token
      { category, content := ByteArray.empty.push c, start := location,
        «end» := location.afterByte c }
  if isWhitespace c then
    if whitespace then pending .whitespace (ByteArray.empty.push c) else .idle
  else if c == byte! '(' then paren .parenOpen
  else if c == byte! ')' then paren .parenClose
  else if c == byte! ';' then pending .comment .empty
  else if c == byte! '#' then pending .hash .empty
  -- the escapes of strings differ between version 2.0 and the later ones
  else if c == byte! '"' then pending (if version == .v2_0 then .legacyString else .string) .empty
  else if c == byte! ':' then pending .keyword .empty
  else if c == byte! '|' then pending .quotedSymbol .empty
  else if isDigit c then pending (.numeral (c == byte! '0')) (ByteArray.empty.push c)
  else if isSymbolByte c then pending .simpleSymbol (ByteArray.empty.push c)
  else .error (failAtByte .unexpectedCharacter location location)

/-- Lexes the byte `c` at `location` in a string under version 2.0, `p`, which has no
backslash pending. -/
def legacyStringByte (p : Pending) (location : Location) (c : UInt8) : Advanced :=
  if c == byte! '"' then .pending { p with mode := .legacyQuote }
  else if c == byte! '\\' then .pending { p with mode := .legacyEscape }
  else if isTextByte c then .pending { p with mode := .legacyString, content := p.content.push c }
  else .error (failAtByte .forbiddenCharInString p.start location)

/--
Lexes the byte `c` at `location` in the token in progress `p`. `whitespace` says whether the
consumer takes whitespace and comments.
-/
def advance (whitespace : Bool) (p : Pending) (location : Location) (c : UInt8) : Advanced :=
  -- the byte is a part of the token
  let extend (mode : Mode) : Advanced := .pending { p with mode, content := p.content.push c }
  -- the byte is a part of the token but not of its content
  let keep (mode : Mode) : Advanced := .pending { p with mode }
  let fail (kind : LexicalErrorKind) : Advanced := .error (failAtByte kind p.start location)
  -- the token ends before the byte, which must delimit it
  let delimited (category : TokenCategory) : Advanced :=
    if isDelimiter c then
      .tokenBefore { category, content := p.content, start := p.start, «end» := location }
    else
      fail .missingDelimiter
  match p.mode with
  | .numeral zero =>
    if isDigit c then
      -- a numeral other than 0 does not start with 0
      if zero then fail .numeralLeadingZero else extend (.numeral false)
    else if c == byte! '.' then extend (.fraction false)
    else delimited .numeral
  | .fraction digits =>
    if isDigit c then extend (.fraction true)
    else if !digits then fail .fractionDigitExpected
    else delimited .decimal
  | .hash =>
    if c == byte! 'x' then keep (.digits .hexadecimal)
    else if c == byte! 'b' then keep (.digits .binary)
    else fail .baseSelectionExpected
  | .digits radix =>
    if radix.allows c then extend (.digits radix)
    else if p.content.isEmpty then fail radix.emptyError
    else delimited radix.category
  | .keyword =>
    if isSymbolByte c then extend .keyword
    else if p.content.isEmpty then fail .forbiddenKeywordName
    else delimited .keyword
  | .simpleSymbol =>
    if isSymbolByte c then extend .simpleSymbol else delimited .unquotedSymbol
  | .quotedSymbol =>
    if c == byte! '|' then keep .quotedSymbolClosed
    else if c == byte! '\\' then fail .backslashInQuotedSymbol
    else if isTextByte c then extend .quotedSymbol
    else fail .forbiddenCharInQuotedSymbol
  | .quotedSymbolClosed => delimited .quotedSymbol
  | .string =>
    if c == byte! '"' then keep .stringQuote
    else if isTextByte c then extend .string
    else fail .forbiddenCharInString
  | .stringQuote =>
    -- a second quote is a quote in the content, anything else ends the string
    if c == byte! '"' then extend .string else delimited .string
  | .legacyString => legacyStringByte p location c
  | .legacyEscape =>
    if c == byte! '"' || c == byte! '\\' then
      -- an escape: only the escaped byte is in the content
      extend .legacyString
    else
      -- not an escape: the backslash is in the content, and the byte is lexed as any other
      legacyStringByte { p with mode := .legacyString, content := p.content.push (byte! '\\') }
        location c
  | .legacyQuote => delimited .string
  | .comment =>
    if c == byte! '\n' || c == byte! '\r' then
      -- the line break ends the comment and is the last byte of its content
      if whitespace then
        .tokenWith
          { category := .comment, content := p.content.push c, start := p.start,
            «end» := location.afterByte c }
      else
        .idle
    else
      extend .comment
  | .whitespace =>
    if isWhitespace c then extend .whitespace
    else
      .tokenBefore
        { category := .whitespace, content := p.content, start := p.start, «end» := location }

/--
Ends the token in progress `p` at the end of the input, at `location`. `whitespace` says whether
the consumer takes whitespace and comments.
-/
def finish (whitespace : Bool) (p : Pending) (location : Location) : Finished :=
  let token (category : TokenCategory) : Finished :=
    .token { category, content := p.content, start := p.start, «end» := location }
  let fail (kind : LexicalErrorKind) : Finished := .error (failAtEnd kind p.start location)
  match p.mode with
  | .numeral _ => token .numeral
  | .fraction digits => if digits then token .decimal else fail .fractionDigitExpected
  | .hash => fail .baseSelectionExpected
  | .digits radix => if p.content.isEmpty then fail radix.emptyError else token radix.category
  | .keyword => if p.content.isEmpty then fail .forbiddenKeywordName else token .keyword
  | .simpleSymbol => token .unquotedSymbol
  | .quotedSymbol => fail .unclosedQuotedSymbol
  | .quotedSymbolClosed => token .quotedSymbol
  | .string | .legacyString | .legacyEscape => fail .unclosedStringLiteral
  | .stringQuote | .legacyQuote => token .string
  | .comment => if whitespace then token .comment else .none
  | .whitespace => token .whitespace

/-! ## The pure step of recovery -/

/--
What the skipping after an error is inside of. It reads the input as parentheses, strings,
quoted symbols, comments, and other bytes.
-/
inductive Skip where
  /-- Outside of strings, quoted symbols and comments. -/
  | plain
  | string
  /-- At the byte after a backslash in a string, under version 2.0. -/
  | stringEscape
  | quotedSymbol
  | comment
  deriving BEq, Repr

/-- What a byte does to the skipping after an error. -/
inductive Scanned where
  /-- It is skipped; the skipping goes on inside of `skip`, with `depth` parentheses open. -/
  | skip (skip : Skip) (depth : Nat)
  /-- The recovery is made before it: it delimits the atom the error was in, with nothing
  open. -/
  | before
  /-- The recovery is made after it: it is the parenthesis that closes the last one open. -/
  | after
  deriving BEq, Repr

/--
Skips the byte `c` inside of `skip`, with `depth` parentheses open. `legacy` says whether the
version is 2.0, where a backslash in a string escapes the byte after it.

With parentheses open, the skipping ends after the one that closes them all. With none open,
it ends at the end of the atom the error was in: before the first delimiter outside of a
string or a quoted symbol.
-/
def scan (legacy : Bool) (skip : Skip) (depth : Nat) (c : UInt8) : Scanned :=
  match skip with
  | .plain =>
    if c == byte! '"' then .skip .string depth
    else if c == byte! '|' then .skip .quotedSymbol depth
    else if isDelimiter c && depth == 0 then .before
    else if c == byte! ';' then .skip .comment depth
    else if c == byte! '(' then .skip .plain (depth + 1)
    -- a parenthesis open, as none open would have ended the skipping before it
    else if c == byte! ')' then
      if depth == 1 then .after else .skip .plain (depth - 1)
    else .skip .plain depth
  | .string =>
    if c == byte! '"' then .skip .plain depth
    else if c == byte! '\\' && legacy then .skip .stringEscape depth
    else .skip .string depth
  | .stringEscape => .skip .string depth
  | .quotedSymbol => if c == byte! '|' then .skip .plain depth else .skip .quotedSymbol depth
  | .comment =>
    if c == byte! '\n' || c == byte! '\r' then .skip .plain depth else .skip .comment depth

/-! ## The lexer state -/

/-- What the lexer is doing. -/
inductive Activity where
  /-- Lexing, between tokens. -/
  | idle
  /-- Lexing a token. -/
  | token (pending : Pending)
  /-- Recovering: the consumer failed after a whole token with no parenthesis open, so there
  is nothing to skip. The consumer is told so at the start of the next call. -/
  | recovered
  /-- Recovering: skipping the input up to the end of what the error was in. -/
  | skipping (skip : Skip)
  /-- Recovering: the end of the input raised the error, so only the end of the input can be
  lexed again. -/
  | ended
  /-- The consumer has finished: the input is discarded up to its end. -/
  | discarding

/- The fields are public, so that proofs about the lexer can read them. -/
/-- The state of the lexer, apart from its consumer. -/
structure Core where
  /-- The SMT-LIB version in force. -/
  version : Version
  /-- The version the lexer was constructed with, in force again after the end of the input. -/
  initialVersion : Version
  /-- The location of the next byte to be fed. -/
  location : Location
  activity : Activity
  /--
  The number of parentheses left open by the tokens handed over, never below zero. A recovery
  skips to where they are closed.
  -/
  depth : Nat

namespace Core

/-- The state at the start of an input. -/
def initial (version : Version) : Core :=
  { version, initialVersion := version, location := Location.initial, activity := .idle,
    depth := 0 }

/-- The state after the end of the input: as at the start, under the initial version. -/
def reset (self : Core) : Core :=
  initial self.initialVersion

end Core

/-! ## Hand-overs -/

/-- A batch of the lexeme alone. -/
def Lexeme.batch (l : Lexeme) : TokenBatch :=
  ({ TokenBatch.empty 1 with bytes := l.content } : TokenBatch).pushLocated l.category 0
    l.content.size l.start l.end

/-- A cursor over the batch of a lexeme alone has a token. -/
theorem Lexeme.hasNext (l : Lexeme) (version : Version) :
    (BatchCursor.new version l.batch).HasNext :=
  Nat.zero_lt_one

/-- The number of parentheses open after a token of the category. -/
def depthAfter (depth : Nat) : TokenCategory → Nat
  | .parenOpen => depth + 1
  -- a closing parenthesis that closes nothing leaves nothing open
  | .parenClose => depth - 1
  | _ => depth

/-- A lexing error with the location where it takes effect. -/
structure Failure (E : Type) where
  cause : LexErrorCause E
  location : Location

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

/- The functions below thread the lexer state `Core` through by hand, each taking it and
giving it back, while the consumer is the state of the monad `StateT H m`, in which the
consumer runs. They make the hand-overs and the consumer's calls; what the bytes mean is
decided by the pure step above. -/

/--
Hands the lexeme over to the consumer, alone in a cursor under the version in force, and
takes its answer. The version on the cursor the consumer gives back is in force from then on.
-/
def handOver (core : Core) (l : Lexeme) :
    StateT H m (Except E (ControlFlow R) × Core) := do
  let cursor := BatchCursor.new core.version l.batch
  let (answer, ⟨after, _⟩) ← Consume.consume (H := H) cursor (l.hasNext core.version)
  -- the consumer has consumed at least one token, and the cursor has just this one
  return (answer, { core with version := after.version, depth := depthAfter core.depth l.category })

/--
Hands the lexeme over and turns the consumer's answer into what lexing does next: go on
(`none`), stop as the consumer has finished (`some`, located at the end of the lexeme, and the
input is discarded from then on), or fail after the lexeme.
-/
def handOverAt (core : Core) (l : Lexeme) :
    StateT H m (Except (Failure E) (Option (Located R)) × Core) := do
  let (answer, core) ← handOver core l
  return match answer with
    | .ok .continue => (.ok none, core)
    | .ok (.break value) =>
      (.ok (some { value, location := l.end }), { core with activity := .discarding })
    | .error err => (.error { cause := .consumer err, location := l.end }, core)

/-- Lexes the byte `c` with no token in progress. -/
def lexStart (core : Core) (c : UInt8) :
    StateT H m (Except (Failure E) (Option (Located R)) × Core) := do
  let whitespace := Consume.consumesWhitespaceAndComments (H := H)
  let after := core.location.afterByte c
  match start core.version whitespace core.location c with
  | .idle => return (.ok none, { core with activity := .idle, location := after })
  | .pending p => return (.ok none, { core with activity := .token p, location := after })
  | .token l => handOverAt { core with activity := .idle, location := after } l
  | .error failure =>
    return (.error { cause := .lexical failure.error, location := failure.location }, core)

/--
Lexes the byte `c`, at the lexer's location, and gives back the lexer state after it. Returns
`some` if the consumer has finished on a token, and the failure if the byte or the consumer
raised one; the lexer is then at the failure point.

`recover` is the consumer's call at the end of a recovery.
-/
def lexByte (recover : Location → StateT H m Unit) (core : Core) (c : UInt8) :
    StateT H m (Except (Failure E) (Option (Located R)) × Core) := do
  let location := core.location
  match core.activity with
  | .discarding => return (.ok none, { core with location := location.afterByte c })
  -- only the end of the input can follow, there is nothing to lex
  | .ended => return (.ok none, core)
  | .recovered =>
    -- the consumer is told of a recovery before any token
    recover location
    lexStart { core with activity := .idle } c
  | .skipping skip =>
    match scan (core.version == .v2_0) skip core.depth c with
    | .skip skip depth =>
      let core := { core with location := location.afterByte c, activity := .skipping skip, depth }
      return (.ok none, core)
    | .before =>
      recover location
      lexStart { core with activity := .idle } c
    | .after =>
      let location := location.afterByte c
      recover location
      return (.ok none, { core with location, activity := .idle, depth := 0 })
  | .idle => lexStart core c
  | .token p =>
    let whitespace := Consume.consumesWhitespaceAndComments (H := H)
    let after := location.afterByte c
    match advance whitespace p location c with
    | .pending p => return (.ok none, { core with activity := .token p, location := after })
    | .idle => return (.ok none, { core with activity := .idle, location := after })
    | .tokenWith l => handOverAt { core with activity := .idle, location := after } l
    | .tokenBefore l =>
      let (result, core) ← handOverAt { core with activity := .idle } l
      match result with
      -- the byte is lexed under the version the consumer has left in force
      | .ok none => lexStart core c
      -- the consumer has finished: the byte is the first one discarded
      | .ok (some located) => return (.ok (some located), { core with location := after })
      | .error failure => return (.error failure, core)
    | .error failure =>
      return (.error { cause := .lexical failure.error, location := failure.location }, core)

/--
Lexes the bytes of the slice from `index` on. `flow` is the consumer's finish, if it has
finished on an earlier byte of the slice.
-/
def lexFrom (recover : Location → StateT H m Unit) (slice : ByteSlice) (index : Nat)
    (core : Core) (flow : ControlFlow (Located R)) :
    StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core) := do
  if h : index < slice.size then
    let (result, core) ← lexByte recover core slice[index]
    match result with
    | .ok none => lexFrom recover slice (index + 1) core flow
    | .ok (some located) => lexFrom recover slice (index + 1) core (.break located)
    | .error failure => return (.error failure, core)
  else
    return (.ok flow, core)
termination_by slice.size - index

/--
Turns the failure into the error to return. A recovering lexer (`recovers`) makes the consumer
abandon its unfinished work and starts skipping from the failure point; `atEnd` says whether
the end of the input raised the failure.
-/
def failCall (recovers : Bool) (abandon : Location → StateT H m Unit) (failure : Failure E)
    (atEnd : Bool) (core : Core) : StateT H m (LexError E × Core) := do
  if !recovers then
    return ({ cause := failure.cause, continuesFrom := none }, core)
  let activity : Activity := if atEnd then
      -- the input has ended, nothing is left to skip
      .ended
    else
      -- the skipping starts inside the string or quoted symbol the error was in
      match failure.cause with
      | .lexical err => match err.kind with
        | .forbiddenCharInString => .skipping .string
        | .backslashInQuotedSymbol | .forbiddenCharInQuotedSymbol => .skipping .quotedSymbol
        | _ => .skipping .plain
      -- the consumer fails after a whole token: with nothing open, nothing is skipped
      | .consumer _ => if core.depth == 0 then .recovered else .skipping .plain
      | .internal _ => .skipping .plain
  abandon failure.location
  return ({ cause := failure.cause, continuesFrom := some failure.location },
    { core with location := failure.location, activity })

/-- Lexes the slice, or discards it if the consumer has finished. -/
def lexSliceStep (recovers : Bool) (abandon recover : Location → StateT H m Unit)
    (slice : ByteSlice) (core : Core) :
    StateT H m (Except (LexError E) (ControlFlow (Located R)) × Core) := do
  let core ← match core.activity with
    -- the consumer failed after a whole token with nothing open: the recovery is made here,
    -- even if the slice is empty
    | .recovered => do
      recover core.location
      pure { core with activity := .idle }
    | _ => pure core
  match core.activity with
  -- the input has ended with the error, there is nothing to lex
  | .ended => return (.ok .continue, core)
  | _ =>
    let (result, core) ← lexFrom recover slice 0 core .continue
    match result with
    | .ok flow => return (.ok flow, core)
    | .error failure =>
      let (err, core) ← failCall recovers abandon failure false core
      return (.error err, core)

/--
Lexes the end of the input: ends the token in progress, and hands over the end-of-file token.
-/
def lexEnd (core : Core) :
    StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core) := do
  let whitespace := Consume.consumesWhitespaceAndComments (H := H)
  let location := core.location
  let (result, core) ← match core.activity with
    | .token p => match finish whitespace p location with
      | .none => pure (.ok none, { core with activity := .idle })
      | .token l => handOverAt { core with activity := .idle } l
      | .error failure =>
        pure (.error { cause := .lexical failure.error, location := failure.location }, core)
    | _ => pure (.ok none, core)
  match result with
  | .error failure => return (.error failure, core)
  -- the consumer has finished on the token, the end-of-file token is not handed over
  | .ok (some located) => return (.ok (.break located), core)
  | .ok none =>
    let eof : Lexeme :=
      { category := .endOfFile, content := .empty, start := location, «end» := location }
    let (result, core) ← handOverAt core eof
    return match result with
      | .ok none => (.ok .continue, core)
      | .ok (some located) => (.ok (.break located), core)
      | .error failure => (.error failure, core)

/-- Lexes the end of the input, which resets the lexer unless it fails and recovers. -/
def lexEofStep (recovers : Bool) (abandon recover : Location → StateT H m Unit) (core : Core) :
    StateT H m (Except (LexError E) (ControlFlow (Located R)) × Core) := do
  match core.activity with
  -- the consumer has finished, nothing is handed over
  | .discarding => return (.ok .continue, core.reset)
  | _ =>
    -- the end of the input ends any skipping
    let recovered := match core.activity with
      | .recovered | .skipping _ | .ended => true
      | _ => false
    let core ← if recovered then do
        recover core.location
        pure { core with activity := .idle }
      else
        pure core
    let (result, core) ← lexEnd core
    match result with
    | .ok flow => return (.ok flow, core.reset)
    | .error failure =>
      if recovered then
        -- the consumer has refused the end of the input with nothing left to abandon:
        -- the error is final, and the input has ended
        return (.error { cause := failure.cause, continuesFrom := none }, core.reset)
      let (err, core) ← failCall recovers abandon failure true core
      return (.error err, core)

end

/-! ## The lexer -/

/-- The naive lexer, with its consumer `H`; `recovery` says whether it recovers from errors. -/
structure Lexer (H : Type) (recovery : Recovery := .failFast) where
  handler : H
  core : Core

/--
What a lexer call that failed gives back: nothing for a lexer that stops at its first error,
which cannot be used again, and the lexer itself for a recovering one, from which the rest of
the input is to be fed.
-/
def Lexer.AfterError (H : Type) : Recovery → Type
  | .failFast => Unit
  | .recovering => Lexer H .recovering

/--
A recovering lexer whose end of the input raised an error.

The input has ended, so only the end of the input can be lexed again, which completes the
recovery.
-/
structure Lexer.PendingEof (H : Type) where
  private mk ::
  private lexer : Lexer H .recovering

/--
What a recovering lexer gives back after its end of the input failed: the lexer, if the error
is final, or the lexer that can only lex the end of the input again, if the error continues at
the end.
-/
inductive Lexer.AfterEof (H : Type) where
  | lexer (lexer : Lexer H .recovering)
  | pending (pending : Lexer.PendingEof H)

/--
What a lexer gives back after its end of the input failed: nothing for a lexer that stops at
its first error, and what remains of a recovering one.
-/
def Lexer.AfterEofError (H : Type) : Recovery → Type
  | .failFast => Unit
  | .recovering => Lexer.AfterEof H

namespace Lexer

/-- Constructs the lexer. The lexer stops at its first error. -/
def new (consumer : H) (version : Version) : Lexer H :=
  { handler := consumer, core := Core.initial version }

/-- Constructs a lexer that recovers from errors. -/
def newRecovering [Recover H m] (consumer : H) (version : Version) : Lexer H .recovering :=
  { handler := consumer, core := Core.initial version }

/-- The location of the next byte to be fed. -/
def currentLocation (self : Lexer H recovery) : Location :=
  self.core.location

/--
The SMT-LIB version currently in force.

The version can change if the token consumer asks for it from the cursor. The end of the
input resets the version to the initial one.
-/
def version (self : Lexer H recovery) : Version :=
  self.core.version

/-- What a failed call gives back: nothing for a lexer that stops at its first error, the lexer
for a recovering one. -/
def afterError : {recovery : Recovery} → Lexer H recovery → AfterError H recovery
  | .failFast, _ => ()
  | .recovering, lexer => lexer

/-- What a failed end of the input gives back: nothing for a lexer that stops at its first error;
for a recovering one, the lexer that can only lex the end of the input again if the error
continues there, and the lexer otherwise. -/
def afterEofError : {recovery : Recovery} → Lexer H recovery → (continues : Bool) →
    AfterEofError H recovery
  | .failFast, _, _ => ()
  | .recovering, lexer, true => .pending ⟨lexer⟩
  | .recovering, lexer, false => .lexer lexer

/-- Runs a step on the lexer's state with its consumer, and puts the lexer together again. -/
def run [Monad m] (self : Lexer H recovery)
    (step : Core → StateT H m (α × Core)) : m (α × Lexer H recovery) := do
  let { handler, core } := self
  let ((result, core), handler) ← (step core).run handler
  return (result, { handler, core })

/--
Lexes the given slice, sending the lexed tokens to the consumer.

If the token consumer returns `ControlFlow.break` on some token, the lexer passes it through,
adding the break location. Subsequent bytes are discarded until EOF, which resets the lexer.

If the token consumer returns `ControlFlow.continue` on all tokens, the lexer is ready for
further lexing.

If an error occurs, a lexer that stops at its first error is not given back. A recovering lexer
makes the consumer abandon its unfinished work and returns the error. `LexError.continuesFrom`
determines the location from which further lexing should be started for error recovery.
-/
def lexSlice [Monad m] [Consume H m R E] [LexRecovery recovery H m] (self : Lexer H recovery)
    (slice : ByteSlice) :
    m (Except (LexError E × AfterError H recovery)
      (ControlFlow (Located R) × Lexer H recovery)) := do
  let step := lexSliceStep (recovery == .recovering) (LexRecovery.abandon recovery)
    (LexRecovery.recover recovery) slice
  let (result, self) ← self.run step
  return match result with
    | .ok flow => .ok (flow, self)
    | .error err => .error (err, afterError self)

/--
Lexes end-of-file, sending the lexed tokens to the consumer.

If the token consumer returns `ControlFlow.break` on the EOF token, the lexer passes it
through, adding the break location.

If the token consumer returns `ControlFlow.continue` on the EOF token, the lexer resets itself
and returns `ControlFlow.continue`.

If an error occurs, a lexer that stops at its first error is not given back. A recovering lexer
makes the consumer abandon its unfinished work and returns the error. `LexError.continuesFrom`
determines the location from which further lexing should be started for error recovery.
-/
def lexEof [Monad m] [Consume H m R E] [LexRecovery recovery H m] (self : Lexer H recovery) :
    m (Except (LexError E × AfterEofError H recovery)
      (ControlFlow (Located R) × Lexer H recovery)) := do
  let step := lexEofStep (recovery == .recovering) (LexRecovery.abandon recovery)
    (LexRecovery.recover recovery)
  let (result, self) ← self.run step
  return match result with
    | .ok flow => .ok (flow, self)
    | .error err => .error (err, afterEofError self err.continuesFrom.isSome)

/--
Lexes the end of the input again, which completes the recovery.

The lexer hands over the end-of-file token. An error is final: the lexer resets itself and
does not continue.
-/
def PendingEof.lexEof [Monad m] [Consume H m R E] [Recover H m] (self : PendingEof H) :
    m (Except (LexError E × Lexer H .recovering)
      (ControlFlow (Located R) × Lexer H .recovering)) := do
  let step := lexEofStep true (Recover.abandon (H := H)) (Recover.recover (H := H))
  let (result, lexer) ← self.lexer.run step
  return match result with
    | .ok flow => .ok (flow, lexer)
    | .error err => .error (err, lexer)

/--
Lexes the whole input including EOF at the end.

If the token consumer returns `ControlFlow.break` on some token, the lexer passes it through,
adding the break location, and resets itself as if at the start of a new input.

If the token consumer returns `ControlFlow.continue` on all tokens including EOF, the lexer
resets itself after EOF and returns `ControlFlow.continue`.

If an error occurs, the lexer is not given back.
-/
def lexAll [Monad m] [Consume H m R E] (self : Lexer H) (input : ByteSlice) :
    m (Except (LexError E × AfterError H .failFast) (ControlFlow (Located R) × Lexer H)) := do
  match ← self.lexSlice input with
  | .ok (.break result, self) =>
    -- reset the lexer as if we are at the start of a new file
    return .ok (.break result, { self with core := self.core.reset })
  | .ok (.continue, self) => self.lexEof
  | .error err => return .error err

end Lexer

end BSmtLib.Proofs.Lexer.V1Naive
