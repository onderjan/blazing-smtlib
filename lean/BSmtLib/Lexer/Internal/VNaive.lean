module

public import BSmtLib.Lexer

public section

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

open BSmtLib.Lexer.Error
open BSmtLib.Token.BatchCursor.Internal (discardRequested)

namespace BSmtLib.Lexer.Internal.VNaive

open BSmtLib.Lexer.Recovery (FailFast Recovering Recovers)

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

def category : Radix → Token.TokenCategory
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
  start : Span.Location
  /-- The content of the token so far. -/
  content : ByteArray

/-- A finished token, to be handed over. -/
structure Lexeme where
  category : Token.TokenCategory
  content : ByteArray
  start : Span.Location
  «end» : Span.Location

/-- A lexical error, its span and its failure point: where the error takes effect. -/
structure LexFailure where
  kind : LexicalErrorKind
  span : Span
  location : Span.Location

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
def failAtByte (kind : LexicalErrorKind) (start location : Span.Location) : LexFailure :=
  -- the end of the span counts the byte as a column, also a line feed
  { kind, span := Span.Internal.newUnchecked start location.afterColumn, location }

/--
The failure at the end of the input at `location`, for the token from `start`: the error spans
the token, and takes effect at the end.
-/
def failAtEnd (kind : LexicalErrorKind) (start location : Span.Location) : LexFailure :=
  { kind, span := Span.Internal.newUnchecked start location, location }

/--
Lexes the byte `c` at `location` with no token in progress, under `version`. `whitespace` says
whether the consumer takes whitespace and comments.
-/
def start (version : Token.Version) (whitespace : Bool) (location : Span.Location)
    (c : UInt8) : Started :=
  let pending (mode : Mode) (content : ByteArray) : Started :=
    .pending { mode, start := location, content }
  let paren (category : Token.TokenCategory) : Started :=
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
def legacyStringByte (p : Pending) (location : Span.Location) (c : UInt8) : Advanced :=
  if c == byte! '"' then .pending { p with mode := .legacyQuote }
  else if c == byte! '\\' then .pending { p with mode := .legacyEscape }
  else if isTextByte c then .pending { p with mode := .legacyString, content := p.content.push c }
  else .error (failAtByte .forbiddenCharInString p.start location)

/--
Lexes the byte `c` at `location` in the token in progress `p`. `whitespace` says whether the
consumer takes whitespace and comments.
-/
def advance (whitespace : Bool) (p : Pending) (location : Span.Location) (c : UInt8) : Advanced :=
  -- the byte is a part of the token
  let extend (mode : Mode) : Advanced := .pending { p with mode, content := p.content.push c }
  -- the byte is a part of the token but not of its content
  let keep (mode : Mode) : Advanced := .pending { p with mode }
  let fail (kind : LexicalErrorKind) : Advanced := .error (failAtByte kind p.start location)
  -- the token ends before the byte, which must delimit it
  let delimited (category : Token.TokenCategory) : Advanced :=
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
def finish (whitespace : Bool) (p : Pending) (location : Span.Location) : Finished :=
  let token (category : Token.TokenCategory) : Finished :=
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

/-! ## Where the lexemes are

A lexeme has a byte, except the end of file, which is empty: the pure step finishes a token
at or after the byte after its start. The facts below are what the hand-overs need to put a
lexeme into a batch (see `TokenBatch.ordered`).
-/

/-- Whether the lexeme has a byte, or is the end of file, which is empty. -/
abbrev Lexeme.Valid (l : Lexeme) : Prop :=
  l.start.offset < l.end.offset ∨ l.category = .endOfFile ∧ l.start.offset = l.end.offset

theorem afterByte_offset (location : Span.Location) (c : UInt8) :
    (location.afterByte c).offset = location.offset + 1 := by
  unfold Span.Location.afterByte Span.Location.afterColumn
  split <;> rfl

/-- A token started by a byte starts at it. -/
theorem start_pending {version : Token.Version} {whitespace : Bool} {location : Span.Location}
    {c : UInt8}
    {p : Pending} (h : start version whitespace location c = .pending p) :
    p.start = location := by
  simp only [start] at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

/-- A byte that is a token by itself is a lexeme with a byte. -/
theorem start_token {version : Token.Version} {whitespace : Bool} {location : Span.Location}
    {c : UInt8}
    {l : Lexeme} (h : start version whitespace location c = .token l) : l.Valid := by
  simp only [start] at h
  repeat' split at h
  all_goals first
    | (cases h; left; show location.offset < (location.afterByte c).offset
       rw [afterByte_offset]; omega)
    | cases h

/-- A byte that is a token by itself spans from it to after it. -/
theorem start_token_span {version : Token.Version} {whitespace : Bool} {location : Span.Location}
    {c : UInt8} {l : Lexeme} (h : start version whitespace location c = .token l) :
    l.start = location ∧ l.end = location.afterByte c := by
  simp only [start] at h
  repeat' split at h
  all_goals first | (cases h; exact ⟨rfl, rfl⟩) | cases h

/-- A token goes on from where it started. -/
theorem advance_pending {whitespace : Bool} {p p' : Pending} {location : Span.Location} {c : UInt8}
    (h : advance whitespace p location c = .pending p') : p'.start = p.start := by
  simp only [advance, legacyStringByte] at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

/-- A token ended with a byte spans from its start to after the byte. -/
theorem advance_tokenWith {whitespace : Bool} {p : Pending} {location : Span.Location} {c : UInt8}
    {l : Lexeme} (h : advance whitespace p location c = .tokenWith l) :
    l.start = p.start ∧ l.end = location.afterByte c := by
  simp only [advance, legacyStringByte] at h
  repeat' split at h
  all_goals first | (cases h; exact ⟨rfl, rfl⟩) | cases h

/-- A token ended before a byte spans from its start to the byte. -/
theorem advance_tokenBefore {whitespace : Bool} {p : Pending} {location : Span.Location} {c : UInt8}
    {l : Lexeme} (h : advance whitespace p location c = .tokenBefore l) :
    l.start = p.start ∧ l.end = location := by
  simp only [advance, legacyStringByte] at h
  repeat' split at h
  all_goals first | (cases h; exact ⟨rfl, rfl⟩) | cases h

/-- A token ended by the end of the input spans from its start to the end. -/
theorem finish_token {whitespace : Bool} {p : Pending} {location : Span.Location} {l : Lexeme}
    (h : finish whitespace p location = .token l) : l.start = p.start ∧ l.end = location := by
  simp only [finish] at h
  repeat' split at h
  all_goals first | (cases h; exact ⟨rfl, rfl⟩) | cases h

/-- What `start` gives, as far as where the lexemes are. -/
abbrev Started.Spec (location : Span.Location) (c : UInt8) : Started → Prop
  | .pending p => p.start = location
  | .token l => l.Valid ∧ l.start = location ∧ l.end = location.afterByte c
  | _ => True

theorem start_spec (version : Token.Version) (whitespace : Bool) (location : Span.Location)
    (c : UInt8) :
    (start version whitespace location c).Spec location c := by
  cases h : start version whitespace location c with
  | pending p => exact start_pending h
  | token l => exact ⟨start_token h, start_token_span h⟩
  | _ => trivial

/-- `start`, with what it gives as far as where the lexemes are. -/
def startS (version : Token.Version) (whitespace : Bool) (location : Span.Location) (c : UInt8) :
    {s : Started // s.Spec location c} :=
  ⟨start version whitespace location c, start_spec version whitespace location c⟩

/-- What `advance` gives, as far as where the lexemes are. -/
abbrev Advanced.Spec (p : Pending) (location : Span.Location) (c : UInt8) : Advanced → Prop
  | .pending p' => p'.start = p.start
  | .tokenWith l => l.start = p.start ∧ l.end = location.afterByte c
  | .tokenBefore l => l.start = p.start ∧ l.end = location
  | _ => True

theorem advance_spec (whitespace : Bool) (p : Pending) (location : Span.Location) (c : UInt8) :
    (advance whitespace p location c).Spec p location c := by
  cases h : advance whitespace p location c with
  | pending p' => exact advance_pending h
  | tokenWith l => exact advance_tokenWith h
  | tokenBefore l => exact advance_tokenBefore h
  | _ => trivial

/-- `advance`, with what it gives as far as where the lexemes are. -/
def advanceS (whitespace : Bool) (p : Pending) (location : Span.Location) (c : UInt8) :
    {a : Advanced // a.Spec p location c} :=
  ⟨advance whitespace p location c, advance_spec whitespace p location c⟩

/-- What `finish` gives, as far as where the lexemes are. -/
abbrev Finished.Spec (p : Pending) (location : Span.Location) : Finished → Prop
  | .token l => l.start = p.start ∧ l.end = location
  | _ => True

theorem finish_spec (whitespace : Bool) (p : Pending) (location : Span.Location) :
    (finish whitespace p location).Spec p location := by
  cases h : finish whitespace p location with
  | token l => exact finish_token h
  | _ => trivial

/-- `finish`, with what it gives as far as where the lexemes are. -/
def finishS (whitespace : Bool) (p : Pending) (location : Span.Location) :
    {f : Finished // f.Spec p location} :=
  ⟨finish whitespace p location, finish_spec whitespace p location⟩

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
  /-- The consumer has had the rest discarded, from the location: the input is discarded up to
  its end. -/
  | discarding (start : Span.Location)

/-- Whether the token in progress, if any, starts before the location. -/
abbrev Activity.StartsBefore : Activity → Span.Location → Prop
  | .token p, location => p.start.offset < location.offset
  | _, _ => True

/-- Where discarding begins when the consumer asks for it at a lexeme that ends at `location`:
where the lexer began to discard, if it discards already. -/
def Activity.discardStart : Activity → Span.Location → Span.Location
  | .discarding start, _ => start
  | _, location => location

/- The fields are public, so that proofs about the lexer can read them. -/
/-- The state of the lexer, apart from its consumer. -/
structure Core where
  /-- The SMT-LIB version in force. -/
  version : Token.Version
  /-- The version the lexer was constructed with, in force again after the end of the input. -/
  initialVersion : Token.Version
  /-- The location of the next byte to be fed. -/
  location : Span.Location
  activity : Activity
  /--
  The number of parentheses left open by the tokens handed over, never below zero. A recovery
  skips to where they are closed.
  -/
  depth : Nat
  /-- The token in progress, if any, starts before the next byte to be fed, so that the token
  has a byte when it ends. -/
  startedBefore : activity.StartsBefore location
  /-- Whether the lexer holds the result the consumer broke with, which it keeps outside its
  state: any token handed over while it is held is trailing input. -/
  holding : Bool

namespace Core

/-- The state at the start of an input. -/
def initial (version : Token.Version) : Core :=
  { version, initialVersion := version, location := Span.Location.initial, activity := .idle,
    depth := 0, startedBefore := trivial, holding := false }

/-- The state after the end of the input: as at the start, under the initial version. -/
def reset (self : Core) : Core :=
  initial self.initialVersion

end Core

/-! ## Hand-overs -/

/-- A batch of the lexeme alone, which has a byte unless it is the end of file. -/
def Lexeme.batch (l : Lexeme) (h : l.Valid) : Token.Internal.TokenBatch :=
  ({ Token.Internal.TokenBatch.empty 1 with bytes :=
      l.content } : Token.Internal.TokenBatch).pushLocated l.category 0
    l.content.size l.start l.end (Nat.zero_le _) h

/-- A cursor over the batch of a lexeme alone has a token. -/
theorem Lexeme.hasNext (l : Lexeme) (h : l.Valid) (version : Token.Version) :
    (Token.BatchCursor.Internal.new version (l.batch h)).HasNext :=
  Token.BatchCursor.hasNext_new version (by
    rw [Lexeme.batch]
    exact Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) (Token.Internal.TokenBatch.len_push ..).symm)

/-- The number of parentheses open after a token of the category. -/
def depthAfter (depth : Nat) : Token.TokenCategory → Nat
  | .parenOpen => depth + 1
  -- a closing parenthesis that closes nothing leaves nothing open
  | .parenClose => depth - 1
  | _ => depth

/-- A lexing error with the location where it takes effect. -/
structure Failure (E : Type) where
  cause : LexErrorCause E
  /-- The span of the error: that of the bytes that raised a lexical error, and for an error of
  the consumer, the empty span where it takes effect. The naive lexer does not keep the span of
  the token the consumer failed at; it agrees with the other lexers on the error's cause, not on
  its span. -/
  span : Span
  location : Span.Location

/-- The token in progress, which starts before the next byte, starts before the byte after
it. -/
theorem startsBefore_afterByte {p : Pending} {location : Span.Location} (c : UInt8)
    (h : p.start.offset < location.offset) :
    (Activity.token p).StartsBefore (location.afterByte c) := by
  show p.start.offset < (location.afterByte c).offset
  rw [afterByte_offset]
  omega

/-- The token in progress of the lexer state starts before its location. -/
theorem Core.started {core : Core} {p : Pending} (h : core.activity = .token p) :
    p.start.offset < core.location.offset := by
  have := core.startedBefore
  rw [h] at this
  exact this

/-- The value, with the proof that it is the value: a match on it gives the equation. -/
def withEq {α : Type} (x : α) : {y : α // x = y} :=
  ⟨x, rfl⟩

/-- The offset that the tokens lexed so far end at or before: the start of the token in
progress, or the location if there is none. -/
abbrev Core.frontier (core : Core) : Nat :=
  match core.activity with
  | .token p => p.start.offset
  | _ => core.location.offset

theorem Core.frontier_of_not_token {core : Core} (h : ∀ p, core.activity ≠ .token p) :
    core.frontier = core.location.offset := by
  unfold Core.frontier
  split
  · exact absurd ‹_› (h _)
  · rfl

theorem Core.frontier_le (core : Core) : core.frontier ≤ core.location.offset := by
  unfold Core.frontier
  split
  · exact Nat.le_of_lt (core.started ‹_›)
  · exact Nat.le_refl _

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]

/- The functions below thread the lexer state `Core` through by hand, each taking it and
giving it back, while the consumer is the state of the monad `StateT H m`, in which the
consumer runs. They make the hand-overs and the consumer's calls; what the bytes mean is
decided by the pure step above. -/

/--
Hands the lexeme over to the consumer, alone in a cursor under the version in force, and
takes its answer, with whether the consumer had the rest discarded. The version on the cursor
the consumer gives back is in force from then on.
-/
def handOver (core : Core) (l : Lexeme) (h : l.Valid) :
    StateT H m (Except E (ControlFlow R) × Bool × Core) := do
  let cursor := Token.BatchCursor.Internal.new core.version (l.batch h)
  let (answer, ⟨after, _⟩) ← Token.ConsumeFrom.consume (H := H) cursor (l.hasNext h core.version)
  -- the consumer has consumed at least one token, and the cursor has just this one
  return (answer, discardRequested after,
    { core with version := after.version, depth := depthAfter core.depth l.category })

/--
Hands the lexeme over and turns the consumer's answer into what lexing does next: go on
(`none`), go on holding the result the consumer finished with (`some`, located at the end of
the lexeme), or fail after the lexeme. While a result is held, the lexeme is not handed over:
it is trailing input. If the consumer has the rest discarded, the input is discarded from the
end of the lexeme on.
-/
def handOverAt (core : Core) (l : Lexeme) (h : l.Valid) :
    StateT H m (Except (Failure E) (Option (Span.Located R)) × Core) := do
  if core.holding then
    -- a result is held: what follows it is trailing input
    return (.error { cause := .lexical .unexpectedTrailingToken
                     span := Span.Internal.newUnchecked l.start l.end, location := l.start }, core)
  let (answer, discards, core) ← handOver core l h
  return match answer with
    | .ok flow =>
      let core := if discards then
          { core with activity := .discarding l.end, startedBefore := trivial }
        else core
      match flow with
      | .continue => (.ok none, core)
      | .break value => (.ok (some { value, location := l.end }), { core with holding := true })
    | .error err =>
      -- the discarding stands, from where it began
      let core := if discards then
          { core with activity := .discarding (core.activity.discardStart l.end)
                      startedBefore := trivial }
        else core
      (.error { cause := .consumer err, span := Span.Internal.newUnchecked l.end l.end
                location := l.end }, core)

/-- Lexes the byte `c` with no token in progress. -/
def lexStart (core : Core) (c : UInt8) :
    StateT H m (Except (Failure E) (Option (Span.Located R)) × Core) := do
  let whitespace := Token.Consume.isConcrete (H := H)
  let after := core.location.afterByte c
  match startS core.version whitespace core.location c with
  | ⟨.idle, _⟩ =>
    return (.ok none, { core with activity := .idle, location := after, startedBefore := trivial })
  | ⟨.pending p, hp⟩ =>
    return (.ok none, { core with
      activity := .token p, location := after
      startedBefore := by
        show p.start.offset < (core.location.afterByte c).offset
        rw [show p.start = core.location from hp, afterByte_offset]; omega })
  | ⟨.token l, hl⟩ =>
    handOverAt { core with activity := .idle, location := after, startedBefore := trivial } l hl.1
  | ⟨.error failure, _⟩ =>
    return (.error { cause := .lexical failure.kind, span := failure.span
                     location := failure.location }, core)

/--
Lexes the byte `c`, at the lexer's location, and gives back the lexer state after it. Returns
`some` if the consumer has finished on a token, and the failure if the byte or the consumer
raised one; the lexer is then at the failure point.

`recover` is the consumer's call at the end of a recovery.
-/
def lexByte (recover : Span.Location → StateT H m Unit) (core : Core) (c : UInt8) :
    StateT H m (Except (Failure E) (Option (Span.Located R)) × Core) := do
  let location := core.location
  match withEq core.activity with
  -- the byte is discarded, and the location stays where the discarding began
  | ⟨.discarding _, _⟩ => return (.ok none, core)
  -- only the end of the input can follow, there is nothing to lex
  | ⟨.ended, _⟩ => return (.ok none, core)
  | ⟨.recovered, _⟩ =>
    -- the consumer is told of a recovery before any token
    recover location
    lexStart { core with activity := .idle, startedBefore := trivial } c
  | ⟨.skipping skip, _⟩ =>
    match scan (core.version == .v2_0) skip core.depth c with
    | .skip skip depth =>
      let core := { core with
        location := location.afterByte c, activity := .skipping skip, depth
        startedBefore := trivial }
      return (.ok none, core)
    | .before =>
      recover location
      lexStart { core with activity := .idle, startedBefore := trivial } c
    | .after =>
      let location := location.afterByte c
      recover location
      return (.ok none, { core with
        location, activity := .idle, depth := 0, startedBefore := trivial })
  | ⟨.idle, _⟩ => lexStart core c
  | ⟨.token p, ha⟩ =>
    let whitespace := Token.Consume.isConcrete (H := H)
    let after := location.afterByte c
    have hp : p.start.offset < location.offset := core.started ha
    match advanceS whitespace p location c with
    | ⟨.pending p', h⟩ =>
      return (.ok none, { core with
        activity := .token p', location := after
        startedBefore :=
          startsBefore_afterByte c (by rw [show p'.start = p.start from h]; exact hp) })
    | ⟨.idle, _⟩ =>
      return (.ok none,
        { core with activity := .idle, location := after, startedBefore := trivial })
    | ⟨.tokenWith l, h⟩ =>
      handOverAt { core with activity := .idle, location := after, startedBefore := trivial } l
        (.inl (by
          rw [show l.start = p.start from h.1, show l.end = location.afterByte c from h.2,
            afterByte_offset]
          omega))
    | ⟨.tokenBefore l, h⟩ =>
      let (result, core) ← handOverAt { core with activity := .idle, startedBefore := trivial } l
        (.inl (by
          rw [show l.start = p.start from h.1, show l.end = location from h.2]; exact hp))
      -- the consumer has had the rest discarded: the byte is the first one discarded, and the
      -- location stays where the discarding began
      let discard (held : Option (Span.Located R)) (start : Span.Location) :
          StateT H m (Except (Failure E) (Option (Span.Located R)) × Core) :=
        return (.ok held, { core with activity := .discarding start, startedBefore := trivial })
      match result with
      | .ok none =>
        match core.activity with
        | .discarding start => discard none start
        -- the byte is lexed under the version the consumer has left in force
        | _ => lexStart core c
      | .ok (some located) =>
        match core.activity with
        | .discarding start => discard (some located) start
        -- the consumer has finished: the byte is lexed as trailing input
        | _ => do
          let (result, core) ← lexStart core c
          return (result.map fun _ => some located, core)
      | .error failure => return (.error failure, core)
    | ⟨.error failure, _⟩ =>
      return (.error { cause := .lexical failure.kind, span := failure.span
                       location := failure.location }, core)

/--
Lexes the bytes of the slice from `index` on. `held` is the result the consumer finished with,
if it has finished on an earlier byte of the slice.
-/
def lexFrom (recover : Span.Location → StateT H m Unit) (slice : ByteSlice) (index : Nat)
    (core : Core) (held : Option (Span.Located R)) :
    StateT H m (Except (Failure E) (Option (Span.Located R)) × Core) := do
  if h : index < slice.size then
    let (result, core) ← lexByte recover core slice[index]
    match result with
    | .ok none => lexFrom recover slice (index + 1) core held
    | .ok (some located) => lexFrom recover slice (index + 1) core (some located)
    | .error failure => return (.error failure, core)
  else
    return (.ok held, core)
termination_by slice.size - index

/--
Turns the failure into the error to return. A recovering lexer (`recovers`) makes the consumer
abandon its unfinished work and starts skipping from the failure point; `atEnd` says whether
the end of the input raised the failure.
-/
def failCall (recovers : Bool) (abandon : Span.Location → StateT H m Unit) (failure : Failure E)
    (atEnd : Bool) (core : Core) : StateT H m (LexError E × Core) := do
  if !recovers then
    return ({ cause := failure.cause, span := failure.span, continuesFrom := none }, core)
  let activity : Activity := if atEnd then
      -- the input has ended, nothing is left to skip
      .ended
    else
      -- the skipping starts inside the string or quoted symbol the error was in
      match failure.cause with
      | .lexical kind => match kind with
        | .forbiddenCharInString => .skipping .string
        | .backslashInQuotedSymbol | .forbiddenCharInQuotedSymbol => .skipping .quotedSymbol
        | _ => .skipping .plain
      -- the consumer fails after a whole token: with nothing open, nothing is skipped
      | .consumer _ => if core.depth == 0 then .recovered else .skipping .plain
  abandon failure.location
  return ({ cause := failure.cause, span := failure.span,
            continuesFrom := some failure.location },
    { core with
      location := failure.location, activity
      -- a value is confirmed only at the end of the input: an error after a break drops it
      holding := false
      startedBefore := by simp only [activity]; split <;> (repeat' split) <;> trivial })

/-- Lexes the slice, or discards it if the consumer has had the rest discarded. Returns the result
the consumer broke with in the slice, if it did. -/
def lexSliceStep (recovers : Bool) (abandon recover : Span.Location → StateT H m Unit)
    (slice : ByteSlice) (core : Core) :
    StateT H m (Except (LexError E) (Option (Span.Located R)) × Core) := do
  let core ← match core.activity with
    -- the consumer failed after a whole token with nothing open: the recovery is made here,
    -- even if the slice is empty
    | .recovered => do
      recover core.location
      pure { core with activity := .idle, startedBefore := trivial }
    | _ => pure core
  match core.activity with
  -- the input has ended with the error, there is nothing to lex
  | .ended => return (.ok none, core)
  | _ =>
    let (result, core) ← lexFrom recover slice 0 core none
    match result with
    | .ok held => return (.ok held, core)
    | .error failure =>
      let (err, core) ← failCall recovers abandon failure false core
      return (.error err, core)

/--
Lexes the end of the input: ends the token in progress, and hands over the end-of-file token
unless a result is held.
-/
def lexEnd (core : Core) :
    StateT H m (Except (Failure E) (ControlFlow (Span.Located R)) × Core) := do
  let whitespace := Token.Consume.isConcrete (H := H)
  let location := core.location
  let (result, core) ← match withEq core.activity with
    | ⟨.token p, ha⟩ => match finishS whitespace p location with
      | ⟨.none, _⟩ => pure (.ok none, { core with activity := .idle, startedBefore := trivial })
      | ⟨.token l, h⟩ =>
        handOverAt { core with activity := .idle, startedBefore := trivial } l
          (.inl (by
            rw [show l.start = p.start from h.1, show l.end = location from h.2]
            exact core.started ha))
      | ⟨.error failure, _⟩ =>
        pure (.error { cause := .lexical failure.kind, span := failure.span
                       location := failure.location }, core)
    | ⟨.idle, _⟩ | ⟨.recovered, _⟩ | ⟨.skipping _, _⟩ | ⟨.ended, _⟩ | ⟨.discarding _, _⟩ =>
      pure (.ok none, core)
  match result with
  | .error failure => return (.error failure, core)
  -- the consumer has finished on the token, the end-of-file token is not handed over
  | .ok (some located) => return (.ok (.break located), core)
  | .ok none =>
    -- a held result is returned without the end of the input handed over
    if core.holding then
      return (.ok .continue, core)
    let eof : Lexeme :=
      { category := .endOfFile, content := .empty, start := location, «end» := location }
    let (result, core) ← handOverAt core eof (.inr ⟨rfl, rfl⟩)
    return match result with
      | .ok none => (.ok .continue, core)
      | .ok (some located) => (.ok (.break located), core)
      | .error failure => (.error failure, core)

/-- Lexes the end of the input, which resets the lexer unless it fails and recovers. -/
def lexEofStep (recovers : Bool) (abandon recover : Span.Location → StateT H m Unit) (core : Core) :
    StateT H m (Except (LexError E) (ControlFlow (Span.Located R)) × Core) := do
  -- the end of the input ends any skipping
  let recovered := match core.activity with
    | .recovered | .skipping _ | .ended => true
    | _ => false
  let core ← if recovered then do
      recover core.location
      pure { core with activity := .idle, startedBefore := trivial }
    else
      pure core
  let (result, core) ← lexEnd core
  match result with
  | .ok flow => return (.ok flow, core.reset)
  | .error failure =>
    if recovered then
      -- the consumer has refused the end of the input with nothing left to abandon:
      -- the error is final, and the input has ended
      return (.error { cause := failure.cause, span := failure.span, continuesFrom := none },
        core.reset)
    let (err, core) ← failCall recovers abandon failure true core
    return (.error err, core)

end

/-! ## The lexer -/

/-- The naive lexer, with its consumer `H`; `recovery` says whether it recovers from errors. -/
structure Lexer (H : Type) {R E : Type} [Token.Consume H R E]
    (recovery : Type := Recovery.FailFast) where
  handler : H
  core : Core
  /-- The result the consumer broke with, located where it broke, held until the end of the
  input. -/
  held : Option (Span.Located R)

section

variable {H : Type} {R E : Type} [Token.Consume H R E]

/-- What a lexer call that failed gives back, by whether the lexer recovers. -/
@[expose]
def Lexer.AfterErrorOf (H : Type) [Token.Consume H R E] (recovery : Type) : Bool → Type
  | false => Unit
  | true => Lexer H recovery

/--
What a lexer call that failed gives back: nothing for a lexer that stops at its first error,
which cannot be used again, and the lexer itself for a recovering one, from which the rest of
the input is to be fed.
-/
@[expose]
def Lexer.AfterError (H : Type) [Token.Consume H R E] (recovery : Type) [Recovers recovery] :
    Type :=
  Lexer.AfterErrorOf H recovery (Recovers.recovers recovery)

/--
A recovering lexer whose end of the input raised an error.

The input has ended, so only the end of the input can be lexed again, which completes the
recovery.
-/
structure Lexer.PendingEof (H : Type) [Token.Consume H R E] (recovery : Type := Recovering)
    where
  private mk ::
  private lexer : Lexer H recovery

/--
What a recovering lexer gives back after its end of the input failed: the lexer, if the error
is final, or the lexer that can only lex the end of the input again, if the error continues at
the end.
-/
inductive Lexer.AfterEof (H : Type) [Token.Consume H R E] (recovery : Type := Recovering) where
  | lexer (lexer : Lexer H recovery)
  | pending (pending : Lexer.PendingEof H recovery)

/-- What a lexer gives back after its end of the input failed, by whether the lexer recovers. -/
@[expose]
def Lexer.AfterEofErrorOf (H : Type) [Token.Consume H R E] (recovery : Type) : Bool → Type
  | false => Unit
  | true => Lexer.AfterEof H recovery

/--
What a lexer gives back after its end of the input failed: nothing for a lexer that stops at
its first error, and what remains of a recovering one.
-/
@[expose]
def Lexer.AfterEofError (H : Type) [Token.Consume H R E] (recovery : Type)
    [Recovers recovery] : Type :=
  Lexer.AfterEofErrorOf H recovery (Recovers.recovers recovery)

namespace Lexer

/-- Constructs the lexer. The lexer stops at its first error. -/
def new (consumer : H) (version : Token.Version) : Lexer H :=
  { handler := consumer, core := Core.initial version, held := none }

/-- Constructs a lexer that recovers from errors. -/
def newRecovering [Token.Recover H m] (consumer : H)
    (version : Token.Version) : Lexer H Recovering :=
  { handler := consumer, core := Core.initial version, held := none }

/-- The location of the next byte to be fed. -/
def currentLocation (self : Lexer H recovery) : Span.Location :=
  self.core.location

/--
The SMT-LIB version currently in force.

The version can change if the token consumer asks for it from the cursor. The end of the
input resets the version to the initial one.
-/
def version (self : Lexer H recovery) : Token.Version :=
  self.core.version

/--
Where the lexer began to discard the input, if it discards.

The consumer asks for discarding through its cursor. The lexer then drops everything it is fed
and hands over nothing but the end of the input. The end of the input ends discarding.
-/
def discardedFrom (self : Lexer H recovery) : Option Span.Location :=
  match self.core.activity with
  | .discarding start => some start
  | _ => none
/-- What a failed call gives back, by whether the lexer recovers. -/
def afterErrorOf : (recovers : Bool) → Lexer H recovery → AfterErrorOf H recovery recovers
  | false, _ => ()
  | true, lexer => lexer

/-- What a failed call gives back: nothing for a lexer that stops at its first error, the lexer
for a recovering one. -/
def afterError [Recovers recovery] (lexer : Lexer H recovery) : AfterError H recovery :=
  afterErrorOf (Recovers.recovers recovery) lexer

/-- What a failed end of the input gives back, by whether the lexer recovers. -/
def afterEofErrorOf : (recovers : Bool) → Lexer H recovery → (continues : Bool) →
    AfterEofErrorOf H recovery recovers
  | false, _, _ => ()
  | true, lexer, true => .pending ⟨lexer⟩
  | true, lexer, false => .lexer lexer

/-- What a failed end of the input gives back: nothing for a lexer that stops at its first error;
for a recovering one, the lexer that can only lex the end of the input again if the error
continues there, and the lexer otherwise. -/
def afterEofError [Recovers recovery] (lexer : Lexer H recovery) (continues : Bool) :
    AfterEofError H recovery :=
  afterEofErrorOf (Recovers.recovers recovery) lexer continues

/-- Runs a step on the lexer's state with its consumer, and puts the lexer together again. -/
def run [Monad m] (self : Lexer H recovery)
    (step : Core → StateT H m (α × Core)) : m (α × Lexer H recovery) := do
  let { handler, core, held } := self
  let ((result, core), handler) ← (step core).run handler
  return (result, { handler, core, held })

/-- The result to return at the end of the input: the held one, else the one the consumer broke
with at the end of the input; none if the consumer continued there, breaking its contract. -/
def eofResult (held : Option (Span.Located R)) (flow : ControlFlow (Span.Located R)) :
    Option (Span.Located R) :=
  match held, flow with
  | some held, _ => some held
  | none, .break located => some located
  | none, .continue => none

/--
Lexes the given slice, sending the lexed tokens to the consumer.

If the token consumer returns `ControlFlow.break` on some token, the lexer holds the result,
located where the consumer broke, and goes on lexing what it is fed. Any token handed over
after it is the error `UnexpectedTrailingToken`. The result is returned by `lexEof`.

If the consumer has the rest discarded, the lexer drops everything it is fed until the end of
the input (see `discardedFrom`).

If an error occurs, a lexer that stops at its first error is not given back. A recovering lexer
makes the consumer abandon its unfinished work, drops the held result, and returns the error.
`LexError.continuesFrom` determines the location from which further lexing should be started
for error recovery.
-/
def lexSlice [Monad m] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]
    [Recovery.Recovers recovery] [Recovery.LexRecovery recovery H m]
    (self : Lexer H recovery) (slice : ByteSlice) :
    m (Except (LexError E × AfterError H recovery) (Lexer H recovery)) := do
  let step := lexSliceStep (Recovers.recovers recovery) (Recovery.LexRecovery.abandon recovery)
    (Recovery.LexRecovery.recover recovery) slice
  let (result, self) ← self.run step
  return match result with
    | .ok held => .ok { self with held := held.or self.held }
    | .error err => .error (err, afterError { self with held := none })

/--
Lexes end-of-file, sending the lexed tokens to the consumer.

If the lexer holds a result, the end of the input is not handed over and the held result is
returned. Otherwise the end-of-file token is handed over, also while the lexer discards, and the
consumer must break on it: the result it breaks with is returned, with its location. A consumer
that continues on the end-of-file token breaks its contract; the lexer then returns `none`.

The end of the input resets the lexer: the version to the initial one, discarding, the held
result, and any partial token.

If an error occurs, a lexer that stops at its first error is not given back. A recovering lexer
makes the consumer abandon its unfinished work and returns the error. `LexError.continuesFrom`
determines the location from which further lexing should be started for error recovery.
-/
def lexEof [Monad m] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]
    [Recovery.Recovers recovery] [Recovery.LexRecovery recovery H m]
    (self : Lexer H recovery) :
    m (Except (LexError E × AfterEofError H recovery) (Option (Span.Located R) × Lexer H recovery))
        := do
  let step := lexEofStep (Recovers.recovers recovery) (Recovery.LexRecovery.abandon recovery)
    (Recovery.LexRecovery.recover recovery)
  let (result, self) ← self.run step
  return match result with
    | .ok flow => .ok (eofResult self.held flow, { self with held := none })
    | .error err => .error (err, afterEofError { self with held := none } err.continuesFrom.isSome)

/--
Lexes the end of the input again, which completes the recovery.

The lexer hands over the end-of-file token, and returns what `lexEof` does. An error is final:
the lexer resets itself and does not continue.
-/
def PendingEof.lexEof [Monad m] [∀ batch, Token.ConsumeFrom H
    (Token.BatchCursor batch) m] [Token.Recover H m]
    (self : PendingEof H) :
    m (Except (LexError E × Lexer H Recovering) (Option (Span.Located R) × Lexer H Recovering))
        := do
  let step := lexEofStep true (Token.Recover.abandon (H := H)) (Token.Recover.recover (H := H))
  let (result, lexer) ← self.lexer.run step
  return match result with
    | .ok flow => .ok (eofResult lexer.held flow, { lexer with held := none })
    | .error err => .error (err, { lexer with held := none })

/--
Lexes the whole input including EOF at the end.

Returns what `lexEof` does, and the lexer reset by the end of the input.

If an error occurs, the lexer is not given back.
-/
def lexAll [Monad m] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] (self : Lexer H)
    (input : ByteSlice) :
    m (Except (LexError E × AfterError H FailFast) (Option (Span.Located R) × Lexer H)) := do
  match ← self.lexSlice input with
  | .ok self => self.lexEof
  | .error err => return .error err

end Lexer

end

end BSmtLib.Lexer.Internal.VNaive
