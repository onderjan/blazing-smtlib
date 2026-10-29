module

public import BSmtLib.Span

public section

namespace BSmtLib.Lexer.Error

/--
Character class expected by the lexer (fraction digit, hexadecimal digit, binary digit, or base).

This is used in `LexicalErrorKind.expected`.
-/
inductive LexicalExpected where
  /-- Digit of the fractional part of a decimal, e.g. `5` in `0.5`. -/
  | fractionDigit
  /-- Hexadecimal digit after `#x`, e.g. `A` in `#xA04`. -/
  | hexadecimalDigit
  /-- Binary digit after `#b`, e.g. `1` in `#b10`. -/
  | binaryDigit
  /-- Base of a number after `#` (`x` or `b`). -/
  | base
  deriving BEq, Hashable, Repr, Inhabited

/-- Why the input is lexically malformed. -/
inductive LexicalErrorKind where
  /-- A byte that cannot start any token appears where a token starts, e.g. `\` or `{`. -/
  | unexpectedByte
  /-- A byte of the class was expected here, e.g. a fraction digit after `7.` in `7.y`. -/
  | expected (item : LexicalExpected)
  /-- A string literal is not closed before the end of the input, e.g. `"abc`. -/
  | unclosedString
  /-- A string literal contains a byte that is not allowed in it, e.g. a null byte. -/
  | forbiddenByteInString
  /-- A colon is not followed by a keyword name, e.g. the `:` in `(get-info :)`. -/
  | emptyKeyword
  /-- A quoted symbol contains a backslash, e.g. `|a\b|`. -/
  | backslashInQuotedSymbol
  /-- A quoted symbol contains a byte that is not allowed in it, e.g. a null byte. -/
  | forbiddenByteInQuotedSymbol
  /-- A quoted symbol is not closed before the end of the input, e.g. `|abc`. -/
  | unclosedQuotedSymbol
  /--
  A numeral, or the whole part of a decimal, starts with a zero followed by another digit, e.g.
  `01` or `00.5`.
  -/
  | numeralLeadingZero
  /-- A token is followed by a byte that does not delimit it, e.g. `12abc` or `"s"t`. -/
  | missingDelimiter
  /--
  A token would be handed over after the consumer broke with a value, e.g. `y` when one term is
  read from `x y`.
  -/
  | unexpectedTrailingToken
  deriving BEq, Hashable, Repr, Inhabited

/-- Why lexing failed (lexical or consumer error). -/
inductive LexerErrorKind (E : Type) where
  /-- The input is lexically malformed. -/
  | lexical (kind : LexicalErrorKind)
  /-- The token consumer returned an error. -/
  | consumer (error : E)
  deriving BEq, Repr

/- LEAN: the constructor is private, as Rust's fields are, and the lexers build an error with
`LexerError.Internal.new`. The fields are readable as `error.kind`, `error.span` and
`error.continuesFrom`, replacing the getters. -/
/--
Error that forced lexing to stop.

Its `ToString` gives the line and the column counted from one, while `Span.Location` counts
them from zero.
-/
structure LexerError (E : Type) where
  private mk ::
  /-- Returns the kind of the error. -/
  kind : LexerErrorKind E
  /-- Returns the span where the error occurred. -/
  span : Span
  /--
  Returns where the rest of the input is to be fed from if the lexer continues (EXPERIMENTAL).

  If present, the lexer is recovering: it expects the input from this
  location on, and the end of the input once none is left.
  If absent, the lexer does not continue this input: either it stops
  at its first error, or the input has ended.

  Lexer recovery is implemented but experimental
  since the exact semantics have not yet been set in stone.
  It can change or be removed in any version and should not be used.
  -/
  continuesFrom : Option Span.Location
  deriving BEq, Repr

@[inline]
def LexerError.Internal.new {E : Type} (kind : LexerErrorKind E) (span : Span)
    (continuesFrom : Option Span.Location) : LexerError E :=
  { kind, span, continuesFrom }

@[simp]
theorem LexerError.Internal.kind_new {E : Type} (kind : LexerErrorKind E) (span : Span)
    (continuesFrom : Option Span.Location) :
    (LexerError.Internal.new kind span continuesFrom).kind = kind :=
  (rfl)

@[simp]
theorem LexerError.Internal.span_new {E : Type} (kind : LexerErrorKind E) (span : Span)
    (continuesFrom : Option Span.Location) :
    (LexerError.Internal.new kind span continuesFrom).span = span :=
  (rfl)

@[simp]
theorem LexerError.Internal.continuesFrom_new {E : Type} (kind : LexerErrorKind E) (span : Span)
    (continuesFrom : Option Span.Location) :
    (LexerError.Internal.new kind span continuesFrom).continuesFrom = continuesFrom :=
  (rfl)

/-- An error is the one built from its fields. -/
@[simp]
theorem LexerError.Internal.new_eta {E : Type} (error : LexerError E) :
    LexerError.Internal.new error.kind error.span error.continuesFrom = error :=
  (rfl)

/-- Two errors built from the same fields are equal. -/
theorem LexerError.Internal.new_inj {E : Type} {kind kind' : LexerErrorKind E}
    {span span' : Span} {continuesFrom continuesFrom' : Option Span.Location} :
    LexerError.Internal.new kind span continuesFrom =
        LexerError.Internal.new kind' span' continuesFrom' ↔
      kind = kind' ∧ span = span' ∧ continuesFrom = continuesFrom' := by
  constructor
  · intro h
    exact ⟨congrArg LexerError.kind h, congrArg LexerError.span h,
      congrArg LexerError.continuesFrom h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/- LEAN: Rust's crate-private `location_in`, which also checks the location in debug builds. -/
/-- The most useful location for deciphering an error of the kind within the span. -/
def LexicalErrorKind.Internal.locationIn (kind : LexicalErrorKind) (span : Span) :
    Span.Location :=
  match kind with
  -- the span ends after the offending byte, which is not a line feed: a line feed is allowed
  -- in both literals and delimits a token
  | .forbiddenByteInString | .backslashInQuotedSymbol | .forbiddenByteInQuotedSymbol
  | .missingDelimiter =>
    Span.Location.Internal.new (span.end.offset - 1) span.end.line (span.end.column - 1)
  | _ => span.start

/--
Returns the most useful location for deciphering the error.

Guaranteed to be within the span.
-/
def LexerError.location {E : Type} (self : LexerError E) : Span.Location :=
  match self.kind with
  | .lexical kind => LexicalErrorKind.Internal.locationIn kind self.span
  | .consumer _ => self.span.start

/- LEAN: Rust's `Display` implementations are `ToString` instances, with the same text. -/
@[no_expose] instance : ToString LexicalExpected where
  toString
    | .fractionDigit => "expected fractional digit"
    | .hexadecimalDigit => "expected hexadecimal digit"
    | .binaryDigit => "expected binary digit"
    | .base => "expected base (`x` or `b`) after `#`"

@[no_expose] instance : ToString LexicalErrorKind where
  toString
    | .unexpectedByte => "unexpected character"
    | .expected expected => toString expected
    | .unclosedString => "unclosed string literal"
    | .forbiddenByteInString => "forbidden character in string literal"
    | .emptyKeyword => "colon without keyword name"
    | .backslashInQuotedSymbol => "backslash in quoted symbol"
    | .forbiddenByteInQuotedSymbol => "forbidden character in quoted symbol"
    | .unclosedQuotedSymbol => "unclosed quoted symbol"
    | .numeralLeadingZero => "numeral with leading zero"
    | .missingDelimiter => "missing delimiter after token"
    | .unexpectedTrailingToken => "unexpected trailing token"

@[no_expose] instance {E : Type} [ToString E] : ToString (LexerErrorKind E) where
  toString
    | .lexical kind => toString kind
    | .consumer error => toString error

@[no_expose] instance {E : Type} [ToString E] : ToString (LexerError E) where
  toString self :=
    let location := self.location
    s!"{self.kind} at line {location.line + 1}, column {location.column + 1}"

/-- Why lexing from a buffered reader or a file failed (I/O, lexical, or consumer error). -/
inductive LexerReadErrorKind (E : Type) where
  /-- Opening or reading the file, or reading from the buffered reader, failed. -/
  | io (error : IO.Error)
  /-- The input is lexically malformed. -/
  | lexical (kind : LexicalErrorKind)
  /-- The token consumer returned an error. -/
  | consumer (error : E)

/- LEAN: Rust's derived `Debug`. Lean's `IO.Error` has no `Repr`, so an I/O error is shown by its
message. -/
@[no_expose] instance {E : Type} [Repr E] : Repr (LexerReadErrorKind E) where
  reprPrec kind prec :=
    let app (name : String) (argument : Std.Format) : Std.Format :=
      Repr.addAppParen (.group (.nest 2 (.text ("BSmtLib.Lexer.Error.LexerReadErrorKind." ++
        name) ++ .line ++ argument))) prec
    match kind with
    | .io error => app "io" (reprArg (toString error))
    | .lexical kind => app "lexical" (reprArg kind)
    | .consumer error => app "consumer" (reprArg error)

/- LEAN: the constructor is private, as Rust's fields are. The fields are readable as
`error.kind` and `error.span`, replacing the getters `kind`, `into_kind` and `span`. -/
/--
Error that forced lexing from a buffered reader or a file to stop.

Its `ToString` gives the line and the column counted from one, while `Span.Location` counts
them from zero.
-/
structure LexerReadError (E : Type) where
  private mk ::
  /-- Returns the kind of the error. -/
  kind : LexerReadErrorKind E
  /--
  Returns the span where the error occurred.

  For I/O errors, the span is empty, at the position where reading failed.
  -/
  span : Span
  deriving Repr

/- LEAN: Rust builds the error from its cause in the module, where its fields are visible. -/
/-- The error of the cause, in the span. -/
@[inline]
def LexerReadError.Internal.new {E : Type} (kind : LexerReadErrorKind E) (span : Span) :
    LexerReadError E :=
  { kind, span }

/--
Returns the most useful location for deciphering the error.

Guaranteed to be within the span.
-/
def LexerReadError.location {E : Type} (self : LexerReadError E) : Span.Location :=
  match self.kind with
  | .lexical kind => LexicalErrorKind.Internal.locationIn kind self.span
  | .io _ | .consumer _ => self.span.start

/- LEAN: Rust's `impl From<SmtLexerError<E>> for SmtLexerReadError<E>`, which Lean's conversion by
name stands for. -/
/-- Converts the error that ended lexing into an error of lexing from a buffered reader. -/
def LexerReadError.ofLex {E : Type} (error : LexerError E) : LexerReadError E :=
  let kind : LexerReadErrorKind E := match error.kind with
    | .lexical kind => .lexical kind
    | .consumer error => .consumer error
  { kind, span := error.span }

@[no_expose] instance {E : Type} [ToString E] : ToString (LexerReadErrorKind E) where
  toString
    | .io error => s!"I/O: {error}"
    | .lexical kind => toString kind
    | .consumer error => toString error

@[no_expose] instance {E : Type} [ToString E] : ToString (LexerReadError E) where
  toString self :=
    let location := self.location
    s!"{self.kind} at line {location.line + 1}, column {location.column + 1}"

end BSmtLib.Lexer.Error
