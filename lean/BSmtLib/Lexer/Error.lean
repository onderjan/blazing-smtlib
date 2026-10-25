module

public import BSmtLib.Span

public section

namespace BSmtLib.Lexer.Error

/-- What the lexer expected, in `LexicalErrorKind.expected`. -/
inductive LexicalExpected where
  /-- A digit of the fractional part of a decimal. -/
  | fractionDigit
  /-- A hexadecimal digit after `#x`. -/
  | hexadecimalDigit
  /-- A binary digit after `#b`. -/
  | binaryDigit
  /-- The base of a number after `#`: `x` or `b`. -/
  | base
  deriving BEq, Hashable, Repr, Inhabited

inductive LexicalErrorKind where
  | unexpectedCharacter
  /-- The item was expected here. -/
  | expected (item : LexicalExpected)
  | unclosedStringLiteral
  | forbiddenCharInString
  /-- A colon is not followed by a keyword name. -/
  | emptyKeyword
  | backslashInQuotedSymbol
  | forbiddenCharInQuotedSymbol
  | unclosedQuotedSymbol
  | numeralLeadingZero
  | missingDelimiter
  /-- An entry was to be handed over after the value the consumer broke with. -/
  | unexpectedTrailingToken
  deriving BEq, Hashable, Repr, Inhabited

/-- The reason why a lexer call failed: a lexical error or a consumer error. -/
inductive LexErrorCause (E : Type) where
  /-- The input is lexically malformed. -/
  | lexical (kind : LexicalErrorKind)
  /-- The token consumer returned an error. -/
  | consumer (error : E)
  deriving BEq, Repr

/- LEAN: the constructor is private, as Rust's fields are, and the lexers build an error with
`LexError.Internal.new`. The fields are readable as `error.cause`, `error.span` and
`error.continuesFrom`, replacing the getters. -/
/-- Error that caused lexing to stop. -/
structure LexError (E : Type) where
  private mk ::
  /-- The reason why the lexer call failed: a lexical error or a consumer error. -/
  cause : LexErrorCause E
  /-- Location where the error occurred. -/
  span : Span
  /--
  Where the rest of the input is to be fed from if the lexer continues (EXPERIMENTAL).

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
def LexError.Internal.new {E : Type} (cause : LexErrorCause E) (span : Span)
    (continuesFrom : Option Span.Location) : LexError E :=
  { cause, span, continuesFrom }

@[simp]
theorem LexError.Internal.cause_new {E : Type} (cause : LexErrorCause E) (span : Span)
    (continuesFrom : Option Span.Location) :
    (LexError.Internal.new cause span continuesFrom).cause = cause :=
  (rfl)

@[simp]
theorem LexError.Internal.span_new {E : Type} (cause : LexErrorCause E) (span : Span)
    (continuesFrom : Option Span.Location) :
    (LexError.Internal.new cause span continuesFrom).span = span :=
  (rfl)

@[simp]
theorem LexError.Internal.continuesFrom_new {E : Type} (cause : LexErrorCause E) (span : Span)
    (continuesFrom : Option Span.Location) :
    (LexError.Internal.new cause span continuesFrom).continuesFrom = continuesFrom :=
  (rfl)

/-- An error is the one built from its fields. -/
@[simp]
theorem LexError.Internal.new_eta {E : Type} (error : LexError E) :
    LexError.Internal.new error.cause error.span error.continuesFrom = error :=
  (rfl)

/-- Two errors built from the same fields are equal. -/
theorem LexError.Internal.new_inj {E : Type} {cause cause' : LexErrorCause E} {span span' : Span}
    {continuesFrom continuesFrom' : Option Span.Location} :
    LexError.Internal.new cause span continuesFrom =
        LexError.Internal.new cause' span' continuesFrom' ↔
      cause = cause' ∧ span = span' ∧ continuesFrom = continuesFrom' := by
  constructor
  · intro h
    exact ⟨congrArg LexError.cause h, congrArg LexError.span h,
      congrArg LexError.continuesFrom h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/- LEAN: Rust's crate-private `location_in`, which also checks the location in debug builds. -/
/-- The most useful location for deciphering an error of the kind within the span. -/
def LexicalErrorKind.Internal.locationIn (kind : LexicalErrorKind) (span : Span) :
    Span.Location :=
  match kind with
  -- the span ends after the offending byte, which is not a line feed: a line feed is allowed
  -- in both literals and delimits a token
  | .forbiddenCharInString | .backslashInQuotedSymbol | .forbiddenCharInQuotedSymbol
  | .missingDelimiter =>
    Span.Location.Internal.new (span.end.offset - 1) span.end.line (span.end.column - 1)
  | _ => span.start

/--
The most useful location for deciphering the error.

Guaranteed to be within the span.
-/
def LexError.location {E : Type} (self : LexError E) : Span.Location :=
  match self.cause with
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
    | .unexpectedCharacter => "unexpected character"
    | .expected expected => toString expected
    | .unclosedStringLiteral => "unclosed string literal"
    | .forbiddenCharInString => "forbidden character in string literal"
    | .emptyKeyword => "colon without keyword name"
    | .backslashInQuotedSymbol => "backslash in quoted symbol"
    | .forbiddenCharInQuotedSymbol => "forbidden character in quoted symbol"
    | .unclosedQuotedSymbol => "unclosed quoted symbol"
    | .numeralLeadingZero => "numeral with leading zero"
    | .missingDelimiter => "missing delimiter after token"
    | .unexpectedTrailingToken => "unexpected trailing token"

@[no_expose] instance {E : Type} [ToString E] : ToString (LexErrorCause E) where
  toString
    | .lexical kind => toString kind
    | .consumer error => toString error

/-- The cause, at the line and the column of `location`, counted from one. -/
@[no_expose] instance {E : Type} [ToString E] : ToString (LexError E) where
  toString self :=
    let location := self.location
    s!"{self.cause} at line {location.line + 1}, column {location.column + 1}"

end BSmtLib.Lexer.Error
