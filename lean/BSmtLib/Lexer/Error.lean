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
  | unexpectedByte
  /-- The item was expected here. -/
  | expected (item : LexicalExpected)
  | unclosedString
  | forbiddenByteInString
  /-- A colon is not followed by a keyword name. -/
  | emptyKeyword
  | backslashInQuotedSymbol
  | forbiddenByteInQuotedSymbol
  | unclosedQuotedSymbol
  | numeralLeadingZero
  | missingDelimiter
  /-- An entry was to be handed over after the value the consumer broke with. -/
  | unexpectedTrailingToken
  deriving BEq, Hashable, Repr, Inhabited

/-- The reason why a lexer call failed: a lexical error or a consumer error. -/
inductive LexerErrorKind (E : Type) where
  /-- The input is lexically malformed. -/
  | lexical (kind : LexicalErrorKind)
  /-- The token consumer returned an error. -/
  | consumer (error : E)
  deriving BEq, Repr

/- LEAN: the constructor is private, as Rust's fields are, and the lexers build an error with
`LexerError.Internal.new`. The fields are readable as `error.kind`, `error.span` and
`error.continuesFrom`, replacing the getters. -/
/-- Error that caused lexing to stop. -/
structure LexerError (E : Type) where
  private mk ::
  /-- The reason why the lexer call failed: a lexical error or a consumer error. -/
  kind : LexerErrorKind E
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
The most useful location for deciphering the error.

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

/-- The cause, at the line and the column of `location`, counted from one. -/
@[no_expose] instance {E : Type} [ToString E] : ToString (LexerError E) where
  toString self :=
    let location := self.location
    s!"{self.kind} at line {location.line + 1}, column {location.column + 1}"

/--
The reason why lexing from a buffered reader or a file failed: an I/O error, a lexical error or
a consumer error.
-/
inductive LexerReadErrorKind (E : Type) where
  /-- Reading from the file or the buffered reader failed. -/
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
/-- Error that ended lexing the input from a buffered reader or a file. -/
structure LexerReadError (E : Type) where
  private mk ::
  /-- The reason why lexing failed. -/
  kind : LexerReadErrorKind E
  /--
  Span where the error occurred.

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
The most useful location for deciphering the error.

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

/-- The cause, at the line and the column of `location`, counted from one. -/
@[no_expose] instance {E : Type} [ToString E] : ToString (LexerReadError E) where
  toString self :=
    let location := self.location
    s!"{self.kind} at line {location.line + 1}, column {location.column + 1}"

end BSmtLib.Lexer.Error
