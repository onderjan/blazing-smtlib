import BlazingSmtlib.Span

namespace BlazingSmtlib.Read.Lexer

open BlazingSmtlib

inductive LexerErrorKind where
  | unexpectedCharacter
  | fractionDigitExpected
  | hexadecimalDigitExpected
  | binaryDigitExpected
  | baseSelectionExpected
  | unclosedStringLiteral
  | forbiddenCharInString
  | forbiddenKeywordName
  | backslashInQuotedSymbol
  | forbiddenCharInQuotedSymbol
  | unclosedQuotedSymbol
  | numeralLeadingZero
  | missingDelimiter
  deriving BEq, Repr, Inhabited

/- LEAN: the fields are readable as `error.kind` and `error.span`, replacing the getters. -/
structure LexerError where
  kind : LexerErrorKind
  span : SmtSpan
  deriving BEq, Repr, Inhabited

inductive LexError (E : Type) where
  | lexer (error : LexerError)
  | handler (error : E)
  deriving BEq, Repr

/- LEAN: a default value is needed for `panic!` in functions returning a `LexError`. It
cannot be derived, since deriving would require one for the handler's error type `E`,
which may have none (like Rust's `Infallible`); the lexer variant provides one for any
`E`. -/
instance : Inhabited (LexError E) := ⟨.lexer default⟩

end BlazingSmtlib.Read.Lexer
