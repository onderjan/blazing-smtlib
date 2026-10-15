module

public import BSmtLib.Span

public section

namespace BSmtLib.Lexer.Error

inductive LexicalErrorKind where
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
  /-- An entry was to be handed over after the value the consumer broke with. -/
  | unexpectedTrailingToken
  deriving BEq, Repr, Inhabited

/-- The reason why a lexer call failed: a lexical error or a consumer error. -/
inductive LexErrorCause (E : Type) where
  /-- The input is lexically malformed. -/
  | lexical (kind : LexicalErrorKind)
  /-- The token consumer returned an error. -/
  | consumer (error : E)
  deriving BEq, Repr

/- LEAN: the fields are readable as `error.cause`, `error.span` and `error.continuesFrom`,
replacing the getters. -/
/-- Error that caused lexing to stop. -/
structure LexError (E : Type) where
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

end BSmtLib.Lexer.Error
