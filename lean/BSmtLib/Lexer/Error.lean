import BSmtLib.Span

namespace BSmtLib

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
  deriving BEq, Repr, Inhabited

/- LEAN: the fields are readable as `error.kind` and `error.span`, replacing the getters. -/
structure LexicalError where
  kind : LexicalErrorKind
  span : Span
  deriving BEq, Repr, Inhabited

/-- The reason why a lexer call failed: a lexical error or a consumer error. -/
inductive LexErrorCause (E : Type) where
  /-- The input is lexically malformed. -/
  | lexical (error : LexicalError)
  /-- The token consumer returned an error. -/
  | consumer (error : E)
  deriving BEq, Repr

/- LEAN: the fields are readable as `error.cause` and `error.continuesFrom`, replacing the
getters. -/
/-- Error that caused lexing to stop. -/
structure LexError (E : Type) where
  /-- The reason why the lexer call failed: a lexical error or a consumer error. -/
  cause : LexErrorCause E
  /--
  The location the rest of the input is to be fed from (if the lexer continues).

  If present, the lexer is recovering: it expects the input from this
  location on, and the end of the input once none is left.
  If absent, the lexer does not continue this input: either it stops
  at its first error, or the input has ended.
  -/
  continuesFrom : Option Location
  deriving BEq, Repr

end BSmtLib
