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

namespace Lexer

/- LEAN: not in Rust, where each of these conditions is a panic. Lean's `panic!` does not stop
the program but goes on with a default value, so these are reported as errors instead,
until it is shown that they cannot occur. -/
/-- A broken contract between the lexer and its handler, or a bug in the lexer. -/
inductive InternalError where
  /-- The lexer was used after a lexer error. -/
  | lexedAfterError
  /-- The token handler stopped before the token the slice started with. -/
  | stoppedBeforeStart
  /- LEAN: a slice whose end is not below `USize.size`, which cannot be in memory; see
  `Input.ofSlice?`. -/
  /-- The slice does not fit the positions of the lexer. -/
  | sliceTooLarge
  deriving BEq, Repr, Inhabited

namespace InternalError

/-- What went wrong, in words. -/
def message : InternalError → String
  | .lexedAfterError => "cannot lex after a lexer error"
  | .stoppedBeforeStart => "the token handler must not stop before the starting token"
  | .sliceTooLarge => "the slice must end below the largest position"

end InternalError

end Lexer

inductive LexError (E : Type) where
  | lexer (error : LexicalError)
  | handler (error : E)
  /- LEAN: not in Rust, see `InternalError`. -/
  | internal (error : Lexer.InternalError)
  deriving BEq, Repr

end BSmtLib
