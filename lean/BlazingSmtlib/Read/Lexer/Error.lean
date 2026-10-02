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

/- LEAN: not in Rust, where each of these conditions is a panic. Lean's `panic!` does not stop
the program but goes on with a default value, so these are reported as errors instead,
until it is shown that they cannot occur. -/
/-- A broken contract between the lexer and its handler, or a bug in the lexer. -/
inductive InternalError where
  /-- A batch without tokens was to be handed over. -/
  | emptyBatch
  /-- The token handler continued without consuming all tokens. -/
  | tokensNotConsumed
  /-- The token handler both finished and requested relex. -/
  | finishedAndRelexed
  /-- The lexer was used after a lexer error. -/
  | lexedAfterError
  /-- The token handler stopped before the token the slice started with. -/
  | stoppedBeforeStart
  /-- The token handler requested relex at end of file. -/
  | relexAtEndOfFile
  deriving BEq, Repr, Inhabited

namespace InternalError

/-- What went wrong, in words. -/
def message : InternalError → String
  | .emptyBatch => "flushed batch must have at least one token"
  | .tokensNotConsumed => "the token handler must consume all tokens before continuing"
  | .finishedAndRelexed => "the token handler cannot both finish and request relex"
  | .lexedAfterError => "cannot lex after a lexer error"
  | .stoppedBeforeStart => "the token handler must not stop before the starting token"
  | .relexAtEndOfFile => "token handler cannot request relex at end of file"

end InternalError

inductive LexError (E : Type) where
  | lexer (error : LexerError)
  | handler (error : E)
  /- LEAN: not in Rust, see `InternalError`. -/
  | internal (error : InternalError)
  deriving BEq, Repr

end BlazingSmtlib.Read.Lexer
