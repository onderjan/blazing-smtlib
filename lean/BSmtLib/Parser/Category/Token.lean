module

public import BSmtLib.Parser

public section

/-!
# Single tokens

The parsers of single tokens: a `(`, a `)`, a symbol, a numeral, a keyword, a string literal,
each as part of a larger construct.
-/

namespace BSmtLib.Parser.Category.Token

open BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Plain (NumeralView KeywordView StringContentView)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- Takes a `(`. -/
@[inline]
def expectOpen (token : Input) : PM H Unit :=
  match token with
  | .parenOpen => pure ()
  | _ => syntaxError (.expectedToken #[.parenOpen])

/-- Takes a `)`. -/
@[inline]
def expectClose (token : Input) : PM H Unit :=
  match token with
  | .parenClose => pure ()
  | _ => syntaxError (.expectedToken #[.parenClose])

/-- Takes a symbol. -/
@[inline]
def expectSymbol (token : Input) : PM H Symbol :=
  match token with
  | .symbol symbol => pure symbol
  | _ => syntaxError .expectedSymbol

/-- Takes a numeral. -/
@[inline]
def expectNumeral (token : Input) : PM H NumeralView :=
  match token with
  | .constant (.numeral digits) => pure digits
  | _ => syntaxError (.expectedToken #[.numeral])

/-- Takes a keyword. -/
@[inline]
def expectKeyword (token : Input) : PM H KeywordView :=
  match token with
  | .keyword name => pure name
  | _ => syntaxError (.expectedToken #[.keyword])

/-- Takes a string literal. -/
@[inline]
def expectString (token : Input) : PM H StringContentView :=
  match token with
  | .constant (.string content) => pure content
  | _ => syntaxError (.expectedToken #[.string])

end

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- The parser of a single symbol, as an element of a list. -/
def symbolStep (_ : Unit) (token : Input) : PM H (Step Unit Symbol) := do
  return .done (← expectSymbol token)

end

end BSmtLib.Parser.Category.Token
