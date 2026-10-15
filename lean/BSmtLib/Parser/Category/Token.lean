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
open BSmtLib.Plain (Numeral NumeralView Keyword KeywordView StringContent StringContentView Symbol
  SymbolView)
open BSmtLib.Parser.Internal (PM call syntaxError)
namespace Internal


section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- Takes a `(`. -/
@[inline]
def expectOpen (token : Internal.Input) : PM H Unit :=
  match token with
  | .parenOpen => pure ()
  | _ => syntaxError (.expectedToken #[.parenOpen])

/-- Takes a `)`. -/
@[inline]
def expectClose (token : Internal.Input) : PM H Unit :=
  match token with
  | .parenClose => pure ()
  | _ => syntaxError (.expectedToken #[.parenClose])

/-- Takes a symbol. -/
@[inline]
def expectSymbol (token : Internal.Input) : PM H SymbolView :=
  match token with
  | .symbol symbol => pure symbol
  | _ => syntaxError .expectedSymbol

/-- Takes a numeral. -/
@[inline]
def expectNumeral (token : Internal.Input) : PM H NumeralView :=
  match token with
  | .constant (.numeral digits) => pure digits
  | _ => syntaxError (.expectedToken #[.numeral])

/-- Takes a keyword. -/
@[inline]
def expectKeyword (token : Internal.Input) : PM H KeywordView :=
  match token with
  | .keyword name => pure name
  | _ => syntaxError (.expectedToken #[.keyword])

/-- Takes a string literal. -/
@[inline]
def expectString (token : Internal.Input) : PM H StringContentView :=
  match token with
  | .constant (.string content) => pure content
  | _ => syntaxError (.expectedToken #[.string])

end

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- The parser of a single symbol, as an element of a list. -/
def symbolStep (_ : Unit) (token : Internal.Input) : PM H (Internal.Step Unit SymbolView) := do
  return .done (← expectSymbol token)

end

end Internal
/-! The parsers of single tokens (`SmtParse`). Each finishes at its first token, which must be of
its kind, and needs no state. -/

/-- The parser of a symbol (`SmtSymbolParser`). -/
structure SymbolParser where

/-- The parser of a `(` (`SmtOpenParenParser`). -/
structure OpenParenParser where

/-- The parser of a `)` (`SmtCloseParenParser`). -/
structure CloseParenParser where

/-- The parser of a numeral (`SmtNumeralParser`). -/
structure NumeralParser where

/-- The parser of a keyword (`SmtKeywordParser`). -/
structure KeywordParser where

/-- The parser of a string literal (`SmtStringParser`). -/
structure StringParser where

/-- The symbol parser. -/
def SymbolParser.new : SymbolParser := {}

/-- The `(` parser. -/
def OpenParenParser.new : OpenParenParser := {}

/-- The `)` parser. -/
def CloseParenParser.new : CloseParenParser := {}

/-- The numeral parser. -/
def NumeralParser.new : NumeralParser := {}

/-- The keyword parser. -/
def KeywordParser.new : KeywordParser := {}

/-- The string literal parser. -/
def StringParser.new : StringParser := {}

instance : Inhabited SymbolParser := ⟨.new⟩

instance : Inhabited OpenParenParser := ⟨.new⟩

instance : Inhabited CloseParenParser := ⟨.new⟩

instance : Inhabited NumeralParser := ⟨.new⟩

instance : Inhabited KeywordParser := ⟨.new⟩

instance : Inhabited StringParser := ⟨.new⟩

namespace Internal

/- LEAN: the handler is a parameter of `Parse` but an `outParam` of `ParseByToken`, which a
parser type that names no handler cannot fix; so the steps of such a parser are a definition for
each handler, which its `parse` uses as a local instance. -/
/-- The steps, with the handler `H`, of a parser of a single token: it finishes at the token,
with what `expect` takes of it. -/
@[instance_reducible]
def singleByToken (H : Type) {m : Type → Type} [Monad m] [Handler H m] {P ρ : Type}
    (expect : Parser.Internal.Input → PM H ρ) :
    Parser.Internal.ParseByToken P H m (Handler.Error H) ρ where
  arrive _ _ := pure ()
  step _ _ token := do return .done (← expect token)
  reset self := self

end Internal

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

instance : Parse SymbolParser H m (Handler.Error H) Symbol where
  parse parser state cursor :=
    letI := Internal.singleByToken (P := SymbolParser) H
      fun token => SymbolView.intoOwned <$> Internal.expectSymbol token
    Parser.Internal.parseByToken parser state cursor

instance : Parse OpenParenParser H m (Handler.Error H) Unit where
  parse parser state cursor :=
    letI := Internal.singleByToken (P := OpenParenParser) H Internal.expectOpen
    Parser.Internal.parseByToken parser state cursor

instance : Parse CloseParenParser H m (Handler.Error H) Unit where
  parse parser state cursor :=
    letI := Internal.singleByToken (P := CloseParenParser) H Internal.expectClose
    Parser.Internal.parseByToken parser state cursor

instance : Parse NumeralParser H m (Handler.Error H) Numeral where
  parse parser state cursor :=
    letI := Internal.singleByToken (P := NumeralParser) H
      fun token => NumeralView.intoOwned <$> Internal.expectNumeral token
    Parser.Internal.parseByToken parser state cursor

instance : Parse KeywordParser H m (Handler.Error H) Keyword where
  parse parser state cursor :=
    letI := Internal.singleByToken (P := KeywordParser) H
      fun token => KeywordView.intoOwned <$> Internal.expectKeyword token
    Parser.Internal.parseByToken parser state cursor

instance : Parse StringParser H m (Handler.Error H) StringContent where
  parse parser state cursor :=
    letI := Internal.singleByToken (P := StringParser) H
      fun token => StringContentView.intoOwned <$> Internal.expectString token
    Parser.Internal.parseByToken parser state cursor

end

end BSmtLib.Parser.Category.Token
