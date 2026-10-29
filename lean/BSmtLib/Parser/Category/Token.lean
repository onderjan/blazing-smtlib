module

public import BSmtLib.Parser

public section

/-!
# Single tokens

The parsers of single tokens: a `(`, a `)`, a symbol, a numeral, a keyword, a string literal,
each as part of a larger construct.
-/

namespace BSmtLib.Parser.Category.Token

open BSmtLib.Grammar.Nodes BSmtLib.Handler
open BSmtLib.Lexicon.Value (NumeralBuf Numeral KeywordBuf Keyword StringContentBuf StringContent
  SymbolBuf Symbol)
open BSmtLib.Parser.Internal (PM call syntaxError)
namespace Internal


section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- Takes a `(`. -/
@[inline]
def expectOpen (token : Internal.Input) : PM H Unit :=
  match token with
  | .parenOpen => pure ()
  | _ => syntaxError (.expected #[.token .parenOpen])

/-- Takes a `)`. -/
@[inline]
def expectClose (token : Internal.Input) : PM H Unit :=
  match token with
  | .parenClose => pure ()
  | _ => syntaxError (.expected #[.token .parenClose])

/-- Takes a symbol. -/
@[inline]
def expectSymbol (token : Internal.Input) : PM H Symbol :=
  match token with
  | .symbol symbol => pure symbol
  | _ => syntaxError (.expected #[.symbol])

/-- Takes a numeral. -/
@[inline]
def expectNumeral (token : Internal.Input) : PM H Numeral :=
  match token with
  | .constant (.numeral digits) => pure digits
  | _ => syntaxError (.expected #[.token .numeral])

/-- Takes a keyword. -/
@[inline]
def expectKeyword (token : Internal.Input) : PM H Keyword :=
  match token with
  | .keyword name => pure name
  | _ => syntaxError (.expected #[.token .keyword])

/-- Takes a string literal. -/
@[inline]
def expectString (token : Internal.Input) : PM H StringContent :=
  match token with
  | .constant (.string content) => pure content
  | _ => syntaxError (.expected #[.token .string])

end

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- The parser of a single symbol, as an element of a list. -/
def symbolStep (_ : Unit) (token : Internal.Input) : PM H (Internal.Step Unit Symbol) := do
  return .done (← expectSymbol token)

end

end Internal
/-! The parsers of single tokens. Each finishes at its first token, which must be of its kind,
and needs no state. -/

/-- Parses a symbol. -/
structure SymbolParser where
  private mk ::

/-- Parses an opening parenthesis. -/
structure OpenParenParser where
  private mk ::

/-- Parses a closing parenthesis. -/
structure CloseParenParser where
  private mk ::

/-- Parses a numeral. -/
structure NumeralParser where
  private mk ::

/-- Parses a keyword. -/
structure KeywordParser where
  private mk ::

/-- Parses a string literal. -/
structure StringParser where
  private mk ::

/-- Creates the parser. -/
def SymbolParser.new : SymbolParser := {}

/-- Creates the parser. -/
def OpenParenParser.new : OpenParenParser := {}

/-- Creates the parser. -/
def CloseParenParser.new : CloseParenParser := {}

/-- Creates the parser. -/
def NumeralParser.new : NumeralParser := {}

/-- Creates the parser. -/
def KeywordParser.new : KeywordParser := {}

/-- Creates the parser. -/
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

instance : Parse SymbolParser H m (Handler.Error H) SymbolBuf where
  parse parser state cursor :=
    letI := Internal.singleByToken (P := SymbolParser) H
      fun token => Symbol.intoOwned <$> Internal.expectSymbol token
    Parser.Internal.parseByToken parser state cursor

instance : Parse OpenParenParser H m (Handler.Error H) Unit where
  parse parser state cursor :=
    letI := Internal.singleByToken (P := OpenParenParser) H Internal.expectOpen
    Parser.Internal.parseByToken parser state cursor

instance : Parse CloseParenParser H m (Handler.Error H) Unit where
  parse parser state cursor :=
    letI := Internal.singleByToken (P := CloseParenParser) H Internal.expectClose
    Parser.Internal.parseByToken parser state cursor

instance : Parse NumeralParser H m (Handler.Error H) NumeralBuf where
  parse parser state cursor :=
    letI := Internal.singleByToken (P := NumeralParser) H
      fun token => Numeral.intoOwned <$> Internal.expectNumeral token
    Parser.Internal.parseByToken parser state cursor

instance : Parse KeywordParser H m (Handler.Error H) KeywordBuf where
  parse parser state cursor :=
    letI := Internal.singleByToken (P := KeywordParser) H
      fun token => Keyword.intoOwned <$> Internal.expectKeyword token
    Parser.Internal.parseByToken parser state cursor

instance : Parse StringParser H m (Handler.Error H) StringContentBuf where
  parse parser state cursor :=
    letI := Internal.singleByToken (P := StringParser) H
      fun token => StringContent.intoOwned <$> Internal.expectString token
    Parser.Internal.parseByToken parser state cursor

end

end BSmtLib.Parser.Category.Token
