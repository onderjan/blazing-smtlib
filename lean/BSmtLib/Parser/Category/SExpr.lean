module

public import BSmtLib.Parser

public section

/-!
# S-expressions

The parser of an s-expression, and the parser of one s-expression that a driver runs
(`SExprParser`).
-/

namespace BSmtLib.Parser.Category.SExpr

open BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Token (Version)
open BSmtLib.Parser.Internal (PM call syntaxError)

namespace Internal

/-- The state of the s-expression parser: the items of the open lists, innermost first. -/
abbrev SExprState (HandledSExpr : Type) := List (Array HandledSExpr)

/-- An s-expression is complete: it is the result, or the next item of the innermost list. -/
def sExprComplete {HandledSExpr : Type} (levels : SExprState HandledSExpr)
    (sExpr : HandledSExpr) : Internal.Step (SExprState HandledSExpr) HandledSExpr :=
  match levels with
  | [] => .done sExpr
  | items :: outer => .more (items.push sExpr :: outer)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A step of the s-expression parser: an atom is handled at its token, a list at its `)`, its items
before it. A reserved word is an s-expression from 2.6 on.
-/
def sExprStep (version : Version) (self : SExprState (Handler.SExpr H)) (token : Internal.Input) :
    PM H (Internal.Step (SExprState (Handler.SExpr H)) (Handler.SExpr H)) := do
  let atom ← match token with
    | .parenOpen => return .more (#[] :: self)
    | .parenClose =>
      match self with
      | [] => syntaxError .expectedSExpr
      | items :: outer => do
        let list ← call (Handler.handleSExpr (.list (.new items)))
        return sExprComplete outer list
    | .constant constant => pure (SExprNode.constant constant)
    | .symbol symbol => pure (.symbol symbol)
    | .keyword name => pure (.keyword name)
    | .reserved word =>
      if version ≥ .v2_6 then pure (.reserved word) else syntaxError .expectedSExpr
    | _ => syntaxError .expectedSExpr
  let handled ← call (Handler.handleSExpr atom)
  return sExprComplete self handled

end

end Internal

/-- The parser of one s-expression (`SmtSExprParser`). -/
structure SExprParser (H : Type) {m : Type → Type} [Handler H m] where
  private mk ::
  private state : Internal.SExprState (Handler.SExpr H)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- The s-expression parser before an s-expression. -/
def SExprParser.new : SExprParser H := ⟨[]⟩

instance : Inhabited (SExprParser H) := ⟨.new⟩

@[no_expose]
instance Internal.instParseByTokenSExprParser :
    Internal.ParseByToken (SExprParser H) H m (Handler.Error H) (Handler.SExpr H) where
  arrive _ _ := pure ()
  step version parser token := do
    match ← Internal.sExprStep version parser.state token with
    | .more state => return .more ⟨state⟩
    | .done result => return .done result
  reset _ := .new

instance : Parse (SExprParser H) H m (Handler.Error H) (Handler.SExpr H) where
  parse := Internal.parseByToken

end

end BSmtLib.Parser.Category.SExpr
