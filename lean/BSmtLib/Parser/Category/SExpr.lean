module

public import BSmtLib.Parser

public section

/-!
# S-expressions

The parser of an S-expression, and the parser of one S-expression that a driver runs
(`SExprParser`).
-/

namespace BSmtLib.Parser.Category.SExpr

open BSmtLib.Grammar.Nodes BSmtLib.Handler
open BSmtLib (Version)
open BSmtLib.Parser.Internal (PM call syntaxError)

namespace Internal

/-- The state of the S-expression parser: the items of the open lists, innermost first. -/
abbrev SExprState (HandledSExpr : Type) := List (Array HandledSExpr)

/-- An S-expression is complete: it is the result, or the next item of the innermost list. -/
def sExprComplete {HandledSExpr : Type} (levels : SExprState HandledSExpr)
    (sExpr : HandledSExpr) : Internal.Step (SExprState HandledSExpr) HandledSExpr :=
  match levels with
  | [] => .done sExpr
  | items :: outer => .more (items.push sExpr :: outer)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A step of the S-expression parser: an atom is handled at its token, a list at its `)`, its items
before it. A reserved word is an S-expression from 2.6 on.
-/
def sExprStep (version : Version) (self : SExprState (Handler.SExpr H)) (token : Internal.Input) :
    PM H (Internal.Step (SExprState (Handler.SExpr H)) (Handler.SExpr H)) := do
  let atom ← match token with
    | .parenOpen => return .more (#[] :: self)
    | .parenClose =>
      match self with
      | [] => syntaxError (.expected #[.sExpr])
      | items :: outer => do
        let list ← call (Handler.handleSExpr (.sExprs (.new items)))
        return sExprComplete outer list
    | .constant constant => pure (Grammar.Nodes.SExpr.specialConstant constant)
    | .symbol symbol => pure (.symbol symbol)
    | .keyword name => pure (.keyword name)
    | .reserved word =>
      if version ≥ .v2_6 then pure (.reserved word) else syntaxError (.expected #[.sExpr])
    | _ => syntaxError (.expected #[.sExpr])
  let handled ← call (Handler.handleSExpr atom)
  return sExprComplete self handled

end

end Internal

/--
Parses an S-expression.

Returns the S-expression that `Handler.handleSExpr` returns for it, having handled the
S-expressions inside it first.
-/
structure SExprParser (H : Type) {m : Type → Type} [Handler H m] where
  private mk ::
  private state : Internal.SExprState (Handler.SExpr H)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- Creates the parser. -/
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
