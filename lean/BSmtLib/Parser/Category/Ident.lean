module

public import BSmtLib.Parser

public section

/-!
# Identifiers

The parser of an identifier: a symbol, or an indexed identifier `(` `_` ⟨symbol⟩ ⟨index⟩+ `)`.
-/

namespace BSmtLib.Parser.Category.Ident

open BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Token (Version)

/-- The state of the identifier parser. -/
inductive IdentState where
  /-- Before the identifier. -/
  | start
  /-- After its `(`, before the `_`. -/
  | opened
  /-- After `(` `_`, before its symbol. -/
  | afterUnderscore
  /-- After its symbol, reading its indices up to the `)`. -/
  | indices (symbol : Symbol) (indices : Array Index)

namespace IdentState

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A step of the identifier parser: a symbol is an identifier by itself; `(` `_` ⟨symbol⟩
⟨index⟩+ `)` an indexed one. A symbol is an index from 2.5 on.
-/
def step (version : Version) (self : IdentState) (token : Internal.Input) :
    PM H (Internal.Step IdentState Identifier) :=
  match self, token with
  | .start, .symbol symbol => pure (.done ⟨symbol, #[]⟩)
  | .start, .parenOpen => pure (.more .opened)
  | .start, _ => syntaxError .expectedIdent
  | .opened, token =>
    if token.isWord .underscore then pure (.more .afterUnderscore)
    else syntaxError .expectedUnderscore
  | .afterUnderscore, .symbol symbol => pure (.more (.indices symbol #[]))
  | .afterUnderscore, _ => syntaxError .expectedSymbol
  | .indices symbol found, .parenClose =>
    if found.isEmpty then syntaxError .emptyIdentIndices
    else pure (.done ⟨symbol, found⟩)
  | .indices symbol found, .constant (.numeral digits) =>
    pure (.more (.indices symbol (found.push (.numeral digits))))
  | .indices symbol found, .symbol index =>
    if version ≥ .v2_5 then pure (.more (.indices symbol (found.push (.symbol index))))
    else syntaxError .expectedIndexOrCloseParen
  | .indices _ _, _ => syntaxError .expectedIndexOrCloseParen

end IdentState

end BSmtLib.Parser.Category.Ident
