module

public import BSmtLib.Parser.Category.Sort
public import BSmtLib.Parser.Category.Token

public section

/-!
# Sorted variables

The parser of a sorted variable `(` ⟨symbol⟩ ⟨sort⟩ `)`.
-/

namespace BSmtLib.Parser.Category.SortedVar

open BSmtLib.Nodes BSmtLib.Traits BSmtLib.Parser.Category.Token BSmtLib.Parser.Category.Sort
open BSmtLib.Token (Version)

/-- The state of the sorted variable parser. -/
inductive SortedVarState (HandledSort : Type) where
  | start
  /-- After its `(`, before its symbol. -/
  | opened
  /-- Reading its sort. -/
  | sort (symbol : Symbol) (sort : SortState HandledSort)
  /-- After its sort, before the `)`. -/
  | close (symbol : Symbol) (sort : HandledSort)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- A step of the sorted variable parser: `(` ⟨symbol⟩ ⟨sort⟩ `)`. -/
def sortedVarStep (version : Version) (self : SortedVarState (Handler.«Sort» H))
    (token : Internal.Input) :
    PM H (Internal.Step (SortedVarState (Handler.«Sort» H)) (Symbol × Handler.«Sort» H)) := do
  match self with
  | .start =>
    expectOpen token
    return .more .opened
  | .opened => return .more (.sort (← expectSymbol token) .init)
  | .sort symbol sort =>
    match ← sortStep version sort token with
    | .more sort => return .more (.sort symbol sort)
    | .done sort => return .more (.close symbol sort)
  | .close symbol sort =>
    expectClose token
    return .done (symbol, sort)

end

end BSmtLib.Parser.Category.SortedVar
