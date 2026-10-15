module

public import BSmtLib.Parser.Category.Sort
public import BSmtLib.Parser.Category.Token

public section

/-!
# Sorted variables

The parser of a sorted variable `(` ⟨symbol⟩ ⟨sort⟩ `)`.
-/

namespace BSmtLib.Parser.Category.SortedVar

open BSmtLib.Plain (Symbol SymbolView)
open BSmtLib.Nodes BSmtLib.Traits BSmtLib.Parser.Category.Token BSmtLib.Parser.Category.Sort
open BSmtLib.Parser.Category.Sort.Internal
open BSmtLib.Parser.Category.Token.Internal
open BSmtLib.Token (Version)
open BSmtLib.Parser.Internal (PM call syntaxError)

namespace Internal

/-- The state of the sorted variable parser. -/
inductive SortedVarState (HandledSort : Type) where
  | start
  /-- After its `(`, before its symbol. -/
  | opened
  /-- Reading its sort. -/
  | sort (symbol : SymbolView) (sort : SortState HandledSort)
  /-- After its sort, before the `)`. -/
  | close (symbol : SymbolView) (sort : HandledSort)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- A step of the sorted variable parser: `(` ⟨symbol⟩ ⟨sort⟩ `)`. -/
def sortedVarStep (version : Version) (self : SortedVarState (Handler.«Sort» H))
    (token : Internal.Input) :
    PM H (Internal.Step (SortedVarState (Handler.«Sort» H)) (SymbolView × Handler.«Sort» H)) := do
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

end Internal

/-- The parser of one sorted variable (`SmtSortedVarParser`). -/
structure SortedVarParser (H : Type) {m : Type → Type} [Handler H m] where
  private mk ::
  private state : Internal.SortedVarState (Handler.«Sort» H)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- The sorted variable parser before a sorted variable. -/
def SortedVarParser.new : SortedVarParser H := ⟨.start⟩

instance : Inhabited (SortedVarParser H) := ⟨.new⟩

@[no_expose]
instance Internal.instParseByTokenSortedVarParser :
    Internal.ParseByToken (SortedVarParser H) H m (Handler.Error H)
    (Symbol × Handler.«Sort» H) where
  arrive _ _ := pure ()
  step version parser token := do
    match ← Internal.sortedVarStep version parser.state token with
    | .more state => return .more ⟨state⟩
    | .done (symbol, sort) => return .done (symbol.intoOwned, sort)
  reset _ := .new

instance : Parse (SortedVarParser H) H m (Handler.Error H) (Symbol × Handler.«Sort» H) where
  parse := Internal.parseByToken

end

end BSmtLib.Parser.Category.SortedVar
