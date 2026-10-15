module

public import BSmtLib.Parser.Category.Ident

public section

/-!
# Sorts

The parser of a sort, and the parser of one sort that a driver runs (`SortParser`).
-/

namespace BSmtLib.Parser.Category.«Sort»

open BSmtLib.Nodes BSmtLib.Traits BSmtLib.Parser.Category.Ident
open BSmtLib.Token (Version)

/-- What the sort parser is doing at its innermost open sort. -/
inductive SortMode where
  /-- Before a sort: the sort itself, or the next argument of the innermost application. -/
  | start
  /-- After the `(` of a sort, before its head. -/
  | opened
  /-- Reading a sort that is an indexed identifier. -/
  | identOnly (ident : IdentState)
  /-- Reading the indexed identifier at the head of an application. -/
  | startingIdent (ident : IdentState)

/-- An application of a sort, open: its head and the argument sorts handled so far. -/
structure SortLevel (HandledSort : Type) where
  head : Identifier
  arguments : Array HandledSort

/-- The state of the sort parser: its mode, and the open applications, innermost first. -/
structure SortState (HandledSort : Type) where
  mode : SortMode
  levels : List (SortLevel HandledSort)

/-- The sort parser before a sort. -/
def SortState.init {HandledSort : Type} : SortState HandledSort :=
  { mode := .start, levels := [] }

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- A sort is complete: it is handled, and is the result or the next argument. -/
def sortComplete (levels : List (SortLevel (Handler.«Sort» H))) (head : Identifier)
    (arguments : Array (Handler.«Sort» H)) :
    PM H (Internal.Step (SortState (Handler.«Sort» H)) (Handler.«Sort» H)) := do
  let sort ← call (Handler.handleSort head arguments)
  match levels with
  | [] => return .done sort
  | level :: outer =>
    return .more
      { mode := .start, levels := { level with arguments := level.arguments.push sort } :: outer }

/--
A step of the sort parser: ⟨identifier⟩ | `(` ⟨identifier⟩ ⟨sort⟩+ `)`. Each sort is handled
at its last token, its arguments before it.
-/
def sortStep (version : Version) (self : SortState (Handler.«Sort» H)) (token : Internal.Input) :
    PM H (Internal.Step (SortState (Handler.«Sort» H)) (Handler.«Sort» H)) :=
  match self.mode with
  | .start =>
    match token with
    | .symbol name => sortComplete self.levels ⟨name, #[]⟩ #[]
    | .parenOpen => pure (.more { self with mode := .opened })
    | .parenClose =>
      match self.levels with
      | [] => syntaxError .expectedSort
      | level :: outer =>
        if level.arguments.isEmpty then syntaxError .emptySortApplication
        else sortComplete outer level.head level.arguments
    | _ => syntaxError .expectedSort
  | .opened =>
    match token with
    | .symbol name =>
      pure (.more { mode := .start, levels := ⟨⟨name, #[]⟩, #[]⟩ :: self.levels })
    | .parenOpen => pure (.more { self with mode := .startingIdent .opened })
    | token =>
      if token.isWord .underscore then
        pure (.more { self with mode := .identOnly .afterUnderscore })
      else syntaxError .expectedSortInner
  | .identOnly ident => do
    match ← ident.step version token with
    | .more ident => return .more { self with mode := .identOnly ident }
    | .done head => sortComplete self.levels head #[]
  | .startingIdent ident => do
    match ← ident.step version token with
    | .more ident => return .more { self with mode := .startingIdent ident }
    | .done head => return .more { mode := .start, levels := ⟨head, #[]⟩ :: self.levels }

end

/-- The parser of one sort (`SmtSortParser`). -/
structure SortParser (H : Type) {m : Type → Type} [Handler H m] where
  state : SortState (Handler.«Sort» H)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- The sort parser before a sort. -/
def SortParser.new : SortParser H := ⟨.init⟩

instance : Internal.ParseByToken (SortParser H) H m (Handler.Error H) (Handler.«Sort» H) where
  arrive _ _ := pure ()
  step version parser token := do
    match ← sortStep version parser.state token with
    | .more state => return .more ⟨state⟩
    | .done result => return .done result
  reset _ := .new

instance : Parse (SortParser H) H m (Handler.Error H) (Handler.«Sort» H) where
  parse := Internal.parseByToken

end

end BSmtLib.Parser.Category.«Sort»
