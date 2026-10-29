module

public import BSmtLib.Grammar.Multiple.MatchCases

public section

/-!
# Owned match cases

The owned buffer from which a user builds the match cases that the end of a `match` hands over.
-/

/- LEAN: a part of Rust's `multiple.rs`, in a module of its own beside
`BSmtLib.Grammar.Multiple.MatchCases`, as each module declares what it is named after. -/

namespace BSmtLib.Grammar.Multiple

open BSmtLib.Grammar.Nodes (Pattern)

/- LEAN: parameterised by the handled terms, as `MatchCases` is. Each pattern is a view of a copy
of its bytes that the buffer made, so the view needs no copy. -/
/-- Owned match cases. -/
structure MatchCasesBuf (HandledTerm : Type) where
  private ofArray ::
  private entries : Array (Pattern × HandledTerm)

namespace MatchCasesBuf

variable {HandledTerm : Type}

/-- Creates empty match cases. -/
def new : MatchCasesBuf HandledTerm := ⟨#[]⟩

/-- Adds a match case after the others. -/
def push (self : MatchCasesBuf HandledTerm) (pattern : Pattern) (term : HandledTerm) :
    MatchCasesBuf HandledTerm :=
  ⟨self.entries.push (Grammar.Nodes.Pattern.Internal.copy pattern, term)⟩

/-- Removes all match cases. -/
def clear (_ : MatchCasesBuf HandledTerm) : MatchCasesBuf HandledTerm := new

/-- Views as `MatchCases`. -/
def viewMut (self : MatchCasesBuf HandledTerm) : MatchCases HandledTerm :=
  MatchCases.Internal.new self.entries

/-- Returns the number of match cases. -/
def len (self : MatchCasesBuf HandledTerm) : Nat := self.entries.size

/-- Returns `true` if there are no match cases. -/
def isEmpty (self : MatchCasesBuf HandledTerm) : Bool := self.entries.isEmpty

@[no_expose] instance : Inhabited (MatchCasesBuf HandledTerm) := ⟨new⟩

@[no_expose] instance [Repr HandledTerm] : Repr (MatchCasesBuf HandledTerm) :=
  ⟨fun self p => reprPrec self.viewMut p⟩

end MatchCasesBuf

end BSmtLib.Grammar.Multiple
