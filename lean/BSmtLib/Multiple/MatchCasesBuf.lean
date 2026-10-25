module

public import BSmtLib.Multiple.MatchCases

public section

/-!
# Owned match cases

The owned buffer from which a user builds the match cases that the end of a `match` hands over.
-/

/- LEAN: a part of Rust's `multiple.rs`, in a module of its own beside
`BSmtLib.Multiple.MatchCases`, as each module declares what it is named after. -/

namespace BSmtLib.Multiple

open BSmtLib.Nodes (Pattern)

/-- Owned match cases, from which `MatchCases` is viewed. -/
/- LEAN: parameterised by the handled terms, as `MatchCases` is. Each pattern is a view of a copy
of its bytes that the buffer made, so the view needs no copy. -/
structure MatchCasesBuf (HandledTerm : Type) where
  private ofArray ::
  private entries : Array (Pattern × HandledTerm)

namespace MatchCasesBuf

variable {HandledTerm : Type}

def new : MatchCasesBuf HandledTerm := ⟨#[]⟩

def push (self : MatchCasesBuf HandledTerm) (pattern : Pattern) (term : HandledTerm) :
    MatchCasesBuf HandledTerm :=
  ⟨self.entries.push (Nodes.Pattern.Internal.copy pattern, term)⟩

def clear (_ : MatchCasesBuf HandledTerm) : MatchCasesBuf HandledTerm := new

def viewMut (self : MatchCasesBuf HandledTerm) : MatchCases HandledTerm :=
  MatchCases.Internal.new self.entries

def len (self : MatchCasesBuf HandledTerm) : Nat := self.entries.size

def isEmpty (self : MatchCasesBuf HandledTerm) : Bool := self.entries.isEmpty

@[no_expose] instance : Inhabited (MatchCasesBuf HandledTerm) := ⟨new⟩

end MatchCasesBuf

end BSmtLib.Multiple
