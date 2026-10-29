module

public import BSmtLib.Grammar.Nodes

public section

/-!
# Match cases to be handled

The cases of a `match` that its end hands over, each a pattern with its handled body.
-/

/- LEAN: a part of Rust's `multiple.rs`, in a module of its own as it holds patterns of
`BSmtLib.Grammar.Nodes`, which imports `BSmtLib.Grammar.Multiple`. -/

namespace BSmtLib.Grammar.Multiple

open BSmtLib.Grammar.Nodes (Pattern)

/- LEAN: Rust's `SmtMatchCases`, parameterised by the handled terms, where Rust's is by the
handler. -/
/-- View of match cases. -/
structure MatchCases (HandledTerm : Type) where
  private mk ::
  /-- The patterns with their bodies, in order. -/
  toArray : Array (Pattern × HandledTerm)

namespace MatchCases

/- LEAN: crate-private in Rust; the library builds the view. -/
@[inline]
def Internal.new {HandledTerm : Type} (toArray : Array (Pattern × HandledTerm)) :
    MatchCases HandledTerm :=
  ⟨toArray⟩

@[simp]
theorem Internal.toArray_new {HandledTerm : Type} (toArray : Array (Pattern × HandledTerm)) :
    (Internal.new toArray : MatchCases HandledTerm).toArray = toArray :=
  (rfl)

variable {HandledTerm : Type}

/-- Returns the number of match cases. -/
@[inline]
def len (self : MatchCases HandledTerm) : Nat := self.toArray.size

/-- Returns `true` if there are no match cases. -/
@[inline]
def isEmpty (self : MatchCases HandledTerm) : Bool := self.toArray.isEmpty

/-- Returns the pattern and term at the position, or `none` if it is out of bounds. -/
@[inline]
def get? (self : MatchCases HandledTerm) (index : Nat) : Option (Pattern × HandledTerm) :=
  self.toArray[index]?

@[no_expose] instance {m : Type → Type} [Monad m] :
    ForIn m (MatchCases HandledTerm) (Pattern × HandledTerm) where
  forIn self init f := ForIn.forIn self.toArray init f

@[no_expose] instance [Repr HandledTerm] : Repr (MatchCases HandledTerm) :=
  ⟨fun self p => reprPrec self.toArray p⟩

end MatchCases

end BSmtLib.Grammar.Multiple
