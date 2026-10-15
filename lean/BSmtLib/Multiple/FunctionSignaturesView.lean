module

public import BSmtLib.Nodes

public section

/-!
# Function signatures to be handled

The signatures of `define-funs-rec`, which its start hands over at once.
-/

/- LEAN: a part of Rust's `multiple.rs`, in a module of its own as it holds signatures of
`BSmtLib.Nodes`, which imports `BSmtLib.Multiple`; its owned buffer is in
`BSmtLib.Multiple.FunctionSignatures`. -/

namespace BSmtLib.Multiple

open BSmtLib.Nodes (Signature)

/-- Function signatures to be handled, such as those of `define-funs-rec`. -/
/- LEAN: Rust's `SmtFunctionSignatures`, the view of `SmtFunctionSignaturesBuf`, named by the
counterpart rule. -/
structure FunctionSignaturesView (S : Type) where
  private mk ::
  /-- The signatures, in order. -/
  toArray : Array (Signature S)

namespace FunctionSignaturesView

/- LEAN: crate-private in Rust; the library builds the view. -/
@[inline]
def Internal.new {S : Type} (toArray : Array (Signature S)) : FunctionSignaturesView S := ⟨toArray⟩

@[simp]
theorem Internal.toArray_new {S : Type} (toArray : Array (Signature S)) :
    (Internal.new toArray : FunctionSignaturesView S).toArray = toArray :=
  (rfl)

variable {S : Type}

@[inline]
def len (self : FunctionSignaturesView S) : Nat := self.toArray.size

@[inline]
def isEmpty (self : FunctionSignaturesView S) : Bool := self.toArray.isEmpty

@[inline]
def get? (self : FunctionSignaturesView S) (index : Nat) : Option (Signature S) :=
  self.toArray[index]?

@[no_expose] instance {m : Type → Type} [Monad m] : ForIn m (FunctionSignaturesView S) (Signature S) where
  forIn self init f := ForIn.forIn self.toArray init f

@[no_expose] instance [Repr S] : Repr (FunctionSignaturesView S) :=
  ⟨fun self p => reprPrec self.toArray p⟩

end FunctionSignaturesView

end BSmtLib.Multiple
