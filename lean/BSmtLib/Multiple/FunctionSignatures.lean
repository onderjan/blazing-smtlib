module

public import BSmtLib.Multiple.FunctionSignaturesView

public section

/-!
# Owned function signatures

The buffer from which a user builds function signatures to hand over.
-/

/- LEAN: a part of Rust's `multiple.rs`, in a module of its own with its view
(`BSmtLib.Multiple.FunctionSignaturesView`). -/

namespace BSmtLib.Multiple

open BSmtLib.Nodes (Signature)
open BSmtLib.Plain (SymbolView)

/-- Owned function signatures, from which `FunctionSignaturesView`
and each `Signature` are viewed. -/
/- LEAN: Rust's `SmtFunctionSignaturesBuf`, named by the counterpart rule. Each name is a view
of a copy of its bytes that the buffer made, so the view needs no copy. -/
structure FunctionSignatures (S : Type) where
  private ofArray ::
  private entries : Array (Signature S)

namespace FunctionSignatures

variable {S : Type}

def new : FunctionSignatures S := ⟨#[]⟩

/-- Starts a signature with no parameters; `pushParam` adds them. -/
def push (self : FunctionSignatures S) (name : SymbolView) (resultSort : S) :
    FunctionSignatures S :=
  ⟨self.entries.push ⟨name.intoOwned.asView, #[], resultSort⟩⟩

def len (self : FunctionSignatures S) : Nat := self.entries.size

def isEmpty (self : FunctionSignatures S) : Bool := self.entries.isEmpty

/-- Adds a parameter to the last signature pushed. -/
/- LEAN: Rust panics when no signature was pushed; here the caller proves that one was. -/
def pushParam (self : FunctionSignatures S) (name : SymbolView) (sort : S) (_ : 0 < self.len) :
    FunctionSignatures S :=
  ⟨self.entries.modify (self.entries.size - 1) fun signature =>
    { signature with params := signature.params.push (name.intoOwned.asView, sort) }⟩

def clear (_ : FunctionSignatures S) : FunctionSignatures S := new

def view (self : FunctionSignatures S) : FunctionSignaturesView S :=
  FunctionSignaturesView.Internal.new self.entries

def get? (self : FunctionSignatures S) (index : Nat) : Option (Signature S) :=
  self.entries[index]?

@[no_expose] instance : Inhabited (FunctionSignatures S) := ⟨new⟩

end FunctionSignatures

end BSmtLib.Multiple
