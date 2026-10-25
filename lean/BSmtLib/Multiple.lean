module

public import BSmtLib.Plain
public import BSmtLib.Token.AppendTokens

public section

/-!
# Multiple values to be handled

The containers in which the parser hands several values over at once: the values of a list, the
names with their values, the symbols, and the parts of the datatype commands, with the owned
buffers from which a user builds them.
-/
/- LEAN: Rust's `multiple.rs`. Its match cases hold patterns, and `nodes.rs` holds multiple
values; Lean's modules cannot import each other, so the match cases are in the module
`BSmtLib.Multiple.MatchCases`, which imports `BSmtLib.Nodes`.

Each container is a structure of one array, which the compiler represents as the array itself,
so handing one over costs nothing. Lean values are immutable: Rust's in-place access (`get_mut`,
`iter_mut`, `as_mut_slice`, `IndexMut`) has no counterpart, and a handler that wants to change a
value builds a new one. A `for` loop over a container (`ForIn`) is Rust's `iter` and its
`IntoIterator`, by reference and by value alike; `GetElem` is `Index`; `Repr` is `Debug`; an
`Inhabited` instance of a buffer is its `Default`. A buffer's methods that change it in Rust return
the changed buffer, as `BytesBuf`'s do. -/

namespace BSmtLib

open BSmtLib.Plain (SymbolBuf Symbol NumeralBuf Numeral)

/--
Multiple values to be handled.

The values can be inspected, and a `for` loop goes through them in order.
-/
/- LEAN: Rust's `SmtMultiple`, a mutable borrow of the parser's stack; here the values
themselves. -/
structure Multiple (α : Type) where
  private mk ::
  /-- The values, in order. -/
  asSlice : Array α

namespace Multiple

/-- The values. -/
/- LEAN: Rust's `SmtMultiple::new`, which borrows a stack of values. -/
@[inline]
def new {α : Type} (asSlice : Array α) : Multiple α := ⟨asSlice⟩

@[simp]
theorem asSlice_new {α : Type} (asSlice : Array α) : (new asSlice).asSlice = asSlice :=
  (rfl)

variable {α : Type}

@[inline]
def len (self : Multiple α) : Nat := self.asSlice.size

@[inline]
def isEmpty (self : Multiple α) : Bool := self.asSlice.isEmpty

@[simp]
theorem len_new (asSlice : Array α) : (new asSlice).len = asSlice.size :=
  (rfl)

theorem size_asSlice (self : Multiple α) : self.asSlice.size = self.len :=
  (rfl)

/-- The values of an array that is not empty are at least one. -/
theorem len_pos_new {asSlice : Array α} (h : ¬asSlice.isEmpty) : 0 < (new asSlice).len :=
  Nat.pos_of_ne_zero fun hz => h (Array.isEmpty_iff_size_eq_zero.mpr hz)

@[inline]
def get? (self : Multiple α) (index : Nat) : Option α := self.asSlice[index]?

@[no_expose] instance : GetElem (Multiple α) Nat α fun self index => index < self.len where
  getElem self index h := self.asSlice[index]'h

@[no_expose] instance {m : Type → Type} [Monad m] : ForIn m (Multiple α) α where
  forIn self init f := ForIn.forIn self.asSlice init f

@[no_expose] instance [Repr α] : Repr (Multiple α) := ⟨fun self p => reprPrec self.asSlice p⟩

/-! ## Named values -/

/--
Named values to be handled: each a symbol with a value,
such as let bindings or sorted variables.

The values can be inspected, and a `for` loop goes through them in order.
-/
structure Named (V : Type) where
  private mk ::
  /-- The names with their values, in order. -/
  toArray : Array (Symbol × V)

/-- Let bindings to be handled: the names with their terms. -/
abbrev Bindings (T : Type) := Named T

/-- Sorted variables to be handled: the names with their sorts. -/
abbrev SortedVars (S : Type) := Named S

namespace Named

/- LEAN: crate-private in Rust; the library builds the view. -/
@[inline]
def Internal.new {V : Type} (toArray : Array (Symbol × V)) : Named V := ⟨toArray⟩

@[simp]
theorem Internal.toArray_new {V : Type} (toArray : Array (Symbol × V)) :
    (Internal.new toArray : Named V).toArray = toArray :=
  (rfl)

variable {V : Type}

@[inline]
def len (self : Named V) : Nat := self.toArray.size

@[inline]
def isEmpty (self : Named V) : Bool := self.toArray.isEmpty

@[inline]
def get? (self : Named V) (index : Nat) : Option (Symbol × V) := self.toArray[index]?

@[no_expose] instance {m : Type → Type} [Monad m] : ForIn m (Named V) (Symbol × V) where
  forIn self init f := ForIn.forIn self.toArray init f

@[no_expose] instance [Repr V] : Repr (Named V) := ⟨fun self p => reprPrec self.toArray p⟩

end Named

/-- Owned named values, from which `Named` is viewed. -/
/- LEAN: each name is a view of a copy of its bytes that the buffer made, so the view needs no
copy. -/
structure NamedBuf (V : Type) where
  private ofArray ::
  private entries : Array (Symbol × V)

/-- Owned let bindings. -/
abbrev BindingsBuf (T : Type) := NamedBuf T

/-- Owned sorted variables. -/
abbrev SortedVarsBuf (S : Type) := NamedBuf S

namespace NamedBuf

variable {V : Type}

def new : NamedBuf V := ⟨#[]⟩

def push (self : NamedBuf V) (name : Symbol) (value : V) : NamedBuf V :=
  ⟨self.entries.push (name.intoOwned.view, value)⟩

def clear (_ : NamedBuf V) : NamedBuf V := new

def viewMut (self : NamedBuf V) : Named V := ⟨self.entries⟩

def len (self : NamedBuf V) : Nat := self.entries.size

def isEmpty (self : NamedBuf V) : Bool := self.entries.isEmpty

@[no_expose] instance : Inhabited (NamedBuf V) := ⟨new⟩

end NamedBuf

/-! ## Symbols -/

/-- Symbols to be handled, such as the parameters of a sort definition. -/
structure Symbols where
  private mk ::
  /-- The symbols, in order. -/
  toArray : Array Symbol

namespace Symbols

/- LEAN: crate-private in Rust; the library builds the view. -/
@[inline]
def Internal.new (toArray : Array Symbol) : Symbols := ⟨toArray⟩

@[simp]
theorem Internal.toArray_new (toArray : Array Symbol) :
    (Internal.new toArray : Symbols).toArray = toArray :=
  (rfl)

@[inline]
def len (self : Symbols) : Nat := self.toArray.size

@[inline]
def isEmpty (self : Symbols) : Bool := self.toArray.isEmpty

@[inline]
def get? (self : Symbols) (index : Nat) : Option Symbol := self.toArray[index]?

@[no_expose] instance {m : Type → Type} [Monad m] : ForIn m Symbols Symbol where
  forIn self init f := ForIn.forIn self.toArray init f

@[no_expose] instance : Repr Symbols := ⟨fun self p => reprPrec self.toArray p⟩

end Symbols

/-- Owned symbols, from which `Symbols` is viewed. -/
structure SymbolsBuf where
  private ofArray ::
  private entries : Array Symbol

namespace SymbolsBuf

def new : SymbolsBuf := ⟨#[]⟩

def push (self : SymbolsBuf) (name : Symbol) : SymbolsBuf :=
  ⟨self.entries.push name.intoOwned.view⟩

def clear (_ : SymbolsBuf) : SymbolsBuf := new

def view (self : SymbolsBuf) : Symbols := ⟨self.entries⟩

def len (self : SymbolsBuf) : Nat := self.entries.size

def isEmpty (self : SymbolsBuf) : Bool := self.entries.isEmpty

@[no_expose] instance : Inhabited SymbolsBuf := ⟨new⟩

end SymbolsBuf

/-! ## Sort arities -/

/-- Sort names with their arities to be handled, such as those
declared by `declare-datatypes`. -/
structure SortArities where
  private mk ::
  /-- The names with their arities, in order. -/
  toArray : Array (Symbol × Numeral)

namespace SortArities

/- LEAN: crate-private in Rust; the library builds the view. -/
@[inline]
def Internal.new (toArray : Array (Symbol × Numeral)) : SortArities := ⟨toArray⟩

@[simp]
theorem Internal.toArray_new (toArray : Array (Symbol × Numeral)) :
    (Internal.new toArray : SortArities).toArray = toArray :=
  (rfl)

@[inline]
def len (self : SortArities) : Nat := self.toArray.size

@[inline]
def isEmpty (self : SortArities) : Bool := self.toArray.isEmpty

@[inline]
def get? (self : SortArities) (index : Nat) : Option (Symbol × Numeral) :=
  self.toArray[index]?

@[no_expose] instance {m : Type → Type} [Monad m] : ForIn m SortArities (Symbol × Numeral) where
  forIn self init f := ForIn.forIn self.toArray init f

@[no_expose] instance : Repr SortArities := ⟨fun self p => reprPrec self.toArray p⟩

end SortArities

/-- Owned sort names with their arities, from which `SortArities` is viewed. -/
structure SortAritiesBuf where
  private ofArray ::
  private entries : Array (Symbol × Numeral)

namespace SortAritiesBuf

def new : SortAritiesBuf := ⟨#[]⟩

def push (self : SortAritiesBuf) (name : Symbol) (arity : Numeral) : SortAritiesBuf :=
  ⟨self.entries.push (name.intoOwned.view, arity.intoOwned.view)⟩

def clear (_ : SortAritiesBuf) : SortAritiesBuf := new

def view (self : SortAritiesBuf) : SortArities := ⟨self.entries⟩

def len (self : SortAritiesBuf) : Nat := self.entries.size

def isEmpty (self : SortAritiesBuf) : Bool := self.entries.isEmpty

@[no_expose] instance : Inhabited SortAritiesBuf := ⟨new⟩

end SortAritiesBuf

/-! ## Datatype constructors -/

/--
Datatype constructors to be handled: each a name with its selectors,
the selectors as sorted variables.

A `for` loop hands over each constructor with its selectors.
-/
structure Constructors (S : Type) where
  private mk ::
  /-- The constructors with their selectors, in order. -/
  toArray : Array (Symbol × SortedVars S)

namespace Constructors

/- LEAN: crate-private in Rust; the library builds the view. -/
@[inline]
def Internal.new {S : Type} (toArray : Array (Symbol × SortedVars S)) :
    Constructors S :=
  ⟨toArray⟩

@[simp]
theorem Internal.toArray_new {S : Type} (toArray : Array (Symbol × SortedVars S)) :
    (Internal.new toArray : Constructors S).toArray = toArray :=
  (rfl)

variable {S : Type}

@[inline]
def len (self : Constructors S) : Nat := self.toArray.size

@[inline]
def isEmpty (self : Constructors S) : Bool := self.toArray.isEmpty

@[no_expose] instance {m : Type → Type} [Monad m] :
    ForIn m (Constructors S) (Symbol × SortedVars S) where
  forIn self init f := ForIn.forIn self.toArray init f

@[no_expose] instance [Repr S] : Repr (Constructors S) :=
  ⟨fun self p => reprPrec self.toArray p⟩

end Constructors

/-- Owned datatype constructors, from which `Constructors` is viewed. -/
structure ConstructorsBuf (S : Type) where
  private ofArray ::
  private entries : Array (Symbol × SortedVars S)

namespace ConstructorsBuf

variable {S : Type}

def new : ConstructorsBuf S := ⟨#[]⟩

/-- Starts a constructor with no selectors; `pushSelector` adds them. -/
def push (self : ConstructorsBuf S) (name : Symbol) : ConstructorsBuf S :=
  ⟨self.entries.push (name.intoOwned.view, ⟨#[]⟩)⟩

def len (self : ConstructorsBuf S) : Nat := self.entries.size

def isEmpty (self : ConstructorsBuf S) : Bool := self.entries.isEmpty

/-- Adds a selector to the last constructor pushed. -/
/- LEAN: Rust panics when no constructor was pushed; here the caller proves that one was. -/
def pushSelector (self : ConstructorsBuf S) (name : Symbol) (sort : S) (_ : 0 < self.len) :
    ConstructorsBuf S :=
  ⟨self.entries.modify (self.entries.size - 1) fun (constructor, selectors) =>
    (constructor, ⟨selectors.toArray.push (name.intoOwned.view, sort)⟩)⟩

def clear (_ : ConstructorsBuf S) : ConstructorsBuf S := new

def viewMut (self : ConstructorsBuf S) : Constructors S := ⟨self.entries⟩

@[no_expose] instance : Inhabited (ConstructorsBuf S) := ⟨new⟩

end ConstructorsBuf

/-! ## Function signatures -/

/--
A function signature to be handled: the name, the parameters
with their sorts, and the result sort.
-/
/- LEAN: Rust's accessors are the fields; the parameters are an array, where Rust's `params` is an
iterator. -/
structure FunctionSignature (HandledSort : Type) where
  private mk ::
  name : Symbol
  /-- The parameters with their sorts, in order. -/
  params : Array (Symbol × HandledSort)
  resultSort : HandledSort
  deriving Repr

namespace FunctionSignature

variable {HandledSort : Type}

/- LEAN: crate-private in Rust; the library builds the signatures. -/
@[inline]
def Internal.new (name : Symbol) (params : Array (Symbol × HandledSort))
    (resultSort : HandledSort) : FunctionSignature HandledSort :=
  ⟨name, params, resultSort⟩

@[simp]
theorem Internal.name_new (name : Symbol) (params : Array (Symbol × HandledSort))
    (resultSort : HandledSort) : (Internal.new name params resultSort).name = name :=
  (rfl)

@[simp]
theorem Internal.params_new (name : Symbol) (params : Array (Symbol × HandledSort))
    (resultSort : HandledSort) : (Internal.new name params resultSort).params = params :=
  (rfl)

@[simp]
theorem Internal.resultSort_new (name : Symbol) (params : Array (Symbol × HandledSort))
    (resultSort : HandledSort) : (Internal.new name params resultSort).resultSort = resultSort :=
  (rfl)

/-- A signature is the one built from its fields. -/
@[simp]
theorem Internal.new_eta (self : FunctionSignature HandledSort) :
    Internal.new self.name self.params self.resultSort = self :=
  (rfl)

end FunctionSignature

/-- Function signatures to be handled, such as those of `define-funs-rec`. -/
structure FunctionSignatures (S : Type) where
  private mk ::
  /-- The signatures, in order. -/
  toArray : Array (FunctionSignature S)

namespace FunctionSignatures

/- LEAN: crate-private in Rust; the library builds the view. -/
@[inline]
def Internal.new {S : Type} (toArray : Array (FunctionSignature S)) : FunctionSignatures S :=
  ⟨toArray⟩

@[simp]
theorem Internal.toArray_new {S : Type} (toArray : Array (FunctionSignature S)) :
    (Internal.new toArray : FunctionSignatures S).toArray = toArray :=
  (rfl)

variable {S : Type}

@[inline]
def len (self : FunctionSignatures S) : Nat := self.toArray.size

@[inline]
def isEmpty (self : FunctionSignatures S) : Bool := self.toArray.isEmpty

@[inline]
def get? (self : FunctionSignatures S) (index : Nat) : Option (FunctionSignature S) :=
  self.toArray[index]?

@[no_expose] instance {m : Type → Type} [Monad m] :
    ForIn m (FunctionSignatures S) (FunctionSignature S) where
  forIn self init f := ForIn.forIn self.toArray init f

@[no_expose] instance [Repr S] : Repr (FunctionSignatures S) :=
  ⟨fun self p => reprPrec self.toArray p⟩

end FunctionSignatures

/-- Owned function signatures, from which `FunctionSignatures`
and each `FunctionSignature` are viewed. -/
/- LEAN: each name is a view of a copy of its bytes that the buffer made, so the view needs no
copy. -/
structure FunctionSignaturesBuf (S : Type) where
  private ofArray ::
  private entries : Array (FunctionSignature S)

namespace FunctionSignaturesBuf

variable {S : Type}

def new : FunctionSignaturesBuf S := ⟨#[]⟩

/-- Starts a signature with no parameters; `pushParam` adds them. -/
def push (self : FunctionSignaturesBuf S) (name : Symbol) (resultSort : S) :
    FunctionSignaturesBuf S :=
  ⟨self.entries.push ⟨name.intoOwned.view, #[], resultSort⟩⟩

def len (self : FunctionSignaturesBuf S) : Nat := self.entries.size

def isEmpty (self : FunctionSignaturesBuf S) : Bool := self.entries.isEmpty

/-- Adds a parameter to the last signature pushed. -/
/- LEAN: Rust panics when no signature was pushed; here the caller proves that one was. -/
def pushParam (self : FunctionSignaturesBuf S) (name : Symbol) (sort : S) (_ : 0 < self.len) :
    FunctionSignaturesBuf S :=
  ⟨self.entries.modify (self.entries.size - 1) fun signature =>
    { signature with params := signature.params.push (name.intoOwned.view, sort) }⟩

def clear (_ : FunctionSignaturesBuf S) : FunctionSignaturesBuf S := new

def view (self : FunctionSignaturesBuf S) : FunctionSignatures S :=
  FunctionSignatures.Internal.new self.entries

def get? (self : FunctionSignaturesBuf S) (index : Nat) : Option (FunctionSignature S) :=
  self.entries[index]?

@[no_expose] instance : Inhabited (FunctionSignaturesBuf S) := ⟨new⟩

end FunctionSignaturesBuf

/-! ## Tokens of the values -/

section AppendTokens

open BSmtLib.Token (AppendTokens SyntaxToken TokensCursor)

/-- Appends the values in order, without enclosing parentheses. -/
@[no_expose] instance {α : Type} [AppendTokens α] : AppendTokens (Multiple α) :=
  ⟨fun self tokens => AppendTokens.appendTokens self.asSlice tokens⟩

/-- Appends each named value as ( name value ). -/
private def appendNamed {V : Type} [AppendTokens V] (named : Array (Symbol × V))
    (tokens : TokensCursor) : TokensCursor :=
  named.foldl (init := tokens) fun tokens (name, value) =>
    let tokens := tokens.push .parenOpen
    let tokens := tokens.push (.symbol name)
    let tokens := AppendTokens.appendTokens value tokens
    tokens.push .parenClose

/-- Appends each name with its value as `(name value)`, in order, without enclosing
parentheses. -/
@[no_expose] instance {V : Type} [AppendTokens V] : AppendTokens (Named V) :=
  ⟨fun self tokens => appendNamed self.toArray tokens⟩

/-- Appends each name with its value as `(name value)`, in order, without enclosing
parentheses. -/
@[no_expose] instance {V : Type} [AppendTokens V] : AppendTokens (NamedBuf V) :=
  ⟨fun self tokens => appendNamed self.viewMut.toArray tokens⟩

end AppendTokens

end Multiple

end BSmtLib
