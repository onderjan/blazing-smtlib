module

public import BSmtLib.Plain

public section

/-!
# Multiple values to be handled

The containers in which the parser hands several values over at once: the values of a list, the
names with their values, the symbols, and the parts of the datatype commands, with the owned
buffers from which a user builds them.
-/

/- LEAN: Rust's `multiple.rs`. Its match cases and function signatures hold nodes, and `nodes.rs`
holds multiple values; Lean's modules cannot import each other, so those two are in the modules
`BSmtLib.Multiple.MatchCases` and `BSmtLib.Multiple.FunctionSignatures` (with
`BSmtLib.Multiple.FunctionSignaturesView`), which import `BSmtLib.Nodes`.

Each container is a structure of one array, which the compiler represents as the array itself,
so handing one over costs nothing. Lean values are immutable: Rust's in-place access (`get_mut`,
`iter_mut`, `as_mut_slice`, `IndexMut`) has no counterpart, and a handler that wants to change a
value builds a new one. A `for` loop over a container (`ForIn`) is Rust's `iter` and its
`IntoIterator`, by reference and by value alike; `GetElem` is `Index`; `Repr` is `Debug`; an
`Inhabited` instance of a buffer is its `Default`. A buffer's methods that change it in Rust return
the changed buffer, as `Bytes`'s do. -/

namespace BSmtLib

open BSmtLib.Plain (Symbol SymbolView Numeral NumeralView)

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
/- LEAN: Rust's `SmtNamed`, the view of `SmtNamedBuf`; the counterpart rule names a view whose
owned type exists with the suffix `View`. -/
structure NamedView (V : Type) where
  private mk ::
  /-- The names with their values, in order. -/
  toArray : Array (SymbolView × V)

/-- Let bindings to be handled: the names with their terms. -/
abbrev BindingsView (T : Type) := NamedView T

/-- Sorted variables to be handled: the names with their sorts. -/
abbrev SortedVarsView (S : Type) := NamedView S

namespace NamedView

/- LEAN: crate-private in Rust; the library builds the view. -/
@[inline]
def Internal.new {V : Type} (toArray : Array (SymbolView × V)) : NamedView V := ⟨toArray⟩

@[simp]
theorem Internal.toArray_new {V : Type} (toArray : Array (SymbolView × V)) :
    (Internal.new toArray : NamedView V).toArray = toArray :=
  (rfl)

variable {V : Type}

@[inline]
def len (self : NamedView V) : Nat := self.toArray.size

@[inline]
def isEmpty (self : NamedView V) : Bool := self.toArray.isEmpty

@[inline]
def get? (self : NamedView V) (index : Nat) : Option (SymbolView × V) := self.toArray[index]?

@[no_expose] instance {m : Type → Type} [Monad m] : ForIn m (NamedView V) (SymbolView × V) where
  forIn self init f := ForIn.forIn self.toArray init f

@[no_expose] instance [Repr V] : Repr (NamedView V) := ⟨fun self p => reprPrec self.toArray p⟩

end NamedView

/-- Owned named values, from which `NamedView` is viewed. -/
/- LEAN: Rust's `SmtNamedBuf`, named without `Buf` as the counterpart rule names owned types.
Each name is a view of a copy of its bytes that the buffer made, so the view needs no copy. -/
structure Named (V : Type) where
  private ofArray ::
  private entries : Array (SymbolView × V)

/-- Owned let bindings. -/
abbrev Bindings (T : Type) := Named T

/-- Owned sorted variables. -/
abbrev SortedVars (S : Type) := Named S

namespace Named

variable {V : Type}

def new : Named V := ⟨#[]⟩

def push (self : Named V) (name : SymbolView) (value : V) : Named V :=
  ⟨self.entries.push (name.intoOwned.asView, value)⟩

def clear (_ : Named V) : Named V := new

def view (self : Named V) : NamedView V := ⟨self.entries⟩

def len (self : Named V) : Nat := self.entries.size

def isEmpty (self : Named V) : Bool := self.entries.isEmpty

@[no_expose] instance : Inhabited (Named V) := ⟨new⟩

end Named

/-! ## Symbols -/

/-- Symbols to be handled, such as the parameters of a sort definition. -/
/- LEAN: Rust's `SmtSymbols`, the view of `SmtSymbolsBuf`, named by the counterpart rule. -/
structure SymbolsView where
  private mk ::
  /-- The symbols, in order. -/
  toArray : Array SymbolView

namespace SymbolsView

/- LEAN: crate-private in Rust; the library builds the view. -/
@[inline]
def Internal.new (toArray : Array SymbolView) : SymbolsView := ⟨toArray⟩

@[simp]
theorem Internal.toArray_new (toArray : Array SymbolView) :
    (Internal.new toArray : SymbolsView).toArray = toArray :=
  (rfl)

@[inline]
def len (self : SymbolsView) : Nat := self.toArray.size

@[inline]
def isEmpty (self : SymbolsView) : Bool := self.toArray.isEmpty

@[inline]
def get? (self : SymbolsView) (index : Nat) : Option SymbolView := self.toArray[index]?

@[no_expose] instance {m : Type → Type} [Monad m] : ForIn m SymbolsView SymbolView where
  forIn self init f := ForIn.forIn self.toArray init f

@[no_expose] instance : Repr SymbolsView := ⟨fun self p => reprPrec self.toArray p⟩

end SymbolsView

/-- Owned symbols, from which `SymbolsView` is viewed. -/
/- LEAN: Rust's `SmtSymbolsBuf`, named by the counterpart rule. -/
structure Symbols where
  private ofArray ::
  private entries : Array SymbolView

namespace Symbols

def new : Symbols := ⟨#[]⟩

def push (self : Symbols) (name : SymbolView) : Symbols :=
  ⟨self.entries.push name.intoOwned.asView⟩

def clear (_ : Symbols) : Symbols := new

def view (self : Symbols) : SymbolsView := ⟨self.entries⟩

def len (self : Symbols) : Nat := self.entries.size

def isEmpty (self : Symbols) : Bool := self.entries.isEmpty

@[no_expose] instance : Inhabited Symbols := ⟨new⟩

end Symbols

/-! ## Sort arities -/

/-- Sort names with their arities to be handled, such as those
declared by `declare-datatypes`. -/
/- LEAN: Rust's `SmtSortArities`, the view of `SmtSortAritiesBuf`, named by the counterpart
rule. -/
structure SortAritiesView where
  private mk ::
  /-- The names with their arities, in order. -/
  toArray : Array (SymbolView × NumeralView)

namespace SortAritiesView

/- LEAN: crate-private in Rust; the library builds the view. -/
@[inline]
def Internal.new (toArray : Array (SymbolView × NumeralView)) : SortAritiesView := ⟨toArray⟩

@[simp]
theorem Internal.toArray_new (toArray : Array (SymbolView × NumeralView)) :
    (Internal.new toArray : SortAritiesView).toArray = toArray :=
  (rfl)

@[inline]
def len (self : SortAritiesView) : Nat := self.toArray.size

@[inline]
def isEmpty (self : SortAritiesView) : Bool := self.toArray.isEmpty

@[inline]
def get? (self : SortAritiesView) (index : Nat) : Option (SymbolView × NumeralView) :=
  self.toArray[index]?

@[no_expose] instance {m : Type → Type} [Monad m] : ForIn m SortAritiesView (SymbolView × NumeralView) where
  forIn self init f := ForIn.forIn self.toArray init f

@[no_expose] instance : Repr SortAritiesView := ⟨fun self p => reprPrec self.toArray p⟩

end SortAritiesView

/-- Owned sort names with their arities, from which `SortAritiesView` is viewed. -/
/- LEAN: Rust's `SmtSortAritiesBuf`, named by the counterpart rule. -/
structure SortArities where
  private ofArray ::
  private entries : Array (SymbolView × NumeralView)

namespace SortArities

def new : SortArities := ⟨#[]⟩

def push (self : SortArities) (name : SymbolView) (arity : NumeralView) : SortArities :=
  ⟨self.entries.push (name.intoOwned.asView, arity.intoOwned.asView)⟩

def clear (_ : SortArities) : SortArities := new

def view (self : SortArities) : SortAritiesView := ⟨self.entries⟩

def len (self : SortArities) : Nat := self.entries.size

def isEmpty (self : SortArities) : Bool := self.entries.isEmpty

@[no_expose] instance : Inhabited SortArities := ⟨new⟩

end SortArities

/-! ## Datatype constructors -/

/--
Datatype constructors to be handled: each a name with its selectors,
the selectors as sorted variables.

A `for` loop hands over each constructor with its selectors.
-/
/- LEAN: Rust's `SmtConstructors`, the view of `SmtConstructorsBuf`, named by the counterpart
rule. -/
structure ConstructorsView (S : Type) where
  private mk ::
  /-- The constructors with their selectors, in order. -/
  toArray : Array (SymbolView × SortedVarsView S)

namespace ConstructorsView

/- LEAN: crate-private in Rust; the library builds the view. -/
@[inline]
def Internal.new {S : Type} (toArray : Array (SymbolView × SortedVarsView S)) :
    ConstructorsView S :=
  ⟨toArray⟩

@[simp]
theorem Internal.toArray_new {S : Type} (toArray : Array (SymbolView × SortedVarsView S)) :
    (Internal.new toArray : ConstructorsView S).toArray = toArray :=
  (rfl)

variable {S : Type}

@[inline]
def len (self : ConstructorsView S) : Nat := self.toArray.size

@[inline]
def isEmpty (self : ConstructorsView S) : Bool := self.toArray.isEmpty

@[no_expose] instance {m : Type → Type} [Monad m] :
    ForIn m (ConstructorsView S) (SymbolView × SortedVarsView S) where
  forIn self init f := ForIn.forIn self.toArray init f

@[no_expose] instance [Repr S] : Repr (ConstructorsView S) :=
  ⟨fun self p => reprPrec self.toArray p⟩

end ConstructorsView

/-- Owned datatype constructors, from which `ConstructorsView` is viewed. -/
/- LEAN: Rust's `SmtConstructorsBuf`, named by the counterpart rule. -/
structure Constructors (S : Type) where
  private ofArray ::
  private entries : Array (SymbolView × SortedVarsView S)

namespace Constructors

variable {S : Type}

def new : Constructors S := ⟨#[]⟩

/-- Starts a constructor with no selectors; `pushSelector` adds them. -/
def push (self : Constructors S) (name : SymbolView) : Constructors S :=
  ⟨self.entries.push (name.intoOwned.asView, ⟨#[]⟩)⟩

def len (self : Constructors S) : Nat := self.entries.size

def isEmpty (self : Constructors S) : Bool := self.entries.isEmpty

/-- Adds a selector to the last constructor pushed. -/
/- LEAN: Rust panics when no constructor was pushed; here the caller proves that one was. -/
def pushSelector (self : Constructors S) (name : SymbolView) (sort : S) (_ : 0 < self.len) :
    Constructors S :=
  ⟨self.entries.modify (self.entries.size - 1) fun (constructor, selectors) =>
    (constructor, ⟨selectors.toArray.push (name.intoOwned.asView, sort)⟩)⟩

def clear (_ : Constructors S) : Constructors S := new

def view (self : Constructors S) : ConstructorsView S := ⟨self.entries⟩

@[no_expose] instance : Inhabited (Constructors S) := ⟨new⟩

end Constructors

end Multiple

end BSmtLib
