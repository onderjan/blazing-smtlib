module

public import BSmtLib.Lexicon.Value

public section

/- LEAN: Rust's module `version`, whose items `lib.rs` re-exports at the root. `SmtVersion` is
named like the module, so it is the module's own name, `BSmtLib.Version`, and the posture and its
builder are in its namespace. -/

namespace BSmtLib

/--
Version of the SMT-LIB standard (2.0, 2.5, 2.6, or 2.7).

A script declares the version it is written in with an attribute, e.g.
`(set-info :smt-lib-version 2.6)`.

A version decides which words are reserved and which syntax is accepted, e.g. `lambda` and
the wildcard `_` from 2.7 on, and `match` and `declare-datatype` from 2.6 on. Under an earlier
version, the name of a later command is a symbol, so the command is nonstandard.

The default version is SMT-LIB 2.7.
-/
inductive Version where
  /-- Version 2.0. -/
  | v2_0
  /-- Version 2.5. -/
  | v2_5
  /-- Version 2.6. -/
  | v2_6
  /-- Version 2.7. -/
  | v2_7
  deriving BEq, Hashable, Repr

namespace Version

/- LEAN: `Inhabited` gives the default value, the Rust `#[default]`. -/
instance : Inhabited Version := ⟨.v2_7⟩

/- LEAN: Lean cannot derive `PartialOrd`/`Ord` for comparison with `≤` from the order of the
variants, so the order is spelled out as a rank, and `≤` and `<` compare the ranks. The rank is
public, in `Internal`, so that the bodies of these instances, which importing modules see, can
name it, and so that the fused reader can compare versions by it. It is inlined, so that a
comparison compiles to the comparison of the ranks in place, without calls. -/
/-- The position of the version in the order of releases. -/
@[expose, inline] def Internal.rank : Version → Nat
  | .v2_0 => 0
  | .v2_5 => 1
  | .v2_6 => 2
  | .v2_7 => 3

instance : LE Version := ⟨fun a b => Internal.rank a ≤ Internal.rank b⟩

instance : LT Version := ⟨fun a b => Internal.rank a < Internal.rank b⟩

/- LEAN: in Lean, `a ≤ b` is a proposition, not a boolean. To use it in an `if`, Lean
needs a `Decidable` instance that computes its truth; these reuse the one of `Nat`. -/
instance (a b : Version) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (Internal.rank a ≤ Internal.rank b))

instance (a b : Version) : Decidable (a < b) :=
  inferInstanceAs (Decidable (Internal.rank a < Internal.rank b))

/- LEAN: Rust's derived `Ord`, in the order of the variants, which is that of the ranks; `compare`
agrees with `≤` and `<` as it compares the ranks too. -/
instance : Ord Version := ⟨fun a b => compare (Internal.rank a) (Internal.rank b)⟩

/-- Returns the version that the decimal names, if any. -/
def fromDecimal? (decimal : Lexicon.Value.Decimal) : Option Version :=
  let decimal := decimal.asSlice
  if decimal == "2.0".toUTF8.toByteSlice then some .v2_0
  else if decimal == "2.5".toUTF8.toByteSlice then some .v2_5
  else if decimal == "2.6".toUTF8.toByteSlice then some .v2_6
  else if decimal == "2.7".toUTF8.toByteSlice then some .v2_7
  else none

/-- Returns the decimal that names the version, as in `:smt-lib-version`. -/
def asDecimal (self : Version) : Lexicon.Value.Decimal :=
  let decimal : String := match self with
    | .v2_0 => "2.0"
    | .v2_5 => "2.5"
    | .v2_6 => "2.6"
    | .v2_7 => "2.7"
  Lexicon.Value.Decimal.Internal.newUnchecked decimal.toUTF8.toByteSlice

/- LEAN: Rust's fields are private and read through the getters `allowed()` and
`max_declarations()`. Here the constructor is private, so a posture is made only by
`VersionPostureBuilder.build`, and the fields are read-only: their projections are the getters. -/
/--
Version posture (versions a script may declare and how many declarations it may make).

The posture applies to version declarations `(set-info :smt-lib-version …)` only; the initial
version is unaffected by the posture.
-/
structure VersionPosture where
  private mk ::
  /-- Returns the allowed versions. -/
  allowed : Array Version
  /-- Returns the maximum number of version declarations, or `none` if unlimited. -/
  maxDeclarations : Option Nat
  deriving BEq, Repr

/- LEAN: the builder methods take the builder and return it updated, as Rust's take it by value
and return it, so that the calls chain the same way:
`(VersionPostureBuilder.new.clearAllowed.addAllowed .v2_6).build`. The fields are read as in
`VersionPosture`. -/
/-- Builds a version posture. -/
structure VersionPostureBuilder where
  private mk ::
  /-- Returns the allowed versions. -/
  allowed : Array Version
  /-- Returns the maximum number of version declarations, or `none` if unlimited. -/
  maxDeclarations : Option Nat
  deriving BEq, Repr

namespace VersionPostureBuilder

/-- Creates a builder with the default posture (`VersionPosture.default`). -/
def new : VersionPostureBuilder :=
  { allowed := #[.v2_5, .v2_6, .v2_7], maxDeclarations := some 1 }

/-- Disallows every version. -/
def clearAllowed (self : VersionPostureBuilder) : VersionPostureBuilder :=
  { self with allowed := #[] }

/-- Allows the version. -/
def addAllowed (self : VersionPostureBuilder) (allowed : Version) : VersionPostureBuilder :=
  { self with allowed := self.allowed.push allowed }

/-- Disallows the version. -/
def removeAllowed (self : VersionPostureBuilder) (allowed : Version) : VersionPostureBuilder :=
  { self with allowed := self.allowed.filter (· != allowed) }

/-- Sets the maximum number of version declarations (`none` for unlimited). -/
def setMaxDeclarations (self : VersionPostureBuilder) (maxDeclarations : Option Nat) :
    VersionPostureBuilder :=
  { self with maxDeclarations }

/-- Builds the version posture. -/
def build (self : VersionPostureBuilder) : VersionPosture :=
  { allowed := self.allowed, maxDeclarations := self.maxDeclarations }

/- LEAN: not in Rust. The methods' definitions are private to this module, as the constructor
is; these state what they do, for proofs elsewhere. -/

@[simp] theorem allowed_new : new.allowed = #[.v2_5, .v2_6, .v2_7] := (rfl)

@[simp] theorem maxDeclarations_new : new.maxDeclarations = some 1 := (rfl)

@[simp] theorem allowed_clearAllowed (self : VersionPostureBuilder) :
    self.clearAllowed.allowed = #[] := (rfl)

@[simp] theorem maxDeclarations_clearAllowed (self : VersionPostureBuilder) :
    self.clearAllowed.maxDeclarations = self.maxDeclarations := (rfl)

@[simp] theorem allowed_addAllowed (self : VersionPostureBuilder) (allowed : Version) :
    (self.addAllowed allowed).allowed = self.allowed.push allowed := (rfl)

@[simp] theorem maxDeclarations_addAllowed (self : VersionPostureBuilder) (allowed : Version) :
    (self.addAllowed allowed).maxDeclarations = self.maxDeclarations := (rfl)

@[simp] theorem allowed_removeAllowed (self : VersionPostureBuilder) (allowed : Version) :
    (self.removeAllowed allowed).allowed = self.allowed.filter (· != allowed) := (rfl)

@[simp] theorem maxDeclarations_removeAllowed (self : VersionPostureBuilder) (allowed : Version) :
    (self.removeAllowed allowed).maxDeclarations = self.maxDeclarations := (rfl)

@[simp] theorem allowed_setMaxDeclarations (self : VersionPostureBuilder)
    (maxDeclarations : Option Nat) :
    (self.setMaxDeclarations maxDeclarations).allowed = self.allowed := (rfl)

@[simp] theorem maxDeclarations_setMaxDeclarations (self : VersionPostureBuilder)
    (maxDeclarations : Option Nat) :
    (self.setMaxDeclarations maxDeclarations).maxDeclarations = maxDeclarations := (rfl)

@[simp] theorem allowed_build (self : VersionPostureBuilder) :
    self.build.allowed = self.allowed := (rfl)

@[simp] theorem maxDeclarations_build (self : VersionPostureBuilder) :
    self.build.maxDeclarations = self.maxDeclarations := (rfl)

end VersionPostureBuilder

/- LEAN: `Inhabited` gives the default value, Rust's `Default`. -/
instance : Inhabited VersionPostureBuilder := ⟨.new⟩

/--
Returns the default posture.

The default posture allows versions 2.5, 2.6 and 2.7, and at most one version declaration.
-/
def VersionPosture.default : VersionPosture :=
  VersionPostureBuilder.new.build

/- LEAN: `Inhabited` gives the default value, Rust's `Default`. -/
instance : Inhabited VersionPosture := ⟨VersionPosture.default⟩

end Version

end BSmtLib
