module

public import Std.Data.ByteSlice
public import BSmtLib.ControlFlow
public import BSmtLib.Span
public import BSmtLib.Plain

public section

/- LEAN: the public items of the Rust crate are in the namespace `BSmtLib`, without the prefix
`Smt`: `SmtToken` is `BSmtLib.Token`. The internals of the lexer are in `BSmtLib.Lexer`.
Variant and function names follow Lean conventions (`TokenCategory.parenOpen` for
`SmtTokenCategory::ParenOpen`, `lastConsumed` for `last_consumed`). An `inductive` without
fields is a Rust enum. -/
namespace BSmtLib.Token

inductive TokenCategory where
  | parenOpen
  | parenClose
  | numeral
  | decimal
  | hexadecimal
  | binary
  | string
  | keyword
  | unquotedSymbol
  | quotedSymbol
  | whitespace
  | comment
  | endOfFile
  deriving BEq, Hashable, Repr, Inhabited

/-- Version of the SMT-LIB standard. -/
inductive Version where
  | v2_0
  | v2_5
  | v2_6
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

/-- The version that the decimal names, if any. -/
def fromDecimal? (decimal : ByteSlice) : Option Version :=
  if decimal == "2.0".toUTF8.toByteSlice then some .v2_0
  else if decimal == "2.5".toUTF8.toByteSlice then some .v2_5
  else if decimal == "2.6".toUTF8.toByteSlice then some .v2_6
  else if decimal == "2.7".toUTF8.toByteSlice then some .v2_7
  else none

/-- The decimal that names the version, as in `:smt-lib-version`. -/
def asDecimal (self : Version) : Plain.Decimal :=
  let decimal : String := match self with
    | .v2_0 => "2.0"
    | .v2_5 => "2.5"
    | .v2_6 => "2.6"
    | .v2_7 => "2.7"
  Plain.Decimal.Internal.newUnchecked decimal.toUTF8.toByteSlice

end Version

/--
Which versions a script may declare, and how many declarations it may make, without a limit if
there is none (`SmtVersionPosture`).
-/
/- LEAN: Rust's fields are private and read through the getters `allowed()` and
`max_declarations()`. Here the constructor is private, so a posture is made only by
`VersionPostureBuilder.build`, and the fields are read-only: their projections are the getters. -/
structure VersionPosture where
  private mk ::
  allowed : Array Version
  maxDeclarations : Option Nat
  deriving BEq, Repr

/--
A builder of a `VersionPosture` (`SmtVersionPostureBuilder`). It starts with 2.5, 2.6 and 2.7
allowed and one declaration.
-/
/- LEAN: Rust's builder methods take `&mut self` and return it; these take the builder and
return it updated, so that the calls chain the same way:
`(VersionPostureBuilder.new.clearAllowed.addAllowed .v2_6).build`. The fields are read as in
`VersionPosture`. -/
structure VersionPostureBuilder where
  private mk ::
  allowed : Array Version
  maxDeclarations : Option Nat
  deriving BEq, Repr

namespace VersionPostureBuilder

def new : VersionPostureBuilder :=
  { allowed := #[.v2_5, .v2_6, .v2_7], maxDeclarations := some 1 }

def clearAllowed (self : VersionPostureBuilder) : VersionPostureBuilder :=
  { self with allowed := #[] }

def addAllowed (self : VersionPostureBuilder) (allowed : Version) : VersionPostureBuilder :=
  { self with allowed := self.allowed.push allowed }

def removeAllowed (self : VersionPostureBuilder) (allowed : Version) : VersionPostureBuilder :=
  { self with allowed := self.allowed.filter (· != allowed) }

def setMaxDeclarations (self : VersionPostureBuilder) (maxDeclarations : Option Nat) :
    VersionPostureBuilder :=
  { self with maxDeclarations }

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

/-- The default posture: 2.5, 2.6 and 2.7, one declaration. -/
def VersionPosture.default : VersionPosture :=
  VersionPostureBuilder.new.build

/- LEAN: `Inhabited` gives the default value, Rust's `Default`. -/
instance : Inhabited VersionPosture := ⟨VersionPosture.default⟩

namespace TokenCategory

namespace Internal

/- LEAN: the batch keeps the types in a byte array, as numbers. -/
/-- The number of the type, in the order of declaration. -/
@[inline]
def toUInt8 : TokenCategory → UInt8
  | .parenOpen => 0
  | .parenClose => 1
  | .numeral => 2
  | .decimal => 3
  | .hexadecimal => 4
  | .binary => 5
  | .string => 6
  | .keyword => 7
  | .unquotedSymbol => 8
  | .quotedSymbol => 9
  | .whitespace => 10
  | .comment => 11
  | .endOfFile => 12

/-- The type of the number given by `toUInt8`. -/
@[inline]
def ofUInt8 : UInt8 → TokenCategory
  | 0 => .parenOpen
  | 1 => .parenClose
  | 2 => .numeral
  | 3 => .decimal
  | 4 => .hexadecimal
  | 5 => .binary
  | 6 => .string
  | 7 => .keyword
  | 8 => .unquotedSymbol
  | 9 => .quotedSymbol
  | 10 => .whitespace
  | 11 => .comment
  | _ => .endOfFile

/- LEAN: that the types are read back from the batch as they were written to it is a `#guard`
in `BSmtLib.Facts.Asserts`, checked when the facts are built. -/

end Internal

end TokenCategory

/- The storage of the lexer's batches. It is public, in `Internal`, only so that the lexer and
the proofs can write and read it; it is not a part of the library's interface. -/
namespace Internal

/--
Whether the first `len` tokens, given by their types and the offsets where they start and
end, are in input order from the offset `origin` on: each token starts at or after the end of
the token before it, the first one at or after `origin`, and each token ends after it starts,
except the end of file, which is empty. The arrays hold an entry for each of the tokens.
-/
@[expose]
def TokensInOrder (origin len : Nat) (types : ByteArray) (starts ends : Array Nat) : Prop :=
  ∃ (_ : len ≤ types.size) (_ : len ≤ starts.size) (_ : len ≤ ends.size),
    ∀ i (_ : i < len),
      (if h : i = 0 then origin else ends[i - 1]) ≤ starts[i] ∧
        (starts[i] < ends[i] ∨
          types[i] = (TokenCategory.Internal.toUInt8 TokenCategory.endOfFile) ∧ starts[i] = ends[i])

/-- `TokensInOrder` with the reads unchecked: the form the proofs about the batch use. -/
theorem tokensInOrder_iff {origin len : Nat} {types : ByteArray} {starts ends : Array Nat} :
    TokensInOrder origin len types starts ends ↔
      len ≤ types.size ∧ len ≤ starts.size ∧ len ≤ ends.size ∧
        ∀ i, i < len →
          (if i = 0 then origin else ends[i - 1]!) ≤ starts[i]! ∧
            (starts[i]! < ends[i]! ∨
              types.get! i = (TokenCategory.Internal.toUInt8 TokenCategory.endOfFile) ∧ starts[i]!
                  = ends[i]!) := by
  have hb : ∀ {i : Nat} (h : i < types.size), types.get! i = types[i] := fun h => by
    obtain ⟨data⟩ := types
    exact getElem!_pos data _ h
  constructor
  · rintro ⟨ht, hs, he, hall⟩
    refine ⟨ht, hs, he, fun i hi => ?_⟩
    obtain ⟨h1, h2⟩ := hall i hi
    rw [getElem!_pos starts i (by omega), getElem!_pos ends i (by omega), hb (by omega)]
    refine ⟨?_, h2⟩
    by_cases z : i = 0
    · simpa [z] using h1
    · simp only [z, ↓reduceIte, ↓reduceDIte] at h1 ⊢
      rw [getElem!_pos ends (i - 1) (by omega)]
      exact h1
  · rintro ⟨ht, hs, he, hall⟩
    refine ⟨ht, hs, he, fun i hi => ?_⟩
    obtain ⟨h1, h2⟩ := hall i hi
    rw [getElem!_pos starts i (by omega), getElem!_pos ends i (by omega), hb (by omega)] at h2
    rw [getElem!_pos starts i (by omega)] at h1
    refine ⟨?_, h2⟩
    by_cases z : i = 0
    · simpa [z] using h1
    · simp only [z, ↓reduceIte, ↓reduceDIte] at h1 ⊢
      rw [getElem!_pos ends (i - 1) (by omega)] at h1
      exact h1

/--
Whether the arrays of the fields that `TokensInOrder` does not cover hold an entry for each of
the first `len` tokens.
-/
@[expose]
def EntriesFit (len : Nat) (contentStarts contentStops startLines startColumns endLines endColumns :
    Array Nat) : Prop :=
  len ≤ contentStarts.size ∧ len ≤ contentStops.size ∧ len ≤ startLines.size ∧
    len ≤ startColumns.size ∧ len ≤ endLines.size ∧ len ≤ endColumns.size

/- LEAN: what the Rust lexer keeps in its batch arrays. Each field is an array with one entry
per token; entries from `len` on are left over from earlier batches and are overwritten. The
contents of all tokens of a batch are in the one array `bytes`: either the input slice the
batch was lexed from, or the lexer's content buffer for a batch of one token. The fields are
public, as the lexer, which is another module, writes them.

Not in Rust: `origin` and `ordered`, the proof that the tokens are in input order, and `fit`,
the proof that every array has an entry for each token, so that a token is read without a
bounds check. Whoever pushes a token proves that it starts at or after the end of the last one
(`lastEnd`) and has a byte; the proofs cost nothing when the lexer runs. -/
/-- The tokens of a batch, field by field. -/
structure TokenBatch where
  /-- The number of tokens in the batch. -/
  len : Nat
  /-- The array of the tokens' contents. -/
  bytes : ByteArray
  /-- The types of the tokens, as `TokenCategory.Internal.toUInt8`. -/
  types : ByteArray
  contentStarts : Array Nat
  contentStops : Array Nat
  startOffsets : Array Nat
  startLines : Array Nat
  startColumns : Array Nat
  endOffsets : Array Nat
  endLines : Array Nat
  endColumns : Array Nat
  /-- The offset at or after which the first token starts. -/
  origin : Nat
  /-- The tokens are in input order from `origin` on, and each but the end of file has a byte. -/
  ordered : TokensInOrder origin len types startOffsets endOffsets
  /-- The other arrays have an entry for each token too. -/
  fit : EntriesFit len contentStarts contentStops startLines startColumns endLines endColumns

namespace TokenBatch

/-- No tokens are in input order from any origin on. -/
theorem tokensInOrder_zero (origin : Nat) (types : ByteArray) (starts ends : Array Nat) :
    TokensInOrder origin 0 types starts ends :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- An empty batch with room for `capacity` tokens. -/
@[expose]
def empty (capacity : Nat) : TokenBatch :=
  { len := 0, bytes := ByteArray.empty, types := ByteArray.emptyWithCapacity capacity,
    contentStarts := Array.emptyWithCapacity capacity,
    contentStops := Array.emptyWithCapacity capacity,
    startOffsets := Array.emptyWithCapacity capacity,
    startLines := Array.emptyWithCapacity capacity,
    startColumns := Array.emptyWithCapacity capacity,
    endOffsets := Array.emptyWithCapacity capacity,
    endLines := Array.emptyWithCapacity capacity,
    endColumns := Array.emptyWithCapacity capacity,
    origin := 0,
    ordered := tokensInOrder_zero _ _ _ _,
    fit := ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
      Nat.zero_le _⟩ }

instance : Inhabited TokenBatch := ⟨empty 0⟩

/-- The offset where the last token ends, or the origin if the batch has no token. -/
@[expose]
def lastEnd (self : TokenBatch) : Nat :=
  if h : self.len = 0 then self.origin
  else self.endOffsets[self.len - 1]'(by have := self.ordered.2.2.1; omega)

/-- The offset where the last token ends, read as the order of the tokens states it. -/
theorem lastEnd_eq (self : TokenBatch) :
    self.lastEnd = if self.len = 0 then self.origin else self.endOffsets[self.len - 1]! := by
  unfold lastEnd
  by_cases h : self.len = 0
  · simp [h]
  · simp only [h, ↓reduceDIte, ↓reduceIte]
    rw [getElem!_pos]

/-- Writes the value at `index` of the array, which is at most its size. -/
@[inline]
private def write (array : Array Nat) (index value : Nat) : Array Nat :=
  if h : index < array.size then array.set index value else array.push value

/-- Writes the byte at `index` of the array, which is at most its size. -/
@[inline]
private def writeByte (array : ByteArray) (index : Nat) (value : UInt8) : ByteArray :=
  if h : index < array.size then array.set index value else array.push value

private theorem size_write (array : Array Nat) (index value : Nat) (h : index ≤ array.size) :
    index < (write array index value).size := by
  unfold write
  split
  · rw [Array.size_set]; assumption
  · rw [Array.size_push]; omega

private theorem getElem!_write (array : Array Nat) (index value i : Nat) (h : index ≤ array.size) :
    (write array index value)[i]! = if i = index then value else array[i]! := by
  unfold write
  by_cases hlt : index < array.size
  · simp only [hlt, ↓reduceDIte, getElem!_def, Array.getElem?_set]
    by_cases e : i = index
    · simp [e]
    · simp [e, Ne.symm e]
  · simp only [hlt, ↓reduceDIte, getElem!_def, Array.getElem?_push]
    by_cases e : i = index
    · simp [e, show index = array.size by omega]
    · simp [e, show i ≠ array.size by omega]

private theorem size_writeByte (array : ByteArray) (index : Nat) (value : UInt8)
    (h : index ≤ array.size) : index < (writeByte array index value).size := by
  obtain ⟨data⟩ := array
  unfold writeByte
  split
  · show index < (data.set index value _).size
    rw [Array.size_set]; assumption
  · show index < (data.push value).size
    rw [Array.size_push]; simp only [ByteArray.size] at h; omega

private theorem get!_writeByte (array : ByteArray) (index : Nat) (value : UInt8) (i : Nat)
    (h : index ≤ array.size) :
    (writeByte array index value).get! i = if i = index then value else array.get! i := by
  unfold writeByte
  by_cases hlt : index < array.size
  · simp only [hlt, ↓reduceDIte]
    obtain ⟨data⟩ := array
    show (data.set index value hlt)[i]! = if i = index then value else data[i]!
    simp only [getElem!_def, Array.getElem?_set]
    by_cases e : i = index
    · simp [e]
    · simp [e, Ne.symm e]
  · simp only [hlt, ↓reduceDIte]
    obtain ⟨data⟩ := array
    show (data.push value)[i]! = if i = index then value else data[i]!
    simp only [ByteArray.size] at h hlt
    simp only [getElem!_def, Array.getElem?_push]
    by_cases e : i = index
    · simp [e, show index = data.size by omega]
    · simp [e, show i ≠ data.size by omega]

/-- A write at the length keeps an entry for each token and has one for the token after. -/
private theorem le_size_write {array : Array Nat} {index : Nat} (h : index ≤ array.size)
    (value : Nat) : index + 1 ≤ (write array index value).size :=
  size_write array index value h

/-- A token appended after the last one, with a byte unless it is the end of file, keeps the
tokens in order. -/
private theorem tokensInOrder_push {origin len : Nat} {types : ByteArray} {starts ends : Array Nat}
    (h : TokensInOrder origin len types starts ends) (ty : UInt8) (start «end» : Nat)
    (after : (if len = 0 then origin else ends[len - 1]!) ≤ start)
    (nonempty : start < «end» ∨ ty = (TokenCategory.Internal.toUInt8 TokenCategory.endOfFile) ∧
        start = «end») :
    TokensInOrder origin (len + 1) (writeByte types len ty) (write starts len start)
      (write ends len «end») := by
  obtain ⟨ht, hs, he, hall⟩ := tokensInOrder_iff.mp h
  refine tokensInOrder_iff.mpr
    ⟨size_writeByte _ _ _ ht, size_write _ _ _ hs, size_write _ _ _ he, ?_⟩
  intro i hi
  have hS := getElem!_write starts len start
  have hE := getElem!_write ends len «end»
  have hT := get!_writeByte types len ty
  rw [hS i hs, hE i he, hT i ht]
  by_cases e : i = len
  · simp only [e, ↓reduceIte]
    refine ⟨?_, nonempty⟩
    by_cases z : len = 0
    · simpa [z] using after
    · simp only [z, ↓reduceIte] at after ⊢
      rw [hE (len - 1) he]
      simpa [show len - 1 ≠ len by omega] using after
  · have hlt : i < len := by omega
    simp only [e, ↓reduceIte]
    obtain ⟨hprev, hne⟩ := hall i hlt
    refine ⟨?_, hne⟩
    by_cases z : i = 0
    · simpa [z] using hprev
    · simp only [z, ↓reduceIte] at hprev ⊢
      rw [hE (i - 1) he]
      simpa [show i - 1 ≠ len by omega] using hprev

/--
Appends a token with the type, its content from `contentStart` to `contentStop` in `bytes`,
and the span given by the numbers of its two locations. The token starts at or after the end
of the last one, and has a byte unless it is the end of file.
-/
/- LEAN: not inlined. Inlined into the lexer's loop, the compiler does not reuse the batch's
cell: every token frees the old cell and allocates a new one. As a call of its own, the cell is
updated in place when nothing else refers to it. -/
@[noinline]
def push (self : TokenBatch) (ty : TokenCategory) (contentStart contentStop : Nat)
    (startOffset startLine startColumn endOffset endLine endColumn : Nat)
    (after : self.lastEnd ≤ startOffset)
    (nonempty : startOffset < endOffset ∨ ty = .endOfFile ∧ startOffset = endOffset) :
    TokenBatch :=
  let index := self.len
  { self with
    len := index + 1
    types := writeByte self.types index (TokenCategory.Internal.toUInt8 ty)
    contentStarts := write self.contentStarts index contentStart
    contentStops := write self.contentStops index contentStop
    startOffsets := write self.startOffsets index startOffset
    startLines := write self.startLines index startLine
    startColumns := write self.startColumns index startColumn
    endOffsets := write self.endOffsets index endOffset
    endLines := write self.endLines index endLine
    endColumns := write self.endColumns index endColumn
    ordered :=
      tokensInOrder_push self.ordered (TokenCategory.Internal.toUInt8 ty) startOffset endOffset
          (self.lastEnd_eq ▸ after)
        (nonempty.imp_right fun h => ⟨by rw [h.1], h.2⟩)
    fit :=
      have ⟨h1, h2, h3, h4, h5, h6⟩ := self.fit
      ⟨le_size_write h1 _, le_size_write h2 _, le_size_write h3 _, le_size_write h4 _,
        le_size_write h5 _, le_size_write h6 _⟩ }

/--
Appends a token with the type, its content from `contentStart` to `contentStop` in `bytes`,
spanning the offsets from `start` to `end` on the line that starts at the offset `lineStart`.
The token starts at or after the end of the last one, and has a byte unless it is the end of
file.
-/
@[inline]
def pushOnLine (self : TokenBatch) (ty : TokenCategory) (contentStart contentStop : Nat)
    (line lineStart start «end» : Nat) (after : self.lastEnd ≤ start)
    (nonempty : start < «end» ∨ ty = .endOfFile ∧ start = «end») : TokenBatch :=
  self.push ty contentStart contentStop start line (start - lineStart) «end» line
    («end» - lineStart)
    after nonempty

/--
Appends a token with the type, its content from `contentStart` to `contentStop` in `bytes`,
spanning from `start` to `end`. The token starts at or after the end of the last one, and has
a byte unless it is the end of file.
-/
@[expose, inline]
def pushLocated (self : TokenBatch) (ty : TokenCategory) (contentStart contentStop : Nat)
    (start «end» : Span.Location) (after : self.lastEnd ≤ start.offset)
    (nonempty : start.offset < «end».offset ∨ ty = .endOfFile ∧ start.offset = «end».offset) :
    TokenBatch :=
  self.push ty contentStart contentStop start.offset start.line start.column
    «end».offset «end».line «end».column after nonempty

/-- Empties the batch, keeping its storage; the tokens appended next start at or after
`origin`. -/
@[expose, inline]
def clear (self : TokenBatch) (origin : Nat) : TokenBatch :=
  { self with
    len := 0
    origin
    ordered := tokensInOrder_zero _ _ _ _
    fit := ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
      Nat.zero_le _⟩ }

theorem lastEnd_push (self : TokenBatch) (ty : TokenCategory) (contentStart contentStop : Nat)
    (startOffset startLine startColumn endOffset endLine endColumn : Nat)
    (after : self.lastEnd ≤ startOffset)
    (nonempty : startOffset < endOffset ∨ ty = .endOfFile ∧ startOffset = endOffset) :
    (self.push ty contentStart contentStop startOffset startLine startColumn endOffset endLine
      endColumn after nonempty).lastEnd = endOffset := by
  rw [lastEnd_eq]
  simp only [push, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  rw [getElem!_write _ _ _ _ self.ordered.2.2.1]; simp

theorem lastEnd_clear (self : TokenBatch) (origin : Nat) :
    (self.clear origin).lastEnd = origin := by
  simp [lastEnd, clear]

theorem lastEnd_default : (default : TokenBatch).lastEnd = 0 :=
  rfl

theorem lastEnd_pushOnLine (self : TokenBatch) (ty : TokenCategory) (contentStart contentStop : Nat)
    (line lineStart start «end» : Nat) (after : self.lastEnd ≤ start)
    (nonempty : start < «end» ∨ ty = .endOfFile ∧ start = «end») :
    (self.pushOnLine ty contentStart contentStop line lineStart start «end» after
      nonempty).lastEnd =
      «end» :=
  lastEnd_push ..

theorem lastEnd_pushLocated (self : TokenBatch) (ty : TokenCategory)
    (contentStart contentStop : Nat)
    (start «end» : Span.Location) (after : self.lastEnd ≤ start.offset)
    (nonempty : start.offset < «end».offset ∨ ty = .endOfFile ∧ start.offset = «end».offset) :
    (self.pushLocated ty contentStart contentStop start «end» after nonempty).lastEnd =
      «end».offset :=
  lastEnd_push ..

theorem len_push (self : TokenBatch) (ty : TokenCategory) (contentStart contentStop : Nat)
    (startOffset startLine startColumn endOffset endLine endColumn : Nat)
    (after : self.lastEnd ≤ startOffset)
    (nonempty : startOffset < endOffset ∨ ty = .endOfFile ∧ startOffset = endOffset) :
    (self.push ty contentStart contentStop startOffset startLine startColumn endOffset endLine
      endColumn after nonempty).len = self.len + 1 :=
  (rfl)

/-- Each token of the batch has an entry in `types`. -/
theorem len_le_types (self : TokenBatch) : self.len ≤ self.types.size :=
  self.ordered.1

/-- Each token of the batch has an entry in `startOffsets`. -/
theorem len_le_startOffsets (self : TokenBatch) : self.len ≤ self.startOffsets.size :=
  self.ordered.2.1

/-- Each token of the batch has an entry in `endOffsets`. -/
theorem len_le_endOffsets (self : TokenBatch) : self.len ≤ self.endOffsets.size :=
  self.ordered.2.2.1

/--
Whether every token of the batch starts at or after the offset and is not the end of file, so
that it ends after the offset.
-/
@[expose]
def StartsFrom (self : TokenBatch) (offset : Nat) : Prop :=
  ∀ i (hi : i < self.len),
    offset ≤ self.startOffsets[i]'(Nat.lt_of_lt_of_le hi self.len_le_startOffsets) ∧
      self.types[i]'(Nat.lt_of_lt_of_le hi self.len_le_types) ≠ (TokenCategory.Internal.toUInt8
          TokenCategory.endOfFile)

/-- `StartsFrom` with the reads unchecked: the form the proofs about the batch use. -/
theorem startsFrom_iff {self : TokenBatch} {offset : Nat} :
    self.StartsFrom offset ↔ ∀ i, i < self.len →
      offset ≤ self.startOffsets[i]! ∧ self.types.get! i ≠
          (TokenCategory.Internal.toUInt8 TokenCategory.endOfFile) := by
  have hb : ∀ (a : ByteArray) {i : Nat} (h : i < a.size), a.get! i = a[i] := fun a _ h => by
    obtain ⟨data⟩ := a
    exact getElem!_pos data _ h
  refine forall_congr' fun i => ⟨fun h hi => ?_, fun h hi => ?_⟩
  · rw [getElem!_pos self.startOffsets i (Nat.lt_of_lt_of_le hi self.len_le_startOffsets),
      hb self.types (Nat.lt_of_lt_of_le hi self.len_le_types)]
    exact h hi
  · have h := h hi
    rwa [getElem!_pos self.startOffsets i (Nat.lt_of_lt_of_le hi self.len_le_startOffsets),
      hb self.types (Nat.lt_of_lt_of_le hi self.len_le_types)] at h

theorem startsFrom_clear (self : TokenBatch) (origin offset : Nat) :
    (self.clear origin).StartsFrom offset :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem startsFrom_empty (capacity offset : Nat) : (empty capacity).StartsFrom offset :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem startsFrom_push {self : TokenBatch} {offset : Nat} (h : self.StartsFrom offset)
    {ty : TokenCategory} {contentStart contentStop : Nat}
    {startOffset startLine startColumn endOffset endLine endColumn : Nat}
    {after : self.lastEnd ≤ startOffset}
    {nonempty : startOffset < endOffset ∨ ty = .endOfFile ∧ startOffset = endOffset}
    (hstart : offset ≤ startOffset) (hty : ty ≠ .endOfFile) :
    (self.push ty contentStart contentStop startOffset startLine startColumn endOffset endLine
      endColumn after nonempty).StartsFrom offset := by
  have h := startsFrom_iff.mp h
  refine startsFrom_iff.mpr fun i hi => ?_
  simp only [push] at hi ⊢
  have hs := self.ordered.2.1
  have ht := self.ordered.1
  have hw := get!_writeByte self.types self.len (TokenCategory.Internal.toUInt8 ty) i ht
  rw [getElem!_write _ _ _ _ hs, hw]
  by_cases e : i = self.len
  · subst e
    simp only [↓reduceIte]
    refine ⟨hstart, fun heq => hty ?_⟩
    cases ty <;> first | rfl | exact absurd heq (by decide)
  · simp only [e, ↓reduceIte]
    exact h i (by omega)

theorem startsFrom_default (offset : Nat) : (default : TokenBatch).StartsFrom offset :=
  startsFrom_empty 0 offset

theorem startsFrom_pushOnLine {self : TokenBatch} {offset : Nat} (h : self.StartsFrom offset)
    {ty : TokenCategory} {contentStart contentStop line lineStart start «end» : Nat}
    {after : self.lastEnd ≤ start} {nonempty : start < «end» ∨ ty = .endOfFile ∧ start = «end»}
    (hstart : offset ≤ start) (hty : ty ≠ .endOfFile) :
    (self.pushOnLine ty contentStart contentStop line lineStart start «end» after
      nonempty).StartsFrom offset :=
  startsFrom_push h hstart hty

theorem startsFrom_pushLocated {self : TokenBatch} {offset : Nat} (h : self.StartsFrom offset)
    {ty : TokenCategory} {contentStart contentStop : Nat} {start «end» : Span.Location}
    {after : self.lastEnd ≤ start.offset}
    {nonempty : start.offset < «end».offset ∨ ty = .endOfFile ∧ start.offset = «end».offset}
    (hstart : offset ≤ start.offset) (hty : ty ≠ .endOfFile) :
    (self.pushLocated ty contentStart contentStop start «end» after nonempty).StartsFrom offset :=
  startsFrom_push h hstart hty

/-- A token of the batch other than the end of file ends after it starts, and so after
`origin`. -/
theorem start_lt_end (self : TokenBatch) {i : Nat} (hi : i < self.len)
    (hty : self.types.get! i ≠ (TokenCategory.Internal.toUInt8 TokenCategory.endOfFile)) :
    self.startOffsets[i]! < self.endOffsets[i]! := by
  rcases ((tokensInOrder_iff.mp self.ordered).2.2.2 i hi).2 with h | h
  · exact h
  · exact absurd h.1 hty

/-- Whether every token of the batch ends after the offset. -/
@[expose]
def EndsAfter (self : TokenBatch) (offset : Nat) : Prop :=
  ∀ i (hi : i < self.len),
    offset < self.endOffsets[i]'(Nat.lt_of_lt_of_le hi self.len_le_endOffsets)

/-- `EndsAfter` with the reads unchecked: the form the proofs about the batch use. -/
theorem endsAfter_iff {self : TokenBatch} {offset : Nat} :
    self.EndsAfter offset ↔ ∀ i, i < self.len → offset < self.endOffsets[i]! :=
  forall_congr' fun i => ⟨fun h hi => by
      rw [getElem!_pos self.endOffsets i (Nat.lt_of_lt_of_le hi self.len_le_endOffsets)]
      exact h hi,
    fun h hi => by
      have h := h hi
      rwa [getElem!_pos self.endOffsets i (Nat.lt_of_lt_of_le hi self.len_le_endOffsets)] at h⟩

/-- Tokens that start at or after the offset and are not the end of file end after it. -/
theorem StartsFrom.endsAfter {self : TokenBatch} {offset : Nat} (h : self.StartsFrom offset) :
    self.EndsAfter offset := by
  have h := startsFrom_iff.mp h
  exact endsAfter_iff.mpr fun i hi =>
    Nat.lt_of_le_of_lt (h i hi).1 (self.start_lt_end hi (h i hi).2)

theorem endsAfter_clear (self : TokenBatch) (origin offset : Nat) :
    (self.clear origin).EndsAfter offset :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem endsAfter_push {self : TokenBatch} {offset : Nat} (h : self.EndsAfter offset)
    {ty : TokenCategory} {contentStart contentStop : Nat}
    {startOffset startLine startColumn endOffset endLine endColumn : Nat}
    {after : self.lastEnd ≤ startOffset}
    {nonempty : startOffset < endOffset ∨ ty = .endOfFile ∧ startOffset = endOffset}
    (hend : offset < endOffset) :
    (self.push ty contentStart contentStop startOffset startLine startColumn endOffset endLine
      endColumn after nonempty).EndsAfter offset := by
  have h := endsAfter_iff.mp h
  refine endsAfter_iff.mpr fun i hi => ?_
  simp only [push] at hi ⊢
  rw [getElem!_write _ _ _ _ self.ordered.2.2.1]
  by_cases e : i = self.len
  · subst e
    simp only [↓reduceIte]
    exact hend
  · simp only [e, ↓reduceIte]
    exact h i (by omega)

theorem endsAfter_pushLocated {self : TokenBatch} {offset : Nat} (h : self.EndsAfter offset)
    {ty : TokenCategory} {contentStart contentStop : Nat} {start «end» : Span.Location}
    {after : self.lastEnd ≤ start.offset}
    {nonempty : start.offset < «end».offset ∨ ty = .endOfFile ∧ start.offset = «end».offset}
    (hend : offset < «end».offset) :
    (self.pushLocated ty contentStart contentStop start «end» after nonempty).EndsAfter offset :=
  endsAfter_push h hend

end TokenBatch

end Internal

/- LEAN: Rust's lifetime `'a` of the token and the cursor is a batch tag here: the type of a
token names the batch it was taken from by its tag, and a token is read only through a cursor
with the same tag. The cursor of the next hand-over has another tag, so a token kept from an
earlier one does not fit it.

A tag is the property of being the batch, not the batch itself, as the compiler erases a
function to propositions but not a batch: a batch as the parameter would be passed, and its
references counted, at every call that takes a cursor or a token, and a tag is not. The tag
of a batch is unique to it (`Internal.TokenBatch.tag_injective`). -/
/-- The name of a batch of tokens, by which the types of its tokens and cursors refer to it. -/
@[expose] def BatchTag : Type :=
  Internal.TokenBatch → Prop

/-- The name of the batch. -/
@[expose] def Internal.TokenBatch.tag (batch : Internal.TokenBatch) : BatchTag :=
  (· = batch)

/-- Batches with the same name are the same. -/
theorem Internal.TokenBatch.tag_injective {a b : Internal.TokenBatch} (h : a.tag = b.tag) : a = b :=
  cast (congrFun h a) (rfl : a = a)

/- LEAN: the Rust token is a pair of references to its entry and its span in the lexer's
batch arrays, valid while the batch is. A Lean array holds every structure as a pointer to
a separate object, so a token held as a structure in the batch would be allocated when it
is lexed and freed when it is overwritten. The batch therefore keeps the tokens' fields in
arrays of their own (`Internal.TokenBatch`), which the lexer overwrites in place, and a token
is its index in the batch. A structure with a single number field is represented as the number
itself, so a token costs nothing; its batch tag is a type index and not stored. Its fields
are read through a cursor over its batch: `cursor.category token`, `cursor.content token`,
`cursor.span token`. -/
/--
A token of the batch named `batch`.

A token is read through a cursor over its batch: the cursor it was taken from, or any cursor
that the consumer's operations make from that one in the same hand-over. A token cannot be
read through the cursor of another hand-over, which is over another batch.
-/
structure _root_.BSmtLib.Token (batch : Token.BatchTag) where
  private mk ::
  private index : Nat
  /- LEAN: not in Rust. The token is within its batch, so that it is read without a bounds
  check; the proof is not stored, and the token stays a number. -/
  private valid : ∀ b, batch b → index < b.len

@[no_expose] instance {batch : BatchTag} : BEq (Token batch) := ⟨fun a b => a.index == b.index⟩

namespace Internal.TokenBatch

/-- A read of a byte array within it is the checked read. -/
theorem get!_eq_getElem (array : ByteArray) {index : Nat} (h : index < array.size) :
    array.get! index = array[index] := by
  obtain ⟨data⟩ := array
  exact getElem!_pos data index h

/- LEAN: the counterparts of the methods of the Rust token, which carries its data, read from
the batch at the token's index, which is within the batch. -/

@[inline]
private def categoryOf (self : TokenBatch) (index : Nat) (h : index < self.len) : TokenCategory :=
  TokenCategory.Internal.ofUInt8 (self.types[index]'(Nat.lt_of_lt_of_le h self.ordered.1))

@[inline]
private def contentOf (self : TokenBatch) (index : Nat) (h : index < self.len) : ByteSlice :=
  self.bytes.toByteSlice (self.contentStarts[index]'(Nat.lt_of_lt_of_le h self.fit.1))
    (self.contentStops[index]'(Nat.lt_of_lt_of_le h self.fit.2.1))

@[inline]
private def spanOf (self : TokenBatch) (index : Nat) (h : index < self.len) : Span :=
  Span.Internal.ofNumbers (self.startOffsets[index]'(Nat.lt_of_lt_of_le h self.ordered.2.1))
    (self.startLines[index]'(Nat.lt_of_lt_of_le h self.fit.2.2.1))
    (self.startColumns[index]'(Nat.lt_of_lt_of_le h self.fit.2.2.2.1))
    (self.endOffsets[index]'(Nat.lt_of_lt_of_le h self.ordered.2.2.1))
    (self.endLines[index]'(Nat.lt_of_lt_of_le h self.fit.2.2.2.2.1))
    (self.endColumns[index]'(Nat.lt_of_lt_of_le h self.fit.2.2.2.2.2))

/-- The category of the token at the index, as the entries of the batch give it. -/
private theorem categoryOf_eq (self : TokenBatch) (index : Nat) (h : index < self.len) :
    self.categoryOf index h = TokenCategory.Internal.ofUInt8 (self.types.get! index) := by
  simp only [categoryOf, get!_eq_getElem _ (Nat.lt_of_lt_of_le h self.ordered.1)]

/-- The content of the token at the index, as the entries of the batch give it. -/
private theorem contentOf_eq (self : TokenBatch) (index : Nat) (h : index < self.len) :
    self.contentOf index h =
      self.bytes.toByteSlice (self.contentStarts[index]!) (self.contentStops[index]!) := by
  have := Nat.lt_of_lt_of_le h self.fit.1
  have := Nat.lt_of_lt_of_le h self.fit.2.1
  simp only [contentOf, getElem!_pos, *]

/-- The span of the token at the index, as the entries of the batch give it. -/
private theorem spanOf_eq (self : TokenBatch) (index : Nat) (h : index < self.len) :
    self.spanOf index h =
      Span.Internal.ofNumbers self.startOffsets[index]! self.startLines[index]!
          self.startColumns[index]!
        self.endOffsets[index]! self.endLines[index]! self.endColumns[index]! := by
  have := Nat.lt_of_lt_of_le h self.ordered.2.1
  have := Nat.lt_of_lt_of_le h self.fit.2.2.1
  have := Nat.lt_of_lt_of_le h self.fit.2.2.2.1
  have := Nat.lt_of_lt_of_le h self.ordered.2.2.1
  have := Nat.lt_of_lt_of_le h self.fit.2.2.2.2.1
  have := Nat.lt_of_lt_of_le h self.fit.2.2.2.2.2
  simp only [spanOf, getElem!_pos, *]

end Internal.TokenBatch

/- LEAN: Rust's `SmtVersionRefused`, without the prefix. -/
/-- Producer refused to switch to a requested version. -/
structure VersionRefused where
  deriving BEq, Hashable, Repr, Inhabited

@[no_expose] instance : ToString VersionRefused := ⟨fun _ => "version switch refused"⟩

/--
A cursor into a batch of tokens, from which elements are consumed sequentially.

A parser reads a batch through a cursor: it consumes the tokens one at
a time, can look at the next one, and can attempt to take several at once.
However, it is not guaranteed how many tokens the batch will actually have,
so an attempt is only useful for fast paths that fall back to slow paths
with the same behaviour if the tokens are not available.

A cursor is over the batch of one hand-over, which its type names. The cursors
that the consumer's operations make from it are over the same batch and read
every token taken from any of them. The cursor of another hand-over is over
another batch.
-/
/- LEAN: Rust narrows the borrowed slices of the batch; here the cursor holds the whole batch
and the range of it that it yields, from `first` to `stop`. A relex request moves `stop`,
which needs no copy. `first` is the first token of the hand-over, Rust's `start`: the tokens
from it to `nextIndex` are the consumed ones. `bounded` keeps the indices in order and within
the batch, which the reads and the proofs about consumption below rest on.

The batch is tagged by the type's parameter, which is not stored, and held in
the field `batch`, which the reads use; `tagged` ties the two. -/
structure BatchCursor (tag : BatchTag) where
  private mk ::
  /-- The SMT-LIB version that applies to the tokens. -/
  version : Version
  private batch : Internal.TokenBatch
  private tagged : tag = batch.tag
  private first : Nat
  private stop : Nat
  private nextIndex : Nat
  private relexFlag : Bool
  private discardFlag : Bool
  private bounded : first ≤ nextIndex ∧ nextIndex ≤ stop ∧ stop ≤ batch.len

/- LEAN: not in Rust, where the lexer reads the cursor's crate-private fields. The cursor's
fields are private to this module; the lexer reads the batch through this accessor. -/
/-- The batch of the cursor. -/
@[inline]
def BatchCursor.Internal.batch {batch : BatchTag} (cursor : BatchCursor batch) :
    Internal.TokenBatch :=
  cursor.batch

/-- The batch of the cursor has the cursor's tag. -/
theorem BatchCursor.Internal.tag_batch {batch : BatchTag} (cursor : BatchCursor batch) :
    (BatchCursor.Internal.batch cursor).tag = batch :=
  cursor.tagged.symm

namespace BatchCursor

variable {batch : BatchTag}

/-- The cursor's batch has the cursor's tag. -/
private theorem tagged_batch (self : BatchCursor batch) : batch self.batch :=
  (congrFun self.tagged self.batch).mpr rfl

/-- A batch with the cursor's tag is the cursor's batch. -/
private theorem eq_batch_of_tag (self : BatchCursor batch) {b : Internal.TokenBatch} (h : batch b) :
    b = self.batch :=
  (congrFun self.tagged b).mp h

/-- A token below the end of the cursor is within every batch with the cursor's tag. -/
private theorem valid_of_lt_stop (self : BatchCursor batch) {index : Nat}
    (h : index < self.stop) : ∀ b, batch b → index < b.len := fun _ hb => by
  rw [self.eq_batch_of_tag hb]
  exact Nat.lt_of_lt_of_le h self.bounded.2.2

/-- A token of the cursor's tag is within the cursor's batch. -/
private theorem lt_len (self : BatchCursor batch) (token : Token batch) :
    token.index < self.batch.len :=
  token.valid _ self.tagged_batch

/- LEAN: crate-private in Rust, like the other functions here in `Internal`, which only the lexer
uses. -/
/-- Returns a cursor at the start of the batch. -/
@[inline]
def Internal.new (version : Version) (batch : Internal.TokenBatch) : BatchCursor batch.tag :=
  { version, batch, tagged := rfl, first := 0, stop := batch.len, nextIndex := 0,
    relexFlag := false, discardFlag := false,
    bounded := ⟨Nat.le_refl _, Nat.zero_le _, Nat.le_refl _⟩ }

/--
Returns a cursor over a single token of this cursor's batch.

This can be used for parsing one token using a cursor-parsing function.
-/
/- LEAN: Rust's `single` takes the version and the token, which carries its own data. A Lean
token is read through its batch, so the new cursor is made from a cursor over the token's
batch. -/
@[inline]
def Internal.single (self : BatchCursor batch) (version : Version) (token : Token batch) :
    BatchCursor batch :=
  { version, batch := self.batch, tagged := self.tagged, first := token.index,
    stop := token.index + 1, nextIndex := token.index, relexFlag := false, discardFlag := false,
    bounded := ⟨Nat.le_refl _, Nat.le_succ _, self.lt_len token⟩ }

/-- Whether a token remains to be consumed. -/
/- LEAN: not in Rust. That a token remains is the producer's law `Cursor.HasNext` for the
cursor, which the consumers take as a proof; Rust's `is_empty` is its negation. -/
def HasNext (self : BatchCursor batch) : Prop :=
  self.nextIndex < self.stop

@[no_expose] instance (self : BatchCursor batch) : Decidable self.HasNext :=
  inferInstanceAs (Decidable (self.nextIndex < self.stop))

/-- A cursor at the start of a batch with a token has a token remaining. -/
theorem hasNext_new {b : Internal.TokenBatch} (version : Version) (h : 0 < b.len) :
    (Internal.new version b).HasNext :=
  h

/--
Whether `self` comes from `origin` through the consumer's operations: it is the
same hand-over of the same batch, with at least the tokens consumed that `origin`
has consumed. The tokens not consumed yet may have been dropped, as a version
switch drops them.
-/
def Internal.Follows (self origin : BatchCursor batch) : Prop :=
  self.first = origin.first ∧ self.stop ≤ origin.stop ∧ origin.nextIndex ≤ self.nextIndex

/--
Whether `self` comes from `origin` through the consumer's operations, with at
least one more token consumed than `origin` has.
-/
/- LEAN: not in Rust. That a cursor took a token is the producer's law `Cursor.Consumed` for
the cursor, by which the loops of the consumers end. -/
def Consumed (self origin : BatchCursor batch) : Prop :=
  (Internal.Follows self) origin ∧ origin.nextIndex < self.nextIndex

theorem Internal.Follows.refl (self : BatchCursor batch) : (Internal.Follows self) self :=
  ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem Internal.Follows.trans {a b c : BatchCursor batch} (ab : (Internal.Follows a) b)
    (bc : (Internal.Follows b) c) :
    (Internal.Follows a) c :=
  ⟨ab.1.trans bc.1, Nat.le_trans ab.2.1 bc.2.1, Nat.le_trans bc.2.2 ab.2.2⟩

theorem Consumed.follows {a b : BatchCursor batch} (ab : a.Consumed b) : (Internal.Follows a) b :=
  ab.1

theorem Consumed.trans_follows {a b c : BatchCursor batch} (ab : a.Consumed b)
    (bc : (Internal.Follows b) c) : a.Consumed c :=
  ⟨ab.1.trans bc, Nat.lt_of_le_of_lt bc.2.2 ab.2⟩

theorem Internal.Follows.trans_consumed {a b c : BatchCursor batch} (ab : (Internal.Follows a) b)
    (bc : b.Consumed c) : a.Consumed c :=
  ⟨ab.trans bc.1, Nat.lt_of_lt_of_le bc.2 ab.2.2⟩

theorem Consumed.trans {a b c : BatchCursor batch} (ab : a.Consumed b) (bc : b.Consumed c) :
    a.Consumed c :=
  ab.trans_follows bc.1

/-- Returns the next token (if any) without consuming it. -/
@[inline]
def peek? (self : BatchCursor batch) : Option (Token batch) :=
  if h : self.nextIndex < self.stop then some ⟨self.nextIndex, self.valid_of_lt_stop h⟩ else none

/-- Returns the next token, which there is, without consuming it. -/
@[inline]
def peek (self : BatchCursor batch) (h : self.HasNext) : Token batch :=
  ⟨self.nextIndex, self.valid_of_lt_stop h⟩

/- LEAN: methods taking `&mut self` in Rust return the updated cursor in Lean, here with the
proof that it consumed the token. -/
/-- Consumes the next token, which there is. -/
@[inline]
def next (self : BatchCursor batch) (h : self.HasNext) :
    Token batch × { c : BatchCursor batch // c.Consumed self } :=
  (⟨self.nextIndex, self.valid_of_lt_stop h⟩,
    ⟨{ self with
        nextIndex := self.nextIndex + 1
        bounded := ⟨Nat.le_succ_of_le self.bounded.1, h, self.bounded.2.2⟩ },
      ⟨⟨rfl, Nat.le_refl _, Nat.le_succ _⟩, Nat.lt_succ_self _⟩⟩)

/-- Consumes the next token (if any). -/
@[inline]
def next? (self : BatchCursor batch) :
    Option (Token batch × { c : BatchCursor batch // c.Consumed self }) :=
  if h : self.HasNext then some (self.next h) else none

/-- A cursor with a token remaining gives it. -/
theorem isSome_next? {self : BatchCursor batch} (h : self.HasNext) : self.next?.isSome := by
  simp [next?, h]

/--
The tokens ahead of a cursor, as the extractor of `BatchCursor.attempt` sees them: they can
only be taken in order.
-/
/- LEAN: Rust's `SmtTokenWindow`, in the namespace of the cursor whose `attempt` hands it over. -/
structure TokenWindow (tag : BatchTag) where
  private mk ::
  /-- The SMT-LIB version that applies to the tokens. -/
  version : Version
  private batch : Internal.TokenBatch
  private tagged : tag = batch.tag
  private stop : Nat
  private nextIndex : Nat
  private bounded : nextIndex ≤ stop ∧ stop ≤ batch.len

/-- A token of the window's tag is within the window's batch. -/
private theorem TokenWindow.lt_len (self : TokenWindow batch) (token : Token batch) :
    token.index < self.batch.len :=
  token.valid _ ((congrFun self.tagged self.batch).mpr rfl)

/--
Whether `self` comes from `origin` by taking at least one token from it.
-/
/- LEAN: not in Rust. That a window took a token, as `Consumed` is for the cursor. -/
def TokenWindow.Consumed (self origin : TokenWindow batch) : Prop :=
  self.stop = origin.stop ∧ origin.nextIndex < self.nextIndex

theorem TokenWindow.Consumed.trans {a b c : TokenWindow batch} (ab : a.Consumed b)
    (bc : b.Consumed c) : a.Consumed c :=
  ⟨ab.1.trans bc.1, Nat.lt_trans bc.2 ab.2⟩

/-- Takes the next token of the window (if any). -/
/- LEAN: Rust's `SmtLookahead::next` for `SmtTokenWindow`, with the proof that it took a token. -/
@[inline]
def TokenWindow.next? (self : TokenWindow batch) :
    Option (Token batch × { w : TokenWindow batch // w.Consumed self }) :=
  if h : self.nextIndex < self.stop then
    some (⟨self.nextIndex, fun _ hb => by
        rw [(congrFun self.tagged _).mp hb]; exact Nat.lt_of_lt_of_le h self.bounded.2⟩,
      ⟨{ self with nextIndex := self.nextIndex + 1, bounded := ⟨h, self.bounded.2⟩ },
        ⟨rfl, Nat.lt_succ_self _⟩⟩)
  else
    none

/-- The category of the token. -/
/- LEAN: Rust's `SmtToken::category`, read through the window, as the token is an index into
its batch (see `Token`). -/
@[inline]
def TokenWindow.category (self : TokenWindow batch) (token : Token batch) : TokenCategory :=
  self.batch.categoryOf token.index (self.lt_len token)

/--
The bytes of the token; empty for the end of file.

The bytes are for use during the hand-over; to keep them, copy them.
-/
/- LEAN: Rust's `SmtToken::content`, read through the window, as the token is an index into
its batch (see `Token`). -/
@[inline]
def TokenWindow.content (self : TokenWindow batch) (token : Token batch) : ByteSlice :=
  self.batch.contentOf token.index (self.lt_len token)

/-- The span of the token. -/
/- LEAN: Rust's `SmtToken::span`, read through the window, as the token is an index into its
batch (see `Token`). -/
@[inline]
def TokenWindow.span (self : TokenWindow batch) (token : Token batch) : Span :=
  self.batch.spanOf token.index (self.lt_len token)

/--
Attempts to consume several tokens at once.

The extractor takes tokens from the window ahead of the cursor, in order.
If it returns `some`, exactly the tokens it took are consumed, which must be at least one.
If it returns `none`, nothing is consumed.

The window ends where the cursor does, which may be after any token.
An extractor that runs out of tokens must return `none`; the
caller must then reach the same result by consuming token by token.
-/
/- LEAN: the extractor returns the window it took the tokens from, with the proof that it
took at least one, where the Rust closure takes the window by `&mut`. -/
@[inline]
def attempt (self : BatchCursor batch)
    (extract : (window : TokenWindow batch) →
      Option (α × { w : TokenWindow batch // w.Consumed window })) :
    Option (α × { c : BatchCursor batch // c.Consumed self }) :=
  let window : TokenWindow batch :=
    { version := self.version, batch := self.batch, tagged := self.tagged, stop := self.stop,
      nextIndex := self.nextIndex,
      bounded := self.bounded.2 }
  match extract window with
  | none => none
  | some (result, ⟨taken, consumed⟩) =>
    -- the extractor succeeded, consume what it took
    let bounded : self.first ≤ taken.nextIndex ∧ taken.nextIndex ≤ self.stop ∧
        self.stop ≤ self.batch.len :=
      ⟨Nat.le_trans self.bounded.1 (Nat.le_of_lt consumed.2),
        Nat.le_trans taken.bounded.1 (Nat.le_of_eq consumed.1), self.bounded.2.2⟩
    some (result, ⟨{ self with nextIndex := taken.nextIndex, bounded },
      ⟨⟨rfl, Nat.le_refl _, Nat.le_of_lt consumed.2⟩, consumed.2⟩⟩)

/-- Location of the end of the last consumed token in this hand-over (if any). -/
@[inline]
def Internal.consumedEnd (self : BatchCursor batch) : Option Span.Location :=
  if h : self.first < self.nextIndex then
    some (self.batch.spanOf (self.nextIndex - 1) (by have := self.bounded; omega)).end
  else none

/- LEAN: for the lexer, which knows from the consumer's proof that a token was consumed. -/
/-- Location of the end of the last consumed token, given that one was consumed. -/
@[inline]
def Internal.consumedEndOf (self : BatchCursor batch) {origin : BatchCursor batch}
    (h : self.Consumed origin) : Span.Location :=
  (self.batch.spanOf (self.nextIndex - 1) (by have := self.bounded; have := h.2; omega)).end

/- LEAN: Rust's `consumed_span`, for a consumer's caller that knows from the consumer's proof
that a token was consumed. -/
/-- Span of the last consumed token in this handover, given that one was consumed. -/
@[inline]
def Internal.consumedSpanOf (self : BatchCursor batch) {origin : BatchCursor batch}
    (h : self.Consumed origin) : Span :=
  self.batch.spanOf (self.nextIndex - 1) (by have := self.bounded; have := h.2; omega)

/--
Whether the cursor yields no token beyond its batch, and every token of its batch ends after
the offset.
-/
def Internal.EndsAfter (self : BatchCursor batch) (offset : Nat) : Prop :=
  self.stop ≤ self.batch.len ∧ self.batch.EndsAfter offset

theorem endsAfter_new {batch : Internal.TokenBatch} {offset : Nat} (h : batch.EndsAfter offset)
    (version : Version) : Internal.EndsAfter (Internal.new version batch) offset :=
  ⟨Nat.le_refl _, h⟩

/-- Two cursors with the same tag are over the same batch. -/
private theorem batch_eq_of_tag (self other : BatchCursor batch) : self.batch = other.batch :=
  Internal.TokenBatch.tag_injective (self.tagged.symm.trans other.tagged)

theorem Internal.Follows.endsAfter {self origin : BatchCursor batch} (h : (Internal.Follows self)
    origin)
    {offset : Nat} (ho : (Internal.EndsAfter origin) offset) :
    (Internal.EndsAfter self) offset := by
  rw [EndsAfter, batch_eq_of_tag self origin]
  exact ⟨Nat.le_trans h.2.1 ho.1, ho.2⟩

/-- The last token consumed ends after the offset that every token of the batch ends after. -/
theorem Consumed.lt_consumedEndOf {self origin : BatchCursor batch} (h : self.Consumed origin)
    {offset : Nat} (ho : (Internal.EndsAfter origin) offset) : offset
        < ((Internal.consumedEndOf self) h).offset := by
  have hs := h.follows.endsAfter ho
  have hlt : self.nextIndex - 1 < self.batch.len := by
    have := h.2
    have := self.bounded.2
    have := hs.1
    omega
  have h2 := Internal.TokenBatch.endsAfter_iff.mp hs.2 _ hlt
  rw [getElem!_pos self.batch.endOffsets _ (Nat.lt_of_lt_of_le hlt self.batch.ordered.2.2.1)] at h2
  simpa only [Internal.consumedEndOf, Internal.TokenBatch.spanOf, Span.end_ofNumbers,
    Span.Location.Internal.offset_new] using h2

/-- Consumes all tokens remaining in the cursor. -/
@[inline]
def consumeAll (self : BatchCursor batch) : BatchCursor batch :=
  { self with nextIndex := self.stop, bounded := ⟨Nat.le_trans self.bounded.1 self.bounded.2.1,
    Nat.le_refl _, self.bounded.2.2⟩ }

theorem consumeAll_follows (self : BatchCursor batch) : (Internal.Follows self.consumeAll) self :=
  ⟨rfl, Nat.le_refl _, self.bounded.2.1⟩

theorem consumeAll_consumed {self : BatchCursor batch} (h : self.HasNext) :
    self.consumeAll.Consumed self :=
  ⟨self.consumeAll_follows, h⟩

/-- Whether every token has been consumed. -/
@[inline]
def isEmpty (self : BatchCursor batch) : Bool :=
  self.nextIndex ≥ self.stop

theorem isEmpty_iff (self : BatchCursor batch) : self.isEmpty = true ↔ ¬ self.HasNext := by
  simp [isEmpty, HasNext]

theorem not_hasNext_consumeAll (self : BatchCursor batch) : ¬ self.consumeAll.HasNext := by
  simp [consumeAll, HasNext]

/--
Requests that the input is lexed again from the end of the last
consumed token.

The tokens not consumed through this cursor are discarded and will be
produced again by the lexer, so the cursor yields no more tokens:
it is empty from now on, and the consumed count stays where it is.
-/
@[inline]
private def relex (self : BatchCursor batch) : BatchCursor batch :=
  { self with
    stop := self.nextIndex
    relexFlag := true
    bounded := ⟨self.bounded.1, Nat.le_refl _, Nat.le_trans self.bounded.2.1 self.bounded.2.2⟩ }

/--
Sets the SMT-LIB version that should apply from now on.

The cursor never refuses: it switches to the new version, and returns it in subsequent calls
of `version`. The version change applies between the last consumed and first unconsumed token,
and the cursor can adjust the non-consumed tokens so they correspond to the set version. There
is no guarantee on their shape or whether any remain at all; the caller must not use any
information gathered on them beforehand.
-/
def setVersion (self : BatchCursor batch) (version : Version) :
    Except VersionRefused (BatchCursor batch) :=
  -- the lexer supports all versions,
  -- but needs to relex when switching between 2.0 and 2.5+
  let isCurrent2_0 := self.version == .v2_0
  let isNew2_0 := version == .v2_0
  -- we need to relex if the lexical rules change
  let self := if isCurrent2_0 != isNew2_0 then self.relex else self
  .ok { self with version }

theorem setVersion_follows {self : BatchCursor batch} {version : Version}
    {next : BatchCursor batch} (h : self.setVersion version = .ok next) :
    (Internal.Follows next) self := by
  unfold setVersion at h
  injection h with h
  subst h
  by_cases hv : ((self.version == .v2_0) != (version == .v2_0)) = true
  · simp only [hv, ite_true]
    exact ⟨rfl, self.bounded.2.1, Nat.le_refl _⟩
  · simp only [hv]
    exact Internal.Follows.refl self

/-- Whether a relex has been requested through this cursor. -/
@[inline]
def Internal.relexRequested (self : BatchCursor batch) : Bool :=
  self.relexFlag

/--
Puts the cursor into discarding: the rest of the input is dropped.

The tokens not consumed through this cursor are dropped, so the cursor yields no more tokens,
and the consumer is not called again, except once with the end of the input, which lies outside
the discarded bytes. Discarding is separate from the version and lasts until the end of the
input.
-/
@[inline]
def discardRest (self : BatchCursor batch) : BatchCursor batch :=
  { self with
    stop := self.nextIndex
    discardFlag := true
    bounded := ⟨self.bounded.1, Nat.le_refl _, Nat.le_trans self.bounded.2.1 self.bounded.2.2⟩ }

theorem discardRest_follows (self : BatchCursor batch) : (Internal.Follows self.discardRest) self :=
  ⟨rfl, self.bounded.2.1, Nat.le_refl _⟩

/-- Whether discarding the rest has been requested through this cursor. -/
@[inline]
def Internal.discardRequested (self : BatchCursor batch) : Bool :=
  self.discardFlag

/--
The cursor over the tokens not consumed yet, as a new hand-over in which nothing is
consumed.
-/
/- LEAN: Rust's `reset_consumed`. -/
@[inline]
def Internal.resetConsumed (self : BatchCursor batch) : BatchCursor batch :=
  { self with first := self.nextIndex, bounded := ⟨Nat.le_refl _, self.bounded.2⟩ }

/-- Folds over the categories of the first `count` tokens of the batch, which has them. -/
private def foldCategories (b : Internal.TokenBatch) (count : Nat) (h : count ≤ b.len) (init : β)
    (f : β → TokenCategory → β) : β :=
  count.fold (init := init) fun index hindex acc =>
    f acc (b.categoryOf index (Nat.lt_of_lt_of_le hindex h))

private theorem foldCategories_eq (b : Internal.TokenBatch) (count : Nat) (h : count ≤ b.len)
    (init : β)
    (f : β → TokenCategory → β) :
    foldCategories b count h init f =
      (List.range count).foldl
        (fun acc index => f acc (TokenCategory.Internal.ofUInt8 (b.types.get! index))) init := by
  induction count with
  | zero => simp [foldCategories]
  | succ n ih =>
    unfold foldCategories at ih ⊢
    rw [Nat.fold_succ, List.range_succ, List.foldl_append, ← ih (by omega),
      Internal.TokenBatch.categoryOf_eq]
    rfl

/- LEAN: for the lexer, Rust's `consumed_entries`. -/
/-- Folds over the categories of the tokens of the batch consumed so far, from its first one. -/
def Internal.foldConsumedCategories (self : BatchCursor batch) (init : β) (f : β → TokenCategory →
    β) :
    β :=
  foldCategories self.batch self.nextIndex (by have := self.bounded; omega) init f

/-- The fold over the consumed categories, as the entries of the batch give them. -/
private theorem foldConsumedCategories_eq (self : BatchCursor batch) (init : β)
    (f : β → TokenCategory → β) :
    (Internal.foldConsumedCategories self) init f =
      (List.range self.nextIndex).foldl
        (fun acc index => f acc
            (TokenCategory.Internal.ofUInt8 (self.batch.types.get! index))) init :=
  foldCategories_eq ..

/-- The number of tokens not consumed yet. -/
def Internal.remaining (self : BatchCursor batch) : Nat :=
  self.stop - self.nextIndex

theorem Consumed.remaining_lt {self origin : BatchCursor batch} (h : self.Consumed origin) :
    (Internal.remaining self) < (Internal.remaining origin) := by
  have := self.bounded.2
  have := h.1.2.1
  have := h.2
  unfold Internal.remaining
  omega

theorem remaining_resetConsumed (self : BatchCursor batch) :
    (Internal.remaining (Internal.resetConsumed self)) = (Internal.remaining self) :=
  (rfl)

theorem endsAfter_resetConsumed {self : BatchCursor batch} {offset : Nat}
    (h : (Internal.EndsAfter self) offset) :
        (Internal.EndsAfter (Internal.resetConsumed self)) offset :=
  h

theorem hasNext_resetConsumed {self : BatchCursor batch} :
    (Internal.resetConsumed self).HasNext ↔ self.HasNext :=
  Iff.rfl

/-- The category of the token. -/
/- LEAN: Rust's `SmtToken::category`, read through the cursor, as the token is an index into
its batch (see `Token`). -/
@[inline]
def category (self : BatchCursor batch) (token : Token batch) : TokenCategory :=
  self.batch.categoryOf token.index (self.lt_len token)

/--
The bytes of the token; empty for the end of file.

The bytes are for use during the hand-over; to keep them, copy them.
-/
/- LEAN: Rust's `SmtToken::content`, read through the cursor, as the token is an index into
its batch (see `Token`). -/
@[inline]
def content (self : BatchCursor batch) (token : Token batch) : ByteSlice :=
  self.batch.contentOf token.index (self.lt_len token)

/-- The span of the token. -/
/- LEAN: Rust's `SmtToken::span`, read through the cursor, as the token is an index into its
batch (see `Token`). -/
@[inline]
def span (self : BatchCursor batch) (token : Token batch) : Span :=
  self.batch.spanOf token.index (self.lt_len token)

/- LEAN: not in Rust: for the proofs, which read the cursor only through this module. -/
/-- Two cursors of a batch alike but for where their handover started: everything a consumer or
the lexer reads of a cursor is the same of both. -/
def Internal.Alike (x y : BatchCursor batch) : Prop :=
  x.version = y.version ∧ x.stop = y.stop ∧ x.nextIndex = y.nextIndex ∧
    x.relexFlag = y.relexFlag ∧ x.discardFlag = y.discardFlag

namespace Internal.Alike

theorem refl (x : BatchCursor batch) : Alike x x := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem symm {x y : BatchCursor batch} (h : Alike x y) : Alike y x :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

theorem trans {x y z : BatchCursor batch} (h : Alike x y) (h' : Alike y z) : Alike x z :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.1.trans h'.2.2.2.1,
    h.2.2.2.2.trans h'.2.2.2.2⟩

theorem resetConsumed (x : BatchCursor batch) : Alike (Internal.resetConsumed x) x := refl x

theorem version {x y : BatchCursor batch} (h : Alike x y) : x.version = y.version := h.1

theorem hasNext_iff {x y : BatchCursor batch} (h : Alike x y) : x.HasNext ↔ y.HasNext := by
  unfold HasNext; rw [h.2.1, h.2.2.1]

theorem next {x y : BatchCursor batch} (h : Alike x y) (hx : x.HasNext) (hy : y.HasNext) :
    (x.next hx).1 = (y.next hy).1 ∧ Alike (x.next hx).2.val (y.next hy).2.val := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, h1, h2, by simp [BatchCursor.next, h3], h4, h5⟩
  simp only [BatchCursor.next, h3]

theorem setVersion {x y : BatchCursor batch} (h : Alike x y) (v : Version)
    {x' y' : BatchCursor batch} (hx : x.setVersion v = .ok x') (hy : y.setVersion v = .ok y') :
    Alike x' y' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold BatchCursor.setVersion at hx hy
  injection hx with hx
  injection hy with hy
  subst hx hy
  rw [h1]
  split <;> simp_all [Alike, BatchCursor.relex]

theorem discardRest {x y : BatchCursor batch} (h : Alike x y) :
    Alike x.discardRest y.discardRest :=
  ⟨h.1, h.2.2.1, h.2.2.1, h.2.2.2.1, rfl⟩

theorem category {x y : BatchCursor batch} (_ : Alike x y) (t : Token batch) :
    x.category t = y.category t := by
  simp only [BatchCursor.category, batch_eq_of_tag x y]

theorem content {x y : BatchCursor batch} (_ : Alike x y) (t : Token batch) :
    x.content t = y.content t := by
  simp only [BatchCursor.content, batch_eq_of_tag x y]

theorem consumedEndOf {x y o o' : BatchCursor batch} (h : Alike x y) (hx : x.Consumed o)
    (hy : y.Consumed o') : (Internal.consumedEndOf x) hx = (Internal.consumedEndOf y) hy := by
  simp only [Internal.consumedEndOf, batch_eq_of_tag x y, h.2.2.1]

theorem consumedSpanOf {x y o o' : BatchCursor batch} (h : Alike x y) (hx : x.Consumed o)
    (hy : y.Consumed o') : (Internal.consumedSpanOf x) hx = (Internal.consumedSpanOf y) hy := by
  simp only [Internal.consumedSpanOf, batch_eq_of_tag x y, h.2.2.1]

theorem span_peek {x y : BatchCursor batch} (h : Alike x y) (hx : x.HasNext)
    (hy : y.HasNext) : x.span (x.peek hx) = y.span (y.peek hy) := by
  simp only [BatchCursor.span, BatchCursor.peek, batch_eq_of_tag x y, h.2.2.1]

theorem relexRequested {x y : BatchCursor batch} (h : Alike x y) :
    (Internal.relexRequested x) = (Internal.relexRequested y) := h.2.2.2.1

theorem discardRequested {x y : BatchCursor batch} (h : Alike x y) :
    (Internal.discardRequested x) = (Internal.discardRequested y) := h.2.2.2.2

theorem resetConsumed_eq {x y : BatchCursor batch} (h : Alike x y) :
    (Internal.resetConsumed x) = (Internal.resetConsumed y) := by
  have hb := batch_eq_of_tag x y
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  cases x; cases y
  simp only at h1 h2 h3 h4 h5 hb
  subst h1 h2 h3 h4 h5 hb
  rfl

theorem foldConsumedCategories {x y : BatchCursor batch} (h : Alike x y) {β : Type} (init : β)
    (f : β → TokenCategory → β) :
    (Internal.foldConsumedCategories x) init f = (Internal.foldConsumedCategories y) init f := by
  simp only [Internal.foldConsumedCategories, batch_eq_of_tag x y, h.2.2.1]

theorem batch_eq {x y : BatchCursor batch} (_ : Alike x y) :
    BatchCursor.Internal.batch x = BatchCursor.Internal.batch y :=
  batch_eq_of_tag x y

/-- A cursor with a request made has no token left, if it had none left when the request was made:
the requests drop the tokens left. -/
theorem flags_hasNext {x : BatchCursor batch} (h : (Internal.relexRequested x) = false)
    (h' : (Internal.discardRequested x) = false) (v : Version) {x' : BatchCursor batch}
    (hx : x.setVersion v = .ok x') (hn : x'.HasNext) :
    (Internal.relexRequested x') = false ∧ (Internal.discardRequested x') = false := by
  unfold BatchCursor.setVersion at hx
  injection hx with hx
  subst hx
  split at hn
  · simp [HasNext, BatchCursor.relex] at hn
  · rename_i hc
    simp only [hc]
    exact ⟨h, h'⟩

end Internal.Alike

theorem discardRest_hasNext (x : BatchCursor batch) : ¬ x.discardRest.HasNext := by
  simp [HasNext, discardRest]

theorem relexRequested_next {x : BatchCursor batch} (hx : x.HasNext) :
    (Internal.relexRequested (x.next hx).2.val) = (Internal.relexRequested x) ∧
      (Internal.discardRequested (x.next hx).2.val) = (Internal.discardRequested x) :=
  ⟨rfl, rfl⟩

end BatchCursor

/- LEAN: not in Rust. The parts of a token's content, read without the content's slice, which is
made by a call that the compiler does not inline: for a reader of the bytes that needs no slice.
They are declared here, where the cursor's fields are visible. -/
namespace Internal

variable {batch : BatchTag}

/-- The bytes that the token's content is a slice of. -/
@[inline]
def contentBytes (cursor : BatchCursor batch) (_ : Token batch) : ByteArray :=
  cursor.batch.bytes

/-- Where the token's content starts in `contentBytes`. -/
@[inline]
def contentStart (cursor : BatchCursor batch) (token : Token batch) : Nat :=
  cursor.batch.contentStarts[token.index]'(Nat.lt_of_lt_of_le (cursor.lt_len token)
    cursor.batch.fit.1)

/-- Where the token's content stops in `contentBytes`. -/
@[inline]
def contentStop (cursor : BatchCursor batch) (token : Token batch) : Nat :=
  cursor.batch.contentStops[token.index]'(Nat.lt_of_lt_of_le (cursor.lt_len token)
    cursor.batch.fit.2.1)

/-- The content is the slice of its bytes between its start and its stop. -/
theorem content_eq_parts (cursor : BatchCursor batch) (token : Token batch) :
    cursor.content token =
      (contentBytes cursor token).toByteSlice (contentStart cursor token)
        (contentStop cursor token) :=
  (rfl)

end Internal

/- LEAN: a class is Lean's trait. The Rust associated types `Result` and `Error` are parameters
marked `outParam`: the consumer type determines them, as an `impl` determines associated types.
The method `consume` is in `ConsumeFrom` (`BSmtLib.Token.Cursor`), which is stated for a
producer. The Rust blanket `impl SmtConsume for &mut T` has no counterpart, as Lean has no
references. -/
/--
A sequential consumer of tokens, finishing with a value of type `R` and failing with an error
of type `E`.
-/
class Consume (H : Type) (R E : outParam Type) where
  /- LEAN: the Rust associated constant `IS_CONCRETE`; a field without a default, so that every
  consumer states it. -/
  /--
  Whether the consumer consumes whitespace and comments.

  If true, the consumer operates over concrete tokens:
  it can reconstruct the byte stream precisely thanks
  to the whitespace and comments. The caller must hand
  over the whitespace and comment tokens present between
  true syntactic tokens (unless the consumer specifically
  allows them to be omitted, as e.g. `LayoutTokenWriter`
  and `CompactTokenWriter` do).

  If false, the consumer operates over abstract tokens:
  it is not interested in whitespace and comments,
  and the caller must not hand them over for consumption.
  -/
  isConcrete : Bool

/- LEAN: Rust's `SmtRecover: SmtConsume`. The supertrait is the instance argument `Consume H R E`,
as for `ConsumeFrom`. The calls cannot fail, and run in the consumer's monad with its state. The
Rust blanket `impl SmtRecover for &mut T` has no counterpart, as Lean has no references. -/
/--
A token consumer that can recover after an error (EXPERIMENTAL).

This is an experimental feature for processing of SMT-LIB scripts
with error recovery: after an error, the current command is abandoned
and the lexer closes all open parentheses before announcing recovery.
If the command remains unclosed at the end of input, recovery is made
before the end of input is handed over (only the unclosed command is
abandoned and dropped).

Lexer recovery is implemented but experimental
since the exact semantics have not yet been set in stone.
It can change or be removed in any version and should not be used.
-/
class Recover (H : Type) (m : outParam (Type → Type)) {R E : outParam Type} [Consume H R E] where
  /--
  Abandons everything the consumer has not finished.

  Called when the input is lexically malformed or the consumer itself
  returns an error, before the failing call returns. The location is
  where the failure occurred: the input from there on is skipped, up
  to the location given to `recover`.

  The tokens consumed so far that belong to an unfinished top-level
  value (typically, an SMT-LIB command) are to be abandoned, as if
  they never were handed over.
  -/
  abandon : Span.Location → StateT H m Unit
  /--
  Finishes the recovery after abandoning.

  Called exactly once after every `abandon` before the
  new token is handed over after the recovery. The tokens handed over
  after the recovery are to be considered to follow the tokens before
  the abandoned top-level value started, as if the abandoned top-level
  value was never started. The input between abandonment and recovery
  is not handed over in any way.
  -/
  recover : Span.Location → StateT H m Unit

end BSmtLib.Token
