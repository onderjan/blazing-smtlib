module

public import Std.Data.ByteSlice
public import BSmtLib.ControlFlow
public import BSmtLib.Span
public import BSmtLib.Lexicon.Value
public import BSmtLib.Version
public import BSmtLib.Lexicon.Reserved

public section

/-!
# Syntax tokens and classes for their manipulation

A token is one unit of SMT-LIB input, e.g. `(`, `|quoted|`, or `"string"`. It is also a natural
point around which **BSmtLib** is split: token consumers implement `Consume` and `ConsumeFrom`
over a token cursor type that implements `Cursor`, and token producers call
`ConsumeFrom.consume`, giving it the cursor to consume tokens from.

The most important producer in the library is `Lexer`, but `TokensCursor` or a custom cursor
can also be used. `Consume` is implemented by `Parser.ParseAdapter` and `Writer`.

`Token` itself is an enumeration over lexical categories with a view into their content, with
the end of file marker (EOF) represented as a token to simplify the API. Whitespace and comments
are also `Token` categories, and a `Consume` implementation can choose whether those should be
passed through via `Consume.isConcrete`. This can be used e.g. for pretty-printing while
preserving comments.

The cursor methods do not return `Token` directly, but values of type `Cursor.Token`, so that
consumers implementing `ConsumeFrom` for a specific cursor type can use its additional token
information, e.g. the span of a `Lexer.Cursor.LexerToken`, which `LexerCursor.span` gives. The
tokens can be converted to syntax tokens using `Cursor.syntax`. For sanity, the cursor must make
sure that the tokens produced are valid under its version in force announced by
`Cursor.version`, e.g. unquoted `lambda` must be produced as `Token.symbol` in SMT-LIB 2.6, but
`Token.reserved` in SMT-LIB 2.7. See `Cursor` for further information.
-/

/- LEAN: the public items of the Rust crate are in the namespace `BSmtLib`, without the prefix
`Smt`: `SmtToken` is `BSmtLib.Token`. The internals of the lexer are in `BSmtLib.Lexer`.
Variant and function names follow Lean conventions (`TokenCategory.parenOpen` for
`SmtTokenCategory::ParenOpen`, `lastConsumed` for `last_consumed`). An `inductive` without
fields is a Rust enum. -/
namespace BSmtLib.Token

/--
Category of a token.

The category does not depend on the version: simple symbols and reserved words are both
`TokenCategory.unquotedSymbol`.
-/
inductive TokenCategory where
  /-- Opening parenthesis (`(`). -/
  | parenOpen
  /-- Closing parenthesis (`)`). -/
  | parenClose
  /-- Numeral, e.g. `0` or `42`. -/
  | numeral
  /-- Decimal, e.g. `0.5` or `3.14`. -/
  | decimal
  /-- Hexadecimal, e.g. `#xA04`. -/
  | hexadecimal
  /-- Binary, e.g. `#b0101`. -/
  | binary
  /-- String literal, e.g. `"hello"` or `""`. -/
  | string
  /-- Keyword, e.g. `:named`. -/
  | keyword
  /-- Unquoted symbol (simple symbol or reserved word), e.g. `x`, `+`, `let` or `check-sat`. -/
  | unquotedSymbol
  /-- Quoted symbol, e.g. `|a b|` or `|let|`. -/
  | quotedSymbol
  /-- Whitespace, e.g. the space in `(assert p)`. -/
  | whitespace
  /-- Comment, e.g. `; note`. -/
  | comment
  /--
  End of file (EOF).

  Marks the end of the input.
  -/
  | endOfFile
  deriving BEq, Hashable, Repr, Inhabited

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

/- LEAN: not inlined. Inlined into the lexer's loop, the compiler does not reuse the batch's
cell: every token frees the old cell and allocates a new one. As a call of its own, the cell is
updated in place when nothing else refers to it. -/
/--
Appends a token with the type, its content from `contentStart` to `contentStop` in `bytes`,
and the span given by the numbers of its two locations. The token starts at or after the end
of the last one, and has a byte unless it is the end of file.
-/
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

namespace Internal.TokenBatch

/-- A read of a byte array within it is the checked read. -/
theorem get!_eq_getElem (array : ByteArray) {index : Nat} (h : index < array.size) :
    array.get! index = array[index] := by
  obtain ⟨data⟩ := array
  exact getElem!_pos data index h

end Internal.TokenBatch

/- LEAN: Rust's `SmtVersionRefused`, without the prefix. -/
/--
Error due to a refused version switch.

Returned by `Cursor.setVersion`.
-/
structure VersionRefused where
  deriving BEq, Hashable, Repr, Inhabited

@[no_expose] instance : ToString VersionRefused := ⟨fun _ => "version switch refused"⟩

/- LEAN: a class is Lean's trait. The Rust associated types `Result` and `Error` are parameters
marked `outParam`: the consumer type determines them, as an `impl` determines associated types.
The method `consume` is in `ConsumeFrom` (`BSmtLib.Token.Cursor`), which is stated for a
producer. The Rust blanket `impl SmtConsume for &mut T` has no counterpart, as Lean has no
references. -/
/--
Consumes tokens sequentially.

`ConsumeFrom` defines the actual consumption function from a given
cursor. The consumer returns a result of type `R` on success and an error of type `E` on
failure.

The most important consumer implemented in the library is `Parser.ParseAdapter`.
-/
class Consume (H : Type) (R E : outParam Type) where
  /- LEAN: the Rust associated constant `IS_CONCRETE`; a field without a default, so that every
  consumer states it. -/
  /--
  Whether the consumer consumes whitespace and comments.

  If `true`, the consumer operates over concrete tokens:
  it can reconstruct the byte stream precisely thanks
  to the whitespace and comments. The caller must hand
  over the whitespace and comment tokens present between
  true syntactic tokens (unless the consumer specifically
  allows them to be omitted, as e.g. `Writer` does).

  If `false`, the consumer operates over abstract tokens:
  it is not interested in whitespace and comments,
  and the caller must not hand them over for consumption.
  -/
  isConcrete : Bool

/- LEAN: Rust's `SmtToken`, the token as the library views it. The token of the lexer, which
names its batch, is `Lexer.Cursor.LexerToken`. -/
/--
View of a syntax token.

Unlike `Token.TokenCategory`, a syntax token depends on the version: an unquoted symbol that
is a reserved word in the version is `Token.reserved`, and every other symbol is
a `Token.symbol`.
-/
inductive _root_.BSmtLib.Token where
  /-- Opening parenthesis (`(`). -/
  | parenOpen
  /-- Closing parenthesis (`)`). -/
  | parenClose
  /-- Numeral, e.g. `0` or `42`. -/
  | numeral (value : Lexicon.Value.Numeral)
  /-- Decimal, e.g. `0.5` or `3.14`. -/
  | decimal (value : Lexicon.Value.Decimal)
  /-- Hexadecimal, e.g. `#xA04`. -/
  | hexadecimal (value : Lexicon.Value.HexDigits)
  /-- Binary, e.g. `#b0101`. -/
  | binary (value : Lexicon.Value.BinDigits)
  /-- String literal, e.g. `"hello"` or `""`. -/
  | string (value : Lexicon.Value.StringContent)
  /-- Keyword, e.g. `:named`. -/
  | keyword (value : Lexicon.Value.Keyword)
  /--
  Symbol (quoted or unquoted), e.g. `x`, `+` or `|a b|`.

  A quoted symbol is a symbol even if its content is a reserved word, such as `|let|`, and
  so is a word reserved only in later versions, such as `lambda` before version 2.7.
  -/
  | symbol (value : Lexicon.Value.Symbol)
  /-- Reserved word, e.g. `let`, `_`, `check-sat`, or `lambda` from version 2.7. -/
  | reserved (value : Lexicon.Reserved)
  /-- Whitespace, e.g. the space in `(assert p)`. -/
  | whitespace (value : Lexicon.Value.Whitespace)
  /-- Comment, e.g. `; note`. -/
  | comment (value : Lexicon.Value.Comment)
  /--
  End of file (EOF).

  Marks the end of the input.
  -/
  | endOfFile
  deriving Repr

section

open BSmtLib.Lexicon.Value

/- LEAN: Rust's `from_lexer_token(token, version)` reads the token's category and content, which
a Lean token keeps in its batch; this takes them read already, so that a cursor and a lookahead
window view their tokens alike. `Token.fromLexerToken` is declared with the cursor. -/
/-- Creates the token kind from the category and the content of a token, and the version. -/
@[inline]
def Internal.fromParts (category : TokenCategory) (content : ByteSlice)
    (version : Version) : Token :=
  match category with
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral => .numeral (Numeral.Internal.newUnchecked content)
  | .decimal => .decimal (Decimal.Internal.newUnchecked content)
  | .hexadecimal => .hexadecimal (HexDigits.Internal.newUnchecked content)
  | .binary => .binary (BinDigits.Internal.newUnchecked content)
  | .unquotedSymbol =>
    -- only the words reserved in the version are reserved words
    match Lexicon.Reserved.fromBytes? content version with
    | some word => .reserved word
    | none => .symbol (Symbol.Internal.newUnchecked false content)
  | .quotedSymbol => .symbol (Symbol.Internal.newUnchecked true content)
  | .string => .string (StringContent.Internal.newUnchecked content)
  | .keyword => .keyword (Keyword.Internal.newUnchecked content)
  | .whitespace => .whitespace (Whitespace.Internal.newUnchecked content)
  | .comment => .comment (Comment.Internal.newUnchecked content)
  | .endOfFile => .endOfFile

end

end BSmtLib.Token

/- LEAN: Rust's `SmtWriteError` and its cause are in `writer`; they are declared here, in the
namespace of the writer, as `Token.writeSmt` fails with them and the writer's module imports
this one. -/
namespace BSmtLib.Writer

/-- Why writing failed (I/O error or a reserved word not in the version). -/
inductive WriteErrorKind where
  /-- Writing to the writer failed. -/
  | io (error : IO.Error)
  /--
  The reserved word is not reserved in the version written in.

  There is no way to write the reserved word, as its text would be read as a symbol,
  e.g. the reserved word `lambda` in SMT-LIB 2.6.
  -/
  | notInVersion (reserved : Lexicon.Reserved)

/- LEAN: Rust's derived `Debug`. Lean's `IO.Error` has no `Repr`, so an I/O error is shown by its
message. -/
@[no_expose] instance : Repr WriteErrorKind where
  reprPrec kind prec :=
    let app (name : String) (argument : Std.Format) : Std.Format :=
      Repr.addAppParen (.group (.nest 2 (.text ("BSmtLib.Writer.WriteErrorKind." ++ name) ++
        .line ++ argument))) prec
    match kind with
    | .io error => app "io" (reprArg (toString error))
    | .notInVersion reserved => app "notInVersion" (reprArg reserved)

/- LEAN: the constructor is private, as Rust's field is. The field is readable as `error.kind`,
replacing the getters `kind` and `into_kind`. -/
/-- Error that forced writing to stop. -/
structure WriteError where
  private mk ::
  /-- Returns the kind of the error. -/
  kind : WriteErrorKind
  deriving Repr

/- LEAN: Rust builds the error from its cause in the crate, where its field is visible. -/
/-- The error of the cause. -/
@[inline]
def WriteError.Internal.new (kind : WriteErrorKind) : WriteError := ⟨kind⟩

@[no_expose] instance : ToString WriteErrorKind where
  toString
    | .io error => s!"I/O: {error}"
    | .notInVersion reserved => s!"`{reserved.asStr}` is not reserved in written version"

@[no_expose] instance : ToString WriteError := ⟨fun self => toString self.kind⟩

end BSmtLib.Writer

namespace BSmtLib.Token

/-- The bytes of the slice appended. -/
private def appendSlice (out : ByteArray) (bytes : ByteSlice) : ByteArray :=
  out ++ bytes.toByteArray

/- LEAN: the text that `writeSmt` writes, appended to `out`, or the reserved word that is not in
the version; `writeSmt` writes it in one piece. -/
/-- The token as SMT-LIB text in the version, appended to `out`. -/
def Internal.appendSmt (self : Token) (out : ByteArray) (version : Version) :
    Except Lexicon.Reserved ByteArray :=
  match self with
  | .parenOpen => .ok (out.push (byte! '('))
  | .parenClose => .ok (out.push (byte! ')'))
  | .numeral digits => .ok (appendSlice out digits.asSlice)
  | .decimal text => .ok (appendSlice out text.asSlice)
  | .hexadecimal digits =>
    .ok (appendSlice ((out.push (byte! '#')).push (byte! 'x')) digits.asSlice)
  | .binary digits => .ok (appendSlice ((out.push (byte! '#')).push (byte! 'b')) digits.asSlice)
  | .string content =>
    let body := content.asSlice.toByteArray.foldl (init := out.push (byte! '"')) fun out c =>
      if version == .v2_0 then
        -- SMT-LIB 2.0: a double quote and a backslash are escaped by a backslash
        -- for sanity, always escape backslashes, even if not strictly needed
        -- e.g. in \q, the backslash does not technically need to be escaped
        if c == byte! '"' || c == byte! '\\' then (out.push (byte! '\\')).push c else out.push c
      else
        -- SMT-LIB 2.5+: a double quote is escaped by another double quote
        if c == byte! '"' then (out.push c).push c else out.push c
    .ok (body.push (byte! '"'))
  | .keyword name => .ok (appendSlice (out.push (byte! ':')) name.asSlice)
  | .symbol name =>
    -- a simple symbol that is a reserved word in the version
    -- would be read as the reserved word, quote it to keep the symbol
    if name.isQuoted || (Lexicon.Reserved.fromBytes? name.asSlice version).isSome then
      .ok ((appendSlice (out.push (byte! '|')) name.asSlice).push (byte! '|'))
    else
      .ok (appendSlice out name.asSlice)
  | .reserved word =>
    -- the reserved word is not in the version
    -- there is no way to write it
    if word.isInVersion version then .ok (out ++ word.asStr.toUTF8) else .error word
  | .whitespace bytes => .ok (appendSlice out bytes.asSlice)
  | .comment text => .ok (appendSlice (out.push (byte! ';')) text.asSlice)
  | .endOfFile => .ok out

/- LEAN: Rust's `writer` is any `Write`; here an `IO.FS.Stream`, as the reader reads one
(`Reader.BufReader.new`). The token is written in one call of the stream's `write`, where Rust
writes it in pieces; the end of the input, which Rust writes in none, calls no `write`. -/
/--
Writes the token as SMT-LIB text in the given version.

Only the token is written, without delimiters. A symbol that spells a reserved word of the
version is written quoted, so that it is read back as a symbol, e.g. `|lambda|` in SMT-LIB
2.7. In SMT-LIB 2.0, every backslash in a string is written escaped, e.g. `"a\\q"` for the
content `a\q`.

Returns an error if the token is a reserved word that is not reserved in the given version,
or if writing fails.
-/
def writeSmt {n : Type → Type} [Monad n] [MonadLiftT IO n] (self : Token)
    (writer : IO.FS.Stream) (version : Version) : n (Except Writer.WriteError Unit) := do
  -- the end of the input has no text, and the writer is not called for it
  if let .endOfFile := self then return .ok ()
  match Internal.appendSmt self ByteArray.empty version with
  | .error word => return .error ⟨.notInVersion word⟩
  | .ok bytes =>
    let written : IO (Except IO.Error Unit) := (writer.write bytes).toBaseIO
    match ← written with
    | .error err => return .error ⟨.io err⟩
    | .ok () => return .ok ()

end BSmtLib.Token
