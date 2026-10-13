import BSmtLib.Proofs.VNaive

/-!
# Runs and bytes of a slice, cursors and contents

What the Rust port's run scans are compared with: the end of a run of bytes that pass a test
(`runEnd`), the bytes of a slice between two indices (`bytesOf`), the location after a run of
bytes other than line feeds (`afterColumns`), and the byte classes of the runs that a token in
progress takes as they are. The naive lexer's step `advance` takes each byte of such a run as it
is (`advance_*_run`), and its step `start` starts the tokens of the fast paths as stated by
`start_symbol`, `start_space` and `start_quoted`.

A step of a cursor keeps its batch and its requests (`intoBatch_next`, `version_next`,
`discard_next`, `relex_next`), and the lookup of reserved words reads only the bytes of a content
(`fromBytes_toByteArray`). A step of the Rust port that consumes the bytes from one index to
another is compared with the naive lexer's pure run by an equation between the run from the first
index and the run from the second, with the lexemes finished between them before it (`Prep`).
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open VNaive BSmtLib.Proofs.Simulation

/-! ## Runs -/

/-- The index of the first byte from `i` on that does not pass `p`, the size of the slice if
none. -/
def runEnd (slice : ByteSlice) (p : UInt8 → Bool) (i : Nat) : Nat :=
  if h : i < slice.size then
    if p slice[i] then runEnd slice p (i + 1) else i
  else
    i
termination_by slice.size - i

theorem le_runEnd (slice : ByteSlice) (p : UInt8 → Bool) (i : Nat) : i ≤ runEnd slice p i := by
  fun_induction runEnd slice p i <;> omega

theorem runEnd_le (s : ByteSlice) (p : UInt8 → Bool) (i : Nat) (h : i ≤ s.size) :
    runEnd s p i ≤ s.size := by
  fun_induction runEnd s p i <;> omega

theorem runEnd_stop (s : ByteSlice) (p : UInt8 → Bool) (i : Nat) (h : runEnd s p i < s.size) :
    p s[runEnd s p i] = false := by
  fun_induction runEnd s p i with
  | case1 i hi hp ih => exact ih h
  | case2 i hi hp => simpa using hp
  | case3 i hi => omega

theorem runEnd_start (s : ByteSlice) (p : UInt8 → Bool) (i : Nat) (h : i < runEnd s p i) :
    ∃ hi : i < s.size, p s[i] = true := by
  rw [runEnd] at h
  split at h
  · rename_i hi
    split at h
    · rename_i hp; exact ⟨hi, hp⟩
    · omega
  · omega

theorem runEnd_succ (s : ByteSlice) (p : UInt8 → Bool) (i : Nat) (hi : i < s.size)
    (hp : p s[i] = true) : runEnd s p i = runEnd s p (i + 1) := by
  rw [runEnd]; simp only [hi, dite_true, hp, ite_true]

/-! ## Bytes -/

/-- The bytes of the slice from `i` to `j`. -/
def bytesOf (slice : ByteSlice) (i j : Nat) : ByteArray :=
  (slice.slice i j).toByteArray

theorem data_bytesOf (s : ByteSlice) {i j : Nat} (hij : i ≤ j) (hj : j ≤ s.size) :
    (bytesOf s i j).data = s.byteArray.data.extract (s.start + i) (s.start + j) := by
  have h1 := s.stop_le_size_byteArray
  have h2 := s.start_le_stop
  simp only [ByteSlice.size] at hj
  have ei : min i (s.stop - s.start) = i := by omega
  have ej : min j (s.stop - s.start) = j := by omega
  simp only [bytesOf, ByteSlice.slice, ByteSlice.size, ei, ej]
  split
  · split
    · simp only [ByteSlice.toByteArray, ByteSlice.byteArray, ByteSlice.start, ByteSlice.size,
        ByteSlice.stop, ByteArray.data_extract]
      congr 1; omega
    · omega
  · omega

theorem bytesOf_self (s : ByteSlice) (i : Nat) (h : i ≤ s.size) : bytesOf s i i = .empty := by
  apply ByteArray.ext
  rw [data_bytesOf s (Nat.le_refl _) h]
  rw [show ByteArray.empty.data = #[] from rfl, Array.extract_eq_empty_iff]
  omega

theorem bytesOf_push (s : ByteSlice) {i j : Nat} (hij : i ≤ j) (hj : j < s.size) :
    bytesOf s i (j + 1) = (bytesOf s i j).push s[j] := by
  apply ByteArray.ext
  rw [ByteArray.data_push, data_bytesOf s hij (Nat.le_of_lt hj), data_bytesOf s (by omega) hj,
    getElem_slice]
  have h1 := start_add_lt s hj
  have h3 : s.byteArray.size = s.byteArray.data.size := rfl
  apply Array.ext
  · simp; omega
  · intro k hk1 hk2
    simp only [Array.size_extract, Array.size_push] at hk1 hk2
    rw [Array.getElem_extract, Array.getElem_push]
    split
    · rw [Array.getElem_extract]
    · rename_i hk
      have e : min (s.start + j) s.byteArray.data.size = s.start + j := Nat.min_eq_left (by omega)
      simp only [Array.size_extract, e] at hk
      congr 1
      omega

theorem push_append_bytesOf (x : ByteArray) (s : ByteSlice) {i j : Nat} (hi : i < s.size)
    (hij : i < j) (hj : j ≤ s.size) :
    x.push s[i] ++ bytesOf s (i + 1) j = x ++ bytesOf s i j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + 1 + k := ⟨j - (i + 1), by omega⟩
  induction k with
  | zero =>
    rw [Nat.add_zero, bytesOf_self s _ hj, bytesOf_push s (Nat.le_refl _) (by omega),
      bytesOf_self s _ (by omega)]
    apply ByteArray.ext
    simp
  | succ k ih =>
    have e := congrArg ByteArray.data (ih (by omega) (by omega))
    rw [← Nat.add_assoc, bytesOf_push s (by omega) (by omega),
      bytesOf_push s (by omega) (by omega)]
    apply ByteArray.ext
    simp only [ByteArray.data_append, ByteArray.data_push] at e ⊢
    rw [Array.append_push, Array.append_push, e]

/-- A cleared content buffer extended from positions in the slice's array holds the bytes of the
slice between them. -/
theorem contentBytes_clear_extendSlice (buf : BSmtLib.Lexer.ContentBuffer) (input : ByteSlice)
    {a b : Nat} (hb : b ≤ input.size) :
    contentBytes (buf.clear.extendFrom input.byteArray (input.start + a) (input.start + b)) =
      (input.slice a b).toByteArray := by
  rw [contentBytes_extendSlice input (fits_clear buf) (.inl hb), contentBytes_clear,
    empty_append]

/-- A cleared content buffer extended from positions in the slice's array fits its array. -/
theorem fits_clear_extendSlice (buf : BSmtLib.Lexer.ContentBuffer) (input : ByteSlice)
    {a b : Nat} (hb : b ≤ input.size) :
    Fits (buf.clear.extendFrom input.byteArray (input.start + a) (input.start + b)) :=
  fits_extendSlice input (fits_clear buf) (.inl hb)

/-! ## Locations -/

/-- The location `n` bytes after `location`, none of which is a line feed. -/
def afterColumns (location : Location) (n : Nat) : Location :=
  { offset := location.offset + n, line := location.line, column := location.column + n }

theorem afterColumns_zero (location : Location) : afterColumns location 0 = location := rfl

theorem afterColumns_afterByte (location : Location) (c : UInt8) (h : c ≠ 10) (n : Nat) :
    afterColumns (location.afterByte c) n = afterColumns location (n + 1) := by
  unfold Location.afterByte
  split
  · rename_i hc
    exact absurd (beq_iff_eq.mp hc) h
  · simp only [afterColumns, Location.afterColumn]
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm 1 n]

/-! ## Byte classes of runs -/

/-- Whether the byte is a part of a quoted symbol that is not acted on: any byte of its content
but the line feed. -/
def isQuotedRun (c : UInt8) : Bool :=
  isTextByte c && c != byte! '|' && c != byte! '\\' && c != byte! '\n'

/-- Whether the byte is a part of a string from version 2.5 on that is not acted on: any byte
of its content but the quote and the line feed. -/
def isStringRun (c : UInt8) : Bool :=
  isTextByte c && c != byte! '"' && c != byte! '\n'

/-- Whether the byte is a part of a string under version 2.0 that is not acted on: any byte of
its content but the quote, the backslash and the line feed. -/
def isLegacyStringRun (c : UInt8) : Bool :=
  isTextByte c && c != byte! '"' && c != byte! '\\' && c != byte! '\n'

/-- Whether the byte is a part of a comment that is not acted on: any byte but a line break. -/
def isCommentRun (c : UInt8) : Bool :=
  c != byte! '\n' && c != byte! '\r'

/-- Whether the byte is a part of whitespace that is not acted on: whitespace but the line
feed. -/
def isWhitespaceRun (c : UInt8) : Bool :=
  isWhitespace c && c != byte! '\n'

theorem isDigit_ne (c : UInt8) (hc : isDigit c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem isSymbolByte_ne (c : UInt8) (hc : isSymbolByte c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem isQuotedRun_ne (c : UInt8) (hc : isQuotedRun c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem isStringRun_ne (c : UInt8) (hc : isStringRun c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem isLegacyStringRun_ne (c : UInt8) (hc : isLegacyStringRun c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem isCommentRun_ne (c : UInt8) (hc : isCommentRun c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem isWhitespaceRun_ne (c : UInt8) (hc : isWhitespaceRun c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem allows_ne (radix : Radix) (c : UInt8) (hc : radix.allows c = true) : c ≠ 10 := by
  intro h; subst h; cases radix <;> exact absurd hc (by decide)

/-! ## The naive lexer's steps over a run -/

theorem advance_numeral_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = (.numeral false)) (hc : isDigit c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance]

theorem advance_fraction_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = (.fraction true)) (hc : isDigit c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance]

theorem advance_digits_run (radix : Radix) (ws : Bool) (q : Pending) (location : Location)
    (c : UInt8)
    (hm : q.mode = (.digits radix)) (hc : radix.allows c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance, Radix.allows]

theorem advance_keyword_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .keyword) (hc : isSymbolByte c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance]

theorem advance_simpleSymbol_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .simpleSymbol) (hc : isSymbolByte c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance]

theorem advance_quotedSymbol_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .quotedSymbol) (hc : isQuotedRun c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance, isQuotedRun]

theorem advance_string_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .string) (hc : isStringRun c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance, isStringRun]

theorem advance_legacyString_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .legacyString) (hc : isLegacyStringRun c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance, legacyStringByte, isLegacyStringRun]

theorem advance_comment_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .comment) (hc : isCommentRun c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance, isCommentRun]

theorem symbol_facts_bool (c : UInt8) :
    (!(isSymbolByte c && !isDigit c) || (!isWhitespace c && c != 40 && c != 41 && c != 59 &&
      c != 35 && c != 34 && c != 58 && c != 124)) = true :=
  byte_cases (P := fun c => (!(isSymbolByte c && !isDigit c) || (!isWhitespace c && c != 40 &&
    c != 41 && c != 59 && c != 35 && c != 34 && c != 58 && c != 124)) = true)
    (by decide +kernel) c

theorem start_symbol (version : Version) (ws : Bool) (location : Location) (c : UInt8)
    (hs : isSymbolByte c = true) (hd : isDigit c = false) :
    start version ws location c = .pending ⟨.simpleSymbol, location, ByteArray.empty.push c⟩ := by
  have := symbol_facts_bool c
  simp only [hs, hd, Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := this
  simp [start, h1, h2, h3, h4, h5, h6, h7, h8, hs, hd]

theorem start_space (version : Version) (ws : Bool) (location : Location) (c : UInt8)
    (hs : isWhitespaceRun c = true) :
    start version ws location c =
      if ws then .pending ⟨.whitespace, location, ByteArray.empty.push c⟩ else .idle := by
  have : isWhitespace c = true := by simp_all [isWhitespaceRun]
  simp [start, this]

theorem start_quoted (version : Version) (ws : Bool) (location : Location) :
    start version ws location 124 = .pending ⟨.quotedSymbol, location, .empty⟩ := rfl

/-! ## Cursors -/

section

open BSmtLib.Lexer.Internal (intoBatch)

variable {g : BatchTag}

theorem intoBatch_next (c : BatchCursor g) (h : c.HasNext) :
    intoBatch (c.next h).2.1 = intoBatch c := rfl

theorem version_next (c : BatchCursor g) (h : c.HasNext) :
    (c.next h).2.1.version = c.version := rfl

theorem discard_next (c : BatchCursor g) (h : c.HasNext) :
    (c.next h).2.1.discardRequested = c.discardRequested := rfl

theorem relex_next (c : BatchCursor g) (h : c.HasNext) :
    (c.next h).2.1.relexRequested = c.relexRequested := rfl

end

/-! ## Contents -/

theorem ofUInt8_toUInt8 (c : TokenCategory) : TokenCategory.ofUInt8 c.toUInt8 = c := by
  cases c <;> rfl

theorem reservedSlot_toByteArray (s : ByteSlice) (h : 0 < s.toByteArray.toByteSlice.size) :
    Reserved.Internal.reservedSlot s.toByteArray.toByteSlice h =
      Reserved.Internal.reservedSlot s (by rwa [size_toByteArray_toByteSlice] at h) := by
  apply Fin.ext
  simp only [Reserved.Internal.reservedSlot, getElem_toByteArray, size_toByteArray_toByteSlice]

theorem slotOf_toByteArray (s : ByteSlice) : slotOf s.toByteArray.toByteSlice = slotOf s := by
  unfold slotOf
  by_cases h : 0 < s.size
  · have h' : 0 < s.toByteArray.toByteSlice.size := by rwa [size_toByteArray_toByteSlice]
    rw [dite_eq_left_of_eq_true (eq_true h'), dite_eq_left_of_eq_true (eq_true h),
      reservedSlot_toByteArray]
  · have h' : ¬ 0 < s.toByteArray.toByteSlice.size := by rwa [size_toByteArray_toByteSlice]
    simp only [h, h', dite_false]

/-- The lookup of reserved words reads only the bytes of the slice. -/
theorem fromBytes_toByteArray (s : ByteSlice) (v : Version) :
    Reserved.fromBytes? s.toByteArray.toByteSlice v = Reserved.fromBytes? s v := by
  by_cases h0 : s.size = 0
  · have h0' : s.toByteArray.toByteSlice.size = 0 := by rw [size_toByteArray_toByteSlice]; exact h0
    simp only [Reserved.fromBytes?, h0, h0', dite_true]
  · have h0' : s.toByteArray.toByteSlice.size ≠ 0 := by rw [size_toByteArray_toByteSlice]; exact h0
    rw [fromBytes_eq _ _ h0', fromBytes_eq _ _ h0, slotOf_toByteArray]
    simp only [beq_toByteArray]

/-! ## The run with lexemes before it -/

/-- The run with the lexemes `ls` before the ones it finishes, also before an error. -/
abbrev Prep (ls : List Lexeme) (e : Except (List Lexeme) (St × Location × List Lexeme)) :
    Except (List Lexeme) (St × Location × List Lexeme) :=
  withBefore ls e

theorem prep_nil (e : Except (List Lexeme) (St × Location × List Lexeme)) : Prep [] e = e :=
  withBefore_nil e

theorem prep_prep (ls ls' : List Lexeme) (e : Except (List Lexeme) (St × Location × List Lexeme)) :
    Prep ls (Prep ls' e) = Prep (ls ++ ls') e :=
  withBefore_withBefore ls ls' e

end BSmtLib.Proofs.Lexer.VNaiveWRustPort
