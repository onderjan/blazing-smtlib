module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Runs
import all BSmtLib.Lexer.Internal.Helpers
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Internal.WRustPort.Slice
import all BSmtLib.Span
import all BSmtLib.Lexer.Error

@[expose] public section

/-!
# The pieces of a slice and their locations

What the Rust port's steps over the pieces of a slice are compared with: the bytes of a piece
(`bytesOf_size`, `bytesOf_get!`, `stored_last`, `borrowed_last`), the bytes of a run
(`runEnd_mem`), the location of an index of the slice (`locOf`, `locAt_eq`, `LocAt.afterByte`,
`LocAt.afterColumns`, `LocAt.lineFeed`), the lexemes of the tokens on one line (`onLine_eq`,
`borrowedLexeme_eq`), and the naive lexer's steps at the end of a comment and on a run of
whitespace (`advance_comment_end`, `start_whitespaceRun`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure

open BSmtLib.Lexer.Internal.VNaive BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
open BSmtLib.Lexer.Internal.WRustPort.Slice (get? get)
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Basic

theorem afterByte_eq_afterColumns' (location : Span.Location) (c : UInt8) (h : c ≠ 10) :
    location.afterByte c = afterColumns location 1 := by
  rw [← afterColumns_afterByte location c h 0, afterColumns_zero]

/-! ## The bytes of a piece of a slice -/

theorem bytesOf_size (s : ByteSlice) {i j : Nat} (hij : i ≤ j) (hj : j ≤ s.size) :
    (bytesOf s i j).size = j - i := by
  show (bytesOf s i j).data.size = j - i
  have h2 := s.stop_le_size_byteArray
  simp only [ByteSlice.size] at hj
  simp only [ByteArray.size] at h2
  rw [data_bytesOf s hij hj, Array.size_extract]
  omega

theorem bytesOf_get! (s : ByteSlice) {i j k : Nat} (hij : i ≤ j) (hj : j ≤ s.size)
    (hk : i + k < j) : (bytesOf s i j).get! k = s[i + k]'(by omega) := by
  have h2 := s.stop_le_size_byteArray
  simp only [ByteSlice.size] at hj
  simp only [ByteArray.size] at h2
  show (bytesOf s i j).data[k]! = _
  rw [data_bytesOf s hij (by simp only [ByteSlice.size]; omega), getElem_slice]
  rw [getElem!_pos _ _ (by rw [Array.size_extract]; omega), Array.getElem_extract]
  congr 1
  omega

/-- Every byte of a run passes its test. -/
theorem runEnd_mem (s : ByteSlice) (P : UInt8 → Bool) (i : Nat) :
    ∀ k (hk : k < s.size), i ≤ k → k < runEnd s P i → P s[k] = true := by
  fun_induction runEnd s P i with
  | case1 i hi hp ih =>
    intro k hk hik hkr
    by_cases e : k = i
    · subst e; exact hp
    · exact ih k hk (by omega) hkr
  | case2 i hi hp => intro k hk hik hkr; omega
  | case3 i hi => intro k hk hik hkr; omega

theorem digit_facts (c : UInt8) :
    (!isDigit c || (!isWhitespace c && c != 40 && c != 41 && c != 59 && c != 35 && c != 34 &&
      c != 58 && c != 124)) = true :=
  byte_table (P := fun c => (!isDigit c || (!isWhitespace c && c != 40 && c != 41 && c != 59 &&
    c != 35 && c != 34 && c != 58 && c != 124)) = true) (by decide +kernel) c

/-- The last stored byte of a piece of a slice. -/
theorem stored_last (s : ByteSlice) {i j : Nat} (hij : i < j) (hj : j ≤ s.size) :
    lastOf (bytesOf s i j) = some (s[j - 1]'(by omega)) := by
  have hs := bytesOf_size s (Nat.le_of_lt hij) hj
  simp only [lastOf, hs, show (j - i == 0) = false by simp; omega,
    Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
  rw [bytesOf_get! s (Nat.le_of_lt hij) hj (k := j - i - 1) (by omega)]
  congr 1
  omega

/-- The last byte of a piece of a slice, borrowed from it. -/
theorem borrowed_last (s : ByteSlice) {i j : Nat} (hij : i < j) (hj : j ≤ s.size)
    (stored : Lexer.Internal.Helpers.ContentBuffer) :
    (Lexer.Internal.WRustPort.Slice.borrow s i j (Nat.le_of_lt hij) hj).last? stored = some
    (s[j - 1]'(by omega)) := by
  have h1 := s.stop_le_size_byteArray
  have h2 := s.start_le_stop
  have hj' := hj
  simp only [ByteSlice.size] at hj'
  simp only [Lexer.Internal.WRustPort.Slice.borrow, Lexer.Internal.Helpers.Content.last?,
    show ¬ (s.start + j = s.start + i) by omega, ↓reduceDIte, Option.some.injEq]
  rw [getElem_slice]
  congr 1
  omega

/-! ## Locations and the lexemes of tokens -/

/-- The location of the index of the slice, from the offset `offset` of the index `base`. -/
def locOf (c : WP.WCore) (offset base index : Nat) : Span.Location :=
  Span.Location.Internal.new (offset + (index - base)) c.line
    (offset + (index - base) - c.lineStart)

theorem locAt_eq {c : WP.WCore} {offset base index : Nat} {location : Span.Location}
    (h : LocAt c offset base index location) : location = locOf c offset base index := by
  obtain ⟨h1, h2, h3⟩ := h
  apply Span.Location.ext <;>
    simp only [locOf, Span.Location.Internal.offset_new, Span.Location.Internal.line_new,
      Span.Location.Internal.column_new] <;>
    omega

/-- A token on the line of the location of its start, with no line feed in it. -/
theorem onLine_eq {c : WP.WCore} {offset base i j : Nat} {location : Span.Location}
    (h : LocAt c offset base i location) (hi : base ≤ i) (hj : i ≤ j) (ty : Token.TokenCategory)
    (content : ByteSlice) :
    onLine ty content c.line c.lineStart (offset + (i - base)) (offset + (j - base)) =
      { category := ty, content := content.toByteArray, start := location,
        «end» := afterColumns location (j - i) } := by
  rw [locAt_eq h]
  obtain ⟨h1, h2, h3⟩ := h
  simp only [onLine, locOf, afterColumns, Lexeme.mk.injEq,
    Span.Location.Internal.new_inj, Span.Location.Internal.offset_new,
    Span.Location.Internal.line_new, Span.Location.Internal.column_new, true_and]
  omega

theorem get?_eq {s : ByteSlice} {i : Nat} {c : UInt8} (h : get? s i = some c) :
    ∃ hi : i < s.size, s[i] = c := by
  unfold get? at h
  split at h
  · exact ⟨‹_›, Option.some.inj h⟩
  · cases h

theorem bytesOf_one (s : ByteSlice) (i : Nat) (hi : i < s.size) :
    bytesOf s i (i + 1) = ByteArray.empty.push s[i] := by
  rw [bytesOf_push s (Nat.le_refl _) hi, bytesOf_self s i (Nat.le_of_lt hi)]

theorem _root_.BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree.LocAt.afterByte {c : WP.WCore}
    {offset base i : Nat} {location : Span.Location}
    (h : LocAt c offset base i location) (hb : base ≤ i) {b : UInt8} (hc : b ≠ 10) :
    LocAt c offset base (i + 1) (location.afterByte b) := by
  rw [Pure.afterByte_eq_afterColumns' _ _ hc]
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, ?_⟩ <;> simp only [afterColumns, Span.Location.Internal.offset_new,
    Span.Location.Internal.column_new] <;> omega

theorem _root_.BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree.LocAt.afterColumns {c : WP.WCore}
    {offset base i j : Nat} {location : Span.Location}
    (h : LocAt c offset base i location) (hb : base ≤ i) (hij : i ≤ j) :
    LocAt c offset base j (afterColumns location (j - i)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, ?_⟩ <;> simp only [Bytes.afterColumns, Span.Location.Internal.offset_new,
    Span.Location.Internal.column_new] <;> omega

theorem get_eq {s : ByteSlice} {i : Nat} (h : i < s.size) : Lexer.Internal.WRustPort.Slice.get s i
    h = s[i] := (rfl)

/-- The location after a line feed, on the line that the lexer state marked after it. -/
theorem _root_.BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree.LocAt.lineFeed {c c' : WP.WCore}
    {offset base i : Nat} {location : Span.Location}
    (h : LocAt c offset base i location) (hb : base ≤ i) (hl : c'.line = c.line + 1)
    (hs : c'.lineStart = offset + (i - base) + 1) :
    LocAt c' offset base (i + 1) (location.afterByte 10) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [afterByte_offset]; omega
  · show (if (10 : UInt8) == '\n'.toUInt8 then _ else _ : Span.Location).line = _
    simp only [show ((10 : UInt8) == '\n'.toUInt8) = true from rfl, ↓reduceIte,
      Span.Location.Internal.line_new]
    rw [hl, h2]
  · rw [afterByte_offset, hs]
    show _ + (if (10 : UInt8) == '\n'.toUInt8 then _ else _ : Span.Location).column = _
    simp only [show ((10 : UInt8) == '\n'.toUInt8) = true from rfl, ↓reduceIte,
      Span.Location.Internal.column_new]
    omega

theorem advance_comment_end (start : Span.Location) (content : ByteArray) (location : Span.Location)
    {c : UInt8} (hc : isCommentRun c = false) :
    advance false ⟨.comment, start, content⟩ location c = .idle := by
  simp only [isCommentRun, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hc
  rcases hc with h | h <;> subst h <;> rfl

/-- A token on the slow path, from the location of `i` to that of `j` on the same line. -/
theorem borrowedLexeme_eq {c : WP.WCore} {offset base i j : Nat} {location : Span.Location}
    (h : LocAt c offset base i location) (hi : base ≤ i) (hj : i ≤ j) (ty : Token.TokenCategory)
    (content : ByteSlice) :
    borrowedLexeme ty content (locOf c offset base i) c.line c.lineStart (offset + (j - base)) =
      ⟨ty, content.toByteArray, location, afterColumns location (j - i)⟩ := by
  rw [locAt_eq h]
  simp only [borrowedLexeme, locOf, afterColumns, Lexeme.mk.injEq,
    Span.Location.Internal.new_inj, Span.Location.Internal.offset_new,
    Span.Location.Internal.line_new, Span.Location.Internal.column_new, true_and]
  obtain ⟨h1, h2, h3⟩ := h
  omega

theorem start_whitespaceRun (v : Token.Version) (location : Span.Location) {c : UInt8}
    (h : isWhitespaceRun c = true) : start v false location c = .idle := by
  rw [start_space v false location c h]
  rfl

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure
