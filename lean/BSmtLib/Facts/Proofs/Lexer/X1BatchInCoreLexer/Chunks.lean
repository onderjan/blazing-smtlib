module

public import BSmtLib.Facts.Proofs.Lexer.Simulation
public import BSmtLibSpec.Lexicon.Properties
import all BSmtLib.Lexer

@[expose] public section

/-!
# The library's lexer on a slice too large for its positions

The library's lexer lexes a slice whose end is not below `USize.size` chunk by chunk
(`Internal.lexChunks`): it copies each chunk into an array of its own and lexes it as a slice of
its own, as `lexSliceStep` lexes a slice that ends below `USize.size` (`Internal.lexSliceFitting`).

This module cuts a slice into the chunks that `lexChunks` lexes (`cut`), and every slice of a
list that is too large (`cutAll`), with the same bytes (`flatten_cutAll`). It also states a chunk
as `lexChunks` makes it: the slice of the bytes of the chunk, which ends below `USize.size`
(`chunk_eq`, `chunk_stop_lt`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Chunks


/-! ### The chunks -/

/-- The chunk of the input from `p` on, as `lexChunks` lexes it. -/
def chunkAt (s : BSmtLibSpec.Regex.Chars) (p : Nat) : BSmtLibSpec.Regex.Chars :=
  (s.drop p).take BSmtLib.Lexer.Internal.CHUNK_SIZE

/-- The chunks of the input from `p` on. -/
def chunksFrom (s : BSmtLibSpec.Regex.Chars) (p : Nat) : List BSmtLibSpec.Regex.Chars :=
  if p < s.length then chunkAt s p :: chunksFrom s (p + BSmtLib.Lexer.Internal.CHUNK_SIZE) else []
termination_by s.length - p
decreasing_by simp only [BSmtLib.Lexer.Internal.CHUNK_SIZE]; omega

/-- The input cut into slices that are not too large for the library's lexer: itself if it is
not, and its chunks if it is. -/
def cut (s : BSmtLibSpec.Regex.Chars) : List BSmtLibSpec.Regex.Chars :=
  if s.length < USize.size then [s] else chunksFrom s 0

theorem flatten_chunksFrom (s : BSmtLibSpec.Regex.Chars) (p : Nat) :
    (chunksFrom s p).flatten = s.drop p := by
  fun_induction chunksFrom s p with
  | case1 p hp ih =>
    rw [List.flatten_cons, ih, chunkAt, ← List.drop_drop, List.take_append_drop]
  | case2 p hp =>
    simp only [List.flatten_nil]
    exact (List.drop_eq_nil_of_le (by omega)).symm

theorem flatten_cut (s : BSmtLibSpec.Regex.Chars) : (cut s).flatten = s := by
  unfold cut
  split
  · simp
  · rw [flatten_chunksFrom, List.drop_zero]

theorem length_chunkAt (s : BSmtLibSpec.Regex.Chars) (p : Nat) :
    (chunkAt s p).length ≤ BSmtLib.Lexer.Internal.CHUNK_SIZE := by
  simp only [chunkAt, List.length_take]; omega

theorem chunk_lt_size : BSmtLib.Lexer.Internal.CHUNK_SIZE < USize.size := by
  have := USize.le_size
  simp only [BSmtLib.Lexer.Internal.CHUNK_SIZE]
  omega

theorem toByteSlice_byteArray (a : ByteArray) : a.toByteSlice.byteArray = a := by
  simp [ByteArray.toByteSlice, ByteSlice.byteArray]

theorem toByteSlice_start (a : ByteArray) : a.toByteSlice.start = 0 := by
  simp [ByteArray.toByteSlice, ByteSlice.start]

theorem toByteSlice_stop (a : ByteArray) : a.toByteSlice.stop = a.size := by
  simp [ByteArray.toByteSlice, ByteSlice.stop]

theorem toByteSlice_size (a : ByteArray) : a.toByteSlice.size = a.size := by
  simp [ByteSlice.size, toByteSlice_start, toByteSlice_stop]

theorem toByteArray_chunkAt (s : BSmtLibSpec.Regex.Chars) (p : Nat) :
    (chunkAt s p).toByteArray =
      s.toByteArray.extract (0 + p) (min (0 + p + BSmtLib.Lexer.Internal.CHUNK_SIZE)
          s.toByteArray.size) := by
  apply ByteArray.ext
  rw [List.data_toByteArray, ByteArray.data_extract, List.data_toByteArray]
  apply Array.toList_inj.mp
  simp only [List.toList_toArray, Array.toList_extract, List.extract_eq_take_drop, chunkAt,
    List.size_toByteArray, Nat.zero_add]
  apply List.take_eq_take_iff.mpr
  simp only [List.length_drop]
  omega

/-- Every slice of the list cut, as `cut` cuts it. -/
def cutAll (slices : List BSmtLibSpec.Regex.Chars) : List BSmtLibSpec.Regex.Chars :=
  slices.flatMap cut

theorem flatten_cutAll (slices : List BSmtLibSpec.Regex.Chars) :
    (cutAll slices).flatten = slices.flatten := by
  induction slices with
  | nil => rfl
  | cons s rest ih =>
    rw [cutAll, List.flatMap_cons, List.flatten_append, ← cutAll, ih, flatten_cut,
      List.flatten_cons]

/-! ### The chunks as slices -/

theorem stop_toByteSlice (a : ByteArray) : a.toByteSlice.stop = a.size := by
  simp [ByteArray.toByteSlice, ByteSlice.stop]

/-- The view of the chunk of the bytes of the input from `p` on, as `lexChunks` makes it. -/
theorem chunk_eq (s : BSmtLibSpec.Regex.Chars) (p : Nat) :
    (s.toByteArray.toByteSlice.byteArray.extract (s.toByteArray.toByteSlice.start + p)
      (min (s.toByteArray.toByteSlice.start + p + BSmtLib.Lexer.Internal.CHUNK_SIZE)
        s.toByteArray.toByteSlice.stop)).toByteSlice =
      (chunkAt s p).toByteArray.toByteSlice := by
  rw [toByteArray_chunkAt, toByteSlice_byteArray, toByteSlice_start, toByteSlice_stop]

theorem chunk_stop_lt (s : BSmtLibSpec.Regex.Chars) (p : Nat) :
    (chunkAt s p).toByteArray.toByteSlice.stop < USize.size := by
  rw [stop_toByteSlice, List.size_toByteArray]
  exact Nat.lt_of_le_of_lt (length_chunkAt s p) chunk_lt_size

end BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Chunks
