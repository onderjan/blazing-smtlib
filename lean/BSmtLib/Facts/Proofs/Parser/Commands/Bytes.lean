module

public import BSmtLib.Facts.Proofs.Parser.Term
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Token
import all Std.Data.ByteSlice
import all Init.Data.String.Defs

@[expose] public section

/-!
# Bytes compared with a string's, and versions

The parser compares a token's bytes with a string's UTF-8 bytes (`not`, `smt-lib-version`, the
numbers of the versions); the bridge reads a view's bytes as a list. A byte array's list is its
data's, and two byte arrays are equal as `==` says exactly when their lists are.
-/

namespace BSmtLib.Facts.Proofs.Parser.Commands.Bytes

open BSmtLibSpec.Grammar
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Parser.Command.Internal.Standard.Symbol BSmtLib.Plain

theorem ByteArray.toList_loop_eq (a : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop a i r = r.reverse ++ a.data.toList.drop i := by
  induction i, r using ByteArray.toList.loop.induct a with
  | case1 i r h ih =>
    rw [ByteArray.toList.loop]
    simp only [h, ↓reduceIte]
    rw [ih]
    have h' : i < a.data.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons h']
    have h'' : i < a.data.size := h
    simp [ByteArray.get!, getElem!_pos a.data i h'']
  | case2 i r h =>
    rw [ByteArray.toList.loop]
    simp only [h, ↓reduceIte]
    have h' : a.data.toList.length ≤ i := by simp; omega
    simp [List.drop_eq_nil_of_le h']

theorem ByteArray.toList_eq_data (a : ByteArray) : a.toList = a.data.toList := by
  simp [ByteArray.toList, ByteArray.toList_loop_eq]

theorem ByteArray.beq_eq_decide (a b : ByteArray) : (a == b) = decide (a.toList = b.toList) := by
  rw [ByteArray.toList_eq_data, ByteArray.toList_eq_data]
  show (a.data == b.data) = _
  cases h : decide (a.data.toList = b.data.toList)
  · have h := of_decide_eq_false h
    rw [Bool.eq_false_iff]
    intro hbeq
    exact h (Array.toList_inj.mpr (beq_iff_eq.mp hbeq))
  · exact beq_iff_eq.mpr (Array.toList_inj.mp (of_decide_eq_true h))

/-- A view against a string's bytes, as the bridge reads the view. -/
theorem slice_beq_utf8 (bytes : ByteSlice) (s : String)
    (hutf8 : s.toUTF8.toList = BSmtLibSpec.Regex.chars s) :
    (bytes.toByteArray == s.toUTF8) = decide (Bridge.chars bytes = BSmtLibSpec.Regex.chars s) := by
  rw [ByteArray.beq_eq_decide, hutf8]
  rfl

theorem toByteArray_toByteSlice (a : ByteArray) : a.toByteSlice.toByteArray = a := by
  simp only [ByteArray.toByteSlice, Nat.le_refl, ↓reduceDIte, Nat.zero_le, ByteSlice.toByteArray,
    ByteSlice.size]
  show a.extract 0 (0 + (a.size - 0)) = a
  simp

/-- A view against a view of a string's bytes, as the bridge reads the first view. -/
theorem slice_beq_slice_utf8 (bytes : ByteSlice) (s : String)
    (hutf8 : s.toUTF8.toList = BSmtLibSpec.Regex.chars s) :
    (bytes == s.toUTF8.toByteSlice) = decide (Bridge.chars bytes = BSmtLibSpec.Regex.chars s) := by
  show ByteSlice.beq _ _ = _
  unfold ByteSlice.beq
  rw [toByteArray_toByteSlice]
  exact slice_beq_utf8 bytes s hutf8

theorem utf8_not : "not".toUTF8.toList = BSmtLibSpec.Regex.chars "not" := by
  rw [ByteArray.toList_eq_data]; decide

theorem utf8_smtLibVersion :
    "smt-lib-version".toUTF8.toList = BSmtLibSpec.Regex.chars "smt-lib-version" := by
  rw [ByteArray.toList_eq_data]; decide

theorem utf8_2_0 : "2.0".toUTF8.toList = BSmtLibSpec.Regex.chars "2.0" := by
  rw [ByteArray.toList_eq_data]; decide
theorem utf8_2_5 : "2.5".toUTF8.toList = BSmtLibSpec.Regex.chars "2.5" := by
  rw [ByteArray.toList_eq_data]; decide
theorem utf8_2_6 : "2.6".toUTF8.toList = BSmtLibSpec.Regex.chars "2.6" := by
  rw [ByteArray.toList_eq_data]; decide
theorem utf8_2_7 : "2.7".toUTF8.toList = BSmtLibSpec.Regex.chars "2.7" := by
  rw [ByteArray.toList_eq_data]; decide

/-- A symbol the spec names `not` is `not` to the literal parser. -/
theorem Symbol.isNot_of_name {s : Nodes.Symbol} (h :
    (Bridge.symbol s).name = BSmtLibSpec.Regex.chars "not") :
    (isNot s) = true := by
  unfold Parser.Command.Internal.Standard.Symbol.isNot
  rw [slice_beq_utf8 _ _ utf8_not]
  exact decide_eq_true h

/-- The parser's test for `smt-lib-version` is the spec's. -/
theorem isVersionKeyword_eq (k : KeywordView) :
    Parser.Command.Internal.Standard.isVersionKeyword k = decide
        (Bridge.keyword k = BSmtLibSpec.Regex.chars "smt-lib-version") := by
  unfold Parser.Command.Internal.Standard.isVersionKeyword
  exact slice_beq_utf8 _ _ utf8_smtLibVersion

/-- The library reads the number of a version as the spec does. -/
theorem fromDecimal_eq (d : ByteSlice) :
    Token.Version.fromDecimal? d = (versionOfNumber (Bridge.chars d)).map Bridge.libVersion := by
  unfold Token.Version.fromDecimal?
  rw [slice_beq_slice_utf8 _ _ utf8_2_0, slice_beq_slice_utf8 _ _ utf8_2_5,
    slice_beq_slice_utf8 _ _ utf8_2_6, slice_beq_slice_utf8 _ _ utf8_2_7]
  simp only [versionOfNumber, List.find?, versionNumber]
  by_cases h0 : Bridge.chars d = BSmtLibSpec.Regex.chars "2.0"
  · simp [h0, Bridge.libVersion]
  by_cases h5 : Bridge.chars d = BSmtLibSpec.Regex.chars "2.5"
  · simp +decide [h5, Bridge.libVersion]
  by_cases h6 : Bridge.chars d = BSmtLibSpec.Regex.chars "2.6"
  · simp +decide [h6, Bridge.libVersion]
  by_cases h7 : Bridge.chars d = BSmtLibSpec.Regex.chars "2.7"
  · simp +decide [h7, Bridge.libVersion]
  simp [h0, h5, h6, h7, Ne.symm h0, Ne.symm h5, Ne.symm h6, Ne.symm h7]

/-! ## Versions -/

theorem versionAtLeast_v2_7_of_ge {version : Token.Version} (h : version ≥ .v2_7) :
    versionAtLeast (Bridge.version version) .v2_7 := by
  cases version <;> simp_all [versionAtLeast, Bridge.version, BSmtLibSpec.Lexicon.Version.upTo] <;>
    exact absurd h (by decide)

end BSmtLib.Facts.Proofs.Parser.Commands.Bytes
