module

public import BSmtLib.Facts.Proofs.Lexer.VNaive.Run
public import BSmtLibSpec.Facts.Proofs.Lexicon.Unique
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# Facts about the bytes and locations of the naive lexer

The byte classes of `VNaive` as the classes of character codes of the spec and its checks,
and the locations the lexer computes byte by byte as the spec's `locate`.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaive.Facts

open BSmtLibSpec.Lexicon BSmtLibSpec.Regex
open BSmtLibSpec (Regex)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Lexer.Internal.VNaive
open BSmtLibSpec.Facts.Proofs.Lexicon.Lemmas BSmtLibSpec.Facts.Proofs.Lexicon.Unique

/-! ## Byte classes -/

/-- A property of every byte, from the property of every byte code. -/
theorem byte_cases {P : UInt8 → Prop} (h : ∀ n, n < 256 → P (UInt8.ofNat n)) (c : UInt8) :
    P c := by
  have := h c.toNat c.toNat_lt
  simpa using this

theorem beq_iff_toNat {c d : UInt8} : (c == d) = true ↔ c.toNat = d.toNat := by
  rw [beq_iff_eq]
  exact ⟨fun h => h ▸ rfl, fun h => UInt8.toNat_inj.mp h⟩

theorem isWhitespace_iff (c : UInt8) :
    isWhitespace c = true ↔ (c.toNat = 9 ∨ c.toNat = 10 ∨ c.toNat = 13 ∨ c.toNat = 32) :=
  byte_cases (P := fun c => isWhitespace c = true ↔
    (c.toNat = 9 ∨ c.toNat = 10 ∨ c.toNat = 13 ∨ c.toNat = 32)) (by decide +kernel) c

theorem isDelimiter_iff (c : UInt8) : isDelimiter c = true ↔ Delim c.toNat :=
  byte_cases (P := fun c => isDelimiter c = true ↔ Delim c.toNat)
    (by unfold Delim; decide +kernel) c

theorem isDigit_iff (c : UInt8) : isDigit c = true ↔ IsDigit c.toNat :=
  byte_cases (P := fun c => isDigit c = true ↔ IsDigit c.toNat)
    (by unfold IsDigit; decide +kernel) c

theorem isSymbolByte_iff (c : UInt8) : isSymbolByte c = true ↔ SymChar c.toNat :=
  byte_cases (P := fun c => isSymbolByte c = true ↔ SymChar c.toNat)
    (by unfold SymChar IsDigit; decide +kernel) c

theorem isTextByte_iff (c : UInt8) :
    isTextByte c = true ↔
      (32 ≤ c.toNat ∧ c.toNat ≤ 126 ∨ 128 ≤ c.toNat ∧ c.toNat ≤ 255) ∨
        (c.toNat = 9 ∨ c.toNat = 10 ∨ c.toNat = 13 ∨ c.toNat = 32) :=
  byte_cases (P := fun c => isTextByte c = true ↔
    (32 ≤ c.toNat ∧ c.toNat ≤ 126 ∨ 128 ≤ c.toNat ∧ c.toNat ≤ 255) ∨
      (c.toNat = 9 ∨ c.toNat = 10 ∨ c.toNat = 13 ∨ c.toNat = 32)) (by decide +kernel) c

theorem isHexDigit_iff (c : UInt8) :
    isHexDigit c = true ↔
      (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 70) ∨
        (97 ≤ c.toNat ∧ c.toNat ≤ 102) :=
  byte_cases (P := fun c => isHexDigit c = true ↔
    (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 70) ∨
      (97 ≤ c.toNat ∧ c.toNat ≤ 102)) (by decide +kernel) c

theorem isBinaryDigit_iff (c : UInt8) : isBinaryDigit c = true ↔ c.toNat = 48 ∨ c.toNat = 49 :=
  byte_cases (P := fun c => isBinaryDigit c = true ↔ c.toNat = 48 ∨ c.toNat = 49)
    (by decide +kernel) c

/-- A text byte is a printable or white space character of the spec. -/
theorem text_iff (c : UInt8) : isTextByte c = true ↔ alt printableChar whiteSpaceChar [c] := by
  rw [isTextByte_iff, printableOrSpace_one]

theorem whitespace_iff (c : UInt8) : isWhitespace c = true ↔ whiteSpaceChar [c] := by
  rw [isWhitespace_iff, whiteSpaceChar_one]

theorem symbolByte_iff (c : UInt8) :
    isSymbolByte c = true ↔ altAll [letter, digit, symbolPunctuation] [c] := by
  rw [isSymbolByte_iff, simpleSymbolChar_one]
  have e : (chars "~!@$%^&*_-+=<>.?/").map UInt8.toNat =
      [126, 33, 64, 36, 37, 94, 38, 42, 95, 45, 43, 61, 60, 62, 46, 63, 47] := by decide
  constructor
  · intro h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ?_)
      rw [← e] at h
      obtain ⟨d, hd, hdc⟩ := List.mem_map.mp h
      rw [show c = d from UInt8.toNat_inj.mp hdc.symm]
      exact hd
  · intro h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ?_)
      rw [← e]
      exact List.mem_map_of_mem h

theorem digit_iff (c : UInt8) : isDigit c = true ↔ digit [c] := by
  rw [isDigit_iff, IsDigit, digit, range_one]

theorem hexDigit_iff (c : UInt8) :
    isHexDigit c = true ↔ altAll [digit, Regex.range 65 70, Regex.range 97 102] [c] := by
  rw [isHexDigit_iff]
  simp [Regex.altAll, digit, range_one]

theorem binaryDigit_iff (c : UInt8) : isBinaryDigit c = true ↔ Regex.oneOf "01" [c] := by
  rw [isBinaryDigit_iff, oneOf_one]
  have e : chars "01" = [48, 49] := rfl
  rw [e]
  constructor
  · rintro (h | h)
    · exact List.mem_cons.mpr (Or.inl (UInt8.toNat_inj.mp h))
    · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr (UInt8.toNat_inj.mp h)))
  · intro h
    rcases List.mem_cons.mp h with h | h
    · exact Or.inl (h ▸ rfl)
    · exact Or.inr ((List.mem_singleton.mp h) ▸ rfl)

theorem lineBreak_iff (c : UInt8) :
    ((c == 10) || (c == 13)) = true ↔ LineBreak c.toNat := by
  simp only [Bool.or_eq_true, beq_iff_toNat, LineBreak]
  rfl

/-! ## Locations -/

/-- The location after the bytes, from `location`. -/
def advanceLoc (location : Span.Location) (bytes : List UInt8) : Span.Location :=
  bytes.foldl Span.Location.afterByte location

/-- The location after the bytes, from the start of the input. -/
def locAfter (bytes : List UInt8) : Span.Location :=
  advanceLoc Span.Location.initial bytes

theorem advanceLoc_append (location : Span.Location) (a b : List UInt8) :
    advanceLoc location (a ++ b) = advanceLoc (advanceLoc location a) b := by
  simp [advanceLoc, List.foldl_append]

theorem locAfter_append (a b : List UInt8) : locAfter (a ++ b) = advanceLoc (locAfter a) b :=
  advanceLoc_append _ a b

theorem locAfter_concat (a : List UInt8) (c : UInt8) :
    locAfter (a ++ [c]) = (locAfter a).afterByte c := by
  simp [locAfter_append, advanceLoc]

/-- The location after the bytes is where the spec locates their end. -/
theorem toLocation_locAfter (bytes : List UInt8) :
    Lexer.Adapters.toLocation (locAfter bytes) = BSmtLibSpec.Lexer.locate bytes bytes.length := by
  suffices h : ∀ rs : List UInt8,
      Lexer.Adapters.toLocation (locAfter rs.reverse) = BSmtLibSpec.Lexer.locate rs.reverse
          rs.reverse.length by
    simpa using h bytes.reverse
  intro rs
  induction rs with
  | nil => rfl
  | cons c rs ih =>
    simp only [List.reverse_cons]
    generalize rs.reverse = bs at ih ⊢
    rw [locAfter_concat]
    simp only [Lexer.Adapters.toLocation, BSmtLibSpec.Lexer.locate, List.take_length] at ih ⊢
    simp only [BSmtLibSpec.Lexer.Location.mk.injEq] at ih
    obtain ⟨h1, h2, h3⟩ := ih
    have h10 : '\n'.toUInt8 = 10 := rfl
    simp only [Span.Location.afterByte, Span.Location.afterColumn, h10]
    by_cases hc : c = 10
    · subst hc
      simp [h1, h2, List.count_append]
    · have hb : (c == 10) = false := by simpa using hc
      simp [hb, h1, h2, h3, List.count_append, hc]

/-- Where the spec locates an offset depends only on the input up to it. -/
theorem locate_append (bytes more : List UInt8) :
    BSmtLibSpec.Lexer.locate (bytes ++ more) bytes.length = BSmtLibSpec.Lexer.locate bytes
        bytes.length := by
  simp [BSmtLibSpec.Lexer.locate]

/-- The location after the bytes, as the spec locates it in an input that starts with them. -/
theorem toLocation_locAfter_append (bytes more : List UInt8) :
    Lexer.Adapters.toLocation (locAfter bytes) = BSmtLibSpec.Lexer.locate
        (bytes ++ more) bytes.length := by
  rw [locate_append, toLocation_locAfter]

theorem feedBytes_location {version : Token.Version} {st st' : St}
    {location location' : Span.Location}
    {bytes : List UInt8} {ls : List Lexeme}
    (h : feedBytes version st location bytes = some (st', location', ls)) :
    location' = advanceLoc location bytes := by
  induction bytes generalizing st location ls st' location' with
  | nil =>
    simp only [feedBytes, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
    rfl
  | cons c bytes ih =>
    simp only [feedBytes] at h
    split at h
    · simp at h
    · obtain ⟨⟨st'', location'', ls'⟩, hf, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      rw [ih hf]
      rfl

end BSmtLib.Facts.Proofs.Lexer.VNaive.Facts
