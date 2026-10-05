import BSmtLib.Spec.Lexicon

/-!
# Lemmas for checking the spec

Facts about the combinators that make the checks short. Not trusted: everything here is
proved.
-/

namespace BSmtLib.SpecChecks.Lexicon

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Lexicon.Regex

theorem range_one {lo hi : Nat} {c : UInt8} : range lo hi [c] ↔ lo ≤ c.toNat ∧ c.toNat ≤ hi := by
  simp [range]

theorem oneOf_one {s : String} {c : UInt8} : oneOf s [c] ↔ c ∈ chars s := by
  simp [oneOf]

theorem lit_iff {s : String} {x : Chars} : lit s x ↔ x = chars s := Iff.rfl

theorem litOneOf_iff {ws : List String} {x : Chars} : litOneOf ws x ↔ x ∈ ws.map chars := by
  simp [litOneOf, eq_comm]

theorem seq_intro {r q : Regex} {a b : Chars} (ha : r a) (hb : q b) : seq r q (a ++ b) :=
  ⟨a, b, rfl, ha, hb⟩

theorem star_parts {r : Regex} (parts : List Chars) (h : ∀ p ∈ parts, r p) :
    star r parts.flatten :=
  ⟨parts, rfl, h⟩

theorem flatten_singletons (s : Chars) : (s.map ([·])).flatten = s := by
  induction s with
  | nil => rfl
  | cons c s ih => simp [ih]

theorem star_each {r : Regex} {s : Chars} (h : ∀ c ∈ s, r [c]) : star r s := by
  refine ⟨s.map ([·]), (flatten_singletons s).symm, ?_⟩
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact h c hc

theorem plus_each {r : Regex} {c : UInt8} {s : Chars} (hc : r [c]) (h : ∀ x ∈ s, r [x]) :
    plus r (c :: s) :=
  seq_intro (a := [c]) hc (star_each h)

theorem startsWith_range {lo hi : Nat} {c : UInt8} {s : Chars} :
    startsWith (range lo hi) (c :: s) ↔ lo ≤ c.toNat ∧ c.toNat ≤ hi := by
  constructor
  · rintro ⟨a, b, h, ⟨d, rfl, h₁, h₂⟩, -⟩
    simp only [List.singleton_append, List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨h₁, h₂⟩
  · intro h
    exact ⟨[c], s, rfl, ⟨c, rfl, h⟩, trivial⟩

theorem startsWith_lit_one {c d : UInt8} {s : Chars} (w : String) (hw : chars w = [d]) :
    startsWith (lit w) (c :: s) ↔ c = d := by
  constructor
  · rintro ⟨a, b, h, ha, -⟩
    rw [lit_iff, hw] at ha
    subst ha
    simp only [List.singleton_append, List.cons.injEq] at h
    exact h.1
  · rintro rfl
    exact ⟨[c], s, rfl, hw.symm, trivial⟩

/-- The single-character classes, unfolded down to comparisons of codes. -/
theorem simpleSymbolChar_one {c : UInt8} :
    altAll [letter, digit, symbolPunctuation] [c] ↔
      (65 ≤ c.toNat ∧ c.toNat ≤ 90 ∨ 97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨
      (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ c ∈ chars "~!@$%^&*_-+=<>.?/" := by
  simp [altAll, letter, digit, symbolPunctuation, alt, range_one, oneOf_one]

theorem printableOrSpace_one {c : UInt8} :
    alt printableChar whiteSpaceChar [c] ↔
      (32 ≤ c.toNat ∧ c.toNat ≤ 126 ∨ 128 ≤ c.toNat ∧ c.toNat ≤ 255) ∨
      (c.toNat = 9 ∨ c.toNat = 10 ∨ c.toNat = 13 ∨ c.toNat = 32) := by
  simp [alt, printableChar, whiteSpaceChar, altAll, code, range_one]
  omega

theorem spaceOrPrintable_one {c : UInt8} :
    alt whiteSpaceChar printableChar [c] ↔ alt printableChar whiteSpaceChar [c] := by
  simp [alt, or_comm]

/-- A simple symbol in the version, from the checks its definition asks for. -/
theorem simpleSymbol_of {version : Version} {c : UInt8} {s : Chars}
    (hchars : ∀ x ∈ c :: s, altAll [letter, digit, symbolPunctuation] [x])
    (hdigit : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57))
    (hreserved : c :: s ∉ (basicReservedWords version ++ commandNames version).map chars) :
    simpleSymbol version (c :: s) := by
  refine ⟨⟨plus_each (hchars c (by simp)) (fun x hx => hchars x (by simp [hx])), ?_⟩, ?_⟩
  · rw [digit, startsWith_range]
    exact hdigit
  · rw [reserved, litOneOf_iff]
    exact hreserved

end BSmtLib.SpecChecks.Lexicon

namespace BSmtLib.SpecChecks.Lexicon

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Lexicon.Regex

theorem whiteSpaceChar_one {c : UInt8} :
    whiteSpaceChar [c] ↔ c.toNat = 9 ∨ c.toNat = 10 ∨ c.toNat = 13 ∨ c.toNat = 32 := by
  simp [whiteSpaceChar, altAll, code, range_one]
  omega

theorem delimited_by {category : Category} {c : UInt8} {more : Chars}
    (h : whiteSpaceChar [c] ∨ oneOf "();" [c]) : Delimited category (c :: more) :=
  Or.inr (Or.inr (Or.inr ⟨c, more, rfl, h⟩))

theorem whitespace_spaces {s : Chars} (h : ∀ c ∈ s, c.toNat = 32) : whitespace s :=
  star_each fun c hc => Or.inl (whiteSpaceChar_one.mpr (Or.inr (Or.inr (Or.inr (h c hc)))))

theorem whitespace_nil : whitespace [] := star_parts [] (by simp)

end BSmtLib.SpecChecks.Lexicon

namespace BSmtLib.SpecChecks.Lexicon

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Lexicon.Regex

/-- A part of the body of a string literal from 2.5 on, checked by computation. -/
def stringPartOk (p : Chars) : Bool :=
  p == [34, 34] || match p with
    | [c] => c != 34 && (32 ≤ c.toNat && c.toNat ≤ 126 || 128 ≤ c.toNat ||
        c.toNat == 9 || c.toNat == 10 || c.toNat == 13)
    | _ => false

theorem stringPart_of_ok {p : Chars} (h : stringPartOk p = true) :
    alt (minus (alt printableChar whiteSpaceChar) (lit "\"")) (lit "\"\"") p := by
  by_cases hq : p = [34, 34]
  · subst hq
    exact Or.inr (show [34, 34] = chars "\"\"" by decide)
  · left
    match p, h, hq with
    | [c], h, _ =>
      have hc : ¬c = 34 ∧ ((((32 ≤ c.toNat ∧ c.toNat ≤ 126 ∨ 128 ≤ c.toNat) ∨
          c.toNat = 9) ∨ c.toNat = 10) ∨ c.toNat = 13) := by
        simpa [stringPartOk] using h
      refine ⟨printableOrSpace_one.mpr ?_, ?_⟩
      · have := c.toNat_lt
        omega
      · intro heq
        have h2 : c = '"'.toUInt8 := by simpa [lit_iff, chars] using heq
        have : c = 34 := by rw [h2]; decide
        exact hc.1 this
    | [], h, _ => simp [stringPartOk] at h
    | _ :: _ :: _, h, hq => simp_all [stringPartOk]

end BSmtLib.SpecChecks.Lexicon

