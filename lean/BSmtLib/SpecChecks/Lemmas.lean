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

namespace BSmtLib.SpecChecks.Lexicon

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Lexicon.Regex

/-! ## Taking matches apart -/

/-- A match of `seq (lit w) q` is the characters of `w` followed by a match of `q`. -/
theorem seq_lit {w : String} {q : Regex} {s : Chars} (h : seq (lit w) q s) :
    ∃ b, s = chars w ++ b ∧ q b := by
  obtain ⟨a, b, rfl, rfl, hb⟩ := h
  exact ⟨b, rfl, hb⟩

/-- When every match of `r` is a single character with the property `P`, every character of
a match of `r` has it. -/
theorem single_mem {r : Regex} {P : UInt8 → Prop} (h : ∀ p, r p → ∃ c, p = [c] ∧ P c) :
    ∀ p, r p → ∀ x ∈ p, P x := by
  intro p hp x hx
  obtain ⟨c, rfl, hc⟩ := h p hp
  rw [List.mem_singleton] at hx
  exact hx ▸ hc

/-- A match of `oneOf s` is one character, whose code is the code of a character of `s`. -/
theorem oneOf_inv {s : String} {p : Chars} (h : oneOf s p) :
    ∃ c, p = [c] ∧ c.toNat ∈ (chars s).map UInt8.toNat := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c, rfl, List.mem_map_of_mem hc⟩

/-- Every character of a match of `star r` is a character of some match of `r`. -/
theorem star_mem {r : Regex} {P : UInt8 → Prop} (h : ∀ p, r p → ∀ x ∈ p, P x) {s : Chars}
    (hs : star r s) : ∀ x ∈ s, P x := by
  obtain ⟨parts, rfl, hparts⟩ := hs
  intro x hx
  obtain ⟨p, hp, hxp⟩ := List.mem_flatten.mp hx
  exact h p (hparts p hp) x hxp

/-- Every character of a match of `plus r` is a character of some match of `r`. -/
theorem plus_mem {r : Regex} {P : UInt8 → Prop} (h : ∀ p, r p → ∀ x ∈ p, P x) {s : Chars}
    (hs : plus r s) : ∀ x ∈ s, P x := by
  obtain ⟨a, b, rfl, ha, hb⟩ := hs
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h a ha x hx
  · exact star_mem h hb x hx

/-- A match of `star r` is empty, or a non-empty match of `r` followed by a match of
`star r`. -/
theorem star_cases {r : Regex} {s : Chars} (hs : star r s) :
    s = [] ∨ ∃ p t, s = p ++ t ∧ p ≠ [] ∧ r p ∧ star r t := by
  obtain ⟨parts, rfl, hparts⟩ := hs
  induction parts with
  | nil => exact Or.inl rfl
  | cons p ps ih =>
    have hps : ∀ q ∈ ps, r q := fun q hq => hparts q (List.mem_cons_of_mem _ hq)
    by_cases hp : p = []
    · subst hp
      simpa using ih hps
    · exact Or.inr ⟨p, ps.flatten, rfl, hp, hparts p (by simp), ps, rfl, hps⟩

/-- Two sequences of characters outside the class `E`, each followed by a character of `E`,
are equal when one input starts with both: the first character of `E` ends them. -/
theorem sep_eq {E : UInt8 → Prop} {b₁ b₂ y₁ y₂ : Chars} {e₁ e₂ : UInt8}
    (hb₁ : ∀ x ∈ b₁, ¬ E x) (hb₂ : ∀ x ∈ b₂, ¬ E x) (he₁ : E e₁) (he₂ : E e₂)
    (h : b₁ ++ e₁ :: y₁ = b₂ ++ e₂ :: y₂) : b₁ = b₂ := by
  induction b₁ generalizing b₂ with
  | nil =>
    cases b₂ with
    | nil => rfl
    | cons x xs =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ he₁) (hb₂ x (by simp))
  | cons x xs ih =>
    cases b₂ with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ he₂) (hb₁ x (by simp))
    | cons x' xs' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rw [ih (fun y hy => hb₁ y (by simp [hy])) (fun y hy => hb₂ y (by simp [hy])) h]

/-- Two matches of `star r` that one input starts with, each followed by a character of the
class `E`, are equal when the matches of `r` are non-empty, none is a proper prefix of
another and none starts with a character of `E`: the first character of `E` at the start
of a part ends them. -/
theorem star_terminated {r : Regex} {E : UInt8 → Prop}
    (hne : ∀ p, r p → p ≠ [])
    (hfree : ∀ p q x y, r p → r q → p ++ x = q ++ y → p = q)
    (hstart : ∀ p c t, r p → p = c :: t → ¬ E c)
    {b₁ b₂ y₁ y₂ : Chars} {e₁ e₂ : UInt8} (h₁ : star r b₁) (h₂ : star r b₂)
    (he₁ : E e₁) (he₂ : E e₂) (h : b₁ ++ e₁ :: y₁ = b₂ ++ e₂ :: y₂) : b₁ = b₂ := by
  obtain ⟨ps, rfl, hps⟩ := h₁
  induction ps generalizing b₂ with
  | nil =>
    rcases star_cases h₂ with rfl | ⟨q, t, rfl, hq, hqr, -⟩
    · rfl
    · obtain ⟨c, u, rfl⟩ := List.exists_cons_of_ne_nil hq
      simp only [List.flatten_nil, List.nil_append, List.cons_append, List.append_assoc,
        List.cons.injEq] at h
      exact absurd (h.1 ▸ he₁) (hstart _ c u hqr rfl)
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hps' : ∀ q ∈ ps, r q := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    rcases star_cases h₂ with rfl | ⟨q, t, rfl, -, hqr, ht⟩
    · obtain ⟨c, u, hcu⟩ := List.exists_cons_of_ne_nil (hne p hp)
      subst hcu
      simp only [List.flatten_cons, List.nil_append, List.cons_append, List.append_assoc,
        List.cons.injEq] at h
      exact absurd (h.1 ▸ he₂) (hstart _ c u hp rfl)
    · simp only [List.flatten_cons, List.append_assoc] at h ⊢
      obtain rfl := hfree p q _ _ hp hqr h
      rw [ih ht hps' (List.append_cancel_left h)]

end BSmtLib.SpecChecks.Lexicon

