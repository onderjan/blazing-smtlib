import BSmtLib.SpecChecks.Lemmas

/-!
# Every input has at most one tokenisation

A proof of the property `Unique`. The induction over `TokenizationFrom` in
`tokenizationFrom_unique` takes one token at a time:

- `ws_eq` shows that the whitespace before a token is determined: a token starts with a
  character that cannot start whitespace, and the comments in whitespace end at their first
  line break.
- `not_atEnd` shows that whitespace at the end of the input cannot be followed by a token.
- `token_eq` shows that the token's characters and category are determined: `text_eq` finds
  its characters by the class of its first character, and `kind_spec` computes its category
  from its characters.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Lexicon

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Lexicon.Regex

/-! ## Classes of character codes -/

/-- The code of a character that may follow a token other than a parenthesis: a white space
character, a parenthesis or `;`. -/
def Delim (n : Nat) : Prop := n = 9 ∨ n = 10 ∨ n = 13 ∨ n = 32 ∨ n = 40 ∨ n = 41 ∨ n = 59

/-- The code of a character that whitespace may start with: a white space character or the
`;` of a comment. -/
def WsStart (n : Nat) : Prop := n = 9 ∨ n = 10 ∨ n = 13 ∨ n = 32 ∨ n = 59

instance (n : Nat) : Decidable (WsStart n) := by
  unfold WsStart
  infer_instance

theorem ite_no {α : Type} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by
  simp [h]

theorem ite_yes {α : Type} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by
  simp [h]

/-- The code of a line-breaking character. -/
def LineBreak (n : Nat) : Prop := n = 10 ∨ n = 13

/-- The code of a character that may occur in a numeral, a decimal, a hexadecimal, a binary,
a simple symbol, a keyword or a reserved word: one that is not a delimiter, `"` or `|`. -/
def AtomChar (n : Nat) : Prop := ¬ Delim n ∧ n ≠ 34 ∧ n ≠ 124

instance (n : Nat) : Decidable (AtomChar n) := by
  unfold AtomChar Delim
  infer_instance

/-- The code of a digit. -/
def IsDigit (n : Nat) : Prop := 48 ≤ n ∧ n ≤ 57

/-- The code of a character of a simple symbol: a letter, a digit or a character of
`symbolPunctuation`. -/
def SymChar (n : Nat) : Prop :=
  (65 ≤ n ∧ n ≤ 90 ∨ 97 ≤ n ∧ n ≤ 122) ∨ IsDigit n ∨
    n ∈ [126, 33, 64, 36, 37, 94, 38, 42, 95, 45, 43, 61, 60, 62, 46, 63, 47]

theorem atomChar_of_symChar {n : Nat} (h : SymChar n) : AtomChar n := by
  simp only [SymChar, IsDigit, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [AtomChar, Delim]
  omega

/-! ## Single characters -/

theorem whiteSpaceChar_inv {p : Chars} (h : whiteSpaceChar p) :
    ∃ c, p = [c] ∧ (c.toNat = 9 ∨ c.toNat = 10 ∨ c.toNat = 13 ∨ c.toNat = 32) := by
  obtain ⟨r, hr, hp⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> obtain ⟨c, rfl, h₁, h₂⟩ := hp <;>
    exact ⟨c, rfl, by omega⟩

theorem printableOrSpace_inv {p : Chars} (h : alt printableChar whiteSpaceChar p) :
    ∃ c, p = [c] := by
  rcases h with (⟨c, rfl, -⟩ | ⟨c, rfl, -⟩) | h
  · exact ⟨c, rfl⟩
  · exact ⟨c, rfl⟩
  · obtain ⟨c, rfl, -⟩ := whiteSpaceChar_inv h
    exact ⟨c, rfl⟩

theorem lineBreak_one {c : UInt8} : lineBreak [c] ↔ LineBreak c.toNat := by
  simp [lineBreak, alt, code, range_one, LineBreak]
  omega

theorem symChar_inv {p : Chars} (h : altAll [letter, digit, symbolPunctuation] p) :
    ∃ c, p = [c] ∧ SymChar c.toNat := by
  obtain ⟨r, hr, hp⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hp with ⟨c, rfl, h₁, h₂⟩ | ⟨c, rfl, h₁, h₂⟩
    · exact ⟨c, rfl, Or.inl (Or.inl ⟨h₁, h₂⟩)⟩
    · exact ⟨c, rfl, Or.inl (Or.inr ⟨h₁, h₂⟩)⟩
  · obtain ⟨c, rfl, h₁, h₂⟩ := hp
    exact ⟨c, rfl, Or.inr (Or.inl ⟨h₁, h₂⟩)⟩
  · obtain ⟨c, rfl, hc⟩ := oneOf_inv hp
    refine ⟨c, rfl, Or.inr (Or.inr ?_)⟩
    have e : (chars "~!@$%^&*_-+=<>.?/").map UInt8.toNat =
        [126, 33, 64, 36, 37, 94, 38, 42, 95, 45, 43, 61, 60, 62, 46, 63, 47] := by decide
    rwa [e] at hc

/-! ## The shapes of the tokens -/

theorem numeral_inv {s : Chars} (h : numeral s) :
    ∃ c t, s = c :: t ∧ IsDigit c.toNat ∧ ∀ x ∈ t, IsDigit x.toNat := by
  rcases h with h | ⟨⟨a, b, rfl, ⟨c, rfl, h₁, h₂⟩, hb⟩, -⟩
  · exact ⟨48, [], h, ⟨by decide, by decide⟩, by simp⟩
  · exact ⟨c, b, rfl, ⟨h₁, h₂⟩,
      star_mem (single_mem fun p ⟨d, hp, h₁, h₂⟩ => ⟨d, hp, h₁, h₂⟩) hb⟩

theorem decimal_inv {s : Chars} (h : decimal s) :
    ∃ c t, s = c :: t ∧ IsDigit c.toNat ∧ 46 ∈ t.map UInt8.toNat ∧
      ∀ x ∈ s, IsDigit x.toNat ∨ x.toNat = 46 := by
  obtain ⟨n, rest, rfl, hn, hrest⟩ := h
  obtain ⟨b, rfl, z, n', rfl, hz, hn'⟩ := seq_lit hrest
  obtain ⟨c, t, rfl, hc, ht⟩ := numeral_inv hn
  obtain ⟨c', t', rfl, hc', ht'⟩ := numeral_inv hn'
  have hz' : ∀ x ∈ z, x.toNat = 48 :=
    star_mem (P := fun x => x.toNat = 48) (single_mem fun p hp => ⟨48, hp, rfl⟩) hz
  refine ⟨c, t ++ (chars "." ++ (z ++ c' :: t')), rfl, hc, ?_, ?_⟩
  · simp only [List.map_append, List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · intro x hx
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
    have hdot : chars "." = [46] := rfl
    rw [hdot] at hx
    rcases hx with rfl | hx | hx | hx | rfl | hx
    · exact Or.inl hc
    · exact Or.inl (ht x hx)
    · simp only [List.mem_singleton] at hx
      subst hx
      exact Or.inr rfl
    · exact Or.inl (by have := hz' x hx; simp [IsDigit]; omega)
    · exact Or.inl hc'
    · exact Or.inl (ht' x hx)

theorem hexadecimal_inv {s : Chars} (h : hexadecimal s) :
    ∃ t, s = 35 :: 120 :: t ∧ ∀ x ∈ t, AtomChar x.toNat := by
  obtain ⟨t, rfl, ht⟩ := seq_lit h
  refine ⟨t, rfl, plus_mem (single_mem fun p hp => ?_) ht⟩
  obtain ⟨r, hr, hp⟩ := hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> obtain ⟨c, rfl, h₁, h₂⟩ := hp <;>
    exact ⟨c, rfl, by simp only [AtomChar, Delim]; omega⟩

theorem binary_inv {s : Chars} (h : binary s) :
    ∃ t, s = 35 :: 98 :: t ∧ ∀ x ∈ t, AtomChar x.toNat := by
  obtain ⟨t, rfl, ht⟩ := seq_lit h
  refine ⟨t, rfl, plus_mem (single_mem fun p hp => ?_) ht⟩
  obtain ⟨c, rfl, hc⟩ := oneOf_inv hp
  have e : (chars "01").map UInt8.toNat = [48, 49] := by decide
  rw [e] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  exact ⟨c, rfl, by simp only [AtomChar, Delim]; omega⟩

theorem keyword_inv {s : Chars} (h : keyword s) :
    ∃ t, s = 58 :: t ∧ ∀ x ∈ t, SymChar x.toNat := by
  obtain ⟨t, rfl, ht⟩ := seq_lit h
  exact ⟨t, rfl, plus_mem (single_mem fun p hp => symChar_inv hp) ht⟩

/-- The reserved words of the version, as character sequences. -/
def reservedWords (version : Version) : List Chars :=
  (basicReservedWords version ++ commandNames version).map chars

theorem simpleSymbol_inv {version : Version} {s : Chars} (h : simpleSymbol version s) :
    ∃ c t, s = c :: t ∧ ¬ IsDigit c.toNat ∧ (∀ x ∈ s, SymChar x.toNat) ∧
      s ∉ reservedWords version := by
  obtain ⟨⟨hplus, hdigit⟩, hres⟩ := h
  have hall := plus_mem (single_mem fun p hp => symChar_inv hp) hplus
  obtain ⟨a, b, rfl, ha, -⟩ := hplus
  obtain ⟨c, rfl, -⟩ := symChar_inv ha
  refine ⟨c, b, rfl, fun hd => hdigit (startsWith_range.mpr hd), hall, fun hr => hres ?_⟩
  exact litOneOf_iff.mpr hr

theorem string_inv {s : Chars} (h : string s) :
    ∃ b, s = 34 :: (b ++ [34]) ∧
      star (alt (minus (alt printableChar whiteSpaceChar) (lit "\"")) (lit "\"\"")) b := by
  obtain ⟨t, rfl, b, e, rfl, hb, rfl⟩ := seq_lit h
  exact ⟨b, rfl, hb⟩

theorem string20_inv {s : Chars} (h : string20 s) :
    ∃ b, s = 34 :: (b ++ [34]) ∧
      star (alt (minus (alt printableChar whiteSpaceChar) (oneOf "\"\\"))
        (seq (lit "\\") (alt printableChar whiteSpaceChar))) b := by
  obtain ⟨t, rfl, b, e, rfl, hb, rfl⟩ := seq_lit h
  exact ⟨b, rfl, hb⟩

theorem quotedSymbol_inv {s : Chars} (h : quotedSymbol s) :
    ∃ b, s = 124 :: (b ++ [124]) ∧ ∀ x ∈ b, x ≠ 124 := by
  obtain ⟨t, rfl, b, e, rfl, hb, rfl⟩ := seq_lit h
  refine ⟨b, rfl, star_mem (single_mem fun p ⟨hp, hn⟩ => ?_) hb⟩
  have hsingle : ∃ c, p = [c] := by
    rcases hp with h | h
    · obtain ⟨c, rfl, -⟩ := whiteSpaceChar_inv h
      exact ⟨c, rfl⟩
    · exact printableOrSpace_inv (Or.inl h)
  obtain ⟨c, rfl⟩ := hsingle
  exact ⟨c, rfl, fun e => hn ⟨124, by decide, by rw [e]⟩⟩

/-! ## The category of a token, from its characters -/

/-- The category of a token with the characters, in the version: the first character tells
the parentheses, string literals, quoted symbols, keywords, the numbers starting with `#`
and the ones starting with a digit apart; the second character tells a hexadecimal from a
binary, a `.` a decimal from a numeral, and the list of reserved words a reserved word from a
simple symbol. `kind_spec` proves that it is the only category the characters can have. -/
def kind (version : Version) : Chars → Category
  | [] => .parenOpen
  | c :: t =>
    if c.toNat = 40 then .parenOpen
    else if c.toNat = 41 then .parenClose
    else if c.toNat = 34 then .string
    else if c.toNat = 124 then .quotedSymbol
    else if c.toNat = 58 then .keyword
    else if c.toNat = 35 then (if t.head?.map UInt8.toNat = some 120 then .hexadecimal
      else .binary)
    else if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then (if 46 ∈ t.map UInt8.toNat then .decimal
      else .numeral)
    else if c :: t ∈ reservedWords version then .reserved
    else .simpleSymbol

/-- Every reserved word is non-empty, consists of characters of atoms, and has the category
`reserved` by `kind`. -/
theorem reservedWords_facts (version : Version) :
    ∀ w ∈ reservedWords version,
      w ≠ [] ∧ (∀ x ∈ w, AtomChar x.toNat) ∧ kind version w = .reserved := by
  cases version <;> decide

theorem kind_simple {version : Version} {c : UInt8} {t : Chars} (hc : SymChar c.toNat)
    (hd : ¬ IsDigit c.toNat) (hr : c :: t ∉ reservedWords version) :
    kind version (c :: t) = .simpleSymbol := by
  simp only [SymChar, IsDigit, List.mem_cons, List.not_mem_nil, or_false] at hc hd
  simp only [kind]
  rw [ite_no (by omega), ite_no (by omega), ite_no (by omega), ite_no (by omega),
    ite_no (by omega), ite_no (by omega), ite_no (by omega), ite_no hr]

theorem kind_digit {version : Version} {c : UInt8} {t : Chars} (hc : IsDigit c.toNat) :
    kind version (c :: t) = if 46 ∈ t.map UInt8.toNat then .decimal else .numeral := by
  simp only [IsDigit] at hc
  simp only [kind]
  rw [ite_no (by omega), ite_no (by omega), ite_no (by omega), ite_no (by omega),
    ite_no (by omega), ite_no (by omega), ite_yes hc]

/-- The category of a token is the one `kind` computes from its characters. -/
theorem kind_spec {version : Version} {category : Category} {s : Chars}
    (h : categoryRegex version category s) : kind version s = category := by
  cases category with
  | parenOpen => exact h ▸ rfl
  | parenClose => exact h ▸ rfl
  | numeral =>
    obtain ⟨c, t, rfl, hc, ht⟩ := numeral_inv h
    rw [kind_digit hc, ite_no]
    intro hm
    obtain ⟨x, hx, hx46⟩ := List.mem_map.mp hm
    have := ht x hx
    simp only [IsDigit] at this
    omega
  | decimal =>
    obtain ⟨c, t, rfl, hc, hm, -⟩ := decimal_inv h
    rw [kind_digit hc, ite_yes hm]
  | hexadecimal =>
    obtain ⟨t, rfl, -⟩ := hexadecimal_inv h
    rfl
  | binary =>
    obtain ⟨t, rfl, -⟩ := binary_inv h
    rfl
  | string =>
    by_cases hv : version = .v2_0
    · rw [show categoryRegex version .string = string20 by simp [categoryRegex, hv]] at h
      obtain ⟨b, rfl, -⟩ := string20_inv h
      rfl
    · rw [show categoryRegex version .string = string by simp [categoryRegex, hv]] at h
      obtain ⟨b, rfl, -⟩ := string_inv h
      rfl
  | simpleSymbol =>
    obtain ⟨c, t, rfl, hd, hall, hr⟩ := simpleSymbol_inv h
    exact kind_simple (hall c (by simp)) hd hr
  | quotedSymbol =>
    obtain ⟨b, rfl, -⟩ := quotedSymbol_inv h
    rfl
  | keyword =>
    obtain ⟨t, rfl, -⟩ := keyword_inv h
    rfl
  | reserved =>
    exact (reservedWords_facts version s (litOneOf_iff.mp h)).2.2

/-! ## The first character of a token -/

/-- The categories, grouped by how the end of a token is found: a parenthesis is one
character, a string literal and a quoted symbol end at their closing character, and the
other categories, the atoms, end at a delimiter. -/
def group : Category → Nat
  | .parenOpen => 0
  | .parenClose => 1
  | .string => 2
  | .quotedSymbol => 3
  | _ => 4

/-- The group of the categories whose tokens can start with the character code. -/
def headGroup (n : Nat) : Nat :=
  if n = 40 then 0 else if n = 41 then 1 else if n = 34 then 2 else if n = 124 then 3 else 4

/-- A token of an atom category is non-empty and consists of characters of atoms. -/
theorem atom_shape {version : Version} {category : Category} {s : Chars}
    (h : categoryRegex version category s) (hg : group category = 4) :
    s ≠ [] ∧ ∀ x ∈ s, AtomChar x.toNat := by
  cases category with
  | parenOpen | parenClose | string | quotedSymbol => simp [group] at hg
  | numeral =>
    obtain ⟨c, t, rfl, hc, ht⟩ := numeral_inv h
    refine ⟨by simp, fun x hx => atomChar_of_symChar (Or.inr (Or.inl ?_))⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hc
    · exact ht x hx
  | decimal =>
    obtain ⟨c, t, rfl, -, -, hall⟩ := decimal_inv h
    refine ⟨by simp, fun x hx => ?_⟩
    rcases hall x hx with hd | hd
    · exact atomChar_of_symChar (Or.inr (Or.inl hd))
    · simp only [AtomChar, Delim]
      omega
  | hexadecimal =>
    obtain ⟨t, rfl, ht⟩ := hexadecimal_inv h
    refine ⟨by simp, fun x hx => ?_⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · decide
    · decide
    · exact ht x hx
  | binary =>
    obtain ⟨t, rfl, ht⟩ := binary_inv h
    refine ⟨by simp, fun x hx => ?_⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · decide
    · decide
    · exact ht x hx
  | simpleSymbol =>
    obtain ⟨c, t, rfl, -, hall, -⟩ := simpleSymbol_inv h
    exact ⟨by simp, fun x hx => atomChar_of_symChar (hall x hx)⟩
  | keyword =>
    obtain ⟨t, rfl, ht⟩ := keyword_inv h
    refine ⟨by simp, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · decide
    · exact atomChar_of_symChar (ht x hx)
  | reserved =>
    obtain ⟨hne, hall, -⟩ := reservedWords_facts version s (litOneOf_iff.mp h)
    exact ⟨hne, hall⟩

/-- A token is non-empty, does not start with a character that starts whitespace, and its
first character tells the group of its category. -/
theorem token_shape {version : Version} {category : Category} {s : Chars}
    (h : categoryRegex version category s) :
    ∃ c t, s = c :: t ∧ ¬ WsStart c.toNat ∧ headGroup c.toNat = group category := by
  by_cases hg : group category = 4
  · obtain ⟨hne, hall⟩ := atom_shape h hg
    obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hc := hall c (by simp)
    simp only [AtomChar, Delim] at hc
    refine ⟨c, t, rfl, by simp only [WsStart]; omega, ?_⟩
    rw [hg, headGroup, ite_no (by omega), ite_no (by omega), ite_no (by omega),
      ite_no (by omega)]
  · cases category with
    | parenOpen => exact ⟨40, [], h, by decide, rfl⟩
    | parenClose => exact ⟨41, [], h, by decide, rfl⟩
    | string =>
      by_cases hv : version = .v2_0
      · rw [show categoryRegex version .string = string20 by simp [categoryRegex, hv]] at h
        obtain ⟨b, rfl, -⟩ := string20_inv h
        exact ⟨34, _, rfl, by decide, rfl⟩
      · rw [show categoryRegex version .string = string by simp [categoryRegex, hv]] at h
        obtain ⟨b, rfl, -⟩ := string_inv h
        exact ⟨34, _, rfl, by decide, rfl⟩
    | quotedSymbol =>
      obtain ⟨b, rfl, -⟩ := quotedSymbol_inv h
      exact ⟨124, _, rfl, by decide, rfl⟩
    | _ => simp [group] at hg

/-! ## The characters of a token -/

/-- What may follow a token other than a parenthesis: the end of the input or a
delimiter. -/
def DelimRest (r : Chars) : Prop := r = [] ∨ ∃ c m, r = c :: m ∧ Delim c.toNat

theorem delimRest_of {category : Category} {r : Chars} (h : Delimited category r)
    (h₀ : category ≠ .parenOpen) (h₁ : category ≠ .parenClose) : DelimRest r := by
  rcases h with h | h | h | ⟨c, m, rfl, hc⟩
  · exact absurd h h₀
  · exact absurd h h₁
  · exact Or.inl h
  · refine Or.inr ⟨c, m, rfl, ?_⟩
    rcases hc with hc | hc
    · have := whiteSpaceChar_one.mp hc
      simp only [Delim]
      omega
    · obtain ⟨d, hcd, hd⟩ := oneOf_inv hc
      simp only [List.cons.injEq, and_true] at hcd
      subst hcd
      have e : (chars "();").map UInt8.toNat = [40, 41, 59] := by decide
      rw [e] at hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      simp only [Delim]
      omega

/-- A delimiter is not `"`. -/
theorem delimRest_head {r : Chars} (h : DelimRest r) : ∀ d m, r = d :: m → d ≠ 34 := by
  rintro d m rfl rfl
  rcases h with h | ⟨c, m', h, hc⟩
  · simp at h
  · simp only [List.cons.injEq] at h
    rw [← h.1] at hc
    simp only [Delim] at hc
    revert hc
    decide

/-- Two tokens of atom categories that one input starts with are equal: each ends at the
first delimiter, and neither contains one. -/
theorem atom_text {s₁ s₂ r₁ r₂ : Chars} (hs₁ : ∀ x ∈ s₁, AtomChar x.toNat)
    (hs₂ : ∀ x ∈ s₂, AtomChar x.toNat) (hr₁ : DelimRest r₁) (hr₂ : DelimRest r₂)
    (h : s₁ ++ r₁ = s₂ ++ r₂) : s₁ = s₂ := by
  rcases List.append_eq_append_iff.mp h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩
  · cases a with
    | nil => simp
    | cons x xs =>
      exfalso
      rcases hr₁ with h0 | ⟨d, m, hd, hdel⟩
      · simp at h0
      · simp only [List.cons_append, List.cons.injEq] at hd
        rw [← hd.1] at hdel
        exact (hs₂ x (by simp)).1 hdel
  · cases a with
    | nil => simp
    | cons x xs =>
      exfalso
      rcases hr₂ with h0 | ⟨d, m, hd, hdel⟩
      · simp at h0
      · simp only [List.cons_append, List.cons.injEq] at hd
        rw [← hd.1] at hdel
        exact (hs₁ x (by simp)).1 hdel

/-- Two quoted symbols that one input starts with are equal: each ends at the first `|`
after the opening one. -/
theorem quoted_text {s₁ s₂ r₁ r₂ : Chars} (hs₁ : quotedSymbol s₁) (hs₂ : quotedSymbol s₂)
    (h : s₁ ++ r₁ = s₂ ++ r₂) : s₁ = s₂ := by
  obtain ⟨b₁, rfl, hb₁⟩ := quotedSymbol_inv hs₁
  obtain ⟨b₂, rfl, hb₂⟩ := quotedSymbol_inv hs₂
  simp only [List.cons_append, List.append_assoc, List.cons.injEq,
    true_and] at h
  rw [sep_eq (E := (· = 124)) hb₁ hb₂ rfl rfl h]

theorem stringUnit_inv {p : Chars}
    (h : alt (minus (alt printableChar whiteSpaceChar) (lit "\"")) (lit "\"\"") p) :
    (∃ c, p = [c] ∧ c ≠ 34) ∨ p = [34, 34] := by
  rcases h with ⟨hp, hn⟩ | h
  · obtain ⟨c, rfl⟩ := printableOrSpace_inv hp
    exact Or.inl ⟨c, rfl, fun e => hn (by rw [e]; rfl)⟩
  · exact Or.inr h

/-- Two bodies of string literals from 2.5 on that one input starts with, each followed by
`"` and then by something other than `"`, are equal: a `"` inside a body is doubled, so the
first `"` that is not followed by another ends the body. -/
theorem string_body_eq {b₁ b₂ y₁ y₂ : Chars}
    (h₁ : star (alt (minus (alt printableChar whiteSpaceChar) (lit "\"")) (lit "\"\"")) b₁)
    (h₂ : star (alt (minus (alt printableChar whiteSpaceChar) (lit "\"")) (lit "\"\"")) b₂)
    (hy₁ : ∀ d m, y₁ = d :: m → d ≠ 34) (hy₂ : ∀ d m, y₂ = d :: m → d ≠ 34)
    (h : b₁ ++ 34 :: y₁ = b₂ ++ 34 :: y₂) : b₁ = b₂ := by
  obtain ⟨ps, rfl, hps⟩ := h₁
  induction ps generalizing b₂ with
  | nil =>
    rcases star_cases h₂ with rfl | ⟨q, t, rfl, -, hq, -⟩
    · rfl
    · exfalso
      rcases stringUnit_inv hq with ⟨c, rfl, hc⟩ | rfl
      · simp only [List.flatten_nil, List.nil_append, List.cons_append,
          List.cons.injEq] at h
        exact hc h.1.symm
      · simp only [List.flatten_nil, List.nil_append, List.cons_append, List.cons.injEq,
          true_and] at h
        exact hy₁ _ _ h rfl
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hps' : ∀ q ∈ ps, _ := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    rcases star_cases h₂ with rfl | ⟨q, t, rfl, -, hq, ht⟩
    · exfalso
      rcases stringUnit_inv hp with ⟨c, rfl, hc⟩ | rfl
      · simp only [List.flatten_cons, List.cons_append, List.nil_append,
          List.cons.injEq] at h
        exact hc h.1
      · simp only [List.flatten_cons, List.cons_append, List.nil_append, List.cons.injEq,
          true_and] at h
        exact hy₂ _ _ h.symm rfl
    · simp only [List.flatten_cons, List.append_assoc] at h ⊢
      have hpq : p = q := by
        rcases stringUnit_inv hp with ⟨c, rfl, hc⟩ | rfl <;>
          rcases stringUnit_inv hq with ⟨d, rfl, hd⟩ | rfl
        · simp only [List.singleton_append, List.cons.injEq] at h
          rw [h.1]
        · simp only [List.cons_append, List.cons.injEq] at h
          exact absurd h.1 hc
        · simp only [List.cons_append, List.cons.injEq] at h
          exact absurd h.1.symm hd
        · rfl
      subst hpq
      rw [ih ht hps' (List.append_cancel_left h)]

theorem stringUnit20_inv {p : Chars}
    (h : alt (minus (alt printableChar whiteSpaceChar) (oneOf "\"\\"))
      (seq (lit "\\") (alt printableChar whiteSpaceChar)) p) :
    (∃ c, p = [c] ∧ c ≠ 34 ∧ c ≠ 92) ∨ ∃ d, p = [92, d] := by
  rcases h with ⟨hp, hn⟩ | h
  · obtain ⟨c, rfl⟩ := printableOrSpace_inv hp
    exact Or.inl ⟨c, rfl, fun e => hn ⟨34, by decide, by rw [e]⟩,
      fun e => hn ⟨92, by decide, by rw [e]⟩⟩
  · obtain ⟨b, rfl, hb⟩ := seq_lit h
    obtain ⟨d, rfl⟩ := printableOrSpace_inv hb
    exact Or.inr ⟨d, rfl⟩

/-- Two bodies of string literals in 2.0 that one input starts with, each followed by `"`,
are equal: a backslash takes the next character with it, so the first `"` not taken by a
backslash ends the body. -/
theorem string20_body_eq {b₁ b₂ y₁ y₂ : Chars}
    (h₁ : star (alt (minus (alt printableChar whiteSpaceChar) (oneOf "\"\\"))
      (seq (lit "\\") (alt printableChar whiteSpaceChar))) b₁)
    (h₂ : star (alt (minus (alt printableChar whiteSpaceChar) (oneOf "\"\\"))
      (seq (lit "\\") (alt printableChar whiteSpaceChar))) b₂)
    (h : b₁ ++ 34 :: y₁ = b₂ ++ 34 :: y₂) : b₁ = b₂ := by
  refine star_terminated (E := (· = 34)) ?_ ?_ ?_ h₁ h₂ rfl rfl h
  · intro p hp
    rcases stringUnit20_inv hp with ⟨c, rfl, -⟩ | ⟨d, rfl⟩ <;> simp
  · intro p q x y hp hq hpq
    rcases stringUnit20_inv hp with ⟨c, rfl, hc, hc'⟩ | ⟨d, rfl⟩ <;>
      rcases stringUnit20_inv hq with ⟨e, rfl, he, he'⟩ | ⟨f, rfl⟩
    · simp only [List.singleton_append, List.cons.injEq] at hpq
      rw [hpq.1]
    · simp only [List.cons_append, List.cons.injEq] at hpq
      exact absurd hpq.1 hc'
    · simp only [List.cons_append, List.cons.injEq] at hpq
      exact absurd hpq.1.symm he'
    · simp only [List.cons_append, List.cons.injEq] at hpq
      rw [hpq.2.1]
  · intro p c t hp hpc
    rcases stringUnit20_inv hp with ⟨d, rfl, hd, -⟩ | ⟨d, rfl⟩
    · simp only [List.cons.injEq] at hpc
      rw [← hpc.1]
      exact hd
    · simp only [List.cons.injEq] at hpc
      rw [← hpc.1]
      decide

/-- Two string literals that one input starts with, each followed by the end of the input
or a delimiter, are equal. -/
theorem string_text {version : Version} {s₁ s₂ r₁ r₂ : Chars}
    (hs₁ : categoryRegex version .string s₁) (hs₂ : categoryRegex version .string s₂)
    (hr₁ : DelimRest r₁) (hr₂ : DelimRest r₂) (h : s₁ ++ r₁ = s₂ ++ r₂) : s₁ = s₂ := by
  by_cases hv : version = .v2_0
  · rw [show categoryRegex version .string = string20 by simp [categoryRegex, hv]] at hs₁ hs₂
    obtain ⟨b₁, rfl, hb₁⟩ := string20_inv hs₁
    obtain ⟨b₂, rfl, hb₂⟩ := string20_inv hs₂
    simp only [List.cons_append, List.append_assoc, List.cons.injEq,
      true_and] at h
    rw [string20_body_eq hb₁ hb₂ h]
  · rw [show categoryRegex version .string = string by simp [categoryRegex, hv]] at hs₁ hs₂
    obtain ⟨b₁, rfl, hb₁⟩ := string_inv hs₁
    obtain ⟨b₂, rfl, hb₂⟩ := string_inv hs₂
    simp only [List.cons_append, List.append_assoc, List.cons.injEq,
      true_and] at h
    rw [string_body_eq hb₁ hb₂ (delimRest_head hr₁) (delimRest_head hr₂) h]

/-- Two tokens that one input starts with, each followed by what `Delimited` allows, have
the same characters. -/
theorem text_eq {version : Version} {cat₁ cat₂ : Category} {s₁ s₂ r₁ r₂ : Chars}
    (hs₁ : categoryRegex version cat₁ s₁) (hs₂ : categoryRegex version cat₂ s₂)
    (hd₁ : Delimited cat₁ r₁) (hd₂ : Delimited cat₂ r₂) (h : s₁ ++ r₁ = s₂ ++ r₂) :
    s₁ = s₂ := by
  obtain ⟨c₁, t₁, hst₁, -, hg₁⟩ := token_shape hs₁
  obtain ⟨c₂, t₂, hst₂, -, hg₂⟩ := token_shape hs₂
  have hc : c₁ = c₂ := by
    subst hst₁ hst₂
    simp only [List.cons_append, List.cons.injEq] at h
    exact h.1
  subst hc
  have hg : group cat₁ = group cat₂ := hg₁.symm.trans hg₂
  have hne : ∀ cat, group cat = 4 → cat ≠ .parenOpen ∧ cat ≠ .parenClose := by
    intro cat hcat
    cases cat <;> simp [group] at hcat ⊢
  by_cases h4 : group cat₁ = 4
  · have h4' : group cat₂ = 4 := hg ▸ h4
    exact atom_text (atom_shape hs₁ h4).2 (atom_shape hs₂ h4').2
      (delimRest_of hd₁ (hne _ h4).1 (hne _ h4).2) (delimRest_of hd₂ (hne _ h4').1 (hne _ h4').2)
      h
  · cases cat₁ <;> cases cat₂
    all_goals first
      | (simp [group] at hg; done)
      | (simp [group] at h4; done)
      | exact hs₁.trans hs₂.symm
      | exact quoted_text hs₁ hs₂ h
      | exact string_text hs₁ hs₂ (delimRest_of hd₁ (by decide) (by decide))
          (delimRest_of hd₂ (by decide) (by decide)) h

/-- Two tokens that one input starts with, each followed by what `Delimited` allows, are
equal in category and characters. -/
theorem token_eq {version : Version} {cat₁ cat₂ : Category} {s₁ s₂ r₁ r₂ : Chars}
    (hs₁ : categoryRegex version cat₁ s₁) (hs₂ : categoryRegex version cat₂ s₂)
    (hd₁ : Delimited cat₁ r₁) (hd₂ : Delimited cat₂ r₂) (h : s₁ ++ r₁ = s₂ ++ r₂) :
    cat₁ = cat₂ ∧ s₁ = s₂ := by
  have hs := text_eq hs₁ hs₂ hd₁ hd₂ h
  subst hs
  exact ⟨(kind_spec hs₁).symm.trans (kind_spec hs₂), rfl⟩

/-! ## Whitespace -/

theorem comment_inv {p : Chars} (h : comment p) :
    ∃ b l, p = 59 :: (b ++ [l]) ∧ (∀ x ∈ b, ¬ LineBreak x.toNat) ∧ LineBreak l.toNat := by
  obtain ⟨t, rfl, b, e, rfl, hb, he⟩ := seq_lit h
  obtain ⟨l, rfl, hl⟩ : ∃ l, e = [l] ∧ LineBreak l.toNat := by
    rcases he with ⟨l, rfl, h₁, h₂⟩ | ⟨l, rfl, h₁, h₂⟩ <;>
      exact ⟨l, rfl, by simp only [LineBreak]; omega⟩
  refine ⟨b, l, rfl, star_mem (single_mem fun p hp => ?_) hb, hl⟩
  obtain ⟨⟨c, rfl, -, -⟩, hn⟩ := hp
  exact ⟨c, rfl, fun hc => hn (lineBreak_one.mpr hc)⟩

theorem commentAtEnd_inv {z : Chars} (h : commentAtEnd z) :
    ∃ b, z = 59 :: b ∧ ∀ x ∈ b, ¬ LineBreak x.toNat := by
  obtain ⟨b, rfl, hb⟩ := seq_lit h
  refine ⟨b, rfl, star_mem (single_mem fun p hp => ?_) hb⟩
  obtain ⟨⟨c, rfl, -, -⟩, hn⟩ := hp
  exact ⟨c, rfl, fun hc => hn (lineBreak_one.mpr hc)⟩

theorem wsPart_inv {p : Chars} (h : alt whiteSpaceChar comment p) :
    (∃ c, p = [c] ∧ c.toNat ≠ 59 ∧ WsStart c.toNat) ∨
      ∃ b l, p = 59 :: (b ++ [l]) ∧ (∀ x ∈ b, ¬ LineBreak x.toNat) ∧ LineBreak l.toNat := by
  rcases h with h | h
  · obtain ⟨c, rfl, hc⟩ := whiteSpaceChar_inv h
    exact Or.inl ⟨c, rfl, by omega, by simp only [WsStart]; omega⟩
  · exact Or.inr (comment_inv h)

theorem wsPart_head {p : Chars} (h : alt whiteSpaceChar comment p) :
    ∃ c t, p = c :: t ∧ WsStart c.toNat := by
  rcases wsPart_inv h with ⟨c, rfl, -, hc⟩ | ⟨b, l, rfl, -, -⟩
  · exact ⟨c, [], rfl, hc⟩
  · exact ⟨59, _, rfl, by decide⟩

/-- Two parts of whitespace that one input starts with are equal: a white space character
is one character, and a comment ends at its first line break. -/
theorem wsPart_eq {p q x y : Chars} (hp : alt whiteSpaceChar comment p)
    (hq : alt whiteSpaceChar comment q) (h : p ++ x = q ++ y) : p = q := by
  rcases wsPart_inv hp with ⟨c, rfl, hc, -⟩ | ⟨b, l, rfl, hb, hl⟩ <;>
    rcases wsPart_inv hq with ⟨d, rfl, hd, -⟩ | ⟨b', l', rfl, hb', hl'⟩
  · simp only [List.singleton_append, List.cons.injEq] at h
    rw [h.1]
  · simp only [List.cons_append, List.cons.injEq] at h
    exact absurd (by rw [h.1]; rfl) hc
  · simp only [List.cons_append, List.cons.injEq] at h
    exact absurd (by rw [← h.1]; rfl) hd
  · simp only [List.cons_append, List.append_assoc, List.cons.injEq,
      true_and] at h
    obtain rfl := sep_eq (E := fun x => LineBreak x.toNat) hb hb' hl hl' h
    simp only [List.append_cancel_left_eq, List.cons.injEq] at h
    rw [h.1]

/-- Whitespace that an input starts with, when the input goes on with a character that
cannot start whitespace, contains every whitespace the input starts with. -/
theorem ws_prefix {w₁ w₂ x₁ x₂ : Chars} {c : UInt8} (h₁ : whitespace w₁) (h₂ : whitespace w₂)
    (hc : ¬ WsStart c.toNat) (h : w₁ ++ c :: x₁ = w₂ ++ x₂) :
    ∃ m, w₁ = w₂ ++ m ∧ whitespace m := by
  obtain ⟨ps, rfl, hps⟩ := h₁
  induction ps generalizing w₂ with
  | nil =>
    rcases star_cases h₂ with rfl | ⟨q, t, rfl, -, hq, -⟩
    · exact ⟨[], rfl, whitespace_nil⟩
    · exfalso
      obtain ⟨d, u, rfl, hd⟩ := wsPart_head hq
      simp only [List.flatten_nil, List.nil_append, List.cons_append, List.append_assoc,
        List.cons.injEq] at h
      exact hc (h.1 ▸ hd)
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hps' : ∀ q ∈ ps, alt whiteSpaceChar comment q :=
      fun q hq => hps q (List.mem_cons_of_mem _ hq)
    rcases star_cases h₂ with rfl | ⟨q, t, rfl, -, hq, ht⟩
    · exact ⟨(p :: ps).flatten, rfl, p :: ps, rfl, hps⟩
    · simp only [List.flatten_cons, List.append_assoc] at h ⊢
      obtain rfl := wsPart_eq hp hq h
      obtain ⟨m, hm, hmw⟩ := ih ht hps' (List.append_cancel_left h)
      exact ⟨m, by rw [hm], hmw⟩

/-- The whitespace before a token is determined: two whitespaces that one input starts
with, each followed by a character that cannot start whitespace, are equal. -/
theorem ws_eq {w₁ w₂ x₁ x₂ : Chars} {c₁ c₂ : UInt8} (h₁ : whitespace w₁)
    (h₂ : whitespace w₂) (hc₁ : ¬ WsStart c₁.toNat) (hc₂ : ¬ WsStart c₂.toNat)
    (h : w₁ ++ c₁ :: x₁ = w₂ ++ c₂ :: x₂) : w₁ = w₂ := by
  obtain ⟨m, hm, -⟩ := ws_prefix h₁ h₂ hc₁ h
  obtain ⟨m', hm', -⟩ := ws_prefix h₂ h₁ hc₂ h.symm
  have hl := congrArg List.length hm'
  rw [hm] at hl
  simp only [List.length_append] at hl
  have hm0 : m = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [hm, hm0, List.append_nil]

/-- Whitespace at the end of the input contains no token: a token starts with a character
that cannot start whitespace, and a comment that runs to the end of the input contains no
line break, so no comment ends in it. -/
theorem not_atEnd {w e x : Chars} {c : UInt8} (hw : whitespace w) (he : whitespaceAtEnd e)
    (hc : ¬ WsStart c.toNat) (h : e = w ++ c :: x) : False := by
  obtain ⟨w', z, rfl, hw', hz⟩ := he
  obtain ⟨m, rfl, hm⟩ := ws_prefix hw hw' hc h.symm
  simp only [List.append_assoc] at h
  have hz' := List.append_cancel_left h
  rcases hz with hz | hz
  · rw [show z = [] from hz] at hz'
    simp at hz'
  · obtain ⟨b, rfl, hb⟩ := commentAtEnd_inv hz
    rcases star_cases hm with rfl | ⟨q, t, rfl, -, hq, -⟩
    · simp only [List.nil_append, List.cons.injEq] at hz'
      exact hc (hz'.1 ▸ by decide)
    · rcases wsPart_inv hq with ⟨d, rfl, hd, -⟩ | ⟨b', l, rfl, -, hl⟩
      · simp only [List.cons_append, List.cons.injEq] at hz'
        exact hd (hz'.1 ▸ rfl)
      · simp only [List.cons_append, List.append_assoc,
          List.cons.injEq, true_and] at hz'
        exact hb l (by rw [hz']; simp) hl

/-! ## The tokenisation -/

theorem tokenizationFrom_inv {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} (h : TokenizationFrom version offset input tokens) :
    (tokens = [] ∧ whitespaceAtEnd input) ∨
      ∃ w category s rest ts, input = w ++ s ++ rest ∧ whitespace w ∧
        categoryRegex version category s ∧ Delimited category rest ∧
        TokenizationFrom version (offset + w.length + s.length) rest ts ∧
        tokens = ⟨category, offset + w.length, s⟩ :: ts := by
  cases h with
  | done hw => exact Or.inl ⟨rfl, hw⟩
  | token hw hs hd hr => exact Or.inr ⟨_, _, _, _, _, rfl, hw, hs, hd, hr, rfl⟩

/-- A tokenisation from any offset is unique. -/
theorem tokenizationFrom_unique {version : Version} {offset : Nat} {input : Chars}
    {t₁ t₂ : List Token} (h₁ : TokenizationFrom version offset input t₁)
    (h₂ : TokenizationFrom version offset input t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | done hw =>
    rcases tokenizationFrom_inv h₂ with ⟨rfl, -⟩ | ⟨w, cat, s, rest, ts, hin, hw', hs, -⟩
    · rfl
    · exfalso
      obtain ⟨c, t, rfl, hc, -⟩ := token_shape hs
      exact not_atEnd (x := t ++ rest) hw' hw hc (by rw [hin]; simp)
  | token hw hs hd hrest ih =>
    rcases tokenizationFrom_inv h₂ with ⟨-, hw'⟩ |
      ⟨w', cat', s', rest', ts', hin, hw', hs', hd', hrest', rfl⟩
    · exfalso
      obtain ⟨c, t, rfl, hc, -⟩ := token_shape hs
      exact not_atEnd hw hw' hc (List.append_assoc _ _ _)
    · obtain ⟨c, t, hct, hc, -⟩ := token_shape hs
      obtain ⟨c', t', hct', hc', -⟩ := token_shape hs'
      have hww := ws_eq hw hw' hc hc'
        (by rw [hct, hct'] at hin; simpa only [List.append_assoc, List.cons_append] using hin)
      subst hww
      simp only [List.append_assoc] at hin
      obtain ⟨rfl, rfl⟩ := token_eq hs hs' hd hd' (List.append_cancel_left hin)
      have hr := List.append_cancel_left (List.append_cancel_left hin)
      subst hr
      rw [ih hrest']

end BSmtLib.SpecChecks.Lexicon
