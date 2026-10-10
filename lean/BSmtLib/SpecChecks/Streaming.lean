import BSmtLib.Spec.Lexer
import BSmtLib.SpecChecks.Unique

/-!
# Examples of a lexer fed in slices

Examples of `Viable`, `Determined` and `HandoverMaximal` on short inputs, which check that the
definitions say what is meant: which tokens a lexer that has been fed the characters so far
hands over, and when it fails. Not trusted: these are proofs.
-/

namespace BSmtLib.SpecChecks.Lexer

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Lexicon.Regex BSmtLib.Spec.Lexer
open BSmtLib.SpecChecks.Lexicon

/-! ## Facts about the tokens handed over -/

/-- A list of tokens that starts another, and whose tokens all have their delimiter seen, is
no longer than the position of a token of the other list whose delimiter has not been seen. -/
theorem delimiterSeen_bound {input : Chars} {tokens all : List Token} {k : Nat}
    (hp : tokens <+: all) (hk : k < all.length) (hn : ¬ DelimiterSeen input all[k])
    (hall : ∀ token ∈ tokens, DelimiterSeen input token) : tokens.length ≤ k := by
  obtain ⟨more, rfl⟩ := hp
  refine Nat.le_of_not_lt fun hlt => hn ?_
  rw [List.getElem_append_left hlt]
  exact hall _ (List.getElem_mem hlt)

/-- When the input is viable, at most one list of tokens is `HandoverMaximal` on it. -/
theorem handoverMaximal_unique {version : Version} {input : Chars} {t₁ t₂ : List Token}
    (hv : Viable version input) (h₁ : HandoverMaximal version input t₁)
    (h₂ : HandoverMaximal version input t₂) :
    t₁ = t₂ := by
  obtain ⟨rest, ts, ht⟩ := hv
  obtain ⟨a, rfl⟩ := determined_prefix h₁.1.1 ht
  obtain ⟨b, hb⟩ := determined_prefix h₂.1.1 ht
  exact (List.append_inj_left hb (Nat.le_antisymm (h₂.2 t₁ h₁.1)
    (h₁.2 t₂ h₂.1)).symm).symm

/-- An input split into whitespace, a token and the characters after it, followed by more. -/
theorem split (input w s x : Chars) {rest : Chars} (h : input = w ++ s ++ x) :
    input ++ rest = w ++ s ++ (x ++ rest) := by
  rw [h, List.append_assoc]

/-! ## The tokens of the examples -/

theorem paren_open : categoryRegex .v2_7 .parenOpen (chars "(") := rfl

theorem symbol_a : categoryRegex .v2_7 .simpleSymbol (chars "a") :=
  simpleSymbol_of (by simp [simpleSymbolChar_one]; decide) (by decide) (by decide)

theorem symbol_x : categoryRegex .v2_7 .simpleSymbol (chars "x") :=
  simpleSymbol_of (by simp [simpleSymbolChar_one]; decide) (by decide) (by decide)

theorem numeral_123 : categoryRegex .v2_7 .numeral (chars "123") :=
  Or.inr ⟨plus_each (by simp [digit, range_one] <;> decide) (by simp [digit, range_one] <;> decide),
    fun h => absurd ((startsWith_lit_one "0" rfl).mp h) (by decide)⟩

theorem numeral_12 : categoryRegex .v2_7 .numeral (chars "12") :=
  Or.inr ⟨plus_each (by simp [digit, range_one] <;> decide) (by simp [digit, range_one] <;> decide),
    fun h => absurd ((startsWith_lit_one "0" rfl).mp h) (by decide)⟩

theorem quoted_abc : quotedSymbol (chars "|abc|") :=
  seq_intro (a := chars "|") rfl (seq_intro (a := chars "abc") (b := chars "|")
    (star_each (by simp [minus, spaceOrPrintable_one, printableOrSpace_one, oneOf_one]; decide))
    rfl)

theorem quoted_a : quotedSymbol (chars "|a|") :=
  seq_intro (a := chars "|") rfl (seq_intro (a := chars "a") (b := chars "|")
    (star_each (by simp [minus, spaceOrPrintable_one, printableOrSpace_one, oneOf_one]; decide))
    rfl)

theorem string20_ab : string20 (chars "\"ab\"") := by
  show string20 (chars "\"" ++ (chars "ab" ++ chars "\""))
  refine seq_intro rfl (seq_intro (star_each fun c hc => Or.inl ⟨?_, ?_⟩) rfl)
  · simp [chars] at hc
    rcases hc with rfl | rfl <;> simp [printableOrSpace_one] <;> decide
  · simp [chars] at hc
    rcases hc with rfl | rfl <;> simp [oneOf_one, chars] <;> decide

theorem string_ab_20 : categoryRegex .v2_0 .string (chars "\"ab\"") := string20_ab

/-- The space after a token delimits it. -/
theorem delimited_space {category : Category} {more : Chars} :
    Delimited category (chars " " ++ more) :=
  delimited_by (Or.inl (whiteSpaceChar_one.mpr (by decide)))

/-- The end of the input delimits a token. -/
theorem delimited_end {category : Category} : Delimited category [] := Or.inr (Or.inr (Or.inl rfl))

/-- The end of the input after whitespace. -/
theorem done_spaces {version : Version} {offset : Nat} {w : Chars} (h : ∀ c ∈ w, c.toNat = 32) :
    TokenizationFrom version offset w [] :=
  TokenizationFrom.done ⟨w, [], by simp, whitespace_spaces h, Or.inl rfl⟩

/-! ## `(a 12` in 2.7 -/

/-- `(a 123` is tokenised as `(`, `a` and `123`. -/
theorem tokenization_a_123 : Tokenization .v2_7 (chars "(a 123")
    [⟨.parenOpen, 0, chars "("⟩, ⟨.simpleSymbol, 1, chars "a"⟩, ⟨.numeral, 3, chars "123"⟩] := by
  apply TokenizationFrom.token (w := []) (s := chars "(") (rest := chars "a 123")
    whitespace_nil paren_open (Or.inl rfl)
  apply TokenizationFrom.token (w := []) (s := chars "a") (rest := chars " 123")
    whitespace_nil symbol_a (delimited_space (more := chars "123"))
  apply TokenizationFrom.token (w := chars " ") (s := chars "123") (rest := [])
    (whitespace_spaces (by decide)) numeral_123 delimited_end
  exact done_spaces (by simp)

/-- After `(a 12`, the tokens `(` and `a` are determined: the space after `a` ends it. -/
theorem determined_a_12 : Determined .v2_7 (chars "(a 12")
    [⟨.parenOpen, 0, chars "("⟩, ⟨.simpleSymbol, 1, chars "a"⟩] := by
  intro rest ts h
  rw [Tokenization, split (chars "(a 12") [] (chars "(") (chars "a 12") (by decide)] at h
  obtain ⟨ts, -, h₁, rfl⟩ := tokenizationFrom_head whitespace_nil paren_open
    (headOf_delimited paren_open (Or.inl rfl)) h
  rw [split (chars "a 12") [] (chars "a") (chars " 12") (by decide)] at h₁
  obtain ⟨ts, -, -, rfl⟩ := tokenizationFrom_head whitespace_nil symbol_a
    (headOf_delimited symbol_a delimited_space) h₁
  exact ⟨ts, rfl⟩

/-- After `(a 12`, the tokens `(`, `a` and `12` are not determined: `(a 123` goes on to
`123`. -/
example : ¬ Determined .v2_7 (chars "(a 12")
    [⟨.parenOpen, 0, chars "("⟩, ⟨.simpleSymbol, 1, chars "a"⟩, ⟨.numeral, 3, chars "12"⟩] := by
  intro h
  obtain ⟨more, hmore⟩ := h (chars "3") _ tokenization_a_123
  simp only [List.cons_append, List.nil_append, List.cons.injEq, Token.mk.injEq] at hmore
  exact absurd hmore.2.2.1.2.2 (by decide)

/-- After `(a 12`, the tokens that can be handed over are exactly `(` and `a`: `12` cannot,
since a digit may still follow it. -/
example : ∀ tokens, HandoverMaximal .v2_7 (chars "(a 12") tokens ↔
    tokens = [⟨.parenOpen, 0, chars "("⟩, ⟨.simpleSymbol, 1, chars "a"⟩] := by
  have hs : HandoverMaximal .v2_7 (chars "(a 12")
      [⟨.parenOpen, 0, chars "("⟩, ⟨.simpleSymbol, 1, chars "a"⟩] := by
    refine ⟨⟨determined_a_12, ?_⟩, ?_⟩
    · intro token htoken
      simp only [List.mem_cons, List.not_mem_nil, or_false] at htoken
      rcases htoken with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (by decide))
    · rintro tokens' ⟨hd, hfed⟩
      exact delimiterSeen_bound (k := 2) (determined_prefix hd tokenization_a_123) (by decide)
        (by simp [DelimiterSeen] <;> decide) hfed
  intro tokens
  constructor
  · intro h
    exact handoverMaximal_unique ⟨chars "3", _, tokenization_a_123⟩ h hs
  · rintro rfl
    exact hs

/-! ## `(x |abc|` and `(x |abc| ` in 2.7 -/

/-- `(x |abc| ` is tokenised as `(`, `x` and `|abc|`. -/
theorem tokenization_x_abc : Tokenization .v2_7 (chars "(x |abc| ")
    [⟨.parenOpen, 0, chars "("⟩, ⟨.simpleSymbol, 1, chars "x"⟩,
      ⟨.quotedSymbol, 3, chars "|abc|"⟩] := by
  apply TokenizationFrom.token (w := []) (s := chars "(") (rest := chars "x |abc| ")
    whitespace_nil paren_open (Or.inl rfl)
  apply TokenizationFrom.token (w := []) (s := chars "x") (rest := chars " |abc| ")
    whitespace_nil symbol_x (delimited_space (more := chars "|abc| "))
  apply TokenizationFrom.token (category := .quotedSymbol) (w := chars " ") (s := chars "|abc|")
    (rest := chars " ") (whitespace_spaces (by decide)) quoted_abc (delimited_space (more := []))
  exact done_spaces (by decide)

/-- After `(x |abc|`, the tokens `(`, `x` and `|abc|` are determined: a quoted symbol ends at
its closing `|`, whatever follows. -/
theorem determined_x_abc : Determined .v2_7 (chars "(x |abc|")
    [⟨.parenOpen, 0, chars "("⟩, ⟨.simpleSymbol, 1, chars "x"⟩,
      ⟨.quotedSymbol, 3, chars "|abc|"⟩] := by
  intro rest ts h
  rw [Tokenization, split (chars "(x |abc|") [] (chars "(") (chars "x |abc|") (by decide)] at h
  obtain ⟨ts, -, h₁, rfl⟩ := tokenizationFrom_head whitespace_nil paren_open
    (headOf_delimited paren_open (Or.inl rfl)) h
  rw [split (chars "x |abc|") [] (chars "x") (chars " |abc|") (by decide)] at h₁
  obtain ⟨ts, -, h₂, rfl⟩ := tokenizationFrom_head (x := chars " |abc|" ++ rest) whitespace_nil
    symbol_x (headOf_delimited symbol_x delimited_space) h₁
  rw [split (chars " |abc|") (chars " ") (chars "|abc|") [] (by decide)] at h₂
  obtain ⟨ts, -, -, rfl⟩ := tokenizationFrom_head (category := .quotedSymbol)
    (whitespace_spaces (by decide)) quoted_abc (headOf_quoted quoted_abc) h₂
  exact ⟨ts, rfl⟩

/-- After `(x |abc|`, the tokens `(`, `x` and `|abc|` are determined, but only `(` and `x`
can be handed over: the character after `|abc|` has not been read yet. -/
example : Determined .v2_7 (chars "(x |abc|")
      [⟨.parenOpen, 0, chars "("⟩, ⟨.simpleSymbol, 1, chars "x"⟩,
        ⟨.quotedSymbol, 3, chars "|abc|"⟩] ∧
    HandoverMaximal .v2_7 (chars "(x |abc|")
      [⟨.parenOpen, 0, chars "("⟩, ⟨.simpleSymbol, 1, chars "x"⟩] := by
  refine ⟨determined_x_abc, ⟨?_, ?_⟩, ?_⟩
  · intro rest ts h
    obtain ⟨more, rfl⟩ := determined_x_abc rest ts h
    exact ⟨_ :: more, rfl⟩
  · intro token htoken
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htoken
    rcases htoken with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (by decide))
  · rintro tokens' ⟨hd, hfed⟩
    exact delimiterSeen_bound (k := 2) (determined_prefix (rest := chars " ") hd tokenization_x_abc)
      (by decide) (by simp [DelimiterSeen] <;> decide) hfed

/-- After `(x |abc| `, the tokens that can be handed over are `(`, `x` and `|abc|`: the space
after `|abc|` has been read. -/
example : HandoverMaximal .v2_7 (chars "(x |abc| ")
    [⟨.parenOpen, 0, chars "("⟩, ⟨.simpleSymbol, 1, chars "x"⟩,
      ⟨.quotedSymbol, 3, chars "|abc|"⟩] := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [show chars "(x |abc| " = chars "(x |abc|" ++ chars " " by decide]
    exact determined_append determined_x_abc
  · intro token htoken
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htoken
    rcases htoken with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (by decide))
    · exact Or.inr (Or.inr (by decide))
  · rintro tokens' ⟨hd, -⟩
    exact (determined_prefix (rest := []) hd (by simpa using tokenization_x_abc)).length_le

/-! ## `"ab"` in 2.7 and in 2.0 -/

/-- In 2.7, `"ab""c"` is one string literal. -/
theorem tokenization_ab_c : Tokenization .v2_7 (chars "\"ab\"\"c\"")
    [⟨.string, 0, chars "\"ab\"\"c\""⟩] := by
  apply TokenizationFrom.token (category := .string) (w := []) (s := chars "\"ab\"\"c\"")
    (rest := []) whitespace_nil ?_ delimited_end
  · exact done_spaces (by simp)
  · have body := star_parts (r := alt (minus (alt printableChar whiteSpaceChar) (lit "\""))
      (lit "\"\"")) [[97], [98], [34, 34], [99]] fun p hp => stringPart_of_ok (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> decide)
    show string (chars "\"" ++ ([[97], [98], [34, 34], [99]].flatten ++ chars "\""))
    exact seq_intro rfl (seq_intro body rfl)

/-- In 2.7, the string literal `"ab"` is not determined by `"ab"`: in `"ab""c"`, the `"` after
`ab` is the first of a doubled `"`. -/
example : ¬ Determined .v2_7 (chars "\"ab\"") [⟨.string, 0, chars "\"ab\""⟩] := by
  intro h
  obtain ⟨more, hmore⟩ := h (chars "\"c\"") _ tokenization_ab_c
  simp only [List.cons_append, List.nil_append, List.cons.injEq, Token.mk.injEq] at hmore
  exact absurd hmore.1.2.2 (by decide)

/-- In 2.0, `"ab"` is one string literal. -/
theorem tokenization_ab_20 : Tokenization .v2_0 (chars "\"ab\"")
    [⟨.string, 0, chars "\"ab\""⟩] := by
  apply TokenizationFrom.token (category := .string) (w := []) (s := chars "\"ab\"")
    (rest := []) whitespace_nil string_ab_20 delimited_end
  exact done_spaces (by simp)

/-- In 2.0, the string literal `"ab"` is determined by `"ab"`, since a `"` inside a string
literal is escaped by a backslash, not doubled; but no token can be handed over yet, since the
character after the string literal has not been read. -/
example : Determined .v2_0 (chars "\"ab\"") [⟨.string, 0, chars "\"ab\""⟩] ∧
    HandoverMaximal .v2_0 (chars "\"ab\"") [] := by
  refine ⟨?_, ⟨fun _ _ _ => ⟨_, rfl⟩, by simp⟩, ?_⟩
  · intro rest ts h
    rw [Tokenization, split (chars "\"ab\"") [] (chars "\"ab\"") [] (by decide)] at h
    obtain ⟨ts, -, -, rfl⟩ := tokenizationFrom_head (category := .string) whitespace_nil
      string_ab_20 (headOf_string20 string20_ab) h
    exact ⟨ts, rfl⟩
  · rintro tokens' ⟨hd, hfed⟩
    exact delimiterSeen_bound (k := 0)
      (determined_prefix (rest := []) hd (by simpa using tokenization_ab_20))
      (by decide) (by simp [DelimiterSeen] <;> decide) hfed

/-! ## `|a|x` in 2.7 -/

/-- `|a|x` is not viable: the quoted symbol `|a|` must be followed by a delimiter, and no
characters that follow can change that `x` follows it. -/
theorem not_viable_a_x : ¬ Viable .v2_7 (chars "|a|x") := by
  rintro ⟨rest, ts, h⟩
  rw [Tokenization, split (chars "|a|x") [] (chars "|a|") (chars "x") (by decide)] at h
  obtain ⟨-, hd, -⟩ := tokenizationFrom_head (category := .quotedSymbol) whitespace_nil
    quoted_a (headOf_quoted quoted_a) h
  rcases delimRest_of hd (by decide) (by decide) with h0 | ⟨c, m, hcm, hc⟩
  · simp [chars] at h0
  · rw [show chars "x" ++ rest = 120 :: rest from rfl, List.cons.injEq] at hcm
    rw [← hcm.1] at hc
    simp only [Delim] at hc
    revert hc
    decide

/-- `|a|x` is not viable, so every list of tokens is determined by it, a non-empty one as
well. -/
example : ¬ Viable .v2_7 (chars "|a|x") ∧
    Determined .v2_7 (chars "|a|x") [⟨.numeral, 7, chars "42"⟩] :=
  ⟨not_viable_a_x, determined_of_not_viable not_viable_a_x⟩

/-- No list of tokens is `HandoverMaximal` on `|a|x`: since it is not viable, every list of `(`
is determined by it, and those lists are as long as one likes. `HandsOverMaximal` asks for
the maximal tokens of the longest viable start only. -/
example : ¬ ∃ tokens, HandoverMaximal .v2_7 (chars "|a|x") tokens := by
  rintro ⟨tokens, -, hmax⟩
  have h := hmax (List.replicate (tokens.length + 1) ⟨.parenOpen, 0, chars "("⟩)
    ⟨determined_of_not_viable not_viable_a_x,
      fun token htoken => Or.inl (List.eq_of_mem_replicate htoken ▸ rfl)⟩
  rw [List.length_replicate] at h
  omega

end BSmtLib.SpecChecks.Lexer
