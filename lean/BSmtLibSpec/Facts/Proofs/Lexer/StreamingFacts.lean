import BSmtLibSpec.Facts.Proofs.Lexer.Streaming

/-!
# Facts about a lexer fed in slices

The definitions of a lexer fed in slices ask for things that need not exist: the longest viable
start of an input, and a list of tokens that are maximal to hand over. This module proves that
they exist, so that `HandsOverMaximal` is not vacuous; and that a lexer that is `Correct` is
`Sequential` and `WholeInputCorrect`. Not trusted: these are proofs.
-/

namespace BSmtLibSpec.Facts.Proofs.Lexer.StreamingFacts

open BSmtLibSpec.Lexicon BSmtLibSpec.Lexer
open BSmtLibSpec.Lexicon.Properties
open BSmtLibSpec.Regex (Chars)
open BSmtLibSpec.Facts.Proofs.Lexer.Streaming BSmtLibSpec.Facts.Proofs.Lexicon.Lemmas
open BSmtLibSpec.Facts.Proofs.Lexicon.Unique

/-! ## Greatest numbers -/

/-- Up to `n`, a property that holds of `0` holds of a greatest number. -/
theorem exists_greatest (P : Nat → Prop) (n : Nat) (h0 : P 0) :
    ∃ k, k ≤ n ∧ P k ∧ ∀ j, j ≤ n → P j → j ≤ k := by
  induction n with
  | zero => exact ⟨0, Nat.le_refl _, h0, fun _ hj _ => hj⟩
  | succ n ih =>
    obtain ⟨k, hk, hpk, hmax⟩ := ih
    by_cases hn : P (n + 1)
    · exact ⟨n + 1, Nat.le_refl _, hn, fun _ hj _ => hj⟩
    · refine ⟨k, Nat.le_succ_of_le hk, hpk, fun j hj hpj => ?_⟩
      rcases Nat.lt_or_eq_of_le hj with hlt | heq
      · exact hmax j (Nat.le_of_lt_succ hlt) hpj
      · exact absurd (heq ▸ hpj) hn

/-! ## Viable starts -/

/-- The empty input is viable: it is its own tokenisation, with no tokens. -/
theorem viable_nil (version : Version) : Viable version [] :=
  ⟨[], [], .done ⟨[], [], rfl, whitespace_nil, Or.inl rfl⟩⟩

/-- A start of a viable input is viable. -/
theorem viable_of_prefix {version : Version} {start input : Chars} (hp : start <+: input)
    (h : Viable version input) : Viable version start := by
  obtain ⟨more, rfl⟩ := hp
  obtain ⟨rest, ts, ht⟩ := h
  exact ⟨more ++ rest, ts, by simpa only [List.append_assoc] using ht⟩

/-- Every input has a longest viable start. -/
theorem exists_longestViableStart (version : Version) (input : Chars) :
    ∃ start, LongestViableStart version input start := by
  obtain ⟨k, -, hk, hmax⟩ := exists_greatest (fun k => Viable version (input.take k))
    input.length (by simpa using viable_nil version)
  refine ⟨input.take k, List.take_prefix k input, hk, fun longer hp hv => ?_⟩
  have hle := hp.length_le
  have e : longer = input.take longer.length := List.prefix_iff_eq_take.mp hp
  have := hmax longer.length hle (e ▸ hv)
  rw [List.length_take]
  omega

/-- An input has at most one longest viable start. -/
theorem longestViableStart_unique {version : Version} {input s₁ s₂ : Chars}
    (h₁ : LongestViableStart version input s₁) (h₂ : LongestViableStart version input s₂) :
    s₁ = s₂ := by
  have hl : s₁.length = s₂.length :=
    Nat.le_antisymm (h₂.2.2 s₁ h₁.1 h₁.2.1) (h₁.2.2 s₂ h₂.1 h₂.2.1)
  rw [List.prefix_iff_eq_take.mp h₁.1, List.prefix_iff_eq_take.mp h₂.1, hl]

/-- The longest viable start of a viable input is all of it. -/
theorem longestViableStart_viable {version : Version} {input start : Chars}
    (h : LongestViableStart version input start) (hv : Viable version input) : start = input :=
  longestViableStart_unique h ⟨List.prefix_refl input, hv, fun _ hp _ => hp.length_le⟩

/-- The longest viable start of an input starts the longest viable start of a longer input. -/
theorem longestViableStart_prefix {version : Version} {input more s s' : Chars}
    (h : LongestViableStart version input s)
    (h' : LongestViableStart version (input ++ more) s') : s <+: s' := by
  have hp : s <+: input ++ more := h.1.trans (List.prefix_append input more)
  exact List.prefix_of_prefix_length_le hp h'.1 (h'.2.2 s hp h.2.1)

/-! ## Tokens ready to be handed over -/

/-- No tokens are ready to be handed over. -/
theorem handoverReady_nil (version : Version) (input : Chars) :
    HandoverReady version input [] :=
  ⟨fun _ _ _ => ⟨_, rfl⟩, fun _ h => absurd h (List.not_mem_nil)⟩

/-- On a viable input, some tokens are maximal to hand over. -/
theorem exists_handoverMaximal {version : Version} {input : Chars} (hv : Viable version input) :
    ∃ tokens, HandoverMaximal version input tokens := by
  obtain ⟨rest, all, ht⟩ := hv
  obtain ⟨k, -, hk, hmax⟩ := exists_greatest
    (fun k => HandoverReady version input (all.take k)) all.length
    (by simpa using handoverReady_nil version input)
  refine ⟨all.take k, hk, fun tokens' h' => ?_⟩
  have hp := determined_prefix h'.1 ht
  have e : tokens' = all.take tokens'.length := List.prefix_iff_eq_take.mp hp
  have := hmax tokens'.length hp.length_le (e ▸ h')
  rw [List.length_take]
  have := hp.length_le
  omega

/-- Tokens that are ready on an input are ready on a longer one. -/
theorem handoverReady_append {version : Version} {input more : Chars} {tokens : List Token}
    (h : HandoverReady version input tokens) : HandoverReady version (input ++ more) tokens := by
  refine ⟨determined_append h.1, fun token htoken => ?_⟩
  rcases h.2 token htoken with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ?_)
    simp only [List.length_append]
    omega

/-! ## Where the tokens ready to be handed over are -/

/-- Every token of a tokenisation is a token of its kind, at or after its offset. -/
theorem tokenizationFrom_mem {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} (h : Tokenization.From version offset input tokens) :
    ∀ token ∈ tokens, categoryRegex version token.category token.text ∧ offset ≤ token.offset := by
  induction h with
  | done => simp
  | token _ hs _ _ ih =>
    intro token htoken
    rcases List.mem_cons.mp htoken with rfl | htoken
    · exact ⟨hs, by simp⟩
    · obtain ⟨hr, hle⟩ := ih token htoken
      exact ⟨hr, by omega⟩

/-- Taking the characters that follow a token keeps it delimited. -/
theorem delimited_take {category : Category} {rest : Chars} (n : Nat)
    (h : Tokenization.Delimited category rest) : Tokenization.Delimited category (rest.take n) := by
  rcases h with h | h | h | ⟨c, more, rfl, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (by simp [h])))
  · cases n with
    | zero => exact Or.inr (Or.inr (Or.inl rfl))
    | succ n => exact Or.inr (Or.inr (Or.inr ⟨c, more.take n, rfl, hc⟩))

/-- Taking past the end of the first of two lists. -/
theorem take_append_ge {α : Type} {xs ys : List α} {n : Nat} (h : xs.length ≤ n) :
    (xs ++ ys).take n = xs ++ ys.take (n - xs.length) := by
  rw [List.take_append, List.take_of_length_le h]

/-- The characters up to a token of a tokenisation are tokenised by the tokens before it. -/
theorem tokenizationFrom_take {version : Version} {offset : Nat} {input : Chars}
    {before : List Token} {token : Token} {after : List Token}
    (h : Tokenization.From version offset input (before ++ token :: after)) :
    Tokenization.From version offset (input.take (token.offset - offset)) before := by
  induction before generalizing offset input with
  | nil =>
    rcases tokenizationFrom_inv h with ⟨he, -⟩ | ⟨w, category, s, rest, ts, rfl, hw, -, -, -, he⟩
    · simp at he
    · simp only [List.nil_append, List.cons.injEq] at he
      rw [he.1]
      simp only [Nat.add_sub_cancel_left, List.append_assoc, List.take_left']
      exact .done ⟨w, [], by simp, hw, Or.inl rfl⟩
  | cons first before ih =>
    rcases tokenizationFrom_inv h with
      ⟨he, -⟩ | ⟨w, category, s, rest, ts, rfl, hw, hs, hd, hrest, he⟩
    · simp at he
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hle := (tokenizationFrom_mem hrest token (by simp)).2
      have e : (w ++ s ++ rest).take (token.offset - offset) =
          w ++ s ++ rest.take (token.offset - (offset + w.length + s.length)) := by
        rw [take_append_ge (by simp; omega)]
        congr 2
        simp only [List.length_append]
        omega
      rw [e]
      exact .token hw hs (delimited_take _ hd) (ih hrest)

/-- The tokens that are ready to be handed over on a viable input end within it. -/
theorem handoverReady_within {version : Version} {input : Chars} {tokens : List Token}
    (hv : Viable version input) (h : HandoverReady version input tokens) :
    ∀ token ∈ tokens, token.offset + token.text.length ≤ input.length := by
  intro token htoken
  obtain ⟨rest, all, ht⟩ := hv
  obtain ⟨more, rfl⟩ := determined_prefix h.1 ht
  obtain ⟨before, after, rfl⟩ := List.append_of_mem htoken
  have hr := (tokenizationFrom_mem ht token (by simp)).1
  rcases h.2 token htoken with hc | hc | hc
  all_goals first
    | omega
    | skip
  all_goals
    have hlen : token.text.length = 1 := by
      have e := hr
      rw [hc] at e
      simp only [categoryRegex] at e
      rw [lit_iff.mp e]
      rfl
    rw [hlen]
    refine Nat.succ_le_of_lt (Nat.lt_of_not_le fun hge => ?_)
    -- the input followed by the characters up to the token is tokenised without it
    have ht' : Tokenization.From version 0 (input ++ rest)
        (before ++ token :: (after ++ more)) := by
      simpa only [Tokenization, List.append_assoc, List.cons_append] using ht
    have hcut := tokenizationFrom_take ht'
    rw [Nat.sub_zero, take_append_ge hge] at hcut
    obtain ⟨more', hmore⟩ := h.1 _ _ hcut
    have := congrArg List.length hmore
    simp only [List.length_append, List.length_cons] at this
    omega

/-- The location of an offset within an input is its location in any longer input. -/
theorem locate_append {input more : Chars} {offset : Nat} (h : offset ≤ input.length) :
    locate (input ++ more) offset = locate input offset := by
  simp only [locate, List.take_append_of_le_length h]

/-! ## A correct lexer -/

/-- A tokenised input is viable. -/
theorem viable_of_tokenization {version : Version} {input : Chars} {tokens : List Token}
    (h : Tokenization version input tokens) : Viable version input :=
  ⟨[], tokens, by simpa using h⟩

/-- A correct lexer has failed exactly when the input can no longer be valid. -/
theorem failsCorrectly_of_correct {feed : Version → List Chars → Bool → Fed} (h : Correct feed)
    (version : Version) (slices : List Chars) (ended : Bool) :
    FailsCorrectly feed version slices ended :=
  (h version slices ended []).1

/-- A correct lexer fed slices of a complete input has handed over all of its tokens. -/
theorem handsOverAll_of_correct {feed : Version → List Chars → Bool → Fed} (h : Correct feed)
    {version : Version} {slices : List Chars} {ended : Bool}
    (hc : Complete version slices.flatten ended) : HandsOverAll feed version slices := by
  have := (h version slices ended []).2
  unfold HandsOverCorrectly at this
  rwa [ite_eq_left_of_eq_true _ _ (eq_true hc)] at this

/-- A correct lexer fed slices of an input that is not complete has handed over the tokens
maximal to hand over on its longest viable start. -/
theorem handsOverMaximal_of_correct {feed : Version → List Chars → Bool → Fed} (h : Correct feed)
    {version : Version} {slices : List Chars} {ended : Bool}
    (hc : ¬ Complete version slices.flatten ended) (start : Chars) :
    HandsOverMaximal feed version slices ended start := by
  have := (h version slices ended start).2
  unfold HandsOverCorrectly at this
  rwa [ite_eq_right_of_eq_false _ _ (eq_false hc)] at this

/-- An input that has not ended is not complete. -/
theorem not_complete_false (version : Version) (input : Chars) :
    ¬ Complete version input false :=
  fun h => Bool.false_ne_true h.1

/-- What a correct lexer has handed over on a start of the input before the end, it has handed
over on the whole input before the end. -/
theorem handed_prefix_of_correct {feed : Version → List Chars → Bool → Fed} (h : Correct feed)
    (version : Version) (slices more : List Chars) :
    (feed version slices false).handed <+: (feed version (slices ++ more) false).handed := by
  obtain ⟨s, hs⟩ := exists_longestViableStart version slices.flatten
  obtain ⟨s', hs'⟩ := exists_longestViableStart version (slices ++ more).flatten
  have hs'' := hs'
  rw [List.flatten_append] at hs'
  obtain ⟨tokens, hmax, he⟩ :=
    handsOverMaximal_of_correct h (not_complete_false version slices.flatten) s hs
  obtain ⟨tokens', hmax', he'⟩ :=
    handsOverMaximal_of_correct h (not_complete_false version (slices ++ more).flatten) s' hs''
  obtain ⟨d, rfl⟩ := longestViableStart_prefix hs hs'
  -- the tokens maximal on the shorter start start those maximal on the longer one
  obtain ⟨rest, all, ht⟩ := hs'.2.1
  have hp : tokens <+: tokens' := by
    have h1 := determined_prefix (handoverReady_append (more := d) hmax.1).1 ht
    have h2 := determined_prefix hmax'.1.1 ht
    have hle := hmax'.2 tokens (handoverReady_append hmax.1)
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    rw [← hb] at ha
    exact List.prefix_iff_eq_take.mpr (by
      rw [← List.prefix_iff_eq_take]
      exact (List.prefix_of_prefix_length_le ⟨a, ha⟩ ⟨b, rfl⟩ hle))
  obtain ⟨extra, rfl⟩ := hp
  rw [he, he', List.flatten_append, List.map_append]
  refine ⟨extra.map (·.handed version (slices.flatten ++ more.flatten)), ?_⟩
  congr 1
  refine List.map_congr_left fun token htoken => ?_
  have hw := handoverReady_within hs.2.1 hmax.1 token htoken
  have hsl := hs.1.length_le
  simp only [Token.handed, locate_append (show token.offset ≤ slices.flatten.length by omega),
    locate_append (show token.offset + token.text.length ≤ slices.flatten.length by omega)]

/-- What a correct lexer has handed over before the end of the input, it has handed over at the
end too. -/
theorem handed_prefix_end_of_correct {feed : Version → List Chars → Bool → Fed} (h : Correct feed)
    (version : Version) (slices : List Chars) :
    (feed version slices false).handed <+: (feed version slices true).handed := by
  obtain ⟨s, hs⟩ := exists_longestViableStart version slices.flatten
  obtain ⟨tokens, hmax, he⟩ :=
    handsOverMaximal_of_correct h (not_complete_false version slices.flatten) s hs
  rw [he]
  by_cases hc : Complete version slices.flatten true
  · -- the tokens maximal on all of the input start its tokenisation
    obtain ⟨all, ht, he'⟩ := handsOverAll_of_correct h hc
    rw [he']
    rw [longestViableStart_viable hs (viable_of_tokenization ht)] at hmax
    obtain ⟨more, rfl⟩ :=
      determined_prefix (rest := []) hmax.1.1 (by simpa only [List.append_nil] using ht)
    rw [List.map_append, List.append_assoc]
    exact List.prefix_append _ _
  · -- the end of the input releases nothing: the same tokens are maximal
    obtain ⟨tokens', hmax', he'⟩ := handsOverMaximal_of_correct h hc s hs
    rw [he', handoverMaximal_unique hs.2.1 hmax hmax']
    exact List.prefix_refl _

/-- A lexer that is `Correct` is `Sequential`: fed more slices, or the end of the input, it has
handed over what it had and possibly more, and once it has failed, it stays failed. -/
theorem sequential_of_correct {feed : Version → List Chars → Bool → Fed} (h : Correct feed) :
    ∀ version slices more, Sequential feed version slices more := by
  intro version slices more
  have hf := failsCorrectly_of_correct h version
  refine ⟨⟨handed_prefix_of_correct h version slices more, fun hfailed => ?_⟩,
    ⟨handed_prefix_end_of_correct h version slices, fun hfailed => ?_⟩⟩
  · have h1 := (hf slices false).mp hfailed
    refine (hf (slices ++ more) false).mpr ?_
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 ⊢
    intro hv
    rw [List.flatten_append] at hv
    exact h1 (viable_of_prefix (List.prefix_append _ _) hv)
  · have h1 := (hf slices false).mp hfailed
    refine (hf slices true).mpr ?_
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 ⊢
    exact fun ⟨tokens, ht⟩ => h1 (viable_of_tokenization ht)

/-- A lexer that is `Correct` is `WholeInputCorrect`: fed slices and the end of the input, it
has not failed and has handed over the tokens of the tokenisation and the end-of-file token
exactly when the input has a tokenisation. -/
theorem wholeInputCorrect_of_correct {feed : Version → List Chars → Bool → Fed}
    (h : Correct feed) : ∀ version slices handed, WholeInputCorrect feed version slices handed := by
  intro version slices handed
  have hf := failsCorrectly_of_correct h version slices true
  simp only [FailsCorrectly, ↓reduceIte] at hf
  simp only [WholeInputCorrect]
  constructor
  · rintro ⟨hnf, rfl⟩
    have hc : Complete version slices.flatten true :=
      ⟨rfl, Classical.not_not.mp fun hn => hnf (hf.mpr hn)⟩
    exact handsOverAll_of_correct h hc
  · rintro ⟨tokens, ht, rfl⟩
    have hc : Complete version slices.flatten true := ⟨rfl, tokens, ht⟩
    obtain ⟨tokens', ht', he⟩ := handsOverAll_of_correct h hc
    refine ⟨fun hfailed => hf.mp hfailed ⟨tokens, ht⟩, ?_⟩
    rw [he, Lexicon.Unique.tokenizationFrom_unique ht' ht]

end BSmtLibSpec.Facts.Proofs.Lexer.StreamingFacts
