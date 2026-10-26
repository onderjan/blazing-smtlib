module

public import BSmtLib.Facts.Proofs.Reader.Requests
public import BSmtLib.Facts.Proofs.Reader.Feed
public import BSmtLib.Facts.Proofs.Parser.Rejection.Discard

@[expose] public section

/-!
# The script consumer at a token, and what a correct lexer hands over

The pieces of the walk through `BSmtLibSpec.Lexer.Runs` in `Classify`:

- what a correct lexer hands over from an offset, read on its own after the end of the input:
  lexical tokens, located in the whole input, and the end-of-file token last unless it
  failed (`segment_mem`, `segment_ofVersion`, `segment_ends`);
- facts about what a parser takes: how it ends (`takes_ending`, `takes_finished_last`), the
  version in force after an item (`versionAt_succ`), where discarding is asked for
  (`takes_discards`);
- the script consumer at a token after tokens that stand for a proper start of what a parser
  takes (`consumer_step`): it rejects the token where no such start goes on with it
  (`RejectsFirstUnviable`), goes on where one does, breaks at the end of the input of a script,
  and fails at the `)` of a declaration that names no supported version.
-/

namespace BSmtLib.Facts.Proofs.Reader.Outcome

open BSmtLibSpec BSmtLibSpec.Grammar BSmtLibSpec.Lexer
open BSmtLibSpec.Parser.Properties (Takes Ending versionAt)
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Facts.Parser.Adapters.Run.Rejection (libraryParser)
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection (rcv)
open BSmtLib.Facts.Proofs.Parser.Rejection.Library (rejects_items)
open BSmtLib.Facts.Proofs.Parser.Rejection.Unique (versionAt_unique)
open BSmtLib.Facts.Proofs.Parser.Rejection.Script (AfterExit)
open BSmtLib.Facts.Proofs.Parser.Trace (requestsAt)
open BSmtLib.Facts.Proofs.Reader.Consumer BSmtLib.Facts.Proofs.Reader.Requests
open BSmtLib.Facts.Reader.Adapters

/-! ## The tokens a correct lexer hands over -/

/-- A token relocated stands for the same parser token. -/
theorem itemOf_after (before : Regex.Chars) (handed : Handed) :
    itemOf (handed.after before) = itemOf handed := by
  cases handed
  rfl

/-- A handed token stands for the end of the input exactly when it is the end-of-file token. -/
theorem rcv_itemOf_endOfInput_iff (handed : Handed) :
    rcv (itemOf handed) = .endOfInput ↔ handed.type = .endOfFile := by
  obtain ⟨type, start, stop, reserved, content⟩ := handed
  cases type <;> simp only [itemOf] <;> (try split) <;>
    simp [rcv, Parser.Adapters.Bridge.Bridge.received]

variable {feed : Lexicon.Version → List Regex.Chars → Bool → Fed}

/-- What a correct lexer hands over from an offset on, read on its own after the end of the
input: the end-of-file token, or lexical tokens located in the whole input. -/
theorem segment_mem (hc : Correct feed) (version : Lexicon.Version) (input : Regex.Chars)
    (offset : Nat) :
    ∀ h ∈ (segment feed version input true offset).handed, h.type = .endOfFile ∨
      ∃ token : Lexicon.Token, Lexicon.categoryRegex version token.category token.text ∧
        h = (token.handed version (input.drop offset)).after (input.take offset) := by
  intro h hh
  simp only [segment] at hh
  obtain ⟨h₀, hh₀, rfl⟩ := List.mem_map.mp hh
  have hf : [input.drop offset].flatten = input.drop offset := by simp
  by_cases hcomp : Complete version [input.drop offset].flatten true
  · obtain ⟨t, ht, e⟩ := Facts.Proofs.Lexer.StreamingFacts.handsOverAll_of_correct hc hcomp
    rw [e, hf] at hh₀
    rw [hf] at ht
    rcases List.mem_append.mp hh₀ with hh₀ | hh₀
    · obtain ⟨token, htoken, rfl⟩ := List.mem_map.mp hh₀
      exact Or.inr ⟨token, (Facts.Proofs.Lexer.StreamingFacts.tokenizationFrom_mem ht token
          htoken).1, rfl⟩
    · rw [List.mem_singleton.mp hh₀]
      exact Or.inl rfl
  · obtain ⟨s, hs⟩ := Facts.Proofs.Lexer.StreamingFacts.exists_longestViableStart version
      [input.drop offset].flatten
    obtain ⟨t, hmax, e⟩ := Facts.Proofs.Lexer.StreamingFacts.handsOverMaximal_of_correct hc hcomp s
        hs
    rw [e, hf] at hh₀
    obtain ⟨token, htoken, rfl⟩ := List.mem_map.mp hh₀
    obtain ⟨rest, all, hall⟩ := hs.2.1
    obtain ⟨more, rfl⟩ := hmax.1.1 rest all hall
    exact Or.inr ⟨token, (Facts.Proofs.Lexer.StreamingFacts.tokenizationFrom_mem hall token
      (List.mem_append_left _ htoken)).1, rfl⟩

/-- A token a correct lexer hands over from an offset on stands for an item that a lexer can hand
over in the version. -/
theorem segment_ofVersion (hc : Correct feed) (version : Lexicon.Version)
    (input : Regex.Chars) (offset : Nat) :
    ∀ h ∈ (segment feed version input true offset).handed,
      (rcv (itemOf h)).OfVersion version := by
  intro h hh
  rcases segment_mem hc version input offset h hh with he | ⟨token, hcat, rfl⟩
  · rw [(rcv_itemOf_endOfInput_iff h).mpr he]
    trivial
  · rw [itemOf_after, rcv_itemOf_handed _ hcat]
    obtain ⟨category, offset, text⟩ := token
    cases category <;> try trivial
    exact Facts.Proofs.Lexicon.Lemmas.litOneOf_iff.mp hcat

/-- A correct lexer that has not failed after the end of the input has handed over the
end-of-file token last. -/
theorem segment_ends (hc : Correct feed) (version : Lexicon.Version) (input : Regex.Chars)
    (offset : Nat) (hf : (segment feed version input true offset).failed = false) :
    ∃ init last, (segment feed version input true offset).handed = init ++ [last] ∧
      last.type = .endOfFile := by
  have hfc := Facts.Proofs.Lexer.StreamingFacts.failsCorrectly_of_correct hc
      version [input.drop offset] true
  simp only [FailsCorrectly, ite_true] at hfc
  simp only [segment] at hf ⊢
  rw [hf] at hfc
  have hex : ∃ tokens, Lexicon.Tokenization version [input.drop offset].flatten tokens := by
    refine Classical.byContradiction fun hne => ?_
    exact Bool.false_ne_true (hfc.mpr hne)
  obtain ⟨t, ht, e⟩ := Facts.Proofs.Lexer.StreamingFacts.handsOverAll_of_correct hc ⟨rfl, hex⟩
  rw [e, List.map_append]
  exact ⟨_, _, rfl, rfl⟩

/-! ## What a parser takes -/

/-- What a parser takes ends finished, or failed on a declaration that names no supported
version. -/
theorem takes_ending {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (h : Takes version commands taken ending) :
    ending = .finished ∨ ending = .failed .unsupportedVersion := by
  induction h with
  | done => exact Or.inl rfl
  | command _ _ _ ih => exact ih
  | stop => exact Or.inl rfl
  | refused => exact Or.inr rfl

/-- What a parser takes for a script ends with the end of the input. -/
theorem takes_finished_last {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (h : Takes version commands taken ending) :
    ending = .finished → taken.getLast? = some .endOfInput := by
  induction h with
  | done => intro; rfl
  | @command v next rest items ending first hv hm _ ih =>
    intro he
    rw [List.getLast?_append, ih he]
    rfl
  | stop => intro; simp
  | refused => intro he; cases he

theorem versionAt_zero (version : Lexicon.Version) (commands : List Tree.Command) :
    versionAt version commands 0 = version := by
  cases commands with
  | nil => rfl
  | cons c cs => simp [versionAt, tokens_length_pos c]

/-- The version in force at the next item is the one asked for after an item, if one is. -/
theorem versionAt_succ : ∀ (commands : List Tree.Command) (version : Lexicon.Version) (k : Nat),
    versionAt version commands (k + 1) =
      (requestsAt commands k).1.getD (versionAt version commands k)
  | [], _, _ => rfl
  | c :: rest, version, k => by
    by_cases h1 : k + 1 < c.tokens.length
    · simp [versionAt, requestsAt, h1, show k < c.tokens.length by omega]
    · by_cases h2 : k + 1 = c.tokens.length
      · simp [versionAt, requestsAt, h2, show k < c.tokens.length by omega, versionAt_zero]
      · have hk : ¬ k < c.tokens.length := by omega
        simp only [versionAt, requestsAt, h1, h2, hk, ite_false]
        rw [show k + 1 - c.tokens.length = (k - c.tokens.length) + 1 by omega]
        exact versionAt_succ rest _ _

/-- Where the producer is asked to discard, at an item of what a parser takes: the `)` of `exit`,
followed by the end of the input alone. -/
theorem takes_discards {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (h : Takes version commands taken ending) :
    ∀ k < taken.length, (requestsAt commands k).2 = true →
      k + 2 = taken.length ∧ taken.getLast? = some .endOfInput ∧ ending = .finished := by
  induction h with
  | done => intro k _ hd; simp [requestsAt] at hd
  | @command v next rest items ending c hv hm hrest ih =>
    intro k hk hd
    have hexit := (Parser.Script.modeAfter_read hm).1
    simp only [List.length_append, List.length_map] at hk
    by_cases h1 : k + 1 < c.tokens.length
    · simp [requestsAt, h1] at hd
    · by_cases h2 : k + 1 = c.tokens.length
      · simp only [requestsAt, h2, Nat.lt_irrefl, ↓reduceIte] at hd
        cases c <;> first | exact absurd rfl hexit | simp at hd
      · simp only [requestsAt, h1, h2, ite_false] at hd
        obtain ⟨e1, e2, e3⟩ := ih (k - c.tokens.length) (by omega) hd
        refine ⟨by simp only [List.length_append, List.length_map]; omega, ?_, e3⟩
        rw [List.getLast?_append, e2]
        rfl
  | @stop v last hv hm =>
    obtain rfl := Parser.Script.modeAfter_unparsed hm
    intro k hk hd
    simp only [List.length_append, List.length_map, List.length_singleton] at hk
    by_cases h1 : k + 1 < Tree.Command.exit.tokens.length
    · simp [requestsAt, h1] at hd
    · by_cases h2 : k + 1 = Tree.Command.exit.tokens.length
      · refine ⟨by simp only [List.length_append, List.length_map, List.length_singleton]; omega,
          by simp, rfl⟩
      · simp [requestsAt, h1, h2] at hd
  | @refused v last hv hm =>
    intro k hk hd
    simp only [List.length_map] at hk
    have hne : last ≠ .exit := by rintro rfl; simp [Tree.Command.modeAfter] at hm
    by_cases h1 : k + 1 < last.tokens.length
    · simp [requestsAt, h1] at hd
    · have h2 : k + 1 = last.tokens.length := by omega
      simp only [requestsAt, h2, Nat.lt_irrefl, ↓reduceIte] at hd
      cases last <;> first | exact absurd rfl hne | simp at hd

theorem eq_take_append_last {α : Type} {l : List α} {n : Nat} {x : α} (hl : l.length = n + 1)
    (hx : l.getLast? = some x) : l = l.take n ++ [x] := by
  have hne : l ≠ [] := by rintro rfl; simp at hl
  rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hx
  rw [← hx, List.take_eq_dropLast hl.symm]
  exact (List.dropLast_concat_getLast hne).symm

/-! ## The consumer at a token -/

/-- After the `)` of `exit`, the script consumer has the rest discarded. -/
theorem discards_afterExit {v₀ : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes v₀ commands taken ending)
    {pre : List Handed} (hpre : pre.map (rcv ∘ itemOf) = taken.take pre.length)
    (hlt : pre.length < taken.length) (hafter : AfterExit v₀ (taken.take pre.length)) :
    (scriptConsumer v₀).discards pre = true := by
  obtain ⟨done, last, hchain, hagree⟩ := hafter
  have hlen := congrArg List.length hagree
  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)] at hlen
  simp only [List.length_append, Parser.Rejection.Unique.toks_length,
    Parser.Rejection.Unique.exit_tokens_length] at hlen
  obtain ⟨rfl, -⟩ := Parser.Rejection.Unique.takes_after_exit htakes hchain hlt hagree
  rw [(requests_takes_prefix htakes hpre (by omega) (Nat.le_of_lt hlt)).2,
    show pre.length - 1 = (Parser.Rejection.Script.cmdToks done).length + 2 by omega]
  exact Parser.Rejection.Discard.requestsAt_exit hchain

/-- Tokens that stand for a proper start of what a parser takes, at the last of which the script
consumer did not have the rest discarded, do not end with `exit`. -/
theorem not_afterExit {v₀ : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes v₀ commands taken ending)
    {pre : List Handed} (hpre : pre.map (rcv ∘ itemOf) <+: taken)
    (hlt : pre.length < taken.length)
    (hnd : pre = [] ∨ (scriptConsumer v₀).discards pre = false) :
    ¬ AfterExit v₀ (pre.map (rcv ∘ itemOf)) := by
  have hpre' : pre.map (rcv ∘ itemOf) = taken.take pre.length := by
    have := List.prefix_iff_eq_take.mp hpre
    simpa using this
  intro hafter
  rcases hnd with rfl | hnd
  · obtain ⟨done, last, -, hagree⟩ := hafter
    have := congrArg List.length hagree
    simp only [List.map_nil, List.length_nil, List.length_append,
      Parser.Rejection.Unique.toks_length, Parser.Rejection.Unique.exit_tokens_length] at this
    omega
  · rw [hpre'] at hafter
    rw [discards_afterExit htakes hpre' hlt hafter] at hnd
    cases hnd

/-- The script consumer at a token after tokens that stand for a proper start of what a parser
takes, at the last of which it did not have the rest discarded, the token standing for an item of
the version in force:
- it rejects the token where the items with it stand for no start of what a parser takes;
- it goes on, asking for what `requestsAt` says, where they stand for a proper start;
- it breaks at the end of the input where they stand for what a parser takes for a script;
- it fails where they stand for commands that a refused declaration ends. -/
theorem consumer_step {v₀ : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes v₀ commands taken ending)
    {pre : List Handed} (hpre : pre.map (rcv ∘ itemOf) <+: taken)
    (hlt : pre.length < taken.length) (token : Handed)
    (hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands pre.length))
    (hnd : pre = [] ∨ (scriptConsumer v₀).discards pre = false) :
    (¬ BSmtLibSpec.Parser.Properties.Viable v₀ ((pre ++ [token]).map (rcv ∘ itemOf)) ∧
        (scriptConsumer v₀).answer (pre ++ [token]) = .fail .rejected) ∨
      (∃ commands' taken' ending', Takes v₀ commands' taken' ending' ∧
        (pre ++ [token]).map (rcv ∘ itemOf) <+: taken' ∧ pre.length + 1 < taken'.length ∧
        (scriptConsumer v₀).answer (pre ++ [token]) = .continue ∧
        (scriptConsumer v₀).switchTo (pre ++ [token]) = (requestsAt commands' pre.length).1 ∧
        (scriptConsumer v₀).discards (pre ++ [token]) = (requestsAt commands' pre.length).2 ∧
        versionAt v₀ commands' pre.length = versionAt v₀ commands pre.length) ∨
      (∃ commands', Takes v₀ commands' ((pre ++ [token]).map (rcv ∘ itemOf)) .finished ∧
        (scriptConsumer v₀).answer (pre ++ [token]) = .break () ∧ token.type = .endOfFile) ∨
      (∃ commands', Takes v₀ commands' ((pre ++ [token]).map (rcv ∘ itemOf))
          (.failed .unsupportedVersion) ∧
        (scriptConsumer v₀).answer (pre ++ [token]) = .fail (.failed .unsupportedVersion)) := by
  have hpre' : pre.map (rcv ∘ itemOf) = taken.take pre.length := by
    have := List.prefix_iff_eq_take.mp hpre
    simpa using this
  by_cases hv : BSmtLibSpec.Parser.Properties.Viable v₀ ((pre ++ [token]).map (rcv ∘ itemOf))
  · obtain ⟨commands', taken', ending', ht', hp'⟩ := hv
    have hst : (pre ++ [token]).map (rcv ∘ itemOf) = taken'.take (pre ++ [token]).length := by
      have := List.prefix_iff_eq_take.mp hp'
      simpa using this
    have hle : (pre ++ [token]).length ≤ taken'.length := by
      have := hp'.length_le
      simpa using this
    have hans := answer_takes ht' hst hle
    by_cases hlt' : (pre ++ [token]).length < taken'.length
    · right; left
      have hreq := requests_takes_prefix ht' hst (by simp) hle
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hreq hlt'
      refine ⟨commands', taken', ending', ht', hp', hlt', ?_, hreq.1, hreq.2, ?_⟩
      · rw [hans]
        split
        · rfl
        · rename_i hn; simp only [List.length_append, List.length_singleton] at hn; omega
      · refine versionAt_unique ht' htakes (by omega) hlt ?_
        have h₁ := congrArg (List.take pre.length) hst
        simp only [List.map_append, List.length_append, List.length_singleton] at h₁
        rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
          List.take_take, Nat.min_eq_left (by omega)] at h₁
        rw [← h₁, hpre']
    · have heq : (pre ++ [token]).length = taken'.length := by omega
      have hall : (pre ++ [token]).map (rcv ∘ itemOf) = taken' := by
        rw [hst, heq, List.take_length]
      rw [hans]
      simp only [heq, Nat.lt_irrefl, ↓reduceIte]
      rw [← hall] at ht'
      rcases takes_ending ht' with rfl | rfl
      · right; right; left
        have hlast := takes_finished_last ht' rfl
        simp only [List.map_append, List.map_cons, List.map_nil, List.getLast?_append,
          List.getLast?_singleton, Option.some_or, Option.some.injEq,
          Function.comp_apply] at hlast
        have htype := (rcv_itemOf_endOfInput_iff token).mp hlast
        exact ⟨commands', ht', by simp only [answerOf]; rfl, htype⟩
      · right; right; right
        exact ⟨commands', ht', rfl⟩
  · left
    refine ⟨hv, ?_⟩
    have hmap : ((pre ++ [token]).map libItem : List Parser.Adapters.Run.Rejection.LibItem).map
        (rcv ∘ Subtype.val) = (pre ++ [token]).map (rcv ∘ itemOf) := by
      simp [libItem, Function.comp_def]
    have h₁ : (((pre ++ [token]).map libItem : List Parser.Adapters.Run.Rejection.LibItem).map
        (rcv ∘ Subtype.val)).take pre.length = taken.take pre.length := by
      rw [hmap, List.map_append, List.take_append_of_le_length (by simp),
        List.take_of_length_le (by simp), hpre']
    have h₂ : ∀ item, (((pre ++ [token]).map libItem : List
        Parser.Adapters.Run.Rejection.LibItem).map
        (rcv ∘ Subtype.val))[pre.length]? = some item →
        item.OfVersion (versionAt v₀ commands pre.length) := by
      rw [hmap]
      intro item hitem
      rw [List.map_append, List.map_singleton, List.getElem?_append_right (by simp)] at hitem
      simp only [List.length_map, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq,
        Function.comp_apply] at hitem
      rw [← hitem]
      exact hof
    have h₃ : ¬ BSmtLibSpec.Parser.Properties.Viable v₀ ((((pre ++ [token]).map libItem :
        List Parser.Adapters.Run.Rejection.LibItem).map (rcv ∘ Subtype.val)).take
            (pre.length + 1)) := by
      rw [hmap, List.take_of_length_le (by simp)]
      exact hv
    have hrejected : ((pre ++ [token]).map libItem :
        List Parser.Adapters.Run.Rejection.LibItem)[pre.length]? = some (libItem token) := by simp
    have h₄ : ¬ AfterExit v₀ (taken.take pre.length) := by
      rw [← hpre']
      exact not_afterExit htakes hpre hlt hnd
    have hrej := rejects_items v₀ commands taken ending ((pre ++ [token]).map libItem)
      pre.length htakes hlt (libItem token) hrejected h₁ h₂ h₄ h₃
    simp only [scriptConsumer]
    erw [hrej.1]
    rfl

end BSmtLib.Facts.Proofs.Reader.Outcome
