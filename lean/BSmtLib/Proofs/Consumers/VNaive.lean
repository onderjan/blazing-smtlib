import BSmtLib.Proofs.Consumers.VReset
import BSmtLib.SpecChecks.Consumers

/-!
# The naive lexer with every consumer of the spec

`correctWithConsumers_vNaive`: the naive lexer, with the adapter's consumer for every consumer
of the spec (`Adapter.lexing VNaive.lexOps`), is `BSmtLibSpec.Lexer.CorrectWithConsumers`. What it
hands over to the collector of the spec is what its pure run hands over (`lexing_fed_vNaive`,
`VNaive.fedRun`), as the collector takes every token ready (`runs_collector`); so it is
`BSmtLibSpec.Lexer.Correct` with it, which `VNaive.fedRun_correct` proves; it handles every consumer
that breaks at the end of the input (`vNaive_runs`, from `walk`), and the end of the input
resets it (`resetsAtEnd_vNaive`).
-/

namespace BSmtLib.Proofs.Lexer.VNaive

open BSmtLib.Proofs.Adapter
open BSmtLibSpec.Lexer (Handed)

/-- Tokens that the collector takes all of: tokens other than the end of file, followed, if the
lexer does not fail, possibly by the end of file. -/
def CollectorReady (ready : List Handed) (failed : Bool) : Prop :=
  ∃ tokens eof, ready = tokens ++ eof ∧ (∀ t ∈ tokens, t.type ≠ .endOfFile) ∧
    (eof = [] ∨ ∃ e, eof = [e] ∧ e.type = .endOfFile ∧ failed = false)

/-- The collector takes every token ready and fails exactly where the lexer fails. -/
theorem runs_collector
    {feed : BSmtLibSpec.Lexicon.Version → List BSmtLibSpec.Regex.Chars → Bool → BSmtLibSpec.Lexer.Fed}
    {start : BSmtLibSpec.Lexicon.Version} {input : BSmtLibSpec.Regex.Chars} {ended : Bool}
    {version : BSmtLibSpec.Lexicon.Version} {ready : List Handed} {failed : Bool} {taken : List Handed}
    {S : BSmtLibSpec.Lexer.Session BSmtLibSpec.Lexer.collector.Result BSmtLibSpec.Lexer.collector.Error}
    (h : BSmtLibSpec.Lexer.Runs feed BSmtLibSpec.Lexer.collector start input ended version ready failed taken S)
    (hready : CollectorReady ready failed) :
    S.taken = taken ++ ready ∧ S.outcome.isFailed = failed := by
  induction h with
  | waiting => rw [settle_not_finished _ _ _ rfl]; exact ⟨by simp, rfl⟩
  | lexical => rw [settle_not_finished _ _ _ rfl]; exact ⟨by simp, rfl⟩
  | fails hans =>
    simp only [BSmtLibSpec.Lexer.collector] at hans
    split at hans <;> cases hans
  | ends hty hans =>
    obtain ⟨tokens, eof, he, ht, hl⟩ := hready
    cases tokens with
    | cons t tokens =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact absurd hty (ht _ (by simp))
    | nil =>
      simp only [List.nil_append] at he
      subst he
      rcases hl with h0 | ⟨e, he, -, hf⟩
      · cases h0
      · simp only [List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [settle_finished]
        exact ⟨by simp, hf.symm⟩
  | continues hty hans hdi hrun ih =>
    refine (ih ?_).imp (fun h => by rw [h]; simp [BSmtLibSpec.Lexer.following, BSmtLibSpec.Lexer.collector]) id
    show CollectorReady _ _
    obtain ⟨tokens, eof, he, ht, hl⟩ := hready

    cases tokens with
    | cons t tokens =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨tokens, eof, rfl, fun t' h' => ht t' (by simp [h']), hl⟩
    | nil =>
      simp only [List.nil_append] at he
      subst he
      rcases hl with h0 | ⟨e, he, he2, -⟩
      · cases h0
      · simp only [List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he
        exact absurd he2 hty
  | breaks hty hans =>
    simp only [BSmtLibSpec.Lexer.collector, List.getLast?_append, List.getLast?_singleton] at hans
    split at hans
    · simp_all
    · cases hans
  | discardsHeld _ _ hdi => simp [BSmtLibSpec.Lexer.collector] at hdi
  | discardsEnds _ _ hdi => simp [BSmtLibSpec.Lexer.collector] at hdi
  | discardsWaiting _ _ hdi => simp [BSmtLibSpec.Lexer.collector] at hdi
  | discardsToEnd _ _ hdi => simp [BSmtLibSpec.Lexer.collector] at hdi
  | discardsFailsAtEnd _ _ hdi => simp [BSmtLibSpec.Lexer.collector] at hdi

theorem handedOf_noEof {version : Version} {ls : List Lexeme} (h : NoEof ls) :
    ∀ t ∈ handedOf version ls, t.type ≠ .endOfFile := by
  intro t ht
  obtain ⟨l, hl, hlt⟩ := List.mem_filterMap.mp ht
  have := (lexemeHanded_some hlt).2.2
  intro hte
  have := this.mp hte
  rw [h l hl] at this
  cases this

/-- The tokens of a run, as the collector takes them. -/
theorem streamFrom_collectorReady (version : Version) (ended : Bool) (location : Location)
    (bytes : List UInt8) :
    CollectorReady (handedOf version (streamFrom version false ended location bytes).1)
      (streamFrom version false ended location bytes).2 := by
  have hn := lexBytesW_noEof version false bytes .idle location
  simp only [lexemesOf] at hn
  unfold streamFrom
  revert hn
  cases lexBytesW version false .idle location bytes with
  | error ls => intro hn; exact ⟨handedOf version ls, [], by simp, handedOf_noEof hn, .inl rfl⟩
  | ok x =>
    obtain ⟨st, location', ls⟩ := x
    intro hn
    cases ended with
    | false => exact ⟨handedOf version ls, [], by simp, handedOf_noEof hn, .inl rfl⟩
    | true =>
      simp only [ite_true]
      cases he : endStepW false st location' with
      | none => exact ⟨handedOf version ls, [], by simp, handedOf_noEof hn, .inl rfl⟩
      | some ls' =>
        dsimp only
        have heof : lexemeHanded version (eofLexeme location') ≠ none := by
          simp [lexemeHanded, eofLexeme, toTokenType]
        obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp heof
        have hte : e.type = .endOfFile := by
          have := (lexemeHanded_some he').2.2
          exact this.mpr rfl
        rcases endStepW_cases he with rfl | ⟨l, rfl, -⟩
        · refine ⟨handedOf version ls, [e], ?_, handedOf_noEof hn, .inr ⟨e, rfl, hte, rfl⟩⟩
          simp [handedOf, List.filterMap_append, he']
        · have hl : (l.category == .endOfFile) = false := by
            cases st with
            | idle => simp [endStepW] at he
            | token p =>
              simp only [endStepW] at he
              split at he
              · cases he
              · rename_i l' hf
                simp only [Option.some.injEq, List.cons.injEq] at he
                obtain ⟨rfl, -⟩ := he
                exact finish_token_ne_eof hf
              · cases he
          refine ⟨handedOf version (ls ++ [l]), [e], ?_, handedOf_noEof ?_,
            .inr ⟨e, rfl, hte, rfl⟩⟩
          · simp only [handedOf, List.filterMap_append]
            rw [show [l, eofLexeme location'] = [l] ++ [eofLexeme location'] from rfl,
              List.filterMap_append]
            simp [he']
          · intro l' hl'
            rcases List.mem_append.mp hl' with hl' | hl'
            · exact hn l' hl'
            · simp at hl'; subst hl'; exact hl

/-- What the naive lexer has done with a consumer that breaks at the end of the input, on its
first input, is what `Runs` states, from the entries ready as the spec gives them from what the
pure run hands over (`fedRun`). -/
theorem vNaive_runs (consumer : BSmtLibSpec.Lexer.Consumer) (hb : consumer.BreaksAtEnd)
    (version : BSmtLibSpec.Lexicon.Version) (slices : List BSmtLibSpec.Regex.Chars) (ended : Bool) :
    BSmtLibSpec.Lexer.Runs fedRun consumer version slices.flatten ended version
      (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete version slices.flatten ended 0).handed
      (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete version slices.flatten ended 0).failed []
      (lexing VNaive.lexOps consumer version [] slices ended) := by
  rw [lexing_vNaive]
  have hw := walk consumer version slices.flatten ended hb _ slices.flatten .idle (Nat.le_refl _)
    0 (toVersion version) (Core.initial (toVersion version)) [] (by simp) (Nat.zero_le _) rfl rfl
    (by simp [Core.initial, locAfter, advanceLoc]) rfl rfl (fun _ => trivial)
  have hseg := ready_stream consumer.concrete (toVersion version) slices.flatten ended 0
    (Nat.zero_le _)
  rw [fromVersion_toVersion] at hseg hw
  rw [hseg]
  simpa [stream, streamFrom_eq] using hw

/-- The naive lexer hands over to the collector of the spec what its pure run hands over. -/
theorem lexing_fed_vNaive : BSmtLibSpec.Lexer.Lexing.fed (lexing VNaive.lexOps) = fedRun := by
  funext version slices ended
  have hr := vNaive_runs BSmtLibSpec.Lexer.collector SpecChecks.Lexer.collector_breaksAtEnd version slices
    ended
  have hready : CollectorReady
      (BSmtLibSpec.Lexer.segment fedRun version slices.flatten ended 0).handed
      (BSmtLibSpec.Lexer.segment fedRun version slices.flatten ended 0).failed := by
    rw [← fromVersion_toVersion version, segment_stream (toVersion version) false]
    exact streamFrom_collectorReady _ _ _ _
  rw [show BSmtLibSpec.Lexer.collector.concrete = false from rfl, readyFrom_plain] at hr
  obtain ⟨h1, h2⟩ := runs_collector hr hready
  unfold BSmtLibSpec.Lexer.Lexing.fed BSmtLibSpec.Lexer.Session.fed
  rw [h1, h2, List.nil_append, SpecChecks.Lexer.segment_zero]
  -- the pure run depends only on the bytes of the slices
  obtain ⟨r, hr'⟩ := fedOf_isSome (toVersion version) ended slices.flatten
  obtain ⟨hs, failed⟩ := r
  have e1 := fedRun_eq_run version slices ended hs failed hr'
  have e2 := fedRun_eq_run version [slices.flatten] ended hs failed
    (by rw [List.flatten_singleton]; exact hr')
  rw [e1, e2]

/-- The naive lexer is correct with every consumer of the spec. -/
theorem correctWithConsumers_vNaive :
    BSmtLibSpec.Lexer.CorrectWithConsumers (lexing VNaive.lexOps) := by
  refine ⟨?_, fun consumer version slices ended hb => ?_, resetsAtEnd_vNaive⟩
  · rw [lexing_fed_vNaive]
    exact fedRun_correct
  · rw [lexing_fed_vNaive]
    exact vNaive_runs consumer hb version slices ended

end BSmtLib.Proofs.Lexer.VNaive
