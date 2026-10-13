import BSmtLib.EndToEnd.Param.General

/-!
# The link of the stand-in consumer and the parse adapter, on runs that fail

`linkRelator` relates the calls of `Flagged (scriptConsumer version)` and of the parse adapter
while the tokens taken stand for a start of a script. `linkRelatorG` relates them on every run
whose tokens are `Good` (`Param.Dom`), the call at which the stand-in consumer fails included:
- of the first computation alone, as `linkRelator` says, that it keeps the consumer spoiled, and
  that from a state where something went wrong it leaves the consumer and the tokens taken as
  they are unless it spoils the consumer;
- from states where nothing went wrong and the adapter stands where the recording run over the
  tokens taken leaves the parser (`InvG`), as long as the consumer is not spoiled: the values are
  related, and the states are in `InvG` again, also where something went wrong, unless the
  consumer was handed whitespace or a comment there (`Flagged.layout`);
- from states where something went wrong, as long as the consumer is not spoiled, which is as
  long as it is not called: the values are related and the adapter stays as it is.

The calls of the two consumers on the same cursor are so related (`link_consumersG`): at a token
that the stand-in consumer fails at, the parse adapter fails too, at whitespace or a comment
because no parser takes it (`Param.Layout`), at any other token because the parser's run on what
the tokens stand for fails there (`loop_agreeG`).
-/

namespace BSmtLib.EndToEnd.Param

open BSmtLib.Spec BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal
open BSmtLib.Spec.Lexer (Handed)
open BSmtLib.ParserProofs BSmtLib.ParserProofs.Rejection
open BSmtLib.Parser (Input ScriptParser Parse ParseAdapter)
open BSmtLib.Proofs.Adapter (toVersion Answering AnswerM toHanded)

section

variable (version : Lexicon.Version)

/-- The adapter stands where the recording run over items standing for the tokens taken leaves
the parser, in the consumer's version. -/
def InvG (flagged : Flagged (scriptConsumer version)) (taken : List Handed)
    (adapter : RecAdapter) : Prop :=
  ∃ items : List LibItem, items.map (rcv ∘ Subtype.val) = taken.map (rcv ∘ itemOf) ∧
    AdapterAtG version items flagged.version adapter

/-- The relator of `Flagged (scriptConsumer version)` and the parse adapter on runs whose tokens
are `Good`. -/
def linkRelatorG : Relator (Flagged (scriptConsumer version)) AnswerM RecAdapter Id where
  rel Q x y :=
    (∀ flagged taken,
      (∃ more, ((x.run flagged).run taken).2 = taken ++ more) ∧
      (flagged.errored = true → ((x.run flagged).run taken).1.2.errored = true) ∧
      (flagged.spoiled = true → ((x.run flagged).run taken).1.2.spoiled = true) ∧
      (flagged.errored = true → ((x.run flagged).run taken).1.2.spoiled = false →
        ((x.run flagged).run taken).1.2 = flagged ∧ ((x.run flagged).run taken).2 = taken) ∧
      ∃ b, Q ((x.run flagged).run taken).1.1 b) ∧
    (∀ flagged taken adapter, flagged.errored = false → InvG version flagged taken adapter →
      Good version ((x.run flagged).run taken).2 →
      ((x.run flagged).run taken).1.2.spoiled = false →
      Q ((x.run flagged).run taken).1.1 (y.run adapter).1 ∧
      (((x.run flagged).run taken).1.2.errored = false →
        InvG version ((x.run flagged).run taken).1.2 ((x.run flagged).run taken).2
          (y.run adapter).2) ∧
      (((x.run flagged).run taken).1.2.errored = true →
        ((x.run flagged).run taken).1.2.layout = true ∨
          InvG version ((x.run flagged).run taken).1.2 ((x.run flagged).run taken).2
            (y.run adapter).2)) ∧
    (∀ flagged taken adapter, flagged.errored = true →
      ((x.run flagged).run taken).1.2.spoiled = false →
      Q ((x.run flagged).run taken).1.1 (y.run adapter).1 ∧ (y.run adapter).2 = adapter)
  pure {_ _ _ a b} h :=
    ⟨fun _ taken => ⟨⟨[], (List.append_nil taken).symm⟩, id, id, fun _ _ => ⟨rfl, rfl⟩, ⟨b, h⟩⟩,
      fun _ _ _ he hinv _ _ => ⟨h, fun _ => hinv, fun h' => absurd (h'.symm.trans he) (by decide)⟩,
      fun _ _ _ _ _ => ⟨h, rfl⟩⟩
  bind {_ _ _ _ _ _ x y f g} hx hk := by
    have e₁ : ∀ flagged taken, ((x >>= f).run flagged).run taken =
        ((f ((x.run flagged).run taken).1.1).run ((x.run flagged).run taken).1.2).run
          ((x.run flagged).run taken).2 := fun _ _ => rfl
    have e₂ : ∀ adapter, (y >>= g).run adapter = (g (y.run adapter).1).run (y.run adapter).2 :=
      fun _ => rfl
    refine ⟨fun flagged taken => ?_, fun flagged taken adapter he hinv hgood hsp => ?_,
      fun flagged taken adapter he hsp => ?_⟩
    · -- the first side alone, through the continuation reached by a partner
      obtain ⟨⟨more, hmore⟩, hmono, hmonos, hkeep, ⟨b', hb'⟩⟩ := hx.1 flagged taken
      rw [e₁]
      generalize (x.run flagged).run taken = X at hmore hmono hmonos hkeep hb'
      obtain ⟨⟨a, flagged₁⟩, taken₁⟩ := X
      obtain ⟨⟨more', hmore'⟩, hmono', hmonos', hkeep', hpart⟩ := (hk a b' hb').1 flagged₁ taken₁
      dsimp only at hmore hmono hmonos hkeep ⊢
      refine ⟨⟨more ++ more', by rw [hmore', hmore, List.append_assoc]⟩,
        fun he => hmono' (hmono he), fun hs => hmonos' (hmonos hs), fun he hs => ?_, hpart⟩
      have hs₁ : flagged₁.spoiled = false := by
        cases h₁ : flagged₁.spoiled
        · rfl
        · exact absurd (hmonos' h₁) (by rw [hs]; decide)
      obtain ⟨rfl, rfl⟩ := hkeep he hs₁
      exact hkeep' he hs
    · obtain ⟨_, -, -, -, ⟨b', hb'⟩⟩ := hx.1 flagged taken
      have hrel := hx.2.1 flagged taken adapter he hinv
      rw [e₁] at hgood hsp ⊢
      rw [e₂]
      generalize (x.run flagged).run taken = X at hb' hrel hgood hsp
      generalize y.run adapter = Y at hrel
      obtain ⟨⟨a, flagged₁⟩, taken₁⟩ := X
      obtain ⟨b, adapter₁⟩ := Y
      obtain ⟨⟨more', hmore'⟩, hmono', hmonos', hkeep', -⟩ := (hk a b' hb').1 flagged₁ taken₁
      have hs₁ : flagged₁.spoiled = false := by
        cases h₁ : flagged₁.spoiled
        · rfl
        · exact absurd (hmonos' h₁) (by rw [hsp]; decide)
      have hgood₁ : Good version taken₁ := by
        rw [hmore'] at hgood
        exact hgood.of_append
      obtain ⟨hab, hinv₁, hfail₁⟩ := hrel hgood₁ hs₁
      cases he₁ : flagged₁.errored with
      | false => exact (hk a b hab).2.1 flagged₁ taken₁ adapter₁ he₁ (hinv₁ he₁) hgood hsp
      | true =>
        obtain ⟨hq, hadapter⟩ := (hk a b hab).2.2 flagged₁ taken₁ adapter₁ he₁ hsp
        obtain ⟨hfl, htk⟩ := hkeep' he₁ hsp
        refine ⟨hq, fun hend => absurd (hmono' he₁) (by rw [hend]; decide), fun _ => ?_⟩
        rw [hfl, htk, hadapter]
        exact hfail₁ he₁
    · obtain ⟨_, hmono, -, hkeep, ⟨b', hb'⟩⟩ := hx.1 flagged taken
      have hrel := hx.2.2 flagged taken adapter he
      rw [e₁] at hsp ⊢
      rw [e₂]
      have he₀ := hmono he
      generalize (x.run flagged).run taken = X at hb' hrel hsp he₀ hkeep
      generalize y.run adapter = Y at hrel
      obtain ⟨⟨a, flagged₁⟩, taken₁⟩ := X
      obtain ⟨b, adapter₁⟩ := Y
      obtain ⟨-, -, hmonos', -, -⟩ := (hk a b' hb').1 flagged₁ taken₁
      have hs₁ : flagged₁.spoiled = false := by
        cases h₁ : flagged₁.spoiled
        · rfl
        · exact absurd (hmonos' h₁) (by rw [hsp]; decide)
      obtain ⟨hab, hadapter⟩ := hrel hs₁
      obtain ⟨hq', hadapter'⟩ := (hk a b hab).2.2 flagged₁ taken₁ adapter₁ he₀ hsp
      exact ⟨hq', hadapter'.trans hadapter⟩
  mono hQ h :=
    ⟨fun flagged taken =>
      let ⟨h₁, h₂, h₃, h₄, ⟨b, hb⟩⟩ := h.1 flagged taken
      ⟨h₁, h₂, h₃, h₄, ⟨b, hQ _ _ hb⟩⟩,
     fun flagged taken adapter he hinv hgood hsp =>
      let ⟨hq, hinv', hfail⟩ := h.2.1 flagged taken adapter he hinv hgood hsp
      ⟨hQ _ _ hq, hinv', hfail⟩,
     fun flagged taken adapter he hsp =>
      let ⟨hq, hadapter⟩ := h.2.2 flagged taken adapter he hsp
      ⟨hQ _ _ hq, hadapter⟩⟩

end

/-- The link of `Flagged (scriptConsumer version)` and the parse adapter on runs whose tokens are
`Good`. -/
def linkLinkG (version : Lexicon.Version) :
    Link (Flagged (scriptConsumer version)) AnswerM (scriptConsumer version).Result
      (Option (scriptConsumer version).Error) RecAdapter Id Unit
      (Parser.ParseErrorCause Unit) :=
  { rc := linkRelatorG version, rr := fun _ _ => True, re := fun _ _ => True }

/-! ## The calls of the two consumers -/

/-- A call whose first token is no whitespace or comment takes that token. -/
theorem ansRest_handed (version : Lexicon.Version) {b : BatchTag} {cursor : BatchCursor b}
    (h : cursor.HasNext) (taken : List Handed) {handed : Handed}
    (hh : toHanded cursor (cursor.next h).1 = some handed) :
    ∃ more, (ansRest version cursor taken).2 = taken ++ [handed] ++ more := by
  rw [ansRest_step version h]
  simp only [hh]
  cases (scriptConsumer version).answer (taken ++ [handed]) with
  | fail e => exact ⟨[], by simp⟩
  | «break» r => exact ⟨[], by simp⟩
  | «continue» =>
    dsimp only
    split
    · exact ⟨[], by simp⟩
    · exact ansRest_extends version (cursor.next h).2.val.remaining.succ
        (cursor.next h).2.val (taken ++ [handed]) (Nat.lt_succ_self _)

/-- Where the recording run over items standing for the tokens has ended, the stand-in consumer
does not go on after them. -/
theorem answer_ne_continue {version : Lexicon.Version} {taken : List Handed}
    (hdom : Dom version (taken.map (rcv ∘ itemOf))) {items : List LibItem}
    (hst : items.map (rcv ∘ Subtype.val) = taken.map (rcv ∘ itemOf))
    (hnot : ∀ v parser log, recRun version items ≠ (.ok (.inl (v, parser)), log)) :
    (scriptConsumer version).answer taken ≠ .continue := by
  have hobs := obs_congr hdom hst (map_libItem taken)
  have hend := congrArg (fun o => o.2.1) hobs
  simp only [Obs] at hend
  intro hc
  rw [answer_eq] at hc
  have hE : (libraryParser.parse version (taken.map libItem)).2 =
      (libraryParser.parse version items).2 := hend.symm
  rw [hE, parse_recRun] at hc
  generalize hR : recRun version items = R at hnot hc
  obtain ⟨res, log⟩ := R
  dsimp only at hc
  rcases res with e | (⟨v, parser⟩ | r)
  · obtain ⟨err, herr⟩ := answerOf_error
      (decide (taken.getLast?.map (·.type) = some .endOfFile)) e
    rw [herr] at hc
    cases hc
  · exact absurd rfl (hnot v parser log)
  · simp [libEnding, answerOf] at hc

theorem link_consumersG (version : Lexicon.Version) : Consumers (linkLinkG version) where
  concrete := rfl
  consume {b} cursor h := by
    have hans : ∀ taken, ansRest version cursor taken =
        ((((Answering.consume (scriptConsumer version) cursor h).run taken).1.1,
          ((Answering.consume (scriptConsumer version) cursor h).run taken).1.2.val),
          ((Answering.consume (scriptConsumer version) cursor h).run taken).2) := fun taken => by
      (unfold ansRest; rw [dite_eq_left_of_eq_true (eq_true h)]) <;> rfl
    refine ⟨fun flagged taken => ?_, fun flagged taken adapter he hinv hgood hsp => ?_,
      fun flagged taken adapter he hsp => ?_⟩
    · have hrun := flagged_run (scriptConsumer version) cursor h flagged taken
      have hext := ansRest_extends version (cursor.remaining + 1) cursor taken
        (Nat.lt_succ_self _)
      rw [hans] at hext
      generalize (Answering.consume (scriptConsumer version) cursor h).run taken = A at hrun hext
      obtain ⟨⟨answer, next⟩, taken'⟩ := A
      change ((Flagged.consume (scriptConsumer version) cursor h).run flagged).run taken = _ at hrun
      erw [hrun]
      dsimp only at hext ⊢
      refine ⟨hext, fun he => by simp [he], fun hs => by simp [hs], fun he hs => by simp [he] at hs,
        (partnerOf answer, next), ?_, rfl⟩
      rcases answer with _ | (_ | _) <;> exact trivial
    · have hrun := flagged_run (scriptConsumer version) cursor h flagged taken
      change ((Flagged.consume (scriptConsumer version) cursor h).run flagged).run taken = _ at hrun
      erw [hrun] at hgood hsp ⊢
      dsimp only at hgood hsp ⊢
      have hA := hans taken
      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hsp
      obtain ⟨⟨-, -⟩, hcv⟩ := hsp
      have hgood' : Good version (ansRest version cursor taken).2 := by rw [hA]; exact hgood
      obtain ⟨items, hst, hat⟩ := hinv
      have hq := consume_eq cursor h adapter
      simp only at hq
      unfold AdapterAtG at hat
      generalize hR : recRun version items = R at hat
      obtain ⟨res, log⟩ := R
      rcases res with e | (⟨v', parser⟩ | r)
      rotate_left
      · -- the recording run goes on: the two loops agree
        obtain ⟨rfl, hparser, hlog, -⟩ := hat
        obtain ⟨hshape, hcur, hadapt⟩ := loop_agreeG (cursor.remaining + 1) cursor taken items
          parser log (Nat.lt_succ_self _) hst (by rw [hR, hcv]) (.inr h) hgood'
        rw [hcv, hlog, hparser] at hq
        simp only [Prod.mk.injEq] at hq
        rw [hq.1, hq.2.2]
        rw [hA] at hshape hcur hadapt
        refine ⟨⟨hshape, Subtype.ext (hcur.trans hq.2.1.symm)⟩, fun herr => ?_, fun herr => ?_⟩
        · simp only [he, Bool.false_or, hcv, bne_self_version] at herr
          refine hadapt ?_
          revert herr
          generalize ((Answering.consume (scriptConsumer version) cursor h).run taken).1.1 = a
          rcases a with (_ | _) | _ <;> simp [isError, isLayoutAnswer]
        · simp only [he, Bool.false_eq_true, ite_false]
          cases hl : isLayoutAnswer ((Answering.consume (scriptConsumer version) cursor h).run
            taken).1.1
          · exact .inr (hadapt hl)
          · exact .inl rfl
      all_goals
        have hnot : ∀ v parser log, recRun version items ≠ (.ok (.inl (v, parser)), log) := by
          intro v parser log h'
          rw [hR] at h'
          cases h'
        cases hh : toHanded cursor (cursor.next h).1 with
        | none =>
          -- whitespace or a comment: both fail at it
          obtain ⟨e', he', hc'⟩ := paLoop_layout h adapter.parser (startLog adapter cursor.version)
            (ofSyntax_layout cursor _ hh)
          have hstep := ansRest_step version h taken
          rw [hh] at hstep
          simp only [Prod.mk.injEq] at hq
          rw [hq.1]
          rw [hA] at hstep
          have hs1 := congrArg (fun p => p.1.1) hstep
          have hs2 := congrArg (fun p => p.1.2) hstep
          dsimp only at hs1 hs2
          refine ⟨⟨by rw [hs1, he']; trivial, Subtype.ext ?_⟩, fun herr => ?_, fun _ => ?_⟩
          · rw [hs2, hq.2.1, hc']
          · rw [hs1] at herr
            simp [isError] at herr
          · left
            simp only [he, Bool.false_eq_true, ite_false]
            rw [hs1]
            rfl
        | some handed =>
          -- any other token: the stand-in consumer went on after the end of the recording run
          exfalso
          obtain ⟨more, hmore⟩ := ansRest_handed version h taken hh
          have hlen : items.length = taken.length := by
            simpa only [List.length_map] using congrArg List.length hst
          have hpos : 0 < taken.length := by
            refine Nat.pos_of_ne_zero fun h0 => ?_
            have hnil : items = [] := List.length_eq_zero_iff.mp (by omega)
            subst hnil
            exact hnot _ _ _ rfl
          have htake : (ansRest version cursor taken).2.take taken.length = taken := by
            rw [hmore, List.append_assoc, List.take_left']
            rfl
          have hcont := hgood'.2 taken.length hpos (by rw [hmore]; simp)
          rw [htake] at hcont
          have hdom := hgood'.1 taken.length (by rw [hmore]; simp)
          rw [htake] at hdom
          exact answer_ne_continue hdom hst hnot hcont
    · have hrun := flagged_run (scriptConsumer version) cursor h flagged taken
      change ((Flagged.consume (scriptConsumer version) cursor h).run flagged).run taken = _ at hrun
      erw [hrun] at hsp
      simp [he] at hsp

end BSmtLib.EndToEnd.Param
