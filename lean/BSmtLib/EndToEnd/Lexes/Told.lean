import BSmtLib.EndToEnd.Reader
import BSmtLib.EndToEnd.Lexes.Good

/-!
# What the reader tells its handler, on every input

The library's lexer with the parse adapter and the lexer with the stand-in consumer
`Flagged (scriptConsumer version)` are related call by call (`Param.link_consumersG`); while
nothing went wrong, the adapter stands where the recording run over the tokens taken leaves the
parser (`Param.InvG`), and so it does after the call at which the stand-in consumer fails,
unless that call was handed whitespace or a comment. The lexer hands no whitespace or comment
to a consumer that does not take them (`NoLayout`, proved from the chain of lexers). So after
any run the handler holds the calls of the recording run over the tokens the stand-in consumer
took (`calls_of_invG`), none before the first token (`feed_told`).
-/

namespace BSmtLib.EndToEnd.Param

open BSmtLib.Lexer BSmtLib.Lexer.Internal
open BSmtLib.Spec BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal
open BSmtLib.Spec.Lexer (Handed)
open BSmtLib.ParserProofs BSmtLib.ParserProofs.Rejection
open BSmtLib.Parser (Input ScriptParser Parse ParseAdapter)
open BSmtLib.Proofs.Adapter (toVersion Answering AnswerM LexOps)

/-! ## No whitespace and comments for a consumer that does not take them -/

/-- The library's lexer with the adapter's consumer for the consumer of the spec, with the
fields and the held result. -/
abbrev zLexer (consumer : Spec.Lexer.Consumer) (c : LexerCore)
    (held : Option (Located consumer.Result)) : Proofs.Adapter.Lexer.lexOps.Lexer consumer :=
  ofParts {} c held

/-- The states of the library's lexer, with the adapter's consumer for the consumer of the spec,
that it reaches from its construction with the version by calls on slices that do not fail. -/
inductive Reach (consumer : Spec.Lexer.Consumer) (version : Version) : LexerCore → Prop
  | new : Reach consumer version (core (Proofs.Adapter.Lexer.lexOps.new consumer {} version))
  | step {c : LexerCore} {held : Option (Located consumer.Result)} {slice : Lexicon.Chars}
      {taken : List Handed} {r : Option (Located consumer.Result)} :
      Reach consumer version c →
      ((Proofs.Adapter.Lexer.lexOps.lexSliceStep (zLexer consumer c held)
        slice.toByteArray.toByteSlice).run taken).1.1 = .ok r →
      Reach consumer version
        (core ((Proofs.Adapter.Lexer.lexOps.lexSliceStep (zLexer consumer c held)
          slice.toByteArray.toByteSlice).run taken).1.2)

/-- From every state the library's lexer reaches with the adapter's consumer, no call fails with
the adapter's error `none`: the consumer is never handed whitespace or a comment it does not
take. -/
def NoLayout (consumer : Spec.Lexer.Consumer) (version : Version) : Prop :=
  ∀ c, Reach consumer version c →
    (∀ held (slice : Lexicon.Chars) taken e,
      ((Proofs.Adapter.Lexer.lexOps.lexSliceStep (zLexer consumer c held)
        slice.toByteArray.toByteSlice).run taken).1.1 = .error e → e.cause ≠ .consumer none) ∧
    (∀ held taken e,
      ((Proofs.Adapter.Lexer.lexOps.lexEofStep (zLexer consumer c held)).run taken).1.1 =
        .error e → e.cause ≠ .consumer none)

/-! ## The stand-in consumer's steps, as the adapter's consumer's -/

section

variable {consumer : Spec.Lexer.Consumer}

theorem answering_slice_alike (slice : ByteSlice) (c : LexerCore) (fl : Flagged consumer)
    (taken : List Handed) :
    ERel (LexErrRel (· = ·)) (ORel (LocRel (· = ·)))
      (((lexSliceStep (H := Answering consumer) (m := AnswerM)
        (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
        slice).run c).run {} |>.run taken).1.1.1
      (((lexSliceStep (H := Flagged consumer) (m := AnswerM)
        (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
        slice).run c).run fl |>.run taken).1.1.1 ∧
    (((lexSliceStep (H := Answering consumer) (m := AnswerM)
        (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
        slice).run c).run {} |>.run taken).1.1.2 =
      (((lexSliceStep (H := Flagged consumer) (m := AnswerM)
        (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
        slice).run c).run fl |>.run taken).1.1.2 ∧
    (((lexSliceStep (H := Answering consumer) (m := AnswerM)
        (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
        slice).run c).run {} |>.run taken).2 =
      (((lexSliceStep (H := Flagged consumer) (m := AnswerM)
        (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
        slice).run c).run fl |>.run taken).2 := by
  have hsim := lexSliceStep_sim (alike_consumers consumer)
    (LexRecovery.abandon (H := Answering consumer) (m := AnswerM) Recovery.failFast)
    (LexRecovery.recover (H := Answering consumer) (m := AnswerM) Recovery.failFast)
    (LexRecovery.abandon (H := Flagged consumer) (m := AnswerM) Recovery.failFast)
    (LexRecovery.recover (H := Flagged consumer) (m := AnswerM) Recovery.failFast)
    (recovery_alike consumer) (recover_alike consumer) slice c {} fl taken
  obtain ⟨⟨hr, hc⟩, ht⟩ := hsim
  exact ⟨hr, hc, ht⟩

theorem answering_eof_alike (c : LexerCore) (fl : Flagged consumer) (taken : List Handed) :
    ERel (LexErrRel (· = ·)) (FlowRel (LocRel (· = ·)))
      (((lexEofStep (H := Answering consumer) (m := AnswerM) (R := consumer.Result)
        (E := Option consumer.Error)
        (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)).run c).run
          {} |>.run taken).1.1.1
      (((lexEofStep (H := Flagged consumer) (m := AnswerM) (R := consumer.Result)
        (E := Option consumer.Error)
        (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)).run c).run
          fl |>.run taken).1.1.1 := by
  have hsim := lexEofStep_sim (alike_consumers consumer)
    (LexRecovery.abandon (H := Answering consumer) (m := AnswerM) Recovery.failFast)
    (LexRecovery.recover (H := Answering consumer) (m := AnswerM) Recovery.failFast)
    (LexRecovery.abandon (H := Flagged consumer) (m := AnswerM) Recovery.failFast)
    (LexRecovery.recover (H := Flagged consumer) (m := AnswerM) Recovery.failFast)
    (recovery_alike consumer) (recover_alike consumer) c {} fl taken
  obtain ⟨⟨hr, -⟩, -⟩ := hsim
  exact hr

end

/-! ## The calls, with the adapter's handler after them -/

section

variable {version : Lexicon.Version}

/-- The parse adapter's lexer after the step of a call on a slice, also where it fails. -/
def slicedP (p : PLexer) (slice : ByteSlice) : PLexer :=
  (Lexer.Internal.run p (lexSliceStep (H := RecAdapter) (m := Id)
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast) slice) :
    Id _).2

/-- The parse adapter's lexer after the step of a call at the end of the input, also where it
fails. -/
def eofedP (p : PLexer) : PLexer :=
  (Lexer.Internal.run p (lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
    (E := Parser.ParseErrorCause Unit)
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)) : Id _).2

theorem cause_ne_of_alike {ε : Type} {α β : Type} {Q : α → β → Prop}
    {x : Except (LexError (Option ε)) α} {y : Except (LexError (Option ε)) β}
    (h : ERel (LexErrRel (· = ·)) Q x y)
    (hx : ∀ e, x = .error e → e.cause ≠ .consumer none) :
    ∀ e, y = .error e → e.cause ≠ .consumer none := by
  intro e he
  subst he
  match x, h with
  | .error e', h => rw [← cause_eq h.1]; exact hx e' rfl

/-- A call on a slice, after which the tokens taken with the first consumer are `Good`, from a
state the lexer reaches: where it does not fail with the first consumer, it does not with the
parse adapter, the lexers are again related and the state is reached; where it fails, it fails
with the parse adapter, which then stands where the recording run over the tokens taken leaves
the parser. -/
theorem slice_stepT (hnl : NoLayout (scriptConsumer version) (toVersion version))
    (slice : ByteSlice) (hslice : ∃ bytes : Lexicon.Chars, slice = bytes.toByteArray.toByteSlice)
    (a : FLexer version) (p : PLexer) (taken : List Handed)
    (hI : InvF version a p taken)
    (hR : Reach (scriptConsumer version) (toVersion version) (core a))
    {res : Except (LexError (Option (scriptConsumer version).Error))
      (Option (Located (scriptConsumer version).Result))} {a' : FLexer version}
    {taken' : List Handed}
    (hr : (flaggedOps.lexSliceStep a slice).run taken = ((res, a'), taken'))
    (hgood : Good version taken') :
    (∃ held₁, res = .ok held₁ ∧ ∃ (p' : PLexer) (held₂ : Option (Located Unit)),
      (Lexer.lexSlice p slice : Id _) = .ok (withHeld p' (held₂.or (held p'))) ∧
      InvF version (withHeld a' (held₁.or (held a'))) (withHeld p' (held₂.or (held p'))) taken' ∧
      Reach (scriptConsumer version) (toVersion version) (core a')) ∨
    (∃ e, res = .error e ∧ (∃ e₂ x, (Lexer.lexSlice p slice : Id _) = .error (e₂, x)) ∧
      InvG version (handler a') taken' (handler (slicedP p slice))) := by
  obtain ⟨hcore, hheld, herr, hsp, hver, hinv⟩ := hI
  obtain ⟨bytes, hb⟩ := hslice
  have h2 := (sliceStepG_sim slice (core a)).2.1 (handler a) taken (handler p) herr hinv
  have hok := lexSliceStep_flag slice (core a) (handler a) taken herr hver
  have halike := answering_slice_alike slice (core a) (handler a) taken
  have hA : ∀ e, (((lexSliceStep (H := Answering (scriptConsumer version)) (m := AnswerM)
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
      slice).run (core a)).run {} |>.run taken).1.1.1 = .error e →
      e.cause ≠ .consumer none :=
    fun e he => (hnl _ hR).1 (held a) bytes taken e (by rw [← hb]; exact he)
  have hreach : ∀ r, (((lexSliceStep (H := Answering (scriptConsumer version)) (m := AnswerM)
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
      slice).run (core a)).run {} |>.run taken).1.1.1 = .ok r →
      Reach (scriptConsumer version) (toVersion version)
        (((lexSliceStep (H := Answering (scriptConsumer version)) (m := AnswerM)
          (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
          slice).run (core a)).run {} |>.run taken).1.1.2 :=
    fun r hr' => by
      have h := Reach.step (held := held a) (slice := bytes) (taken := taken) hR
        (by rw [← hb]; exact hr')
      rwa [← hb] at h
  unfold irun at hok
  simp only [flaggedOps] at hr
  rw [run_answerM] at hr
  unfold slicedP
  simp only [Lexer.lexSlice]
  rw [run_id, ← hcore]
  generalize ((StateT.run (lexSliceStep (H := Answering (scriptConsumer version)) (m := AnswerM)
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast) slice)
    (core a)).run {}).run taken = RA at halike hA hreach
  generalize ((StateT.run (lexSliceStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast) slice)
    (core a)).run (handler a)).run taken = R at hr h2 hok halike
  generalize (StateT.run (lexSliceStep (H := RecAdapter) (m := Id)
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast) slice)
    (core a)).run (handler p) = R₂ at h2 ⊢
  obtain ⟨⟨⟨res', core'⟩, fl'⟩, taken''⟩ := R
  obtain ⟨⟨⟨resA, coreA⟩, _⟩, _⟩ := RA
  obtain ⟨⟨res₂, core₂⟩, adapter₂⟩ := R₂
  simp only at hr
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
  obtain ⟨hv₁, he₁, hs₁⟩ := hok
  obtain ⟨hAl, hAc, -⟩ := halike
  dsimp only at hv₁ he₁ hs₁ h2 hAl hAc hA hreach
  obtain ⟨⟨hrel, rfl⟩, hinv', hfail⟩ := h2 hgood (hs₁.trans hsp)
  have hnone := cause_ne_of_alike hAl hA
  match res, res₂, hrel with
  | .ok held₁, .ok held₂, hh =>
    have hfl : fl'.errored = false := by
      cases h : fl'.errored
      · rfl
      · exact absurd (he₁ h) id
    have hR' : Reach (scriptConsumer version) (toVersion version) core' := by
      match resA, hAl with
      | .ok r, _ => rw [← hAc]; exact hreach r rfl
    exact .inl ⟨held₁, rfl, _, held₂, rfl, ⟨rfl, heldRel_or hh hheld, hfl, hs₁.trans hsp,
      hv₁ hfl, hinv' hfl⟩, hR'⟩
  | .error e, .error e₂, _ =>
    refine .inr ⟨e, rfl, ⟨e₂, _, rfl⟩, ?_⟩
    show InvG version fl' taken' adapter₂
    cases h : fl'.errored with
    | false => exact hinv' h
    | true =>
      rcases hfail h with hl | hinv''
      · exact absurd (he₁ h hl) (hnone e rfl)
      · exact hinv''

/-- The end of the input, after which the tokens taken with the first consumer are `Good`, from
a state the lexer reaches: where it does not fail with the first consumer, it does not with the
parse adapter, returns a result exactly where it does with the first, and the parse adapter then
stands where the recording run over the tokens taken leaves the parser; where it fails, it fails
with the parse adapter, which stands there too. -/
theorem eof_stepT (hnl : NoLayout (scriptConsumer version) (toVersion version))
    (a : FLexer version) (p : PLexer) (taken : List Handed)
    (hI : InvF version a p taken)
    (hR : Reach (scriptConsumer version) (toVersion version) (core a))
    {res : Except (LexError (Option (scriptConsumer version).Error))
      (ControlFlow (Located (scriptConsumer version).Result))} {a' : FLexer version}
    {taken' : List Handed}
    (hr : (flaggedOps.lexEofStep a).run taken = ((res, a'), taken'))
    (hgood : Good version taken') :
    (∃ flow, res = .ok flow ∧ ∃ (p' : PLexer) (result : Option (Located Unit)),
      (Lexer.lexEof p : Id _) = .ok (result, withHeld p' none) ∧
      HeldRel' (Proofs.Adapter.eofResult (flaggedOps.held a') flow) result ∧
      InvG version (handler a') taken' (handler p')) ∨
    (∃ e, res = .error e ∧ (∃ e₂ x, (Lexer.lexEof p : Id _) = .error (e₂, x)) ∧
      InvG version (handler a') taken' (handler (eofedP p))) := by
  obtain ⟨hcore, hheld, herr, hsp, hver, hinv⟩ := hI
  have h2 := (eofStepG_sim (core a)).2.1 (handler a) taken (handler p) herr hinv
  have hok := lexEofStep_flag (core a) (handler a) taken herr hver
  have halike := answering_eof_alike (core a) (handler a) taken
  have hA : ∀ e, (((lexEofStep (H := Answering (scriptConsumer version)) (m := AnswerM)
      (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)).run
        (core a)).run {} |>.run taken).1.1.1 = .error e →
      e.cause ≠ .consumer none :=
    fun e he => (hnl _ hR).2 (held a) taken e he
  unfold irun at hok
  simp only [flaggedOps] at hr
  rw [run_answerM] at hr
  unfold eofedP
  simp only [Lexer.lexEof]
  rw [run_id, ← hcore]
  generalize ((StateT.run (lexEofStep (H := Answering (scriptConsumer version)) (m := AnswerM)
    (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast))
    (core a)).run {}).run taken = RA at halike hA
  generalize ((StateT.run (lexEofStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
    (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast))
    (core a)).run (handler a)).run taken = R at hr h2 hok halike
  generalize (StateT.run (lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
    (E := Parser.ParseErrorCause Unit)
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast))
    (core a)).run (handler p) = R₂ at h2 ⊢
  obtain ⟨⟨⟨res', core'⟩, fl'⟩, taken''⟩ := R
  obtain ⟨⟨⟨resA, coreA⟩, _⟩, _⟩ := RA
  obtain ⟨⟨res₂, core₂⟩, adapter₂⟩ := R₂
  simp only at hr
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
  obtain ⟨he₁, hs₁⟩ := hok
  dsimp only at hs₁ h2 he₁ halike hA
  obtain ⟨⟨hrel, rfl⟩, hinv', hfail⟩ := h2 hgood (hs₁.trans hsp)
  have hnone := cause_ne_of_alike halike hA
  match res, res₂, hrel with
  | .ok flow, .ok flow₂, hh =>
    have hfl : fl'.errored = false := by
      cases h : fl'.errored
      · rfl
      · exact absurd (he₁ h) id
    refine .inl ⟨flow, rfl, ofParts adapter₂ core' (held p), _, rfl, ?_, hinv' hfl⟩
    dsimp only [flaggedOps, held_ofParts]
    generalize held p = hp at hheld ⊢
    generalize held a = ha at hheld ⊢
    match ha, hp, hheld with
    | none, none, _ =>
      match flow, flow₂, hh with
      | .continue, .continue, _ => exact trivial
      | .break _, .break _, h => exact h
    | some _, some _, h => exact h
  | .error e, .error e₂, _ =>
    refine .inr ⟨e, rfl, ⟨e₂, _, rfl⟩, ?_⟩
    show InvG version fl' taken' adapter₂
    cases h : fl'.errored with
    | false => exact hinv' h
    | true =>
      rcases hfail h with hl | hinv''
      · exact absurd (he₁ h hl) (hnone e rfl)
      · exact hinv''

/-- Where the parse adapter stands where the recording run over items standing for good tokens
leaves the parser, its handler holds the calls of the library's parser's run on the tokens, none
if there are no tokens. -/
theorem calls_of_invG {fl : Flagged (scriptConsumer version)} {taken : List Handed}
    {adapter : RecAdapter} (hinv : InvG version fl taken adapter) (hgood : Good version taken) :
    adapter.handler.reverse =
      if taken = [] then []
      else (libraryParser.parse version (taken.map libItem)).1.filter Event.isCall := by
  obtain ⟨items, hst, hat⟩ := hinv
  have hlen : items.length = taken.length := by
    simpa only [List.length_map] using congrArg List.length hst
  have hdom : Dom version (taken.map (rcv ∘ itemOf)) := by
    have := hgood.1 taken.length (Nat.le_refl _)
    rwa [List.take_length] at this
  have hcalls : (libraryParser.parse version (taken.map libItem)).1.filter Event.isCall =
      (recRun version items).2.reverse.filter Event.isCall := by
    have h := congrArg (fun o => o.1) (obs_congr hdom (map_libItem taken) hst)
    simp only [Obs] at h
    refine h.trans ?_
    rw [parse_recRun]
  rw [hcalls]
  unfold AdapterAtG at hat
  have hnil : items = [] ↔ taken = [] := by
    rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, hlen]
  generalize hR : recRun version items = R at hat
  obtain ⟨res, log⟩ := R
  rcases res with e | (⟨v', parser⟩ | r)
  · have hne : taken ≠ [] := by
      intro ht
      rw [hnil.mpr ht, recRun_nil] at hR
      cases hR
    simp only [hne, ite_false]
    rw [hat, List.filter_reverse]
  · obtain ⟨-, -, hlog, hvs⟩ := hat
    by_cases ht : taken = []
    · have hi := hnil.mpr ht
      subst hi
      rw [recRun_nil] at hR
      cases hR
      simp only [ht, ite_true]
      simp only [List.isEmpty_nil, Bool.not_true] at hvs
      simp only [startLog, hvs, Bool.false_eq_true, ite_false, startEvents, calls,
        List.filter_cons, Event.isCall, ite_true, List.filter_nil, List.cons.injEq] at hlog
      rw [hlog.2]
      rfl
    · have hi : items.isEmpty = false := by
        cases items with
        | nil => exact absurd (hnil.mp rfl) ht
        | cons _ _ => rfl
      rw [hi] at hvs
      simp only [startLog, hvs, Bool.not_false, ite_true] at hlog
      simp only [ht, ite_false]
      rw [hlog, List.filter_reverse]
  · have hne : taken ≠ [] := by
      intro ht
      rw [hnil.mpr ht, recRun_nil] at hR
      cases hR
    simp only [hne, ite_false]
    rw [hat, List.filter_reverse]

theorem runInput_extendsT :
    ∀ (ended : Bool) (slices : List Lexicon.Chars) (a : FLexer version) (taken : List Handed),
      ∃ more, ((flaggedOps.runInput a ended slices).run taken).2 = taken ++ more
  | false, [], a, taken => ⟨[], by simp [LexOps.runInput]; rfl⟩
  | true, [], a, taken => runInputG_extends [] a taken
  | ended, slice :: slices, a, taken => by
    obtain ⟨more, hmore⟩ := sliceStepG_extends slice.toByteArray.toByteSlice a taken
    simp only [LexOps.runInput, StateT.run_bind]
    generalize (flaggedOps.lexSliceStep a slice.toByteArray.toByteSlice).run taken = r at hmore
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq]
    dsimp only at hmore ⊢
    rcases res with e | held
    · exact ⟨more, hmore⟩
    · obtain ⟨more', hmore'⟩ := runInput_extendsT ended slices
        (flaggedOps.withHeld a' (held.or (flaggedOps.held a'))) taken'
      exact ⟨more ++ more', by rw [hmore', hmore, List.append_assoc]⟩

/-- The reader over the lexer with the parse adapter, and the lexer with the first consumer,
fed the same slices, and then the end of the input if it has ended, from related lexers and a
state the lexer reaches, the tokens taken with the first consumer being good: the reader's
handler holds, in order, what the parse adapter's handler holds where it stands where the
recording run over the tokens taken leaves the parser, and the reader finishes exactly where the
first lexer does. -/
theorem feed_told (hnl : NoLayout (scriptConsumer version) (toVersion version)) :
    ∀ (ended : Bool) (slices : List Lexicon.Chars) (a : FLexer version) (p : PLexer)
      (taken : List Handed), InvF version a p taken →
      Reach (scriptConsumer version) (toVersion version) (core a) →
      Good version ((flaggedOps.runInput a ended slices).run taken).2 →
      ∃ (fl : Flagged (scriptConsumer version)) (adapter : RecAdapter),
        readerRun (Reader.Internal.ofLexer p) slices ended =
          (adapter.handler.reverse,
            ((flaggedOps.runInput a ended slices).run taken).1.1.isFinished) ∧
        InvG version fl ((flaggedOps.runInput a ended slices).run taken).2 adapter
  | false, [], a, p, taken, hI, _, _ =>
    ⟨handler a, handler p, by
      simp only [readerRun, LexOps.runInput, Bool.false_eq_true, ite_false]
      refine Prod.ext rfl ?_
      show false = (flaggedOps.standing a).isFinished
      unfold LexOps.standing
      split <;> rfl, hI.2.2.2.2.2⟩
  | true, [], a, p, taken, hI, hR, hgood => by
    simp only [LexOps.runInput, ite_true, StateT.run_bind] at hgood ⊢
    generalize hr : (flaggedOps.lexEofStep a).run taken = r at hgood ⊢
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq] at hgood ⊢
    have hgood' : Good version taken' := by
      dsimp only at hgood
      rcases res with e | flow
      · exact hgood
      · dsimp only at hgood
        split at hgood <;> exact hgood
    simp only [readerRun, readEof_ofLexer]
    rcases eof_stepT hnl a p taken hI hR hr hgood' with
        ⟨flow, rfl, p₂, r₂, hp, hrel, hinv⟩ | ⟨e, rfl, ⟨e₂, x, hp⟩, hinv⟩
    · rw [hp]
      refine ⟨handler a', handler p₂, ?_, ?_⟩
      · dsimp only
        refine Prod.ext rfl ?_
        dsimp only
        revert hrel
        generalize Proofs.Adapter.eofResult (flaggedOps.held a') flow = o
        intro hrel
        match o, r₂, hrel with
        | some _, some _, _ => rfl
        | none, none, _ => rfl
      · dsimp only
        generalize Proofs.Adapter.eofResult (flaggedOps.held a') flow = o
        cases o <;> exact hinv
    · rw [hp]
      exact ⟨handler a', handler (eofedP p), rfl, hinv⟩
  | ended, slice :: slices, a, p, taken, hI, hR, hgood => by
    simp only [LexOps.runInput, StateT.run_bind] at hgood ⊢
    generalize hr : (flaggedOps.lexSliceStep a slice.toByteArray.toByteSlice).run taken = r
      at hgood ⊢
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq] at hgood ⊢
    have hgood' : Good version taken' := by
      dsimp only at hgood
      rcases res with e | held₁
      · exact hgood
      · obtain ⟨more, hmore⟩ := runInput_extendsT ended slices
          (flaggedOps.withHeld a' (held₁.or (flaggedOps.held a'))) taken'
        rw [hmore] at hgood
        exact hgood.of_append
    simp only [readerRun, readSlice_ofLexer]
    rcases slice_stepT hnl _ ⟨slice, rfl⟩ a p taken hI hR hr hgood' with
        ⟨held₁, rfl, p₂, held₂, hp, hI', hR'⟩ | ⟨e, rfl, ⟨e₂, x, hp⟩, hinv⟩
    · rw [hp]
      exact feed_told hnl ended slices _ _ taken' hI' hR' hgood
    · rw [hp]
      exact ⟨handler a', handler (slicedP p slice.toByteArray.toByteSlice), rfl, hinv⟩

end

end BSmtLib.EndToEnd.Param
