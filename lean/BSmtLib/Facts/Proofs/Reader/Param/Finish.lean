module

public import BSmtLib.Facts.Proofs.Reader.Param.Failing
public import BSmtLib.Facts.Proofs.Reader.Param.Run
import all BSmtLib.Lexer

@[expose] public section

/-!
# The library's lexer with the parse adapter finishes only where the stand-in consumer does

The library's lexer fed with `Flagged (scriptConsumer version)` and fed with the parse adapter
are related call by call by step 1 on `linkLinkG` (`link_consumersG`), on every run whose tokens
are `Good`, and, while nothing went wrong, by the unary walk (`lexSliceStep_flag`,
`lexEofStep_flag`), which keeps the consumer from being spoiled. So where a call fails with the
first consumer, it fails with the parse adapter too; where the end of the input returns no result
with the first, it returns none with the second (`feed_finishes`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Finish

open BSmtLib.Lexer
open BSmtLibSpec
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM LexOps)
open BSmtLib.Facts.Proofs.Reader.Param.Adapter BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Facts.Proofs.Reader.Param.Calls BSmtLib.Facts.Proofs.Reader.Param.Failing
open BSmtLib.Facts.Proofs.Reader.Param.Run BSmtLib.Facts.Proofs.Reader.Param.UnaryCalls
open BSmtLib.Facts.Reader.Adapters BSmtLib.Lexer.Error

section

variable (version : Lexicon.Version)

/-- What holds between the two lexers between the calls: the same fields and held result,
nothing gone wrong with the first and its consumer not spoiled, and the adapter where the
recording run over the tokens taken leaves the parser. -/
def InvF (a : FLexer version) (p : PLexer) (taken : List Handed) : Prop :=
  Internal.core a = Internal.core p ∧ HeldRel' (Internal.held a) (Internal.held p) ∧
      (Internal.handler a).errored = false ∧
    (Internal.handler a).spoiled = false ∧ (Internal.core a).version =
    (Internal.handler a).version ∧
    InvG version (Internal.handler a) taken (Internal.handler p)

end

section

variable {version : Lexicon.Version}

theorem link_abandonG (l : Span.Location) :
    (linkLinkG version).rc.rel (· = ·)
      (Recovery.LexRecovery.abandon (H := Flagged (scriptConsumer version)) (m := AnswerM)
        Recovery.failFast l)
      (Recovery.LexRecovery.abandon (H := RecAdapter) (m := Id) Recovery.failFast l) :=
  (linkLinkG version).rc.pure rfl

theorem link_recoverG (l : Span.Location) :
    (linkLinkG version).rc.rel (· = ·)
      (Recovery.LexRecovery.recover (H := Flagged (scriptConsumer version)) (m := AnswerM)
        Recovery.failFast l)
      (Recovery.LexRecovery.recover (H := RecAdapter) (m := Id) Recovery.failFast l) :=
  (linkLinkG version).rc.pure rfl

theorem sliceStepG_sim (slice : ByteSlice) :
    SSim (linkLinkG version) (SliceRel (linkLinkG version))
      (Internal.lexSliceStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
        (Recovery.LexRecovery.abandon Recovery.failFast)
            (Recovery.LexRecovery.recover Recovery.failFast) slice)
      (Internal.lexSliceStep (H := RecAdapter) (m := Id)
        (Recovery.LexRecovery.abandon Recovery.failFast)
            (Recovery.LexRecovery.recover Recovery.failFast) slice) :=
  lexSliceStep_sim (link_consumersG version) _ _ _ _ link_abandonG link_recoverG slice

theorem eofStepG_sim :
    SSim (linkLinkG version) (EofRel (linkLinkG version))
      (Internal.lexEofStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
        (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
        (Recovery.LexRecovery.abandon Recovery.failFast)
            (Recovery.LexRecovery.recover Recovery.failFast))
      (Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
          (E := Parser.ParseErrorCause Unit)
        (Recovery.LexRecovery.abandon Recovery.failFast)
            (Recovery.LexRecovery.recover Recovery.failFast)) :=
  lexEofStep_sim (link_consumersG version) _ _ _ _ link_abandonG link_recoverG

theorem sliceStepG_extends (slice : ByteSlice) (a : FLexer version) (taken : List Handed) :
    ∃ more, ((Flagged.flaggedOps.lexSliceStep a slice).run taken).2 = taken ++ more := by
  obtain ⟨hext, -, -, -⟩ := (sliceStepG_sim slice (Internal.core a)).1 (Internal.handler a) taken
  simp only [Flagged.flaggedOps]
  exact hext

theorem eofStepG_extends (a : FLexer version) (taken : List Handed) :
    ∃ more, ((Flagged.flaggedOps.lexEofStep a).run taken).2 = taken ++ more := by
  obtain ⟨hext, -, -, -⟩ := (eofStepG_sim (Internal.core a)).1 (Internal.handler a) taken
  simp only [Flagged.flaggedOps]
  exact hext

theorem runInputG_extends :
    ∀ (slices : List Regex.Chars) (a : FLexer version) (taken : List Handed),
      ∃ more, ((Flagged.flaggedOps.runInput a true slices).run taken).2 = taken ++ more
  | [], a, taken => by
    obtain ⟨more, hmore⟩ := eofStepG_extends a taken
    simp only [LexOps.runInput, ite_true, StateT.run_bind]
    generalize (Flagged.flaggedOps.lexEofStep a).run taken = r at hmore
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq]
    dsimp only at hmore ⊢
    rcases res with e | flow
    · exact ⟨more, hmore⟩
    · dsimp only
      split <;> exact ⟨more, hmore⟩
  | slice :: slices, a, taken => by
    obtain ⟨more, hmore⟩ := sliceStepG_extends slice.toByteArray.toByteSlice a taken
    simp only [LexOps.runInput, StateT.run_bind]
    generalize (Flagged.flaggedOps.lexSliceStep a slice.toByteArray.toByteSlice).run taken =
        r at hmore
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq]
    dsimp only at hmore ⊢
    rcases res with e | held
    · exact ⟨more, hmore⟩
    · obtain ⟨more', hmore'⟩ := runInputG_extends slices
        (Flagged.flaggedOps.withHeld a' (held.or (Flagged.flaggedOps.held a'))) taken'
      exact ⟨more ++ more', by rw [hmore', hmore, List.append_assoc]⟩

/-- A call on a slice, after which the tokens taken with the first consumer are `Good`: it fails
with the parse adapter where it fails with the first consumer; where it does not, it does not
with the parse adapter either, and the lexers are again related. -/
theorem slice_stepG (slice : ByteSlice) (a : FLexer version) (p : PLexer) (taken : List Handed)
    (hI : InvF version a p taken)
    {res : Except (LexError (Option (scriptConsumer version).Error))
      (Option (Span.Located (scriptConsumer version).Result))} {a' : FLexer version}
    {taken' : List Handed}
    (hr : (Flagged.flaggedOps.lexSliceStep a slice).run taken = ((res, a'), taken'))
    (hgood : Dom.Good version taken') :
    (∃ held₁, res = .ok held₁ ∧ ∃ (p' : PLexer) (held₂ : Option (Span.Located Unit)),
      (Lexer.lexSlice p slice : Id _) = .ok (Internal.withHeld p' (held₂.or (Internal.held p'))) ∧
      InvF version (Internal.withHeld a' (held₁.or (Internal.held a')))
          (Internal.withHeld p' (held₂.or (Internal.held p'))) taken') ∨
    (∃ e, res = .error e ∧ ∃ e₂ x, (Lexer.lexSlice p slice : Id _) = .error (e₂, x)) := by
  obtain ⟨hcore, hheld, herr, hsp, hver, hinv⟩ := hI
  have h2 := (sliceStepG_sim slice (Internal.core a)).2.1 (Internal.handler a) taken
      (Internal.handler p) herr hinv
  have hok := lexSliceStep_flag slice (Internal.core a) (Internal.handler a) taken herr hver
  unfold irun at hok
  simp only [Flagged.flaggedOps] at hr
  rw [Flagged.run_answerM] at hr
  simp only [Lexer.lexSlice]
  rw [run_id, ← hcore]
  generalize ((StateT.run (Internal.lexSliceStep (H := Flagged (scriptConsumer version))
      (m := AnswerM)
    (Recovery.LexRecovery.abandon Recovery.failFast)
    (Recovery.LexRecovery.recover Recovery.failFast) slice)
    (Internal.core a)).run (Internal.handler a)).run taken = R at hr h2 hok
  generalize (StateT.run (Internal.lexSliceStep (H := RecAdapter) (m := Id)
    (Recovery.LexRecovery.abandon Recovery.failFast)
    (Recovery.LexRecovery.recover Recovery.failFast) slice)
    (Internal.core a)).run (Internal.handler p) = R₂ at h2 ⊢
  obtain ⟨⟨⟨res', core'⟩, fl'⟩, taken''⟩ := R
  obtain ⟨⟨res₂, core₂⟩, adapter₂⟩ := R₂
  simp only at hr
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
  obtain ⟨hv₁, he₁, hs₁⟩ := hok
  dsimp only at hv₁ he₁ hs₁ h2
  obtain ⟨⟨hrel, rfl⟩, hinv', -⟩ := h2 hgood (hs₁.trans hsp)
  match res, res₂, hrel with
  | .ok held₁, .ok held₂, hh =>
    have hfl : fl'.errored = false := by
      cases h : fl'.errored
      · rfl
      · exact absurd (he₁ h) id
    exact .inl ⟨held₁, rfl, _, held₂, rfl, rfl, heldRel_or hh hheld, hfl, hs₁.trans hsp,
      hv₁ hfl, hinv' hfl⟩
  | .error e, .error e₂, _ => exact .inr ⟨e, rfl, e₂, _, rfl⟩

/-- The end of the input, after which the tokens taken with the first consumer are `Good`: it
fails with the parse adapter where it fails with the first consumer; where it does not, it does
not with the parse adapter either, and returns a result exactly where it does with the first. -/
theorem eof_stepG (a : FLexer version) (p : PLexer) (taken : List Handed)
    (hI : InvF version a p taken)
    {res : Except (LexError (Option (scriptConsumer version).Error))
      (ControlFlow (Span.Located (scriptConsumer version).Result))} {a' : FLexer version}
    {taken' : List Handed}
    (hr : (Flagged.flaggedOps.lexEofStep a).run taken = ((res, a'), taken'))
    (hgood : Dom.Good version taken') :
    (∃ flow, res = .ok flow ∧ ∃ (p' : PLexer) (result : Option (Span.Located Unit)),
      (Lexer.lexEof p : Id _) = .ok (result, Internal.withHeld p' none) ∧
      HeldRel' (Lexer.Adapters.eofResult (Flagged.flaggedOps.held a') flow) result) ∨
    (∃ e, res = .error e ∧ ∃ e₂ x, (Lexer.lexEof p : Id _) = .error (e₂, x)) := by
  obtain ⟨hcore, hheld, herr, hsp, hver, hinv⟩ := hI
  have h2 := (eofStepG_sim (Internal.core a)).2.1 (Internal.handler a) taken
      (Internal.handler p) herr hinv
  have hok := lexEofStep_flag (Internal.core a) (Internal.handler a) taken herr hver
  unfold irun at hok
  simp only [Flagged.flaggedOps] at hr
  rw [Flagged.run_answerM] at hr
  simp only [Lexer.lexEof]
  rw [run_id, ← hcore]
  generalize ((StateT.run (Internal.lexEofStep (H := Flagged (scriptConsumer version))
      (m := AnswerM)
    (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
    (Recovery.LexRecovery.abandon Recovery.failFast)
    (Recovery.LexRecovery.recover Recovery.failFast))
    (Internal.core a)).run (Internal.handler a)).run taken = R at hr h2 hok
  generalize (StateT.run (Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
    (E := Parser.ParseErrorCause Unit)
    (Recovery.LexRecovery.abandon Recovery.failFast)
    (Recovery.LexRecovery.recover Recovery.failFast))
    (Internal.core a)).run (Internal.handler p) = R₂ at h2 ⊢
  obtain ⟨⟨⟨res', core'⟩, fl'⟩, taken''⟩ := R
  obtain ⟨⟨res₂, core₂⟩, adapter₂⟩ := R₂
  simp only at hr
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
  obtain ⟨-, hs₁⟩ := hok
  dsimp only at hs₁ h2
  obtain ⟨⟨hrel, rfl⟩, -⟩ := h2 hgood (hs₁.trans hsp)
  match res, res₂, hrel with
  | .ok flow, .ok flow₂, hh =>
    refine .inl ⟨flow, rfl, Internal.ofParts adapter₂ core' (Internal.held p), _, rfl, ?_⟩
    dsimp only [Flagged.flaggedOps, Flagged.held_ofParts]
    generalize Internal.held p = hp at hheld ⊢
    generalize Internal.held a = ha at hheld ⊢
    match ha, hp, hheld with
    | none, none, _ =>
      match flow, flow₂, hh with
      | .continue, .continue, _ => exact trivial
      | .break _, .break _, h => exact h
    | some _, some _, h => exact h
  | .error e, .error e₂, _ => exact .inr ⟨e, rfl, e₂, _, rfl⟩

/-- Where the run with the parse adapter returns a result at the end of the input, and the tokens
the run with the first consumer takes are `Good`, the run with the first consumer finishes. -/
theorem feed_finishes :
    ∀ (slices : List Regex.Chars) (a : FLexer version) (p : PLexer) (taken : List Handed),
      InvF version a p taken →
      Dom.Good version ((Flagged.flaggedOps.runInput a true slices).run taken).2 →
      ∀ {result : Span.Located Unit} {p' : PLexer}, paFeed p slices = .ok (some result, p') →
        ((Flagged.flaggedOps.runInput a true slices).run taken).1.1.isFinished = true
  | [], a, p, taken, hI, hgood, result, p', hfeed => by
    simp only [LexOps.runInput, ite_true, StateT.run_bind] at hgood ⊢
    generalize hr : (Flagged.flaggedOps.lexEofStep a).run taken = r at hgood ⊢
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq] at hgood ⊢
    have hgood' : Dom.Good version taken' := by
      dsimp only at hgood
      rcases res with e | flow
      · exact hgood
      · dsimp only at hgood
        split at hgood <;> exact hgood
    rcases eof_stepG a p taken hI hr hgood' with ⟨flow, rfl, p₂, r₂, hp, hrel⟩ |
        ⟨e, rfl, e₂, x, hp⟩
    · simp only [paFeed, hp] at hfeed
      cases hfeed
      dsimp only
      revert hrel
      generalize Lexer.Adapters.eofResult (Flagged.flaggedOps.held a') flow = o
      intro hrel
      match o, hrel with
      | some _, _ => rfl
    · simp only [paFeed, hp] at hfeed
      cases hfeed
  | slice :: slices, a, p, taken, hI, hgood, result, p', hfeed => by
    simp only [LexOps.runInput, StateT.run_bind] at hgood ⊢
    generalize hr : (Flagged.flaggedOps.lexSliceStep a slice.toByteArray.toByteSlice).run taken = r
      at hgood ⊢
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq] at hgood ⊢
    have hgood' : Dom.Good version taken' := by
      dsimp only at hgood
      rcases res with e | held₁
      · exact hgood
      · obtain ⟨more, hmore⟩ := runInputG_extends slices
          (Flagged.flaggedOps.withHeld a' (held₁.or (Flagged.flaggedOps.held a'))) taken'
        rw [hmore] at hgood
        exact hgood.of_append
    rcases slice_stepG _ a p taken hI hr hgood' with ⟨held₁, rfl, p₂, held₂, hp, hI'⟩ |
        ⟨e, rfl, e₂, x, hp⟩
    · simp only [paFeed, hp] at hfeed
      exact feed_finishes slices _ _ taken' hI' hgood hfeed
    · simp only [paFeed, hp] at hfeed
      cases hfeed

end

end BSmtLib.Facts.Proofs.Reader.Param.Finish
