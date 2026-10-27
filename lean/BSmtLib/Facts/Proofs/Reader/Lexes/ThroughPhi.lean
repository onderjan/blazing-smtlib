module

public import BSmtLib.Facts.Proofs.Reader.Lexes.Through
public import BSmtLib.Facts.Proofs.Reader.Param.PhiR
public import BSmtLib.Facts.Proofs.Parser.Canon.Through
public import BSmtLib.Facts.Proofs.Lexer.Consumers.RunE
import all BSmtLib.Lexer

@[expose] public section

/-!
# The parse adapter's errors, against the replaying consumer

This module compares four calls of the library's lexer from the same state: with the stand-in
consumer, with `Phi`, with the parse adapter and with the adapter's consumer for `replay`. In
that state the stand-in consumer and the parse adapter are related as `Param.InvG` says. The
parse adapter's call then ends as the replaying one does (`sliceStep_replay`, `eofStep_replay`):
- with the same span and the same lexical error;
- with, as the parse adapter's error, the one on which the recording runs over items standing
  for the tokens the replaying consumer reports fail.
-/

namespace BSmtLib.Facts.Proofs.Reader.Lexes.ThroughPhi

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLibSpec
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM LexOps)
open BSmtLib.Facts.Proofs.Reader.Param
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.Calls
open BSmtLib.Facts.Proofs.Reader.Param.HandOver
open BSmtLib.Facts.Proofs.Reader.Param.Phi BSmtLib.Facts.Proofs.Reader.Param.PhiR
open BSmtLib.Facts.Reader.Adapters
open BSmtLib.Facts.Proofs.Reader.Param.Failing (InvG)
open BSmtLib.Lexer.Cursor.LexerCursor.Internal (remaining)

variable {version : Lexicon.Version}

abbrev abandonP := Recovery.LexerRecovery.abandon (H := Phi version) (m := AnswerM)
  Recovery.FailFast
abbrev recoverP := Recovery.LexerRecovery.recover (H := Phi version) (m := AnswerM)
  Recovery.FailFast

theorem phiSlice_sim (slice : ByteSlice) :
    SSim (linkPhi version) (SliceRel (linkPhi version))
      (Internal.lexSliceStep (H := Phi version) (m := AnswerM) abandonP recoverP slice)
      (Internal.lexSliceStep (H := RecAdapter) (m := Id)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
        (Recovery.LexerRecovery.recover Recovery.FailFast) slice) :=
  lexSliceStep_sim (consumersPhi version) _ _ _ _ (fun _ => (linkPhi version).rc.pure rfl)
    (fun _ => (linkPhi version).rc.pure rfl) slice

theorem phiEof_sim :
    SSim (linkPhi version) (EofRel (linkPhi version))
      (Internal.lexEofStep (H := Phi version) (m := AnswerM) (R := Unit)
        (E := Option ScriptError × List Handed) abandonP recoverP)
      (Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
        (E := Parser.ParseError Unit)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
        (Recovery.LexerRecovery.recover Recovery.FailFast)) :=
  lexEofStep_sim (consumersPhi version) _ _ _ _ (fun _ => (linkPhi version).rc.pure rfl)
    (fun _ => (linkPhi version).rc.pure rfl)

theorem fSlice_sim (slice : ByteSlice) :
    SSim (linkF version) (SliceRel (linkF version))
      (Internal.lexSliceStep (H := Phi version) (m := AnswerM) abandonP recoverP slice)
      (Internal.lexSliceStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
        (Recovery.LexerRecovery.recover Recovery.FailFast) slice) :=
  lexSliceStep_sim consumersF _ _ _ _ (fun _ => (linkF version).rc.pure rfl)
    (fun _ => (linkF version).rc.pure rfl) slice

theorem fEof_sim :
    SSim (linkF version) (EofRel (linkF version))
      (Internal.lexEofStep (H := Phi version) (m := AnswerM) (R := Unit)
        (E := Option ScriptError × List Handed) abandonP recoverP)
      (Internal.lexEofStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
        (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
        (Recovery.LexerRecovery.recover Recovery.FailFast)) :=
  lexEofStep_sim consumersF _ _ _ _ (fun _ => (linkF version).rc.pure rfl)
    (fun _ => (linkF version).rc.pure rfl)

theorem rSlice_sim (slice : ByteSlice) :
    SSim (linkR version) (SliceRel (linkR version))
      (Internal.lexSliceStep (H := Phi version) (m := AnswerM) abandonP recoverP slice)
      (Internal.lexSliceStep (H := Answering (replay version)) (m := AnswerM)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
        (Recovery.LexerRecovery.recover Recovery.FailFast) slice) :=
  lexSliceStep_sim consumersR _ _ _ _ (fun _ => (linkR version).rc.pure rfl)
    (fun _ => (linkR version).rc.pure rfl) slice

theorem rEof_sim :
    SSim (linkR version) (EofRel (linkR version))
      (Internal.lexEofStep (H := Phi version) (m := AnswerM) (R := Unit)
        (E := Option ScriptError × List Handed) abandonP recoverP)
      (Internal.lexEofStep (H := Answering (replay version)) (m := AnswerM)
        (R := (replay version).Result) (E := Option (replay version).Error)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
        (Recovery.LexerRecovery.recover Recovery.FailFast)) :=
  lexEofStep_sim consumersR _ _ _ _ (fun _ => (linkR version).rc.pure rfl)
    (fun _ => (linkR version).rc.pure rfl)

/-! ## A call, against the replaying consumer -/

variable (version) in
/-- The parse adapter's error against the replaying consumer's: whitespace or a comment, or the
error on which the recording runs over items standing for the tokens reported fail. -/
def CM (ae : Parser.ParseError Unit) (o : Option (List Handed)) : Prop :=
  o = none ∨ ∃ t, o = some t ∧ ae = causeOfT version t

theorem compose_err {fe : Option ScriptError × List Handed} {ae : Parser.ParseError Unit}
    {o : Option (List Handed)} (h₁ : ReE version fe ae)
    (h₂ : (linkR version).re fe o) : CM version ae o := by
  change o = fe.1.map (fun _ => fe.2) at h₂
  subst h₂
  rcases h₁ with h | h
  · left; rw [h]; rfl
  · cases hf : fe.1 with
    | none => left; rfl
    | some e => right; exact ⟨fe.2, rfl, h⟩

theorem compose_lexErr {x : LexerError (Option ScriptError × List Handed)}
    {a : LexerError (Parser.ParseError Unit)} {z : LexerError (Option (List Handed))}
    (h₁ : LexErrRel (ReE version) x a) (h₂ : LexErrRel (linkR version).re x z) :
    LexErrRel (CM version) a z := by
  obtain ⟨c₁, s₁, f₁⟩ := h₁
  obtain ⟨c₂, s₂, f₂⟩ := h₂
  refine ⟨?_, s₁.symm.trans s₂, f₁.symm.trans f₂⟩
  revert c₁ c₂
  rcases x.kind with k | fe <;> rcases a.kind with k' | ae <;> rcases z.kind with k'' | o <;>
    simp only [CauseRel, imp_self, implies_true, false_implies]
  · intro h₁ h₂; exact h₁.symm.trans h₂
  · intro h₁ h₂; exact compose_err h₁ h₂

theorem compose_loc {α β : Type} {x : Span.Located α} {a : Span.Located β}
    {z : Span.Located α} (h₁ : LocRel (fun _ _ => True) x a) (h₂ : LocRel (· = ·) x z) :
    LocRel (fun _ _ => True) a z :=
  ⟨trivial, h₁.2.symm.trans h₂.2⟩

theorem compose_slice {x : Except (LexerError (Option ScriptError × List Handed))
      (Option (Span.Located Unit))}
    {a : Except (LexerError (Parser.ParseError Unit)) (Option (Span.Located Unit))}
    {z : Except (LexerError (Option (List Handed))) (Option (Span.Located Unit))}
    (h₁ : SliceRel (linkPhi version) x a) (h₂ : SliceRel (linkR version) x z) :
    ERel (LexErrRel (CM version)) (ORel (LocRel fun _ _ => True)) a z := by
  rcases x with ex | ox <;> rcases a with ea | oa <;> rcases z with ez | oz <;>
    simp only [ERel] at h₁ h₂ ⊢
  · exact compose_lexErr h₁ h₂
  · rcases ox with _ | lx <;> rcases oa with _ | la <;> rcases oz with _ | lz <;>
      simp only [ORel] at h₁ h₂ ⊢
    exact compose_loc h₁ h₂

theorem compose_eof {x : Except (LexerError (Option ScriptError × List Handed))
      (ControlFlow (Span.Located Unit))}
    {a : Except (LexerError (Parser.ParseError Unit)) (ControlFlow (Span.Located Unit))}
    {z : Except (LexerError (Option (List Handed))) (ControlFlow (Span.Located Unit))}
    (h₁ : EofRel (linkPhi version) x a) (h₂ : EofRel (linkR version) x z) :
    ERel (LexErrRel (CM version)) (FlowRel (LocRel fun _ _ => True)) a z := by
  rcases x with ex | ox <;> rcases a with ea | oa <;> rcases z with ez | oz <;>
    simp only [ERel] at h₁ h₂ ⊢
  · exact compose_lexErr h₁ h₂
  · rcases ox with _ | lx <;> rcases oa with _ | la <;> rcases oz with _ | lz <;>
      simp only [FlowRel] at h₁ h₂ ⊢
    exact compose_loc h₁ h₂

abbrev abandonF := Recovery.LexerRecovery.abandon (H := Flagged (scriptConsumer version))
  (m := AnswerM) Recovery.FailFast
abbrev recoverF := Recovery.LexerRecovery.recover (H := Flagged (scriptConsumer version))
  (m := AnswerM) Recovery.FailFast
abbrev abandonZ := Recovery.LexerRecovery.abandon (H := Answering (replay version))
  (m := AnswerM) Recovery.FailFast
abbrev recoverZ := Recovery.LexerRecovery.recover (H := Answering (replay version))
  (m := AnswerM) Recovery.FailFast

/-- A call on a slice from a state where the stand-in consumer and the parse adapter are related:
the parse adapter's ends as the replaying consumer's does, from the same state, with the same
lexer state after. -/
theorem sliceStep_replay (slice : ByteSlice) (c : Internal.LexerCore)
    (fl : Flagged (scriptConsumer version)) (taken : List Handed) (ad : RecAdapter)
    (he : fl.errored = false) (hinv : InvG version fl taken ad)
    (hgood : Dom.Good version ((((Internal.lexSliceStep (H := Flagged (scriptConsumer version))
      (m := AnswerM) abandonF recoverF slice).run c).run fl).run taken).2)
    (hsp : ((((Internal.lexSliceStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
      abandonF recoverF slice).run c).run fl).run taken).1.2.spoiled = false) :
    ERel (LexErrRel (CM version)) (ORel (LocRel fun _ _ => True))
        (((Internal.lexSliceStep (H := RecAdapter) (m := Id)
          (Recovery.LexerRecovery.abandon Recovery.FailFast)
          (Recovery.LexerRecovery.recover Recovery.FailFast) slice).run c).run ad).1.1
        ((((Internal.lexSliceStep (H := Answering (replay version)) (m := AnswerM) abandonZ
          recoverZ slice).run c).run {}).run taken).1.1.1 ∧
      (((Internal.lexSliceStep (H := RecAdapter) (m := Id)
          (Recovery.LexerRecovery.abandon Recovery.FailFast)
          (Recovery.LexerRecovery.recover Recovery.FailFast) slice).run c).run ad).1.2 =
        ((((Internal.lexSliceStep (H := Answering (replay version)) (m := AnswerM) abandonZ
          recoverZ slice).run c).run {}).run taken).1.1.2 ∧
      ((((Internal.lexSliceStep (H := Answering (replay version)) (m := AnswerM) abandonZ
          recoverZ slice).run c).run {}).run taken).2 =
        ((((Internal.lexSliceStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
          abandonF recoverF slice).run c).run fl).run taken).2 := by
  obtain ⟨-, hFs, hFt⟩ := fSlice_sim (version := version) slice c fl taken
  have hP := (phiSlice_sim (version := version) slice c).2.1 fl taken ad he hinv
    (by rw [hFt]; exact hgood) (by rw [hFs]; exact hsp)
  obtain ⟨⟨hR, hRc⟩, hRt⟩ := rSlice_sim (version := version) slice c ⟨fl⟩ {} taken
  obtain ⟨⟨hPr, hPc⟩, -, -⟩ := hP
  exact ⟨compose_slice hPr hR, hPc.symm.trans hRc, hRt.symm.trans hFt⟩

/-- The end of the input from a state where the stand-in consumer and the parse adapter are
related: the parse adapter's ends as the replaying consumer's does, from the same state, with the
same lexer state after. -/
theorem eofStep_replay (c : Internal.LexerCore)
    (fl : Flagged (scriptConsumer version)) (taken : List Handed) (ad : RecAdapter)
    (he : fl.errored = false) (hinv : InvG version fl taken ad)
    (hgood : Dom.Good version ((((Internal.lexEofStep (H := Flagged (scriptConsumer version))
      (m := AnswerM) (R := (scriptConsumer version).Result)
      (E := Option (scriptConsumer version).Error) abandonF recoverF).run c).run fl).run taken).2)
    (hsp : ((((Internal.lexEofStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
      (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
      abandonF recoverF).run c).run fl).run taken).1.2.spoiled = false) :
    ERel (LexErrRel (CM version)) (FlowRel (LocRel fun _ _ => True))
        (((Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
          (E := Parser.ParseError Unit)
          (Recovery.LexerRecovery.abandon Recovery.FailFast)
          (Recovery.LexerRecovery.recover Recovery.FailFast)).run c).run ad).1.1
        ((((Internal.lexEofStep (H := Answering (replay version)) (m := AnswerM)
          (R := (replay version).Result) (E := Option (replay version).Error) abandonZ
          recoverZ).run c).run {}).run taken).1.1.1 ∧
      (((Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
          (E := Parser.ParseError Unit)
          (Recovery.LexerRecovery.abandon Recovery.FailFast)
          (Recovery.LexerRecovery.recover Recovery.FailFast)).run c).run ad).1.2 =
        ((((Internal.lexEofStep (H := Answering (replay version)) (m := AnswerM)
          (R := (replay version).Result) (E := Option (replay version).Error) abandonZ
          recoverZ).run c).run {}).run taken).1.1.2 ∧
      ((((Internal.lexEofStep (H := Answering (replay version)) (m := AnswerM)
          (R := (replay version).Result) (E := Option (replay version).Error) abandonZ
          recoverZ).run c).run {}).run taken).2 =
        ((((Internal.lexEofStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
          (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
          abandonF recoverF).run c).run fl).run taken).2 := by
  obtain ⟨-, hFs, hFt⟩ := fEof_sim (version := version) c fl taken
  have hP := (phiEof_sim (version := version) c).2.1 fl taken ad he hinv
    (by rw [hFt]; exact hgood) (by rw [hFs]; exact hsp)
  obtain ⟨⟨hR, hRc⟩, hRt⟩ := rEof_sim (version := version) c ⟨fl⟩ {} taken
  obtain ⟨⟨hPr, hPc⟩, -, -⟩ := hP
  exact ⟨compose_eof hPr hR, hPc.symm.trans hRc, hRt.symm.trans hFt⟩

/-! ## Fed an input to its end -/

open BSmtLib.Facts.Proofs.Reader.Param.Run (HeldRel' heldRel_or)
open BSmtLib.Facts.Proofs.Reader.Param.Finish (InvF)
open BSmtLib.Facts.Proofs.Reader.Param.Run (FLexer)
open BSmtLib.Facts.Proofs.Reader.Lexes.Told
open BSmtLib.Facts.Proofs.Lexer.Consumers.RunE (runInputE runInputE_cons runInputE_nil_true)
open BSmtLib.Facts.Proofs.Reader.Param.Adapter (id_bind_eq)

/-- The library's lexer with the adapter's consumer for a consumer of the formalism. -/
abbrev ZOps := BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps

theorem eofResult_rel {x : Option (Span.Located Unit)} {y : Option (Span.Located Unit)}
    {f g : ControlFlow (Span.Located Unit)} (hh : HeldRel' x y)
    (hf : FlowRel (LocRel fun _ _ => True) f g) :
    HeldRel' (Parser.Canon.Through.eofResultT x f) (Lexer.Adapters.eofResult y g) := by
  rcases x with _ | lx <;> rcases y with _ | ly <;> simp only [HeldRel', ORel] at hh
  · rcases f with _ | lf <;> rcases g with _ | lg <;> simp only [FlowRel] at hf
    · trivial
    · exact hf
  · exact hh

theorem answering_handler {C : BSmtLibSpec.Lexer.Consumer} (z : BSmtLib.Lexer (Answering C)) :
    Internal.handler z = {} := by
  cases Internal.handler z; rfl

theorem run_answerZ {C : BSmtLibSpec.Lexer.Consumer} {α : Type} (z : BSmtLib.Lexer (Answering C))
    (x : Internal.InnerM (Answering C) AnswerM α) (taken : List Handed) :
    (Internal.run z x).run taken =
      let r := ((x.run (Internal.core z)).run {}).run taken
      ((r.1.1.1, Internal.ofParts r.1.2 r.1.1.2 (Internal.held z)), r.2) := by
  rw [Param.Flagged.run_answerM, answering_handler]

/-- The parse adapter's lexer and the one with the adapter's consumer for the replaying consumer
end alike when fed the same slices and then the end of the input. The parse adapter's error is
the one on which the recording runs over items standing for the tokens the replaying consumer
reports fail. The two start from lexers related to a lexer with the stand-in consumer, with the
same state and related held results. -/
theorem through_replay (hnl : NoLayout (scriptConsumer version) (toVersion version)) :
    ∀ (slices : List Regex.Chars) (a : FLexer version) (p : PLexer)
      (z : ZOps.Lexer (replay version)) (taken : List Handed),
      InvF version a p taken →
      Reach (scriptConsumer version) (toVersion version) (Internal.core a) →
      Internal.core z = Internal.core a → HeldRel' (Internal.held p) (Internal.held z) →
      Param.Dom.Good version ((Param.Flagged.flaggedOps.runInput a true slices).run taken).2 →
      ERel (LexErrRel (CM version)) HeldRel'
        ((Parser.Canon.Through.lexThrough (R := Unit) (E := Parser.ParseError Unit) p
          slices).map (·.1))
        ((runInputE ZOps z true slices).run taken).1.1
  | [], a, p, z, taken, hI, hR, hz, hzh, hgood => by
    simp only [LexOps.runInput, ite_true, StateT.run_bind] at hgood
    generalize hr : (Param.Flagged.flaggedOps.lexEofStep a).run taken = r at hgood
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq] at hgood
    have hgood' : Param.Dom.Good version taken' := by
      dsimp only at hgood
      rcases res with e | flow
      · exact hgood
      · dsimp only at hgood
        split at hgood <;> exact hgood
    have htk := congrArg Prod.snd hr
    simp only [Param.Flagged.flaggedOps, Param.Flagged.run_answerM] at htk
    obtain ⟨hcore, hheld, herr, hsp, hver, hinv⟩ := hI
    have hok := Param.UnaryCalls.lexEofStep_flag (Internal.core a) (Internal.handler a) taken herr
      hver
    unfold Param.UnaryCalls.irun at hok
    obtain ⟨-, hs₁⟩ := hok
    obtain ⟨hst, hsc, -⟩ := eofStep_replay (Internal.core a) (Internal.handler a) taken
      (Internal.handler p) herr hinv (by rw [htk]; exact hgood') (hs₁.trans hsp)
    unfold Parser.Canon.Through.lexThrough
    simp only [Parser.Canon.Through.lexFeed]
    rw [runInputE_nil_true]
    rw [show (ZOps.lexEofStep z).run taken = _ from run_answerZ z _ taken,
      Parser.Canon.Through.run_eq, ← hcore, hz]
    dsimp only
    generalize ((Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
      (E := Parser.ParseError Unit) (Recovery.LexerRecovery.abandon Recovery.FailFast)
      (Recovery.LexerRecovery.recover Recovery.FailFast)).run (Internal.core a)).run
      (Internal.handler p) = A at hst hsc ⊢
    generalize (((Internal.lexEofStep (H := Answering (replay version)) (m := AnswerM)
      (R := (replay version).Result) (E := Option (replay version).Error) abandonZ
      recoverZ).run (Internal.core a)).run {}).run taken = Z at hst hsc ⊢
    obtain ⟨⟨ra, ca⟩, ha⟩ := A
    obtain ⟨⟨⟨rz, cz⟩, hz'⟩, tz⟩ := Z
    dsimp only at hst ⊢
    rcases ra with ea | fa <;> rcases rz with ez | fz <;> simp only [ERel] at hst ⊢
    · exact hst
    · exact eofResult_rel hzh hst
  | slice :: slices, a, p, z, taken, hI, hR, hz, hzh, hgood => by
    simp only [LexOps.runInput, StateT.run_bind] at hgood
    generalize hr : (Param.Flagged.flaggedOps.lexSliceStep a slice.toByteArray.toByteSlice).run
        taken = r at hgood
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq] at hgood
    have hgood' : Param.Dom.Good version taken' := by
      dsimp only at hgood
      rcases res with e | held₁
      · exact hgood
      · obtain ⟨more, hmore⟩ := runInput_extendsT true slices
          (Param.Flagged.flaggedOps.withHeld a' (held₁.or (Param.Flagged.flaggedOps.held a')))
              taken'
        rw [hmore] at hgood
        exact hgood.of_append
    have htk := congrArg Prod.snd hr
    simp only [Param.Flagged.flaggedOps, Param.Flagged.run_answerM] at htk
    have hT := slice_stepT hnl _ ⟨slice, rfl⟩ a p taken hI hR hr hgood'
    obtain ⟨hcore, hheld, herr, hsp, hver, hinv⟩ := hI
    have hok := Param.UnaryCalls.lexSliceStep_flag slice.toByteArray.toByteSlice
      (Internal.core a) (Internal.handler a) taken herr hver
    unfold Param.UnaryCalls.irun at hok
    obtain ⟨-, -, hs₁⟩ := hok
    obtain ⟨hst, hsc, hstk⟩ := sliceStep_replay slice.toByteArray.toByteSlice (Internal.core a)
      (Internal.handler a) taken (Internal.handler p) herr hinv (by rw [htk]; exact hgood')
      (hs₁.trans hsp)
    -- the parse adapter's call on the slice, by its parts
    have hL : (Lexer.lexSlice p slice.toByteArray.toByteSlice : Id _) =
        match Internal.run p (Internal.lexSliceStep (R := Unit) (E := Parser.ParseError Unit)
          Parser.Canon.Chain.abandonI Parser.Canon.Chain.recoverI
          slice.toByteArray.toByteSlice) with
        | (.ok held, l) => .ok (Internal.withHeld l (held.or (Internal.held l)))
        | (.error e, l) => .error (e, Internal.handler (H := RecAdapter) l) := by
      simp only [Lexer.lexSlice]
      rcases Internal.run p (Internal.lexSliceStep (R := Unit) (E := Parser.ParseError Unit)
          Parser.Canon.Chain.abandonI Parser.Canon.Chain.recoverI
          slice.toByteArray.toByteSlice) with ⟨_ | _, l⟩ <;> rfl
    unfold Parser.Canon.Through.lexThrough at ⊢
    simp only [Parser.Canon.Through.lexFeed]
    rw [runInputE_cons]
    rw [show (ZOps.lexSliceStep z slice.toByteArray.toByteSlice).run taken = _ from
      run_answerZ z _ taken]
    rw [Parser.Canon.Through.run_eq] at hL ⊢
    rw [← hcore] at hL ⊢
    rw [hz]
    dsimp only at hL ⊢
    generalize ((Internal.lexSliceStep (H := RecAdapter) (m := Id) (R := Unit)
      (E := Parser.ParseError Unit) (Recovery.LexerRecovery.abandon Recovery.FailFast)
      (Recovery.LexerRecovery.recover Recovery.FailFast) slice.toByteArray.toByteSlice).run
      (Internal.core a)).run (Internal.handler p) = A at hst hsc hL ⊢
    generalize (((Internal.lexSliceStep (H := Answering (replay version)) (m := AnswerM)
      abandonZ recoverZ slice.toByteArray.toByteSlice).run (Internal.core a)).run {}).run
      taken = Z at hst hsc hstk ⊢
    obtain ⟨⟨ra, ca⟩, ha⟩ := A
    obtain ⟨⟨⟨rz, cz⟩, hz'⟩, tz⟩ := Z
    dsimp only at hst hsc hstk hL ⊢
    rcases ra with ea | oa <;> rcases rz with ez | oz <;> simp only [ERel] at hst
    · exact hst
    · rcases hT with ⟨held₁, rfl, p₂, held₂, hp, hI', hR'⟩ | ⟨e, -, ⟨e₂, x, hp⟩, -⟩
      · rw [hL] at hp
        injection hp with hp
        dsimp only
        rw [hp]
        have htz : tz = taken' := hstk.trans htk
        rw [htz]
        refine through_replay hnl slices (Internal.withHeld a' (held₁.or (Internal.held a'))) _ _
          taken' hI' hR' ?_ ?_ hgood
        · show cz = _
          rw [hI'.1, ← hp]
          exact hsc.symm
        · rw [← hp]
          exact heldRel_or hst hzh
      · rw [hL] at hp
        cases hp

/-! ## The replaying consumer and the script consumer -/

variable (version) in
/-- The relator of the adapter's consumers for `replay version` and for the script consumer:
from the same tokens taken, related values and the same tokens taken. -/
def relatorS : Relator (Answering (replay version)) AnswerM (Answering (scriptConsumer version))
    AnswerM where
  rel Q x y := ∀ a b l, Q ((x.run a).run l).1.1 ((y.run b).run l).1.1 ∧
    ((x.run a).run l).2 = ((y.run b).run l).2
  pure h _ _ _ := ⟨h, rfl⟩
  bind {_ _ _ _ _ _ x y f g} hx hk a b l := by
    obtain ⟨h₁, h₂⟩ := hx a b l
    have e₁ : ((x >>= f).run a).run l =
        ((f ((x.run a).run l).1.1).run ((x.run a).run l).1.2).run ((x.run a).run l).2 := rfl
    have e₂ : ((y >>= g).run b).run l =
        ((g ((y.run b).run l).1.1).run ((y.run b).run l).1.2).run ((y.run b).run l).2 := rfl
    rw [e₁, e₂, h₂]
    exact hk _ _ h₁ _ _ _
  mono hQ h a b l := ⟨hQ _ _ (h a b l).1, (h a b l).2⟩

variable (version) in
/-- The link of the adapter's consumers for `replay version` and for the script consumer: equal
results, and errors that are both `none` or neither. -/
def linkS : Link (Answering (replay version)) AnswerM Unit (Option (List Handed))
    (Answering (scriptConsumer version)) AnswerM Unit (Option ScriptError) where
  rc := relatorS version
  rr := (· = ·)
  re o o' := o.isSome = o'.isSome

theorem callsS : Calls (linkS version) where
  concrete := rfl
  consume cursor h a b l := by
    obtain ⟨h1, h2, h3⟩ := answering_replay (version := version) (remaining cursor + 1) cursor h l
      (Nat.lt_succ_self _)
    have eA : ((Token.ConsumeFrom.consume (m := AnswerM) cursor h :
        StateT (Answering (replay version)) AnswerM _).run a).run l =
        ((((Answering.consume (replay version) cursor h).run l).1, a),
          ((Answering.consume (replay version) cursor h).run l).2) := rfl
    have eB : ((Token.ConsumeFrom.consume (m := AnswerM) cursor h :
        StateT (Answering (scriptConsumer version)) AnswerM _).run b).run l =
        ((((Answering.consume (scriptConsumer version) cursor h).run l).1, b),
          ((Answering.consume (scriptConsumer version) cursor h).run l).2) := rfl
    erw [eA, eB]
    dsimp only
    rw [h1, h2, h3]
    refine ⟨⟨?_, rfl⟩, rfl⟩
    generalize ((Answering.consume (scriptConsumer version) cursor h).run l).1.1 = x
    rcases x with e | (_ | r) <;> simp [ERel, FlowRel, linkS, Except.mapError] <;> rfl

theorem consumersS : Consumers (linkS version) := .ofCalls callsS


abbrev abandonS := Recovery.LexerRecovery.abandon (H := Answering (scriptConsumer version))
  (m := AnswerM) Recovery.FailFast
abbrev recoverS := Recovery.LexerRecovery.recover (H := Answering (scriptConsumer version))
  (m := AnswerM) Recovery.FailFast

theorem sSlice_sim (slice : ByteSlice) :
    SSim (linkS version) (SliceRel (linkS version))
      (Internal.lexSliceStep (H := Answering (replay version)) (m := AnswerM) abandonZ recoverZ
        slice)
      (Internal.lexSliceStep (H := Answering (scriptConsumer version)) (m := AnswerM) abandonS
        recoverS slice) :=
  lexSliceStep_sim consumersS _ _ _ _ (fun _ => (linkS version).rc.pure rfl)
    (fun _ => (linkS version).rc.pure rfl) slice

theorem sEof_sim :
    SSim (linkS version) (EofRel (linkS version))
      (Internal.lexEofStep (H := Answering (replay version)) (m := AnswerM)
        (R := (replay version).Result) (E := Option (replay version).Error) abandonZ recoverZ)
      (Internal.lexEofStep (H := Answering (scriptConsumer version)) (m := AnswerM)
        (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
        abandonS recoverS) :=
  lexEofStep_sim consumersS _ _ _ _ (fun _ => (linkS version).rc.pure rfl)
    (fun _ => (linkS version).rc.pure rfl)

theorem eofResult_relS {x y : Option (Span.Located Unit)}
    {f g : ControlFlow (Span.Located Unit)} (hh : HeldRel' x y)
    (hf : FlowRel (LocRel (· = ·)) f g) :
    HeldRel' (Lexer.Adapters.eofResult x f) (Lexer.Adapters.eofResult y g) := by
  rcases x with _ | lx <;> rcases y with _ | ly <;> simp only [HeldRel', ORel] at hh
  · rcases f with _ | lf <;> rcases g with _ | lg <;> simp only [FlowRel] at hf
    · trivial
    · exact ⟨trivial, hf.2⟩
  · exact hh

theorem heldRel_of_eq {x y : Option (Span.Located Unit)} (h : ORel (LocRel (· = ·)) x y) :
    HeldRel' x y := by
  rcases x with _ | lx <;> rcases y with _ | ly <;> simp only [HeldRel', ORel] at h ⊢
  exact ⟨trivial, h.2⟩

theorem zsEof_step (z₁ : ZOps.Lexer (replay version)) (z₂ : ZOps.Lexer (scriptConsumer version))
    (taken : List Handed) (hc : Internal.core z₁ = Internal.core z₂) :
    EofRel (linkS version) ((ZOps.lexEofStep z₁).run taken).1.1
        ((ZOps.lexEofStep z₂).run taken).1.1 ∧
      Internal.core ((ZOps.lexEofStep z₁).run taken).1.2 =
        Internal.core ((ZOps.lexEofStep z₂).run taken).1.2 ∧
      ZOps.held ((ZOps.lexEofStep z₁).run taken).1.2 = ZOps.held z₁ ∧
      ZOps.held ((ZOps.lexEofStep z₂).run taken).1.2 = ZOps.held z₂ ∧
      ((ZOps.lexEofStep z₁).run taken).2 = ((ZOps.lexEofStep z₂).run taken).2 := by
  rw [show (ZOps.lexEofStep z₁).run taken = _ from run_answerZ z₁ _ taken,
    show (ZOps.lexEofStep z₂).run taken = _ from run_answerZ z₂ _ taken, hc]
  obtain ⟨⟨hst, hsc⟩, htk⟩ := sEof_sim (version := version) (Internal.core z₂) {} {} taken
  exact ⟨hst, hsc, rfl, rfl, htk⟩

theorem zsSlice_step (slice : ByteSlice) (z₁ : ZOps.Lexer (replay version))
    (z₂ : ZOps.Lexer (scriptConsumer version))
    (taken : List Handed) (hc : Internal.core z₁ = Internal.core z₂) :
    SliceRel (linkS version) ((ZOps.lexSliceStep z₁ slice).run taken).1.1
        ((ZOps.lexSliceStep z₂ slice).run taken).1.1 ∧
      Internal.core ((ZOps.lexSliceStep z₁ slice).run taken).1.2 =
        Internal.core ((ZOps.lexSliceStep z₂ slice).run taken).1.2 ∧
      ZOps.held ((ZOps.lexSliceStep z₁ slice).run taken).1.2 = ZOps.held z₁ ∧
      ZOps.held ((ZOps.lexSliceStep z₂ slice).run taken).1.2 = ZOps.held z₂ ∧
      ((ZOps.lexSliceStep z₁ slice).run taken).2 = ((ZOps.lexSliceStep z₂ slice).run taken).2 := by
  rw [show (ZOps.lexSliceStep z₁ slice).run taken = _ from run_answerZ z₁ _ taken,
    show (ZOps.lexSliceStep z₂ slice).run taken = _ from run_answerZ z₂ _ taken, hc]
  obtain ⟨⟨hst, hsc⟩, htk⟩ := sSlice_sim (version := version) slice (Internal.core z₂) {} {}
    taken
  exact ⟨hst, hsc, rfl, rfl, htk⟩

/-- The library's lexer with the adapter's consumer for the replaying consumer and the one with
the adapter's consumer for the script consumer take the same tokens and give the same results,
and errors alike but for the consumer's. The two start from the same state and related held
results, and are fed the same slices and then the end of the input. -/
theorem replay_script : ∀ (slices : List Regex.Chars) (z₁ : ZOps.Lexer (replay version))
    (z₂ : ZOps.Lexer (scriptConsumer version)) (taken : List Handed),
    Internal.core z₁ = Internal.core z₂ → HeldRel' (ZOps.held z₁) (ZOps.held z₂) →
      ERel (LexErrRel (linkS version).re) HeldRel'
          ((runInputE ZOps z₁ true slices).run taken).1.1
          ((runInputE ZOps z₂ true slices).run taken).1.1 ∧
        ((runInputE ZOps z₁ true slices).run taken).2 =
          ((runInputE ZOps z₂ true slices).run taken).2
  | [], z₁, z₂, taken, hc, hh => by
    rw [runInputE_nil_true, runInputE_nil_true]
    obtain ⟨hst, -, h₁, h₂, htk⟩ := zsEof_step z₁ z₂ taken hc
    generalize (ZOps.lexEofStep z₁).run taken = A at hst h₁ htk ⊢
    generalize (ZOps.lexEofStep z₂).run taken = B at hst h₂ htk ⊢
    obtain ⟨⟨ra, la⟩, ta⟩ := A
    obtain ⟨⟨rb, lb⟩, tb⟩ := B
    dsimp only at hst h₁ h₂ htk ⊢
    rcases ra with ea | fa <;> rcases rb with eb | fb
    · exact ⟨hst, htk⟩
    · exact (hst : False).elim
    · exact (hst : False).elim
    · refine ⟨?_, htk⟩
      show HeldRel' (Lexer.Adapters.eofResult (ZOps.held la) fa)
        (Lexer.Adapters.eofResult (ZOps.held lb) fb)
      rw [h₁, h₂]
      exact eofResult_relS hh hst
  | slice :: slices, z₁, z₂, taken, hc, hh => by
    rw [runInputE_cons, runInputE_cons]
    obtain ⟨hst, hsc, h₁, h₂, htk⟩ := zsSlice_step slice.toByteArray.toByteSlice z₁ z₂ taken hc
    generalize (ZOps.lexSliceStep z₁ slice.toByteArray.toByteSlice).run taken = A
      at hst hsc h₁ htk ⊢
    generalize (ZOps.lexSliceStep z₂ slice.toByteArray.toByteSlice).run taken = B
      at hst hsc h₂ htk ⊢
    obtain ⟨⟨ra, la⟩, ta⟩ := A
    obtain ⟨⟨rb, lb⟩, tb⟩ := B
    dsimp only at hst hsc h₁ h₂ htk ⊢
    rcases ra with ea | oa <;> rcases rb with eb | ob
    · exact ⟨hst, htk⟩
    · exact (hst : False).elim
    · exact (hst : False).elim
    · rw [htk]
      refine replay_script slices _ _ tb hsc ?_
      show HeldRel' (oa.or (ZOps.held la)) (ob.or (ZOps.held lb))
      rw [h₁, h₂]
      exact heldRel_or (heldRel_of_eq hst) hh

end BSmtLib.Facts.Proofs.Reader.Lexes.ThroughPhi
