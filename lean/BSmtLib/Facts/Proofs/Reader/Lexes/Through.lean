module

public import BSmtLib.Facts.Proofs.Reader.Lexes.Told
public import BSmtLib.Facts.PublicApi.Adapters
import all BSmtLib.Lexer
import all BSmtLib.Reader

@[expose] public section

/-!
# The reader after an input it read to the end

`through_flagged` runs two things from related lexers, each fed an input to its end by its public
calls: the reader over the lexer with the parse adapter, and the lexer with the stand-in consumer
`Flagged (scriptConsumer version)`. Where the reader does not fail:
- the lexer with the stand-in consumer does not fail either;
- it ends with the fields of the reader's lexer;
- the parse adapter stands where the recording run over the tokens that lexer took leaves the
  parser.
-/

namespace BSmtLib.Facts.Proofs.Reader.Lexes.Through

open BSmtLib.Lexer
open BSmtLibSpec
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM LexOps)
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Parser.Adapters.Run.Rejection BSmtLib.Facts.Proofs.Reader.Param
open BSmtLib.Facts.Proofs.Reader.Param.Adapter BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Facts.Proofs.Reader.Param.Calls BSmtLib.Facts.Proofs.Reader.Param.Erase
open BSmtLib.Facts.Proofs.Reader.Param.Failing BSmtLib.Facts.Proofs.Reader.Param.Final
open BSmtLib.Facts.Proofs.Reader.Param.Finish BSmtLib.Facts.Proofs.Reader.Param.General
open BSmtLib.Facts.Proofs.Reader.Param.Link BSmtLib.Facts.Proofs.Reader.Param.Run
open BSmtLib.Facts.Proofs.Reader.Param.UnaryCalls BSmtLib.Facts.Proofs.Reader.Reader
open BSmtLib.Facts.Reader.Adapters BSmtLib.Lexer.Error
open BSmtLib.Facts.Proofs.Reader.Lexes.Told
open BSmtLib.Facts.PublicApi.Adapters (ByteList feed readThrough)

variable {version : Lexicon.Version}

/-- The end of the input from a state the lexer reaches, after which the tokens taken with the
first consumer are `Good`:
- where it does not fail with the first consumer, nothing has gone wrong with the first; with the
  parse adapter, it does not fail either, returns a result exactly where it does with the first,
  and ends with the fields it ends with with the first; the parse adapter then stands where the
  recording run over the tokens taken leaves the parser;
- where it fails, it fails with the parse adapter, which stands there too. -/
theorem eof_stepC (hnl : NoLayout (scriptConsumer version) (toVersion version))
    (a : FLexer version) (p : PLexer) (taken : List Handed)
    (hI : InvF version a p taken)
    (hR : Reach (scriptConsumer version) (toVersion version) (Internal.core a))
    {res : Except (LexerError (Option (scriptConsumer version).Error))
      (ControlFlow (Span.Located (scriptConsumer version).Result))} {a' : FLexer version}
    {taken' : List Handed}
    (hr : (Param.Flagged.flaggedOps.lexEofStep a).run taken = ((res, a'), taken'))
    (hgood : Param.Dom.Good version taken') :
    (∃ flow, res = .ok flow ∧ ∃ (p' : PLexer) (result : Option (Span.Located Unit)),
      (Lexer.lexEof p : Id _) = .ok (result, Internal.withHeld p' none) ∧
      HeldRel' (Lexer.Adapters.eofResult (Param.Flagged.flaggedOps.held a') flow) result ∧
      InvG version (Internal.handler a') taken' (Internal.handler p') ∧
      Internal.core p' = Internal.core a' ∧ (Internal.handler a').errored = false) ∨
    (∃ e, res = .error e ∧ (∃ e₂ x, (Lexer.lexEof p : Id _) = .error (e₂, x)) ∧
      InvG version (Internal.handler a') taken' (Internal.handler (eofedP p))) := by
  obtain ⟨hcore, hheld, herr, hsp, hver, hinv⟩ := hI
  have h2 := (eofStepG_sim (Internal.core a)).2.1 (Internal.handler a) taken
      (Internal.handler p) herr hinv
  have hok := lexEofStep_flag (Internal.core a) (Internal.handler a) taken herr hver
  have halike := answering_eof_alike (Internal.core a) (Internal.handler a) taken
  have hA : ∀ e, (((Internal.lexEofStep (H := Answering (scriptConsumer version)) (m := AnswerM)
      (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
      (Recovery.LexerRecovery.abandon Recovery.FailFast)
          (Recovery.LexerRecovery.recover Recovery.FailFast)).run
        (Internal.core a)).run {} |>.run taken).1.1.1 = .error e →
      e.kind ≠ .consumer none :=
    fun e he => (hnl _ hR).2 (Internal.held a) taken e he
  unfold irun at hok
  simp only [Param.Flagged.flaggedOps] at hr
  rw [Param.Flagged.run_answerM] at hr
  unfold eofedP
  simp only [Lexer.lexEof]
  rw [run_id, ← hcore]
  generalize ((StateT.run (Internal.lexEofStep (H := Answering (scriptConsumer version))
      (m := AnswerM)
    (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
    (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast))
    (Internal.core a)).run {}).run taken = RA at halike hA
  generalize ((StateT.run (Internal.lexEofStep (H := Flagged (scriptConsumer version))
      (m := AnswerM)
    (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
    (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast))
    (Internal.core a)).run (Internal.handler a)).run taken = R at hr h2 hok halike
  generalize (StateT.run (Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
    (E := Parser.ParseError Unit)
    (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast))
    (Internal.core a)).run (Internal.handler p) = R₂ at h2 ⊢
  obtain ⟨⟨⟨res', core'⟩, fl'⟩, taken''⟩ := R
  obtain ⟨⟨⟨resA, coreA⟩, _⟩, _⟩ := RA
  obtain ⟨⟨res₂, core₂⟩, adapter₂⟩ := R₂
  simp only at hr
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
  obtain ⟨he₁, hs₁⟩ := hok
  dsimp only at hs₁ h2 he₁ halike hA
  obtain ⟨⟨hrel, rfl⟩, hinv', hfail⟩ := h2 hgood (hs₁.trans hsp)
  have hnone := kind_ne_of_alike halike hA
  match res, res₂, hrel with
  | .ok flow, .ok flow₂, hh =>
    have hfl : fl'.errored = false := by
      cases h : fl'.errored
      · rfl
      · exact absurd (he₁ h) id
    refine .inl ⟨flow, rfl, Internal.ofParts adapter₂ core'
        (Internal.held p), _, rfl, ?_, hinv' hfl, rfl, hfl⟩
    dsimp only [Param.Flagged.flaggedOps, Param.Flagged.held_ofParts]
    generalize Internal.held p = hp at hheld ⊢
    generalize Internal.held a = ha at hheld ⊢
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

/-- A read through slices reads the first slice, then the rest. -/
theorem readThrough_cons (reader : RecReader) (slice : ByteList) (slices : List ByteList) :
    readThrough reader (slice :: slices) =
      match (reader.readSlice slice.toByteArray.toByteSlice : Id _) with
      | .ok reader => readThrough reader slices
      | .error failure => .error failure := by
  unfold readThrough
  rw [feed]
  cases (reader.readSlice slice.toByteArray.toByteSlice : Id _) <;> rfl

/-- The reader over a lexer related to a lexer with the stand-in consumer, fed an input to its end:
where it does not fail, the lexer with the stand-in consumer does not fail either, ends with the
fields of the reader's lexer, and the parse adapter stands where the recording run over the tokens
that lexer took leaves the parser. -/
theorem through_flagged (hnl : NoLayout (scriptConsumer version) (toVersion version)) :
    ∀ (slices : List Regex.Chars) (a : FLexer version) (p : PLexer) (taken : List Handed),
      InvF version a p taken →
      Reach (scriptConsumer version) (toVersion version) (Internal.core a) →
      Param.Dom.Good version ((Param.Flagged.flaggedOps.runInput a true slices).run taken).2 →
      ∀ {result : Option (Span.Located Unit)} {before after : RecReader},
        readThrough (Reader.Internal.ofLexer p : RecReader) slices = .ok (result, before, after) →
        ((Param.Flagged.flaggedOps.runInput a true slices).run taken).1.1.isFailed = false ∧
        Internal.core (Reader.Internal.lexer after) =
          Internal.core ((Param.Flagged.flaggedOps.runInput a true slices).run taken).1.2 ∧
        ∃ fl, InvG version fl ((Param.Flagged.flaggedOps.runInput a true slices).run taken).2
          (Internal.handler (Reader.Internal.lexer after))
  | [], a, p, taken, hI, hR, hgood, result, before, after, h => by
    simp only [LexOps.runInput, ite_true, StateT.run_bind] at hgood ⊢
    generalize hr : (Param.Flagged.flaggedOps.lexEofStep a).run taken = r at hgood ⊢
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq] at hgood ⊢
    have hgood' : Param.Dom.Good version taken' := by
      dsimp only at hgood
      rcases res with e | flow
      · exact hgood
      · dsimp only at hgood
        split at hgood <;> exact hgood
    unfold readThrough at h
    rw [feed] at h
    dsimp only at h
    rw [readEof_ofLexer] at h
    rcases eof_stepC hnl a p taken hI hR hr hgood' with
        ⟨flow, rfl, p₂, r₂, hp, -, hinv, hcore, -⟩ | ⟨e, rfl, ⟨e₂, x, hp⟩, -⟩
    · rw [hp] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      dsimp only
      generalize Lexer.Adapters.eofResult (Param.Flagged.flaggedOps.held a') flow = o
      cases o <;>
        exact ⟨rfl, hcore, Internal.handler a', hinv⟩
    · rw [hp] at h
      cases h
  | slice :: slices, a, p, taken, hI, hR, hgood, result, before, after, h => by
    simp only [LexOps.runInput, StateT.run_bind] at hgood ⊢
    generalize hr : (Param.Flagged.flaggedOps.lexSliceStep a slice.toByteArray.toByteSlice).run
        taken = r at hgood ⊢
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq] at hgood ⊢
    have hgood' : Param.Dom.Good version taken' := by
      dsimp only at hgood
      rcases res with e | held₁
      · exact hgood
      · obtain ⟨more, hmore⟩ := runInput_extendsT true slices
          (Param.Flagged.flaggedOps.withHeld a' (held₁.or (Param.Flagged.flaggedOps.held a')))
              taken'
        rw [hmore] at hgood
        exact hgood.of_append
    rw [readThrough_cons, readSlice_ofLexer] at h
    rcases slice_stepT hnl _ ⟨slice, rfl⟩ a p taken hI hR hr hgood' with
        ⟨held₁, rfl, p₂, held₂, hp, hI', hR'⟩ | ⟨e, rfl, ⟨e₂, x, hp⟩, -⟩
    · rw [hp] at h
      exact through_flagged hnl slices _ _ taken' hI' hR' hgood h
    · rw [hp] at h
      cases h

end BSmtLib.Facts.Proofs.Reader.Lexes.Through
