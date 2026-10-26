module

public import BSmtLib.Facts.Proofs.Reader.Param.Relate
import all BSmtLib.Lexer

@[expose] public section

/-!
# The library's lexer with the parse adapter, call by call

The library's lexer fed with `Flagged (scriptConsumer version)` and fed with the parse adapter
(`RecAdapter`) are related call by call: by the lexer's steps on two consumers
(`Calls.lexSliceStep_sim`, `Calls.lexEofStep_sim`) on the link of the two consumers
(`link_consumers`), and, where nothing went wrong, by the unary walk (`lexSliceStep_flag`,
`lexEofStep_flag`). `Inv` is what holds between the two lexers between the calls: the same
fields and held result, nothing gone wrong with the first, and the adapter where the recording
run leaves the parser (`InvB`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Run

open BSmtLib.Lexer
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLibSpec BSmtLibSpec.Grammar
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM LexOps)
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Facts.Proofs.Reader.Param.Adapter BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Facts.Proofs.Reader.Param.Calls BSmtLib.Facts.Proofs.Reader.Param.Loop
open BSmtLib.Facts.Proofs.Reader.Param.Relate BSmtLib.Facts.Proofs.Reader.Param.UnaryCalls
open BSmtLib.Facts.Reader.Adapters

/-! ## Results -/

/-- Held results related as the link relates them. -/
abbrev HeldRel' {R₁ R₂ : Type} : Option (Span.Located R₁) → Option (Span.Located R₂) → Prop :=
  ORel (LocRel (fun _ _ => True))

theorem heldRel_or {R₁ R₂ : Type} {x u : Option (Span.Located R₁)} {y v : Option (Span.Located R₂)}
    (h₁ : HeldRel' x y) (h₂ : HeldRel' u v) : HeldRel' (x.or u) (y.or v) := by
  match x, y, h₁ with
  | none, none, _ => exact h₂
  | some _, some _, h => exact h

theorem isError_ok_of_eRel {ε₁ ε₂ α β : Type} {Qe : ε₁ → ε₂ → Prop} {Q : α → β → Prop}
    {x : Except ε₁ α} {y : Except ε₂ β} (h : ERel Qe Q x y) (hx : Flagged.isError x = false) :
    ∃ a b, x = .ok a ∧ y = .ok b ∧ Q a b := by
  match x, y, h with
  | .ok a, .ok b, h => exact ⟨a, b, rfl, rfl, h⟩
  | .error _, .error _, _ => cases hx

/-! ## The two lexers -/

section

variable (version : Lexicon.Version) (commands : List Tree.Command)

/-- The lexer with the first consumer. -/
abbrev FLexer := BSmtLib.Lexer (Flagged (scriptConsumer version))

/-- What holds between the two lexers between the calls. -/
def Inv (a : FLexer version) (p : PLexer) (taken : List Handed) : Prop :=
  Internal.core a = Internal.core p ∧ HeldRel' (Internal.held a) (Internal.held p) ∧
      (Internal.handler a).errored = false ∧
    (Internal.core a).version = (Internal.handler a).version ∧
    InvB version commands (Internal.handler a) taken (Internal.handler p)

end

/-! ## The calls -/

section

variable {version : Lexicon.Version} {commands : List Tree.Command}

theorem link_abandon (l : Span.Location) :
    (linkLink version commands).rc.rel (· = ·)
      (Recovery.LexerRecovery.abandon (H := Flagged (scriptConsumer version)) (m := AnswerM)
        Recovery.FailFast l)
      (Recovery.LexerRecovery.abandon (H := RecAdapter) (m := Id) Recovery.FailFast l) :=
  (linkLink version commands).rc.pure rfl

theorem link_recover (l : Span.Location) :
    (linkLink version commands).rc.rel (· = ·)
      (Recovery.LexerRecovery.recover (H := Flagged (scriptConsumer version)) (m := AnswerM)
        Recovery.FailFast l)
      (Recovery.LexerRecovery.recover (H := RecAdapter) (m := Id) Recovery.FailFast l) :=
  (linkLink version commands).rc.pure rfl

end

section

variable {version : Lexicon.Version} {commands : List Tree.Command}

theorem sliceStep_sim (hscript : Script version commands) (slice : ByteSlice) :
    SSim (linkLink version commands) (SliceRel (linkLink version commands))
      (Internal.lexSliceStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
            (Recovery.LexerRecovery.recover Recovery.FailFast) slice)
      (Internal.lexSliceStep (H := RecAdapter) (m := Id)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
            (Recovery.LexerRecovery.recover Recovery.FailFast) slice) :=
  lexSliceStep_sim (link_consumers hscript) _ _ _ _ link_abandon link_recover slice

theorem sliceStep_extends (hscript : Script version commands) (slice : ByteSlice)
    (a : FLexer version) (taken : List Handed) :
    ∃ more, ((Flagged.flaggedOps.lexSliceStep a slice).run taken).2 = taken ++ more := by
  obtain ⟨hext, -, -⟩ := (sliceStep_sim hscript slice (Internal.core a)).1
      (Internal.handler a) taken
  simp only [Flagged.flaggedOps]
  exact hext

theorem run_id {H R E : Type} [Token.Consume H R E] {α : Type} (lexer : BSmtLib.Lexer H)
    (step : InnerM H Id α) :
    (Internal.run lexer step : Id _) =
      (((step.run (Internal.core lexer)).run (Internal.handler lexer)).1.1,
        Internal.ofParts ((step.run (Internal.core lexer)).run (Internal.handler lexer)).2
          ((step.run (Internal.core lexer)).run (Internal.handler lexer)).1.2
              (Internal.held lexer)) := (rfl)

/-- A call on a slice that does not fail with the first consumer, after which the tokens taken
stand for a start of the script: the call with the parse adapter does not fail, and the lexers
are again related. -/
theorem slice_step (hscript : Script version commands) (slice : ByteSlice) (a : FLexer version)
    (p : PLexer) (taken : List Handed) (hI : Inv version commands a p taken)
    {held₁ : Option (Span.Located (scriptConsumer version).Result)} {a' : FLexer version}
    {taken' : List Handed}
    (hr : (Flagged.flaggedOps.lexSliceStep a slice).run taken = ((.ok held₁, a'), taken'))
    (hv : Link.Viable commands taken') :
    ∃ (p' : PLexer) (held₂ : Option (Span.Located Unit)),
      (Lexer.lexSlice p slice : Id _) = .ok (Internal.withHeld p' (held₂.or (Internal.held p'))) ∧
      Inv version commands (Internal.withHeld a' (held₁.or (Internal.held a')))
          (Internal.withHeld p' (held₂.or (Internal.held p')))
        taken' := by
  obtain ⟨hcore, hheld, herr, hver, hinv⟩ := hI
  have h2 := (sliceStep_sim hscript slice (Internal.core a)).2 (Internal.handler a) taken
      (Internal.handler p) hinv
  have hok := lexSliceStep_flag slice (Internal.core a) (Internal.handler a) taken herr hver
  unfold irun at hok
  simp only [Flagged.flaggedOps] at hr
  rw [Flagged.run_answerM] at hr
  simp only [Lexer.lexSlice]
  rw [run_id, ← hcore]
  generalize ((StateT.run (Internal.lexSliceStep (H := Flagged (scriptConsumer version))
      (m := AnswerM)
    (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast) slice)
    (Internal.core a)).run (Internal.handler a)).run taken = R at hr h2 hok
  generalize (StateT.run (Internal.lexSliceStep (H := RecAdapter) (m := Id)
    (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast) slice)
    (Internal.core a)).run (Internal.handler p) = R₂ at h2 ⊢
  obtain ⟨⟨⟨res, core'⟩, fl'⟩, taken''⟩ := R
  obtain ⟨⟨res₂, core₂⟩, adapter₂⟩ := R₂
  simp only at hr
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
  obtain ⟨hv₁, he₁, -⟩ := hok
  have hfl : fl'.errored = false := by
    cases h : fl'.errored
    · rfl
    · exact absurd (he₁ h) id
  obtain ⟨⟨hrel, rfl⟩, hinv'⟩ := h2 hfl hv
  obtain ⟨_, held₂, hx, rfl, hh⟩ := isError_ok_of_eRel hrel rfl
  cases hx
  exact ⟨_, held₂, rfl, rfl, heldRel_or hh hheld, hfl, hv₁ hfl, hinv'⟩

theorem eofStep_sim (hscript : Script version commands) :
    SSim (linkLink version commands) (EofRel (linkLink version commands))
      (Internal.lexEofStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
        (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
            (Recovery.LexerRecovery.recover Recovery.FailFast))
      (Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
          (E := Parser.ParseError Unit)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
            (Recovery.LexerRecovery.recover Recovery.FailFast)) :=
  lexEofStep_sim (link_consumers hscript) _ _ _ _ link_abandon link_recover

theorem eofStep_extends (hscript : Script version commands) (a : FLexer version)
    (taken : List Handed) :
    ∃ more, ((Flagged.flaggedOps.lexEofStep a).run taken).2 = taken ++ more := by
  obtain ⟨hext, -, -⟩ := (eofStep_sim hscript (Internal.core a)).1 (Internal.handler a) taken
  simp only [Flagged.flaggedOps]
  exact hext

/-- The end of the input, if it does not fail with the first consumer and the tokens taken then
stand for a start of the script: it does not fail with the parse adapter, with the same result,
and the adapter stands where the recording run leaves the parser. -/
theorem eof_step (hscript : Script version commands) (a : FLexer version) (p : PLexer)
    (taken : List Handed) (hI : Inv version commands a p taken)
    {flow : ControlFlow (Span.Located (scriptConsumer version).Result)} {a' : FLexer version}
    {taken' : List Handed}
    (hr : (Flagged.flaggedOps.lexEofStep a).run taken = ((.ok flow, a'), taken'))
    (hv : Link.Viable commands taken') :
    ∃ (p' : PLexer) (result : Option (Span.Located Unit)),
      (Lexer.lexEof p : Id _) = .ok (result, Internal.withHeld p' none) ∧
      HeldRel' (Lexer.Adapters.eofResult (Flagged.flaggedOps.held a') flow) result ∧
      (Internal.handler a').errored = false ∧ InvB version commands (Internal.handler a') taken'
          (Internal.handler p') := by
  obtain ⟨hcore, hheld, herr, hver, hinv⟩ := hI
  have h2 := (eofStep_sim hscript (Internal.core a)).2 (Internal.handler a) taken
      (Internal.handler p) hinv
  have hok := lexEofStep_flag (Internal.core a) (Internal.handler a) taken herr hver
  unfold irun at hok
  simp only [Flagged.flaggedOps] at hr
  rw [Flagged.run_answerM] at hr
  simp only [Lexer.lexEof]
  rw [run_id, ← hcore]
  generalize ((StateT.run (Internal.lexEofStep (H := Flagged (scriptConsumer version))
      (m := AnswerM)
    (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
    (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast))
    (Internal.core a)).run (Internal.handler a)).run taken = R at hr h2 hok
  generalize (StateT.run (Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
    (E := Parser.ParseError Unit)
    (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast))
    (Internal.core a)).run (Internal.handler p) = R₂ at h2 ⊢
  obtain ⟨⟨⟨res, core'⟩, fl'⟩, taken''⟩ := R
  obtain ⟨⟨res₂, core₂⟩, adapter₂⟩ := R₂
  simp only at hr
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
  have hfl : fl'.errored = false := by
    cases h : fl'.errored
    · rfl
    · exact absurd (hok.1 h) id
  obtain ⟨⟨hrel, rfl⟩, hinv'⟩ := h2 hfl hv
  obtain ⟨_, flow₂, hx, rfl, hh⟩ := isError_ok_of_eRel hrel rfl
  cases hx
  refine ⟨Internal.ofParts adapter₂ core' (Internal.held p), _, rfl, ?_, hfl, hinv'⟩
  dsimp only [Flagged.flaggedOps, Flagged.held_ofParts]
  generalize Internal.held p = hp at hheld ⊢
  generalize Internal.held a = ha at hheld ⊢
  match ha, hp, hheld with
  | none, none, _ =>
    match flow, flow₂, hh with
    | .continue, .continue, _ => exact trivial
    | .break _, .break _, h => exact h
  | some _, some _, h => exact h

theorem runInput_extends (hscript : Script version commands) :
    ∀ (slices : List Regex.Chars) (a : FLexer version) (taken : List Handed),
      ∃ more, ((Flagged.flaggedOps.runInput a true slices).run taken).2 = taken ++ more
  | [], a, taken => by
    obtain ⟨more, hmore⟩ := eofStep_extends hscript a taken
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
    obtain ⟨more, hmore⟩ := sliceStep_extends hscript slice.toByteArray.toByteSlice a taken
    simp only [LexOps.runInput, StateT.run_bind]
    generalize (Flagged.flaggedOps.lexSliceStep a slice.toByteArray.toByteSlice).run taken =
        r at hmore
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq]
    dsimp only at hmore ⊢
    rcases res with e | held
    · exact ⟨more, hmore⟩
    · obtain ⟨more', hmore'⟩ := runInput_extends hscript slices
        (Flagged.flaggedOps.withHeld a' (held.or (Flagged.flaggedOps.held a'))) taken'
      exact ⟨more ++ more', by rw [hmore', hmore, List.append_assoc]⟩

end

section

variable {version : Lexicon.Version} {commands : List Tree.Command}

/-- Where the run with the first consumer finishes and the tokens taken stand for a start of the
script, the run with the parse adapter finishes with a result, and the adapter stands where the
recording run over items standing for the tokens leaves the parser. -/
theorem feed_agree (hscript : Script version commands) :
    ∀ (slices : List Regex.Chars) (a : FLexer version) (p : PLexer) (taken : List Handed),
      Inv version commands a p taken →
      ((Flagged.flaggedOps.runInput a true slices).run taken).1.1.isFinished = true →
      Link.Viable commands ((Flagged.flaggedOps.runInput a true slices).run taken).2 →
      ∃ result p', paFeed p slices = .ok (some result, p') ∧
        ∃ items : List LibItem, items.map (rcv ∘ Subtype.val) =
            ((Flagged.flaggedOps.runInput a true slices).run taken).2.map (rcv ∘ itemOf) ∧
          AdapterAt version items
            (Internal.handler ((Flagged.flaggedOps.runInput a true slices).run taken).1.2).version
                (Internal.handler p')
  | [], a, p, taken, hI, hfin, hv => by
    simp only [LexOps.runInput, ite_true, StateT.run_bind] at hfin hv ⊢
    generalize hr : (Flagged.flaggedOps.lexEofStep a).run taken = r at hfin hv ⊢
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq] at hfin hv ⊢
    dsimp only at hfin hv ⊢
    rcases res with e | flow
    · cases hfin
    · obtain ⟨p', r, hp, hrel, herr, hinv⟩ := eof_step hscript a p taken hI hr (by
        dsimp only at hv; split at hv <;> exact hv)
      dsimp only at hfin hv ⊢
      revert hfin hv hrel
      generalize Lexer.Adapters.eofResult (Flagged.flaggedOps.held a') flow = e
      intro hfin hv hrel
      rcases e with _ | result
      · cases hfin
      · dsimp only at hfin hv ⊢
        match r, hrel with
        | some r', _ =>
          simp only [paFeed, hp]
          obtain ⟨items, hst, hat⟩ := hinv herr hv
          exact ⟨r', _, rfl, items, hst, hat⟩
  | slice :: slices, a, p, taken, hI, hfin, hv => by
    simp only [LexOps.runInput, StateT.run_bind] at hfin hv ⊢
    generalize hr : (Flagged.flaggedOps.lexSliceStep a slice.toByteArray.toByteSlice).run taken = r
      at hfin hv ⊢
    obtain ⟨⟨res, a'⟩, taken'⟩ := r
    rw [id_bind_eq] at hfin hv ⊢
    dsimp only at hfin hv ⊢
    rcases res with e | held₁
    · cases hfin
    · obtain ⟨more, hmore⟩ := runInput_extends hscript slices
        (Flagged.flaggedOps.withHeld a' (held₁.or (Flagged.flaggedOps.held a'))) taken'
      have hv' : Link.Viable commands taken' := by rw [hmore] at hv; exact hv.of_append
      obtain ⟨p', held₂, hp, hI'⟩ := slice_step hscript _ a p taken hI hr hv'
      simp only [paFeed, hp]
      exact feed_agree hscript slices _ _ taken' hI' hfin hv

end

end BSmtLib.Facts.Proofs.Reader.Param.Run
