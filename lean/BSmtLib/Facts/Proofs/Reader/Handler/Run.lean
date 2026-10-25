module

public import BSmtLib.Facts.Proofs.Reader.Handler.Relate
public import BSmtLib.Facts.Proofs.Reader.Param.Run
import all BSmtLib.Lexer

@[expose] public section

/-!
# The library's lexer with the parse adapter over any handler that never fails, call by call

As `Param.Run` for the recording handler: the library's lexer fed with
`Flagged (scriptConsumer version)` and fed with the parse adapter over a handler whose calls
never fail are related call by call (`Relate.link_consumers`, and the unary walk where nothing went
wrong); where the first finishes and the tokens taken stand for a start of the script, the second
returns a result at the end of the input, and the adapter stands where the driver over items
standing for the tokens leaves it (`feed_agree`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Handler.Run

open BSmtLib.Lexer
open BSmtLibSpec BSmtLibSpec.Grammar
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Handler
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM LexOps)
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Facts.Proofs.Reader.Param.Adapter BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Facts.Proofs.Reader.Param.Calls BSmtLib.Facts.Proofs.Reader.Param.UnaryCalls
open BSmtLib.Facts.Proofs.Reader.Param (Flagged)
open BSmtLib.Facts.Proofs.Reader.Param.Run (FLexer HeldRel' heldRel_or isError_ok_of_eRel run_id
  runInput_extends)
open BSmtLib.Facts.Proofs.Reader.Handler.Relate BSmtLib.Facts.Proofs.Reader.Handler.Loop
open BSmtLib.Facts.Proofs.Parser.Blank.Basic
open BSmtLib.Facts.Reader.Adapters

variable {H : Type} [CommandHandler H Id]

/-- The library's lexer with the parse adapter over the handler. -/
abbrev HLexer (H : Type) [CommandHandler H Id] := BSmtLib.Lexer (ParseAdapter H (ScriptParser H))

/-- The library's lexer with the parse adapter, fed the slices and then the end of the input by
its public calls: the result at the end of the input and the lexer, or the first error. -/
def hFeed (lexer : HLexer H) :
    List Regex.Chars →
      Except (Lexer.Error.LexerError (Parser.ParseError (Handler.Error H)))
        (Option (Span.Located Unit) × HLexer H)
  | [] =>
    match (Lexer.lexEof lexer : Id _) with
    | .ok result => .ok result
    | .error (error, _) => .error error
  | slice :: slices =>
    match (Lexer.lexSlice lexer slice.toByteArray.toByteSlice : Id _) with
    | .ok next => hFeed next slices
    | .error (error, _) => .error error

section

variable (version : Lexicon.Version) (commands : List Tree.Command) (init : H)

/-- What holds between the two lexers between the calls. -/
def Inv (a : FLexer version) (p : HLexer H) (taken : List Handed) : Prop :=
  Internal.core a = Internal.core p ∧ HeldRel' (Internal.held a) (Internal.held p) ∧
      (Internal.handler a).errored = false ∧
    (Internal.core a).version = (Internal.handler a).version ∧
    InvB version commands init (Internal.handler a) taken (Internal.handler p)

end

/-! ## The calls -/

section

variable {version : Lexicon.Version} {commands : List Tree.Command} {init : H} [NoFails H]

omit [NoFails H] in
theorem link_abandon (l : Span.Location) :
    (linkLink version commands init).rc.rel (· = ·)
      (Recovery.LexerRecovery.abandon (H := Flagged (scriptConsumer version)) (m := AnswerM)
        Recovery.FailFast l)
      (Recovery.LexerRecovery.abandon (H := (ParseAdapter H (ScriptParser H))) (m := Id)
        Recovery.FailFast l) :=
  (linkLink version commands init).rc.pure rfl

omit [NoFails H] in
theorem link_recover (l : Span.Location) :
    (linkLink version commands init).rc.rel (· = ·)
      (Recovery.LexerRecovery.recover (H := Flagged (scriptConsumer version)) (m := AnswerM)
        Recovery.FailFast l)
      (Recovery.LexerRecovery.recover (H := (ParseAdapter H (ScriptParser H))) (m := Id)
        Recovery.FailFast l) :=
  (linkLink version commands init).rc.pure rfl

end

section

variable {version : Lexicon.Version} {commands : List Tree.Command} {init : H} [NoFails H]

theorem sliceStep_sim (hscript : Script version commands) (slice : ByteSlice) :
    SSim (linkLink version commands init) (SliceRel (linkLink version commands init))
      (Internal.lexSliceStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
            (Recovery.LexerRecovery.recover Recovery.FailFast) slice)
      (Internal.lexSliceStep (H := (ParseAdapter H (ScriptParser H))) (m := Id)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
            (Recovery.LexerRecovery.recover Recovery.FailFast) slice) :=
  lexSliceStep_sim (link_consumers hscript init) _ _ _ _ link_abandon link_recover slice

theorem slice_step (hscript : Script version commands) (slice : ByteSlice) (a : FLexer version)
    (p : HLexer H) (taken : List Handed) (hI : Inv version commands init a p taken)
    {held₁ : Option (Span.Located (scriptConsumer version).Result)} {a' : FLexer version}
    {taken' : List Handed}
    (hr : (Flagged.flaggedOps.lexSliceStep a slice).run taken = ((.ok held₁, a'), taken'))
    (hv : Param.Link.Viable commands taken') :
    ∃ (p' : HLexer H) (held₂ : Option (Span.Located Unit)),
      (Lexer.lexSlice p slice : Id _) = .ok (Internal.withHeld p' (held₂.or (Internal.held p'))) ∧
      Inv version commands init (Internal.withHeld a' (held₁.or (Internal.held a')))
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
  generalize (StateT.run (Internal.lexSliceStep (H := (ParseAdapter H (ScriptParser H))) (m := Id)
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
    SSim (linkLink version commands init) (EofRel (linkLink version commands init))
      (Internal.lexEofStep (H := Flagged (scriptConsumer version)) (m := AnswerM)
        (R := (scriptConsumer version).Result) (E := Option (scriptConsumer version).Error)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
            (Recovery.LexerRecovery.recover Recovery.FailFast))
      (Internal.lexEofStep (H := (ParseAdapter H (ScriptParser H))) (m := Id) (R := Unit)
          (E := Parser.ParseError (Handler.Error H))
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
            (Recovery.LexerRecovery.recover Recovery.FailFast)) :=
  lexEofStep_sim (link_consumers hscript init) _ _ _ _ link_abandon link_recover

theorem eof_step (hscript : Script version commands) (a : FLexer version) (p : HLexer H)
    (taken : List Handed) (hI : Inv version commands init a p taken)
    {flow : ControlFlow (Span.Located (scriptConsumer version).Result)} {a' : FLexer version}
    {taken' : List Handed}
    (hr : (Flagged.flaggedOps.lexEofStep a).run taken = ((.ok flow, a'), taken'))
    (hv : Param.Link.Viable commands taken') :
    ∃ (p' : HLexer H) (result : Option (Span.Located Unit)),
      (Lexer.lexEof p : Id _) = .ok (result, Internal.withHeld p' none) ∧
      HeldRel' (Lexer.Adapters.eofResult (Flagged.flaggedOps.held a') flow) result ∧
      (Internal.handler a').errored = false ∧
        InvB version commands init (Internal.handler a') taken'
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
  generalize (StateT.run (Internal.lexEofStep (H := (ParseAdapter H (ScriptParser H))) (m := Id)
    (R := Unit)
    (E := Parser.ParseError (Handler.Error H))
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

end

section

variable {version : Lexicon.Version} {commands : List Tree.Command} {init : H} [NoFails H]

/-- Where the run with the first consumer finishes and the tokens taken stand for a start of the
script, the run with the parse adapter finishes with a result, and the adapter stands where the
recording run over items standing for the tokens leaves the parser. -/
theorem feed_agree (hscript : Script version commands) :
    ∀ (slices : List Regex.Chars) (a : FLexer version) (p : HLexer H) (taken : List Handed),
      Inv version commands init a p taken →
      ((Flagged.flaggedOps.runInput a true slices).run taken).1.1.isFinished = true →
      Param.Link.Viable commands ((Flagged.flaggedOps.runInput a true slices).run taken).2 →
      ∃ result p', hFeed p slices = .ok (some result, p') ∧
        ∃ items : List LibItem, items.map (rcv ∘ Subtype.val) =
            ((Flagged.flaggedOps.runInput a true slices).run taken).2.map (rcv ∘ itemOf) ∧
          At version init items
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
          simp only [hFeed, hp]
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
      have hv' : Param.Link.Viable commands taken' := by rw [hmore] at hv; exact hv.of_append
      obtain ⟨p', held₂, hp, hI'⟩ := slice_step hscript _ a p taken hI hr hv'
      simp only [hFeed, hp]
      exact feed_agree hscript slices _ _ taken' hI' hfin hv

end

end BSmtLib.Facts.Proofs.Reader.Handler.Run
