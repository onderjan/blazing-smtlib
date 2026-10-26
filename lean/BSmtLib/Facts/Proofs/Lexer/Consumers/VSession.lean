module

public import BSmtLib.Facts.Proofs.Lexer.Consumers.VEnd
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Recovery
import all BSmtLib.Span
import all BSmtLib.Lexer.Error

@[expose] public section

/-!
# What the adapter makes of the naive lexer with a consumer of the formalism

The adapter's feeding of the naive lexer with the consumer `Answering consumer`
(`Adapters.lexing VNaive.lexOps`) is the loop over the bytes of the slices, whatever they are cut
into, and then, if the input has ended, the end of the input (`vSession`, `lexing_vNaive`). The
lexer stays lexing or discarding (`Core.Plain`), so its call on a slice is the loop over the
slice's bytes (`lexSliceStep_vBytes`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.VSession

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.Consumers.VEnd
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Lexer.Internal.VNaive

/-- The activity of a lexer that stops at its first error: lexing, or discarding. -/
def Core.Plain (core : Core) : Prop :=
  match core.activity with
  | .idle | .token _ | .discarding _ => True
  | _ => False

/-- An activity of a lexer that stops at its first error, idle or discarding. -/
def Core.IdleOrDiscarding (core : Core) : Prop :=
  core.activity = .idle ∨ ∃ s, core.activity = .discarding s

theorem Core.IdleOrDiscarding.plain {core : Core} (h : (IdleOrDiscarding core)) : (Plain core) := by
  rcases h with h | ⟨s, h⟩ <;> simp [Core.Plain, h]

section
variable (consumer : BSmtLibSpec.Lexer.Consumer)

/-- The hand-over of a lexeme leaves the lexer in its activity, or discarding. -/
theorem handOverAt_activity (core : Core) (l : Lexeme) (hl : l.Valid) (taken : List Handed) :
    (vRun consumer (handOverAt (H := Answering consumer) core l hl) taken).1.2.activity =
        core.activity ∨
      ∃ s, (vRun consumer (handOverAt (H := Answering consumer) core l hl) taken).1.2.activity =
        .discarding s := by
  cases hh : core.holding with
  | true => rw [handOverAt_holding consumer core l hl hh]; exact .inl rfl
  | false =>
    rw [handOverAt_reply consumer core l hl hh]
    generalize reply consumer core.version taken l = r
    obtain ⟨answer, version, discards, taken'⟩ := r
    unfold coreAfter
    cases answer with
    | error e =>
      dsimp only
      unfold coreAfterError
      cases discards
      · exact .inl rfl
      · exact .inr ⟨_, rfl⟩
    | ok flow =>
      cases flow <;> cases discards
      all_goals first | exact .inl rfl | exact .inr ⟨_, rfl⟩

theorem lexStart_idleOrDiscarding_or_token (core : Core) (c : UInt8) (taken : List Handed)
    (hp : (Core.Plain core)) :
    (Core.Plain (vRun consumer (lexStart (H := Answering consumer) core c) taken).1.2) := by
  cases hs : start core.version consumer.concrete core.location c with
  | idle =>
    obtain ⟨core', h, -, ha, -⟩ := lexStart_none consumer core c taken (st := .idle)
      (by simp [startStepW, hs])
    rw [h]; simp [Core.Plain, ha, St.activity]
  | pending p =>
    obtain ⟨core', h, -, ha, -⟩ := lexStart_none consumer core c taken (st := .token p)
      (by simp [startStepW, hs])
    rw [h]; simp [Core.Plain, ha, St.activity]
  | token l =>
    obtain ⟨hl, h⟩ := lexStart_token consumer core c taken hs
    rw [h]
    rcases handOverAt_activity consumer (idleAfter core c) l hl taken with h' | ⟨s, h'⟩ <;>
      (unfold Core.Plain; rw [h']) <;> simp [idleAfter]
  | error f =>
    obtain ⟨f', h⟩ := lexStart_error consumer core c taken (by simp [startStepW, hs])
    rw [h]; exact hp


theorem vByte_plain (core : Core) (c : UInt8) (taken : List Handed) (hp : (Core.Plain core)) :
    (Core.Plain (vByte consumer core c taken).1.2) := by
  unfold Core.Plain at hp
  split at hp
  · rename_i ha
    rw [lexByte_idle consumer core c taken ha]
    exact lexStart_idleOrDiscarding_or_token consumer core c taken (by simp [Core.Plain, ha])
  · rename_i p ha
    cases hadv : advance consumer.concrete p core.location c with
    | pending p' =>
      obtain ⟨core', h, -, ha', -⟩ := lexByte_pending consumer core c taken ha hadv
      rw [h]; simp [Core.Plain, ha']
    | idle =>
      obtain ⟨core', h, -, ha', -⟩ := lexByte_advance_idle consumer core c taken ha hadv
      rw [h]; simp [Core.Plain, ha']
    | tokenWith l =>
      obtain ⟨hl, h⟩ := lexByte_tokenWith consumer core c taken ha hadv
      rw [h]
      rcases handOverAt_activity consumer (idleAfter core c) l hl taken with h' | ⟨s, h'⟩ <;>
        (unfold Core.Plain; rw [h']) <;> simp [idleAfter]
    | tokenBefore l =>
      obtain ⟨hl, h⟩ := lexByte_tokenBefore consumer core c taken ha hadv
      have hact := handOverAt_activity consumer (idleAt core) l hl taken
      generalize hr : vRun consumer (handOverAt (H := Answering consumer) (idleAt core) l hl)
        taken = r at hact
      obtain ⟨⟨res, core2⟩, taken2⟩ := r
      rw [h hr]
      have hp2 : (Core.Plain core2) := by
        rcases hact with h' | ⟨s, h'⟩ <;> simp only at h' <;> simp [Core.Plain, h', idleAt]
      cases res with
      | error f => exact hp2
      | ok held =>
        cases held with
        | none =>
          dsimp only
          split
          · simp [Core.Plain, discardingAfter]
          · exact lexStart_idleOrDiscarding_or_token consumer core2 c taken2 hp2
        | some located =>
          dsimp only
          split
          · simp [Core.Plain, discardingAfter]
          · have := lexStart_idleOrDiscarding_or_token consumer core2 c taken2 hp2
            generalize vRun consumer (lexStart (H := Answering consumer) core2 c) taken2 = r3
              at this
            obtain ⟨⟨r3, core3⟩, taken3⟩ := r3
            exact this
    | error f =>
      rw [lexByte_advance_error consumer core c taken ha hadv]
      simp [Core.Plain, ha]
  · rename_i s ha
    obtain ⟨core', h, -, ha', -⟩ := lexByte_discarding consumer core c taken ha
    rw [h]; simp [Core.Plain, ha']
  · exact hp.elim

theorem vBytes_plain (bytes : List UInt8) :
    ∀ (core : Core) (held : Option (Span.Located consumer.Result)) (taken : List Handed),
      (Core.Plain core) → (Core.Plain (vBytes consumer core held bytes taken).1.2) := by
  induction bytes with
  | nil => intro core held taken hp; exact hp
  | cons c bytes ih =>
    intro core held taken hp
    have h := vByte_plain consumer core c taken hp
    simp only [vBytes]
    generalize vByte consumer core c taken = r at h
    obtain ⟨⟨res, core'⟩, taken'⟩ := r
    cases res with
    | error f => exact h
    | ok held' => cases held' <;> exact ih _ _ _ h


/-- The step of a call on a slice, from a lexer that lexes or discards, is the loop over its
bytes, with the error given the location to continue from of a lexer that stops at its first
error. -/
theorem lexSliceStep_vBytes (core : Core) (hp : (Core.Plain core)) (bytes : List UInt8)
    (taken : List Handed) :
    vRun consumer (lexSliceStep (H := Answering consumer) false (fun _ => pure ())
      (fun _ => pure ()) bytes.toByteArray.toByteSlice core) taken =
      match vBytes consumer core none bytes taken with
      | ((.ok held, core'), taken') => ((.ok held, core'), taken')
      | ((.error f, core'), taken') =>
        ((.error (Lexer.Error.LexerError.Internal.new f.cause f.span none), core'), taken') := by
  have hf := lexFrom_vBytes consumer bytes _ 0 rfl core none taken
  simp only [List.drop_zero] at hf
  unfold Core.Plain at hp
  split at hp <;> try exact hp.elim
  all_goals
    rename_i ha
    simp only [lexSliceStep, ha, pure_bind]
    rw [vRun_bind, show ((lexFrom (H := Answering consumer) (fun _ => pure ())
      bytes.toByteArray.toByteSlice 0 core none).run {}).run taken =
      (((vBytes consumer core none bytes taken).1, {}), (vBytes consumer core none bytes taken).2)
      from run_of_vRun consumer (by rw [hf])]
    generalize vBytes consumer core none bytes taken = r
    obtain ⟨⟨res, core'⟩, taken'⟩ := r
    cases res <;> rfl


theorem vBytes_append (core : Core) (held : Option (Span.Located consumer.Result))
    (a b : List UInt8) (taken : List Handed) :
    vBytes consumer core held (a ++ b) taken =
      match vBytes consumer core held a taken with
      | ((.ok held', core'), taken') => vBytes consumer core' held' b taken'
      | ((.error f, core'), taken') => ((.error f, core'), taken') := by
  induction a generalizing core held taken with
  | nil => rfl
  | cons c a ih =>
    simp only [List.cons_append, vBytes]
    generalize vByte consumer core c taken = r
    obtain ⟨⟨res, core'⟩, taken'⟩ := r
    cases res with
    | error f => rfl
    | ok held' => cases held' <;> exact ih _ _ _

theorem vBytes_held (core : Core) (held : Option (Span.Located consumer.Result))
    (bytes : List UInt8)
    (taken : List Handed) :
    vBytes consumer core held bytes taken =
      match vBytes consumer core none bytes taken with
      | ((.ok held', core'), taken') => ((.ok (held'.or held), core'), taken')
      | ((.error f, core'), taken') => ((.error f, core'), taken') := by
  induction bytes generalizing core held taken with
  | nil => cases held <;> rfl
  | cons c bytes ih =>
    simp only [vBytes]
    generalize vByte consumer core c taken = r
    obtain ⟨⟨res, core'⟩, taken'⟩ := r
    cases res with
    | error f => rfl
    | ok held' =>
      cases held' with
      | none => exact ih _ _ _
      | some located =>
        dsimp only
        rw [ih core' (some located) taken']
        generalize vBytes consumer core' none bytes taken' = r
        obtain ⟨⟨res, core⟩, taken⟩ := r
        cases res with
        | error f => rfl
        | ok h => cases h <;> rfl

/-- Where the lexer began to discard, if it discards. -/
def discardedOf (core : Core) : Option Span.Location :=
  match core.activity with
  | .discarding start => some start
  | _ => none

/-- The session of the naive lexer, in the formalism's form: the tokens taken, where it stands, and
its version and discarding. -/
def sessionOf (taken : List Handed) (outcome : BSmtLibSpec.Lexer.Outcome consumer.Result
    consumer.Error)
    (core : Core) : BSmtLibSpec.Lexer.Session consumer.Result consumer.Error :=
  { taken, outcome, version := fromVersion core.version
    discardedFrom := (discardedOf core).map toLocation }

/-- What the adapter makes of the naive lexer with the consumer, from the lexer state and the
held result, fed the bytes and then, if the input has ended, the end of the input, after the
tokens taken. -/
def vSession (core : Core) (held : Option (Span.Located consumer.Result)) (bytes : List UInt8)
    (ended : Bool) (taken : List Handed) : BSmtLibSpec.Lexer.Session consumer.Result consumer.Error
    :=
  match vBytes consumer core held bytes taken with
  | ((.error f, core'), taken') =>
    sessionOf consumer taken'
      (.failed (failureOf (Lexer.Error.LexerError.Internal.new f.cause f.span none))) core'
  | ((.ok held', core'), taken') =>
    if ended then
      match vEnd consumer core' taken' with
      | ((.ok flow, core''), taken'') =>
        sessionOf consumer taken''
          (match eofResult held' flow with
            | some result => .finished result.value (toLocation result.location)
            | none => .running) core''
      | ((.error e, core''), taken'') => sessionOf consumer taken'' (.failed (failureOf e)) core''
    else
      sessionOf consumer taken'
        (match held' with
          | some result => .holding result.value (toLocation result.location)
          | none => .running) core'


theorem recovers_failFast :
    Lexer.Recovery.Recovers.recovers Lexer.Recovery.FailFast = false := (rfl)

theorem abandon_failFast :
    (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast : Span.Location → StateT
    (Answering consumer) AnswerM Unit) =
      fun _ => pure () := rfl

theorem recover_failFast :
    (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast : Span.Location → StateT
    (Answering consumer) AnswerM Unit) =
      fun _ => pure () := rfl

theorem lexOps_lexSliceStep (core : Core) (held : Option (Span.Located consumer.Result))
    (slice : ByteSlice) (taken : List Handed) :
    (VNaive.lexOps.lexSliceStep (consumer := consumer) ⟨{}, core, held⟩ slice).run taken =
      match vRun consumer (lexSliceStep (H := Answering consumer) false (fun _ => pure ())
          (fun _ => pure ()) slice core) taken with
      | ((r, core'), taken') => ((r, ⟨{}, core', held⟩), taken') := by
  simp only [VNaive.lexOps, Lexer.Internal.VNaive.Lexer.run, vRun, StateT.run_bind,
      recovers_failFast,
    abandon_failFast, recover_failFast]
  generalize ((lexSliceStep (H := Answering consumer) false (fun _ => pure ()) (fun _ => pure ())
    slice core).run {}).run taken = r
  obtain ⟨⟨⟨res, core'⟩, h⟩, taken'⟩ := r
  rw [answering_eq h {}]
  rfl

theorem lexOps_lexEofStep (core : Core) (held : Option (Span.Located consumer.Result))
    (taken : List Handed) :
    (VNaive.lexOps.lexEofStep (consumer := consumer) ⟨{}, core, held⟩).run taken =
      match vEnd consumer core taken with
      | ((r, core'), taken') => ((r, ⟨{}, core', held⟩), taken') := by
  simp only [VNaive.lexOps, Lexer.Internal.VNaive.Lexer.run, vEnd, vRun, StateT.run_bind,
      recovers_failFast,
    abandon_failFast, recover_failFast]
  generalize ((lexEofStep (H := Answering consumer) false (fun _ => pure ()) (fun _ => pure ())
    core).run {}).run taken = r
  obtain ⟨⟨⟨res, core'⟩, h⟩, taken'⟩ := r
  rw [answering_eq h {}]
  rfl


/-- The adapter's feeding of the naive lexer is the loop over the bytes of the slices, and then,
if the input has ended, the end of the input. -/
theorem runInput_vSession (ended : Bool) (slices : List BSmtLibSpec.Regex.Chars) :
    ∀ (core : Core) (held : Option (Span.Located consumer.Result)) (taken : List Handed),
        (Core.Plain core) →
      let r := (VNaive.lexOps.runInput (consumer := consumer) ⟨{}, core, held⟩ ended slices).run
        taken
      sessionOf consumer r.2 r.1.1 r.1.2.core =
        vSession consumer core held slices.flatten ended taken := by
  induction slices with
  | nil =>
    intro core held taken hp
    cases ended with
    | false => rfl
    | true =>
      simp only [LexOps.runInput, ite_true, StateT.run_bind, lexOps_lexEofStep, vSession,
        List.flatten_nil, vBytes]
      generalize vEnd consumer core taken = r
      obtain ⟨⟨res, core'⟩, taken'⟩ := r
      cases res with
      | error e => rfl
      | ok flow =>
        dsimp only
        simp only [id_bind]
        show sessionOf consumer _ _ _ = _
        cases h : eofResult held flow with
        | none => simp [VNaive.lexOps, h, StateT.run_pure]; rfl
        | some r => simp [VNaive.lexOps, h, StateT.run_pure]; rfl
  | cons slice slices ih =>
    intro core held taken hp
    simp only [LexOps.runInput, StateT.run_bind, lexOps_lexSliceStep, List.flatten_cons]
    rw [lexSliceStep_vBytes consumer core hp slice taken]
    have hpl := vBytes_plain consumer slice core none taken hp
    unfold vSession
    rw [vBytes_append, vBytes_held consumer core held slice taken]
    generalize vBytes consumer core none slice taken = r at hpl
    obtain ⟨⟨res, core'⟩, taken'⟩ := r
    cases res with
    | error f => rfl
    | ok held' =>
      simp only [id_bind]
      have := ih core' (held'.or held) taken' hpl
      exact this


theorem initial_plain (version : Version) : (Core.Plain (Core.initial version)) := trivial

/-- What the adapter makes of the naive lexer with the consumer, on its first input. -/
theorem lexing_vNaive (version : BSmtLibSpec.Lexicon.Version)
    (slices : List BSmtLibSpec.Regex.Chars)
    (ended : Bool) :
    lexing VNaive.lexOps consumer version [] slices ended =
      vSession consumer (Core.initial (toVersion version)) none slices.flatten ended [] := by
  have h := runInput_vSession consumer ended slices (Core.initial (toVersion version)) none []
    (initial_plain _)
  simp only at h
  rw [← h]
  rfl

end

end BSmtLib.Facts.Proofs.Lexer.Consumers.VSession
