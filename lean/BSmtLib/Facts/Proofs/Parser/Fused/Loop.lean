module

public import BSmtLib.Parser.Internal.Fused
import all BSmtLib.Parser.Adapter
import all BSmtLib.Parser.Internal.Fused
import all BSmtLib.Token

@[expose] public section

/-!
# The fused reader against the parse adapter: the loop

The fused script reader (`Parser.Internal.Fused`) is the parse adapter of the script parser in
another runtime shape. Its consumer gives what the parse adapter's gives, in every lawful monad,
with every handler, on every cursor: the same answer, the same parser to go on from, the same
cursor and the same handler (`consume_eq`).

The proof here rests on the step of one token (`StepSimulates`, proved in
`Facts.Proofs.Parser.Fused.Step`): the fused step, run with a continuation that reads its outcome
as the adapter's result, is the adapter's `takeOne` on the parser that the loop's arguments stand
for (`assemble`), followed by the continuation. The loop then follows by well-founded induction
over the tokens left in the cursor, as the loop and `ParseAdapter.rest` go on alike after a
token.
-/

namespace BSmtLib.Facts.Proofs.Parser.Fused.Loop

open BSmtLib.Traits
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Parser.Category.Term (TermLevelOf)
open BSmtLib.Parser.Command (CommandStateOf)
open BSmtLib.Parser.Internal.Fused
open BSmtLib.Parser.Internal.Fused.Basic (Cause LoopResult OutcomeOf TermContext TermModeOf)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Token (BatchTag BatchCursor Produce VersionPosture)
open BSmtLib.Token.Produce (HasNext)

/-! ## The adapter's token, taken from further back -/

section

variable {H P R E : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Parse P H m E R]
variable {Z : Type} [Produce Z]

/-- The adapter's token, with its cursors' consumption counted from a cursor further back. -/
theorem takeOne_trans (parser : P) {origin cursor next : Z} (token : Produce.Token Z)
    (step : Produce.Consumed next cursor) (consumed : Produce.Consumed cursor origin) :
    ParseAdapter.takeOne parser origin token next (Produce.consumed_trans step consumed) =
      (fun (after, (z : { z : Z // Produce.Consumed z cursor })) =>
        (after,
          (⟨z.1, Produce.consumed_trans z.2 consumed⟩ : { z : Z // Produce.Consumed z origin })))
        <$> ParseAdapter.takeOne parser cursor token next step := by
  unfold ParseAdapter.takeOne
  simp only [map_bind]
  congr 1
  funext r
  split
  · simp
  · simp
  · simp
  · split
    · simp
    · simp only [map_bind]
      congr 1
      funext r'
      split <;> simp
  · simp only [map_bind]
    congr 1
    funext r'
    split
    · simp
    · rename_i st
      cases st <;> simp [ParseAdapter.resumed]

end

/-! ## The loop -/

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/-- The adapter's result of a token, taken from `origin` on, with the handler after it. -/
abbrev PortOut (H : Type) {m : Type → Type} [Handler H m] {batch : BatchTag}
    (origin : BatchCursor batch) :=
  (ParseAdapter.After (ScriptParser H) Unit (Handler.Error H) ×
    { z : BatchCursor batch // z.Consumed origin }) × H

/-- The fused step's outcome, read as the adapter's result of the token: going on in the parser
that the outcome stands for, or stopping. -/
def toPort (posture : VersionPosture) {batch : BatchTag} {origin next : BatchCursor batch}
    (consumed : next.Consumed origin) : OutcomeOf H next → PortOut H origin
  | .command h decl cmd =>
    ((.goOn { posture, command := cmd, declarations := decl }, ⟨next, consumed⟩), h)
  | .term h decl ctx mode levels =>
    ((.goOn (assemble posture decl .awaiting true ctx mode levels), ⟨next, consumed⟩), h)
  | .stop answer parser cursor follows h =>
    ((.stop answer parser, ⟨cursor, follows.trans_consumed consumed⟩), h)

/--
The step of one token simulates the adapter's: run with a continuation that reads its outcome
as the adapter's result, it is the adapter's `takeOne` of the token on the parser that the loop's
arguments stand for, followed by the continuation.
-/
def StepSimulates (H : Type) (m : Type → Type) [Monad m] [CommandHandler H m] : Prop :=
  ∀ (posture : VersionPosture) {batch : BatchTag} {origin next : BatchCursor batch} (h : H)
    (decl : Nat) (cmd : CommandStateOf H) (inTerm : Bool) (ctx : TermContext (Handler.«Sort» H))
    (mode : TermModeOf H) (levels : List (TermLevelOf H)) (token : Token batch)
    (consumed : next.Consumed origin) {β : Type} (k : PortOut H origin → m β),
    step posture h decl cmd inTerm ctx mode levels token next
        (fun out => k (toPort posture consumed out)) =
      ((ParseAdapter.takeOne (assemble posture decl cmd inTerm ctx mode levels) origin token next
        consumed).run h >>= k)

/-- The port's run from a token taken from a cursor that leaves `next`: the adapter's `takeOne`,
then, if it goes on, the rest of the cursor. -/
def portGo {batch : BatchTag} (origin : BatchCursor batch) (parser : ScriptParser H) (h : H)
    (token : Token batch) (next : BatchCursor batch) (consumed : next.Consumed origin) :
    m (LoopResult H origin) :=
  (ParseAdapter.takeOne parser origin token next consumed).run h >>= portRest origin
where
  /-- After a token: the rest of the cursor, or the stop. -/
  portRest (origin : BatchCursor batch) : PortOut H origin → m (LoopResult H origin)
    | ((.goOn parser, ⟨later, taken⟩), h) => do
      let ((answer, parser, done), h) ← (ParseAdapter.rest origin parser later taken).run h
      return (answer, parser, done, h)
    | ((.stop answer parser, done), h) => return (answer, parser, done, h)

variable [LawfulMonad m]

/-- The adapter's token, its consumption counted from the cursor before it. -/
theorem takeOne_from {batch : BatchTag} (parser : ScriptParser H)
    {origin cursor next : BatchCursor batch} (token : Token batch) (step : next.Consumed cursor)
    (consumed : cursor.Consumed origin) :
    ParseAdapter.takeOne (m := m) parser origin token next (step.trans consumed) =
      (fun (after, (z : { z : BatchCursor batch // z.Consumed cursor })) =>
        (after, (⟨z.1, z.2.trans consumed⟩ : { z : BatchCursor batch // z.Consumed origin })))
        <$> ParseAdapter.takeOne parser cursor token next step :=
  takeOne_trans (Z := BatchCursor batch) parser token step consumed

/-- The rest of a cursor that has a token: its token, then the rest. -/
theorem rest_next {batch : BatchTag} (origin : BatchCursor batch) (parser : ScriptParser H) (h : H)
    (next : BatchCursor batch) (consumed : next.Consumed origin) (hn : next.HasNext) :
    (do
        let ((answer, parser, done), h) ←
          (ParseAdapter.rest (m := m) origin parser next consumed).run h
        return (answer, parser, done, h)) =
      portGo origin parser h (next.next hn).1 (next.next hn).2.1
        ((next.next hn).2.2.trans consumed) := by
  rw [ParseAdapter.rest]
  have : Produce.next? next = some (next.next hn) := by
    show BatchCursor.next? next = _
    simp [BatchCursor.next?, hn]
  simp only [this]
  simp only [portGo, StateT.run_bind, bind_assoc]
  rw [takeOne_from parser (next.next hn).1 (next.next hn).2.2 consumed]
  simp only [map_eq_pure_bind, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  congr 1
  funext x
  obtain ⟨⟨after, ⟨later, taken⟩⟩, h'⟩ := x
  cases after <;> simp [portGo.portRest]

/-- The rest of a cursor that has no token: the parser goes on. -/
theorem rest_none {batch : BatchTag} (origin : BatchCursor batch) (parser : ScriptParser H) (h : H)
    (next : BatchCursor batch) (consumed : next.Consumed origin) (hn : ¬next.HasNext) :
    (do
        let ((answer, parser, done), h) ←
          (ParseAdapter.rest (m := m) origin parser next consumed).run h
        return (answer, parser, done, h)) =
      (pure (.ok .continue, parser, ⟨next, consumed⟩, h) : m (LoopResult H origin)) := by
  rw [ParseAdapter.rest]
  have : Produce.next? next = none := by
    show BatchCursor.next? next = _
    simp [BatchCursor.next?, hn]
  simp only [this, StateT.run_pure, pure_bind]

/-- The loop from a token is the port's run from it, on the parser its arguments stand for. -/
theorem loop_eq (hstep : StepSimulates H m) (posture : VersionPosture) {batch : BatchTag}
    (origin : BatchCursor batch) (next : BatchCursor batch) (h : H) (decl : Nat)
    (cmd : CommandStateOf H) (inTerm : Bool) (ctx : TermContext (Handler.«Sort» H))
    (mode : TermModeOf H) (levels : List (TermLevelOf H)) (token : Token batch)
    (consumed : next.Consumed origin) :
    loop posture origin h decl cmd inTerm ctx mode levels token next consumed =
      portGo origin (assemble posture decl cmd inTerm ctx mode levels) h token next consumed := by
  rw [loop, portGo, ← hstep]
  congr 1
  funext out
  cases out with
  | command h' d c =>
    simp only [toPort, portGo.portRest]
    by_cases hn : next.HasNext
    · simp only [hn, ↓reduceDIte]
      rw [rest_next origin _ h' next consumed hn]
      obtain ⟨token', ⟨after, taken⟩⟩ := next.next hn
      have : after.remaining < next.remaining := taken.remaining_lt
      dsimp only
      split
      · rw [loop_eq hstep]; rfl
      · rw [loop_eq hstep]; rfl
      · rw [loop_eq hstep]; rfl
    · simp only [hn, ↓reduceDIte]
      rw [rest_none origin _ h' next consumed hn]
  | term h' d c mo le =>
    simp only [toPort, portGo.portRest]
    by_cases hn : next.HasNext
    · simp only [hn, ↓reduceDIte]
      rw [rest_next origin _ h' next consumed hn]
      obtain ⟨token', ⟨after, taken⟩⟩ := next.next hn
      have : after.remaining < next.remaining := taken.remaining_lt
      dsimp only
      rw [loop_eq hstep]
    · simp only [hn, ↓reduceDIte]
      rw [rest_none origin _ h' next consumed hn]
  | stop answer parser cursor follows h' =>
    simp only [toPort, portGo.portRest]
termination_by next.remaining

/-- The loop from the first token of a hand-over is the port's run from it, on the parser. -/
theorem start_eq (hstep : StepSimulates H m) {batch : BatchTag} (parser : ScriptParser H) (h : H)
    (token : Token batch) (producer next : BatchCursor batch) (consumed : next.Consumed producer) :
    start parser h token producer next consumed = portGo producer parser h token next consumed := by
  unfold start
  split <;> rw [loop_eq hstep] <;> congr 1 <;> cases parser <;> simp_all [assemble, withTerm]

/-- The parse adapter's first token of a producer is the cursor's next. -/
theorem first_eq {batch : BatchTag} (producer : BatchCursor batch) (hp : Produce.HasNext producer) :
    ParseAdapter.first producer hp = producer.next hp := by
  have hnext : Produce.next? producer = some (producer.next hp) := by
    show BatchCursor.next? producer = _
    simp [BatchCursor.next?, show producer.HasNext from hp]
  unfold ParseAdapter.first
  split
  · rename_i heq
    rw [hnext] at heq
    exact (Option.some.inj heq).symm
  · rename_i heq
    rw [hnext] at heq
    cases heq

/-- The fused reader's consumer is the parse adapter's: the same answer, cursor, parser and
handler, and so the same state of the adapter. -/
theorem consume_eq (hstep : StepSimulates H m) {batch : BatchTag} (producer : BatchCursor batch)
    (hp : Produce.HasNext producer) (adapter : ParseAdapter H (ScriptParser H)) :
    (Token.ConsumeFrom.consume (H := ScriptAdapter H) (m := m) producer hp).run ⟨adapter⟩ =
      (fun (out, adapter) => (out, (⟨adapter⟩ : ScriptAdapter H))) <$>
        (Token.ConsumeFrom.consume (H := ParseAdapter H (ScriptParser H)) (m := m) producer hp).run
          adapter := by
  have hfirst := first_eq producer hp
  simp only [Token.ConsumeFrom.consume]
  generalize ParseAdapter.first producer hp = pr at hfirst ⊢
  subst hfirst
  simp only [start_eq hstep]
  simp only [portGo, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
    map_bind, liftM, monadLift, MonadLift.monadLift, StateT.run_lift, bind_assoc]
  congr 1
  funext a
  congr 1
  funext b
  obtain ⟨⟨after, ⟨later, taken⟩⟩, h⟩ := b
  cases after <;> simp [portGo.portRest, StateT.run_bind, StateT.run_set, StateT.run_lift,
    StateT.run_map]

end

end BSmtLib.Facts.Proofs.Parser.Fused.Loop
