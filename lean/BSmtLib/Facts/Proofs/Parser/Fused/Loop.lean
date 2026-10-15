module

public import BSmtLib.Parser.Internal.Fused
import all BSmtLib.Parser
import all BSmtLib.Parser.Adapter
import all BSmtLib.Parser.Internal.Fused
import all BSmtLib.Parser.Script
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
over the tokens left in the cursor, as the loop and `Parser.Internal.rest` go on alike after a
token.
-/

namespace BSmtLib.Facts.Proofs.Parser.Fused.Loop

open BSmtLib.Traits
open BSmtLib.Token.BatchCursor.Internal (remaining)
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Category.Term.Internal (TermLevelOf)
open BSmtLib.Parser.Command.Internal (CommandStateOf)
open BSmtLib.Parser.Internal.Fused
open BSmtLib.Parser.Internal.Fused.Basic (Cause LoopResult OutcomeOf TermContext TermModeOf)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Token (BatchTag BatchCursor Produce VersionPosture)
open BSmtLib.Token.Produce (HasNext)

/-! ## The adapter's token, taken from further back -/

section

variable {H P R E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  [Parser.Internal.ParseByToken P H m E R]
variable {Z : Type} [Produce Z]

/-- The adapter's token, with its cursors' consumption counted from a cursor further back. -/
theorem takeOne_trans (parser : P) {origin cursor next : Z} (token : Produce.Token Z)
    (step : Produce.Consumed next cursor) (consumed : Produce.Consumed cursor origin) :
    Parser.Internal.takeOne parser origin token next (Produce.consumed_trans step consumed) =
      (fun (after, (z : { z : Z // Produce.Consumed z cursor })) =>
        (after,
          (⟨z.1, Produce.consumed_trans z.2 consumed⟩ : { z : Z // Produce.Consumed z origin })))
        <$> Parser.Internal.takeOne parser cursor token next step := by
  unfold Parser.Internal.takeOne
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
      cases st <;> simp [Parser.Internal.resumed]

end

/-! ## The loop -/

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/-- The adapter's result of a token, taken from `origin` on, with the handler after it. -/
abbrev PortOut (H : Type) {m : Type → Type} [CommandHandler H m] {batch : BatchTag}
    (origin : BatchCursor batch) :=
  (Parser.Internal.After (ScriptParser H) Unit (Handler.Error H) ×
    { z : BatchCursor batch // z.Consumed origin }) × H

/-- The fused step's outcome, read as the adapter's result of the token: going on in the parser
that the outcome stands for, or stopping. -/
def toPort (posture : VersionPosture) {batch : BatchTag} {origin next : BatchCursor batch}
    (consumed : next.Consumed origin) : OutcomeOf H next → PortOut H origin
  | .command h decl cmd =>
    ((.goOn (ScriptParser.Internal.mk posture cmd decl), ⟨next, consumed⟩), h)
  | .term h decl ctx mode levels =>
    ((.goOn (assemble posture decl .awaiting true ctx mode levels), ⟨next, consumed⟩), h)
  | .resume h parser cursor follows =>
    ((.goOn parser, ⟨cursor, follows.trans_consumed consumed⟩), h)
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
      ((Parser.Internal.takeOne (assemble posture decl cmd inTerm ctx mode levels) origin token next
        consumed).run h >>= k)

/-- The port's run from a token taken from a cursor that leaves `next`: the adapter's `takeOne`,
then, if it goes on, the rest of the cursor. -/
def portGo {batch : BatchTag} (origin : BatchCursor batch) (parser : ScriptParser H) (h : H)
    (token : Token batch) (next : BatchCursor batch) (consumed : next.Consumed origin) :
    m (LoopResult H origin) :=
  (Parser.Internal.takeOne parser origin token next consumed).run h >>= portRest origin
where
  /-- After a token: the rest of the cursor, or the stop. -/
  portRest (origin : BatchCursor batch) : PortOut H origin → m (LoopResult H origin)
    | ((.goOn parser, ⟨later, taken⟩), h) => do
      let ((answer, parser, done), h) ← (Parser.Internal.rest origin parser later taken).run h
      return (answer, parser, done, h)
    | ((.stop answer parser, done), h) => return (answer, parser, done, h)

variable [LawfulMonad m]

/-- The adapter's token, its consumption counted from the cursor before it. -/
theorem takeOne_from {batch : BatchTag} (parser : ScriptParser H)
    {origin cursor next : BatchCursor batch} (token : Token batch) (step : next.Consumed cursor)
    (consumed : cursor.Consumed origin) :
    Parser.Internal.takeOne (m := m) parser origin token next (step.trans consumed) =
      (fun (after, (z : { z : BatchCursor batch // z.Consumed cursor })) =>
        (after, (⟨z.1, z.2.trans consumed⟩ : { z : BatchCursor batch // z.Consumed origin })))
        <$> Parser.Internal.takeOne parser cursor token next step :=
  takeOne_trans (Z := BatchCursor batch) parser token step consumed

/-- The rest of a cursor that has a token: its token, then the rest. -/
theorem rest_next {batch : BatchTag} (origin : BatchCursor batch) (parser : ScriptParser H) (h : H)
    (next : BatchCursor batch) (consumed : next.Consumed origin) (hn : next.HasNext) :
    (do
        let ((answer, parser, done), h) ←
          (Parser.Internal.rest (m := m) origin parser next consumed).run h
        return (answer, parser, done, h)) =
      portGo origin parser h (next.next hn).1 (next.next hn).2.1
        ((next.next hn).2.2.trans consumed) := by
  rw [Parser.Internal.rest]
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
          (Parser.Internal.rest (m := m) origin parser next consumed).run h
        return (answer, parser, done, h)) =
      (pure (.ok .continue, parser, ⟨next, consumed⟩, h) : m (LoopResult H origin)) := by
  rw [Parser.Internal.rest]
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
      have : remaining after < remaining next := taken.remaining_lt
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
      have : remaining after < remaining next := taken.remaining_lt
      dsimp only
      rw [loop_eq hstep]
    · simp only [hn, ↓reduceDIte]
      rw [rest_none origin _ h' next consumed hn]
  | resume h' parser cursor follows =>
    simp only [toPort, portGo.portRest]
    by_cases hn : cursor.HasNext
    · simp only [hn, ↓reduceDIte]
      rw [rest_next origin _ h' cursor (follows.trans_consumed consumed) hn]
      obtain ⟨token', ⟨after, taken⟩⟩ := cursor.next hn
      have : remaining after < remaining next := (taken.trans_follows follows).remaining_lt
      dsimp only
      obtain ⟨posture', command', declarations'⟩ := parser
      dsimp only [ScriptParser.Internal.posture, ScriptParser.Internal.command,
        ScriptParser.Internal.declarations]
      split <;> rw [loop_eq hstep] <;> congr 1 <;>
        simp_all [assemble, withTerm, ScriptParser.Internal.mk]
    · simp only [hn, ↓reduceDIte]
      rw [rest_none origin _ h' cursor (follows.trans_consumed consumed) hn]
  | stop answer parser cursor follows h' =>
    simp only [toPort, portGo.portRest]
termination_by remaining next

/-- The loop from the first token of a hand-over is the port's run from it, on the parser. -/
theorem start_eq (hstep : StepSimulates H m) {batch : BatchTag} (parser : ScriptParser H) (h : H)
    (token : Token batch) (producer next : BatchCursor batch) (consumed : next.Consumed producer) :
    start parser h token producer next consumed = portGo producer parser h token next consumed := by
  unfold start
  split <;> rw [loop_eq hstep] <;> congr 1 <;> cases parser <;>
    simp_all [assemble, withTerm, ScriptParser.Internal.mk, ScriptParser.Internal.posture,
      ScriptParser.Internal.command, ScriptParser.Internal.declarations]

/-- The fused reader parses a batch cursor as the script parser's loop over single tokens does:
the same answer, parser, parse state, cursor and handler. -/
theorem parse_eq (hstep : StepSimulates H m) {batch : BatchTag} (parser : ScriptParser H)
    (state : Parser.ParseState H) (producer : BatchCursor batch) :
    BSmtLib.Parser.Internal.Fused.parse (m := m) parser state producer =
      Parser.Internal.parseByToken parser state producer := by
  unfold Parser.Internal.parseByToken
  split
  · rename_i heq
    have hp : ¬ producer.HasNext := fun hp => by
      have : Produce.next? producer = some (producer.next hp) := by
        show BatchCursor.next? producer = _
        simp [BatchCursor.next?, hp]
      rw [this] at heq; cases heq
    funext h
    simp only [BSmtLib.Parser.Internal.Fused.parse, Produce.asBatch?, hp, ↓reduceDIte]
    rfl
  · rename_i token next consumed heq
    have hp : producer.HasNext := by
      refine Decidable.byContradiction fun hn => ?_
      have h2 : Produce.next? producer = none := by
        show BatchCursor.next? producer = _
        simp [BatchCursor.next?, hn]
      rw [h2] at heq; cases heq
    have hnx : producer.next hp = (token, ⟨next, consumed⟩) := by
      have : Produce.next? producer = some (producer.next hp) := by
        show BatchCursor.next? producer = _
        simp [BatchCursor.next?, hp]
      rw [this] at heq
      exact Option.some.inj heq
    funext h
    simp only [BSmtLib.Parser.Internal.Fused.parse, Produce.asBatch?, hp, ↓reduceDIte, hnx]
    rw [start_eq hstep]
    simp only [portGo, bind_assoc]
    congr 1
    funext b
    obtain ⟨⟨after, ⟨later, taken⟩⟩, h'⟩ := b
    cases after with
    | goOn p =>
      simp only [portGo.portRest, bind_pure_comp]
      show _ = StateT.run _ h'
      rw [StateT.run_map, Functor.map_map]
      rfl
    | stop answer p =>
      simp only [portGo.portRest]
      show _ = StateT.run _ h'
      rw [StateT.run_pure, pure_bind]
      rfl

end

end BSmtLib.Facts.Proofs.Parser.Fused.Loop
