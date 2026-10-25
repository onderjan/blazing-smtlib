module

public import BSmtLib.Parser.Internal.Fused
public import BSmtLib.Facts.Proofs.Parser.HandOver
import all BSmtLib.Parser
import all BSmtLib.Parser.Adapter
import all BSmtLib.Parser.Internal.Fused
import all BSmtLib.Parser.Script
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor

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

open BSmtLib.Handler
open BSmtLib.Lexer.Cursor.LexerCursor.Internal (remaining)
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Category.Term.Internal (TermLevelOf)
open BSmtLib.Parser.Command.Internal (CommandStateOf)
open BSmtLib.Parser.Internal.Fused
open BSmtLib.Parser.Internal.Fused.Basic (Cause LoopResult OutcomeOf TermContext TermModeOf)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Token (BatchTag Cursor)
open BSmtLib.Lexer.Cursor (LexerCursor LexerToken)
open BSmtLib.Version (VersionPosture)
open BSmtLib.Token.Cursor (HasNext)

/-! ## The adapter's token, taken from further back -/

section

variable {H P R E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  [Parser.Internal.ParseByToken P H m E R]
variable {Z : Type} [Cursor Z]

/-- The adapter's token, with its cursors' consumption counted from a cursor further back. -/
theorem takeOne_trans (parser : P) {origin cursor next : Z} (token : Cursor.Token Z)
    (step : Cursor.Consumed next cursor) (consumed : Cursor.Consumed cursor origin) :
    Parser.Internal.takeOne parser origin token next (Cursor.consumed_trans step consumed) =
      (fun (after, (z : { z : Z // Cursor.Consumed z cursor })) =>
        (after,
          (⟨z.1, Cursor.consumed_trans z.2 consumed⟩ : { z : Z // Cursor.Consumed z origin })))
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
    (origin : LexerCursor batch) :=
  (Parser.Internal.After (ScriptParser H) Unit (Handler.Error H) ×
    { z : LexerCursor batch // z.Consumed origin }) × H

/-- The fused step's outcome, read as the adapter's result of the token: going on in the parser
that the outcome stands for, or stopping. -/
def toPort (posture : VersionPosture) {batch : BatchTag} {origin next : LexerCursor batch}
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
  ∀ (posture : VersionPosture) {batch : BatchTag} {origin next : LexerCursor batch} (h : H)
    (decl : Nat) (cmd : CommandStateOf H) (inTerm : Bool) (ctx : TermContext (Handler.«Sort» H))
    (mode : TermModeOf H) (levels : List (TermLevelOf H)) (token : LexerToken batch)
    (consumed : next.Consumed origin) {β : Type} (k : PortOut H origin → m β),
    step posture h decl cmd inTerm ctx mode levels token next
        (fun out => k (toPort posture consumed out)) =
      ((Parser.Internal.takeOne (assemble posture decl cmd inTerm ctx mode levels) origin token next
        consumed).run h >>= k)

/-- The port's run from a token taken from a cursor that leaves `next`: the adapter's `takeOne`,
then, if it goes on, the rest of the cursor. -/
def portGo {batch : BatchTag} (origin : LexerCursor batch) (parser : ScriptParser H) (h : H)
    (token : LexerToken batch) (next : LexerCursor batch) (consumed : next.Consumed origin) :
    m (LoopResult H origin) :=
  (Parser.Internal.takeOne parser origin token next consumed).run h >>= portRest origin
where
  /-- After a token: the rest of the cursor, or the stop. -/
  portRest (origin : LexerCursor batch) : PortOut H origin → m (LoopResult H origin)
    | ((.goOn parser, ⟨later, taken⟩), h) => do
      let ((answer, parser, done), h) ← (Parser.Internal.rest origin parser later taken).run h
      return (answer, parser, done, h)
    | ((.stop answer parser, done), h) => return (answer, parser, done, h)

variable [LawfulMonad m]

/-- The adapter's token, its consumption counted from the cursor before it. -/
theorem takeOne_from {batch : BatchTag} (parser : ScriptParser H)
    {origin cursor next : LexerCursor batch} (token : LexerToken batch) (step : next.Consumed cursor)
    (consumed : cursor.Consumed origin) :
    Parser.Internal.takeOne (m := m) parser origin token next (step.trans consumed) =
      (fun (after, (z : { z : LexerCursor batch // z.Consumed cursor })) =>
        (after, (⟨z.1, z.2.trans consumed⟩ : { z : LexerCursor batch // z.Consumed origin })))
        <$> Parser.Internal.takeOne parser cursor token next step :=
  takeOne_trans (Z := LexerCursor batch) parser token step consumed

/-- The rest of a cursor that has a token, from a parser that does not hand it over: its token,
then the rest. -/
theorem rest_next {batch : BatchTag} (origin : LexerCursor batch) (parser : ScriptParser H) (h : H)
    (next : LexerCursor batch) (consumed : next.Consumed origin) (hn : next.HasNext)
    (hno : Parser.Internal.ParseByToken.handOver? parser next = none) :
    (do
        let ((answer, parser, done), h) ←
          (Parser.Internal.rest (m := m) origin parser next consumed).run h
        return (answer, parser, done, h)) =
      portGo origin parser h (next.next hn).1 (next.next hn).2.1
        ((next.next hn).2.2.trans consumed) := by
  rw [HandOver.rest_of_none consumed hno]
  have : Cursor.next? next = some (next.next hn) := by
    show LexerCursor.next? next = _
    simp [LexerCursor.next?, hn]
  simp only [this]
  simp only [portGo, StateT.run_bind, bind_assoc]
  rw [takeOne_from parser (next.next hn).1 (next.next hn).2.2 consumed]
  simp only [map_eq_pure_bind, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  congr 1
  funext x
  obtain ⟨⟨after, ⟨later, taken⟩⟩, h'⟩ := x
  cases after <;> simp [portGo.portRest]

/-- The rest of a cursor that has no token: the parser goes on. -/
theorem rest_none {batch : BatchTag} (origin : LexerCursor batch) (parser : ScriptParser H) (h : H)
    (next : LexerCursor batch) (consumed : next.Consumed origin) (hn : ¬next.HasNext) :
    (do
        let ((answer, parser, done), h) ←
          (Parser.Internal.rest (m := m) origin parser next consumed).run h
        return (answer, parser, done, h)) =
      (pure (.ok .continue, parser, ⟨next, consumed⟩, h) : m (LoopResult H origin)) := by
  rw [Parser.Internal.rest]
  split
  · split
    · rename_i has _
      exact absurd has hn
    · simp only [StateT.run_pure, pure_bind]
  · have : Cursor.next? next = none := by
      show LexerCursor.next? next = _
      simp [LexerCursor.next?, hn]
    simp only [this, StateT.run_pure, pure_bind]

omit [LawfulMonad m] in
/-- A script parser awaiting a command hands no cursor over. -/
theorem awaiting_handOver (posture : VersionPosture) (declarations : Nat) {batch : BatchTag}
    (cursor : LexerCursor batch) :
    Parser.Internal.ParseByToken.handOver? (m := m)
      (ScriptParser.Internal.mk (H := H) posture .awaiting declarations) cursor = none :=
  HandOver.script_handOver_none (fun _ h => by simp at h) cursor

omit [LawfulMonad m] in
/-- In a non-standard command, the script parser hands the cursor to the command's parser. -/
theorem handOver?_eq {batch : BatchTag} {parser : ScriptParser H}
    {nonstandard : CommandHandler.NonstandardParser H}
    (hc : ScriptParser.Internal.command parser = .nonstandard nonstandard)
    (cursor : LexerCursor batch) :
    Parser.Internal.ParseByToken.handOver? (m := m) parser cursor = some (do
      let (answer, next) ← Parser.Command.Internal.nonstandardParse nonstandard cursor
      match answer with
      | .error error =>
        return (.stop (.error error) (.new (ScriptParser.Internal.posture parser)), next)
      | .ok (some nonstandard) =>
        return (.goOn (ScriptParser.Internal.mk (ScriptParser.Internal.posture parser)
          (.nonstandard nonstandard) (ScriptParser.Internal.declarations parser)), next)
      | .ok none =>
        return (.goOn (ScriptParser.Internal.mk (ScriptParser.Internal.posture parser) .awaiting
          (ScriptParser.Internal.declarations parser)), next)) := by
  show ScriptParser.Internal.handOver? parser cursor = _
  unfold ScriptParser.Internal.handOver?
  rw [hc]
  rfl

/-- What the loop's rest gives, as a value of the type of `rest`'s run on the handler. -/
abbrev RestOut (H : Type) {m : Type → Type} [CommandHandler H m] {batch : BatchTag}
    (origin : LexerCursor batch) :=
  (Except (Parser.ParseError (Handler.Error H)) (ControlFlow Unit) × ScriptParser H ×
    { z : LexerCursor batch // Cursor.Consumed z origin }) × H

/-- The rest of a cursor that has no token, followed by anything: the parser goes on. -/
theorem rest_none_k {batch : BatchTag} (origin : LexerCursor batch) (parser : ScriptParser H)
    (h : H) (next : LexerCursor batch) (consumed : next.Consumed origin) (hn : ¬next.HasNext)
    {β : Type} (k : RestOut H origin → m β) :
    (Parser.Internal.rest (m := m) origin parser next consumed).run h >>= k =
      k ((.ok .continue, parser, ⟨next, consumed⟩), h) := by
  rw [Parser.Internal.rest]
  split
  · split
    · rename_i has _
      exact absurd has hn
    · simp only [StateT.run_pure, pure_bind]
  · have : Cursor.next? next = none := by
      show LexerCursor.next? next = _
      simp [LexerCursor.next?, hn]
    simp only [this, StateT.run_pure, pure_bind]

/-- The rest of a cursor that has a token, in a non-standard command, followed by anything: the
fused reader's hand-over, then, after the command, the rest of the cursor awaiting the next
one. -/
theorem rest_handOver {batch : BatchTag} (origin base : LexerCursor batch)
    (parser : ScriptParser H) (nonstandard : CommandHandler.NonstandardParser H)
    (hc : ScriptParser.Internal.command parser = .nonstandard nonstandard)
    (cursor : LexerCursor batch) (h : H) (has : cursor.HasNext)
    (lift : ∀ {next : LexerCursor batch}, next.Consumed cursor → next.Consumed base)
    (toOrigin : ∀ {next : LexerCursor batch}, next.Consumed base → next.Consumed origin)
    (consumed : cursor.Consumed origin) {β : Type} (k : RestOut H origin → m β) :
    (Parser.Internal.rest (m := m) origin parser cursor consumed).run h >>= k =
      handOver (ScriptParser.Internal.posture parser) origin base h
          (ScriptParser.Internal.declarations parser) nonstandard cursor has lift toOrigin >>=
        fun r => match r with
        | .inl (answer, after, done, h) => k ((answer, after, done), h)
        | .inr (⟨ended, taken⟩, h) =>
          (Parser.Internal.rest origin (ScriptParser.Internal.mk
            (ScriptParser.Internal.posture parser) .awaiting
            (ScriptParser.Internal.declarations parser)) ended (toOrigin taken)).run h >>= k := by
  rw [Parser.Internal.rest, handOver?_eq hc]
  have hd : Cursor.decideHasNext cursor = isTrue has := Subsingleton.elim _ _
  simp only [hd]
  rw [handOver]
  simp only [StateT.run_bind, bind_assoc]
  refine bind_congr fun x => ?_
  obtain ⟨⟨answer, ⟨next, taken⟩⟩, h'⟩ := x
  rcases answer with error | (_ | nonstandard')
  · simp
  · simp
  · by_cases hn : next.HasNext
    · simp only [hn, ↓reduceDIte]
      have : remaining next < remaining cursor := LexerCursor.Consumed.remaining_lt (taken has)
      have ih := rest_handOver origin base
        (ScriptParser.Internal.mk (ScriptParser.Internal.posture parser)
          (.nonstandard nonstandard') (ScriptParser.Internal.declarations parser))
        nonstandard' (by simp) next h' hn
        (fun step => lift (LexerCursor.Consumed.trans step (taken has))) toOrigin
        (Cursor.consumed_trans (taken has) consumed) k
      simp only [ScriptParser.Internal.posture_mk, ScriptParser.Internal.declarations_mk] at ih
      simp only [StateT.run_pure, pure_bind]
      exact ih
    · simp only [hn, ↓reduceDIte, StateT.run_pure, pure_bind]
      exact rest_none_k origin _ h' next _ hn k
termination_by remaining cursor


/-- The loop from a token is the port's run from it, on the parser its arguments stand for. -/
theorem loop_eq (hstep : StepSimulates H m) (posture : VersionPosture) {batch : BatchTag}
    (origin : LexerCursor batch) (next : LexerCursor batch) (h : H) (decl : Nat)
    (cmd : CommandStateOf H) (inTerm : Bool) (ctx : TermContext (Handler.«Sort» H))
    (mode : TermModeOf H) (levels : List (TermLevelOf H)) (token : LexerToken batch)
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
      split
      · rename_i nonstandard
        rw [rest_handOver origin next
          (ScriptParser.Internal.mk posture (.nonstandard nonstandard) d)
          nonstandard (by simp) next h' hn id (fun step => step.trans consumed) consumed]
        simp only [ScriptParser.Internal.posture_mk, ScriptParser.Internal.declarations_mk]
        refine bind_congr fun r => ?_
        rcases r with ⟨answer, after, done, h''⟩ | ⟨⟨ended, taken⟩, h''⟩
        · rfl
        · dsimp only
          by_cases hc : ended.HasNext
          · simp only [hc, ↓reduceDIte]
            rw [rest_next origin _ h'' ended _ hc (awaiting_handOver posture d ended)]
            obtain ⟨token', ⟨after, taken'⟩⟩ := ended.next hc
            have : remaining after < remaining next := (taken'.trans taken).remaining_lt
            dsimp only
            rw [loop_eq hstep]
            rfl
          · simp only [hc, ↓reduceDIte]
            rw [rest_none origin _ h'' ended _ hc]
      · rename_i hne
        rw [rest_next origin _ h' next consumed hn
          (HandOver.script_handOver_none (fun n hc => hne n (by simpa using hc)) next)]
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
      rw [rest_next origin _ h' next consumed hn (HandOver.script_handOver_none
        (fun n hc => by simp [assemble, withTerm] at hc; split at hc <;> cases hc) next)]
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
      split
      · rename_i nonstandard hcmd
        rw [rest_handOver origin cursor parser nonstandard hcmd cursor h' hn id
          (fun step => step.trans (follows.trans_consumed consumed))
          (follows.trans_consumed consumed)]
        refine bind_congr fun r => ?_
        rcases r with ⟨answer, after, done, h''⟩ | ⟨⟨ended, taken⟩, h''⟩
        · rfl
        · dsimp only
          by_cases hc : ended.HasNext
          · simp only [hc, ↓reduceDIte]
            rw [rest_next origin _ h'' ended _ hc (awaiting_handOver _ _ ended)]
            obtain ⟨token', ⟨after, taken'⟩⟩ := ended.next hc
            have : remaining after < remaining next :=
              ((taken'.trans taken).trans_follows follows).remaining_lt
            dsimp only
            rw [loop_eq hstep]
            rfl
          · simp only [hc, ↓reduceDIte]
            rw [rest_none origin _ h'' ended _ hc]
      · rename_i hne
        rw [rest_next origin _ h' cursor (follows.trans_consumed consumed) hn
          (HandOver.script_handOver_none hne cursor)]
        obtain ⟨token', ⟨after, taken⟩⟩ := cursor.next hn
        have : remaining after < remaining next := (taken.trans_follows follows).remaining_lt
        dsimp only
        obtain ⟨posture', command', declarations'⟩ := parser
        dsimp only [ScriptParser.Internal.posture, ScriptParser.Internal.command,
          ScriptParser.Internal.declarations] at hne ⊢
        split <;> rw [loop_eq hstep] <;> congr 1 <;>
          simp_all [assemble, withTerm, ScriptParser.Internal.mk]
    · simp only [hn, ↓reduceDIte]
      rw [rest_none origin _ h' cursor (follows.trans_consumed consumed) hn]
  | stop answer parser cursor follows h' =>
    simp only [toPort, portGo.portRest]
termination_by remaining next
/-- The loop from the first token of a hand-over is the port's run from it, on the parser. -/
theorem start_eq (hstep : StepSimulates H m) {batch : BatchTag} (parser : ScriptParser H) (h : H)
    (token : LexerToken batch) (cursor next : LexerCursor batch) (consumed : next.Consumed cursor) :
    start parser h token cursor next consumed = portGo cursor parser h token next consumed := by
  unfold start
  split <;> rw [loop_eq hstep] <;> congr 1 <;> cases parser <;>
    simp_all [assemble, withTerm, ScriptParser.Internal.mk, ScriptParser.Internal.posture,
      ScriptParser.Internal.command, ScriptParser.Internal.declarations]

/-- The rest of a cursor that has a token, from a parser that does not hand it over, followed by
anything: its token, then the rest. -/
theorem rest_next_k {batch : BatchTag} (origin : LexerCursor batch) (parser : ScriptParser H)
    (h : H) (next : LexerCursor batch) (consumed : next.Consumed origin) (hn : next.HasNext)
    (hno : Parser.Internal.ParseByToken.handOver? parser next = none) {β : Type}
    (k : RestOut H origin → m β) :
    (Parser.Internal.rest (m := m) origin parser next consumed).run h >>= k =
      portGo origin parser h (next.next hn).1 (next.next hn).2.1
          ((next.next hn).2.2.trans consumed) >>=
        fun (answer, after, done, h) => k ((answer, after, done), h) := by
  rw [← rest_next origin parser h next consumed hn hno]
  simp only [bind_assoc, pure_bind]

/-- The fused reader parses a batch cursor as the script parser's loop over single tokens does:
the same answer, parser, parse state, cursor and handler. -/
theorem parse_eq (hstep : StepSimulates H m) {batch : BatchTag} (parser : ScriptParser H)
    (state : Parser.ParseState H) (cursor : LexerCursor batch) :
    BSmtLib.Parser.Internal.Fused.parse (m := m) parser state cursor =
      Parser.Internal.parseByToken parser state cursor := by
  funext h
  by_cases hp : cursor.HasNext
  · by_cases hns : ∃ nonstandard, ScriptParser.Internal.command parser = .nonstandard nonstandard
    · obtain ⟨nonstandard, hcmd⟩ := hns
      show _ = (Parser.Internal.parseByToken parser state cursor).run h
      rw [Parser.Internal.parseByToken, handOver?_eq hcmd]
      have hd : Cursor.decideHasNext cursor = isTrue hp := Subsingleton.elim _ _
      simp only [hd]
      simp only [BSmtLib.Parser.Internal.Fused.parse, Cursor.asBatch?, hp, ↓reduceDIte, begin,
        hcmd]
      rw [handOver]
      simp only [StateT.run_bind, bind_assoc]
      refine bind_congr fun x => ?_
      obtain ⟨⟨answer, ⟨next, taken⟩⟩, h'⟩ := x
      rcases answer with error | (_ | nonstandard')
      · simp
      · simp only [pure_bind, StateT.run_pure, StateT.run_bind]
        by_cases hc : next.HasNext
        · simp only [hc, ↓reduceDIte]
          rw [rest_next_k cursor _ h' next _ hc (awaiting_handOver _ _ next)]
          obtain ⟨token', ⟨after, step⟩⟩ := next.next hc
          dsimp only
          rw [loop_eq hstep]
          simp only [assemble, Bool.false_eq_true, ite_false]
          refine bind_congr fun r => ?_
          obtain ⟨answer, after, ⟨done, taken⟩, h''⟩ := r
          rfl
        · simp only [hc, ↓reduceDIte]
          rw [rest_none_k cursor _ h' next _ hc]
          simp
      · simp only [StateT.run_pure, pure_bind, StateT.run_bind]
        by_cases hn : next.HasNext
        · simp only [hn, ↓reduceDIte]
          rw [rest_handOver cursor cursor _ nonstandard' (by simp) next h' hn
            (fun step => LexerCursor.Consumed.trans step (taken hp)) id (taken hp)]
          simp only [ScriptParser.Internal.posture_mk, ScriptParser.Internal.declarations_mk]
          refine bind_congr fun r => ?_
          rcases r with ⟨answer, after, ⟨done, taken'⟩, h''⟩ | ⟨⟨ended, taken'⟩, h''⟩
          · simp
          · simp only
            by_cases hc : ended.HasNext
            · simp only [hc, ↓reduceDIte]
              rw [rest_next_k cursor _ h'' ended _ hc (awaiting_handOver _ _ ended)]
              obtain ⟨token', ⟨after, step⟩⟩ := ended.next hc
              dsimp only
              rw [loop_eq hstep]
              simp only [assemble, Bool.false_eq_true, ite_false]
              refine bind_congr fun r => ?_
              obtain ⟨answer, after, ⟨done, taken⟩, h'''⟩ := r
              rfl
            · simp only [hc, ↓reduceDIte]
              rw [rest_none_k cursor _ h'' ended _ hc]
              simp
        · simp only [hn, ↓reduceDIte, pure_bind]
          rw [rest_none_k cursor _ h' next _ hn]
          simp
    · have hno := HandOver.script_handOver_none (m := m)
        (fun nonstandard hc => hns ⟨nonstandard, hc⟩) cursor
      rw [HandOver.parseByToken_of_none state hno]
      split
      · rename_i heq
        have : Cursor.next? cursor = some (cursor.next hp) := by
          show LexerCursor.next? cursor = _
          simp [LexerCursor.next?, hp]
        rw [this] at heq; cases heq
      · rename_i token next consumed heq
        have hnx : cursor.next hp = (token, ⟨next, consumed⟩) := by
          have : Cursor.next? cursor = some (cursor.next hp) := by
            show LexerCursor.next? cursor = _
            simp [LexerCursor.next?, hp]
          rw [this] at heq
          exact Option.some.inj heq
        simp only [BSmtLib.Parser.Internal.Fused.parse, Cursor.asBatch?, hp, ↓reduceDIte, begin]
        split
        · rename_i nonstandard hc
          exact absurd ⟨nonstandard, hc⟩ hns
        simp only [hnx]
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
  · have h2 : Cursor.next? cursor = none := by
      show LexerCursor.next? cursor = _
      simp [LexerCursor.next?, hp]
    have hd : Cursor.decideHasNext cursor = isFalse hp := Subsingleton.elim _ _
    cases hh : Parser.Internal.ParseByToken.handOver? (m := m) parser cursor with
    | none =>
      have e : Parser.Internal.parseByToken (m := m) parser state cursor =
          pure (.ok .continue, parser, state, ⟨cursor, fun has => absurd has hp⟩) := by
        rw [HandOver.parseByToken_of_none state hh]
        split
        · rfl
        · rename_i heq
          rw [h2] at heq
          cases heq
      rw [e]
      simp only [BSmtLib.Parser.Internal.Fused.parse, Cursor.asBatch?, hp, ↓reduceDIte]
      rfl
    | some _ =>
      rw [Parser.Internal.parseByToken, hh]
      simp only [BSmtLib.Parser.Internal.Fused.parse, Cursor.asBatch?, hp, ↓reduceDIte, hd]
      rfl

end

end BSmtLib.Facts.Proofs.Parser.Fused.Loop
