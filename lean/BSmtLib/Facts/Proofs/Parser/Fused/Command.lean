module

public import BSmtLib.Facts.Proofs.Parser.Fused.Category
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Command
import all BSmtLib.Parser.Command.Standard
import all BSmtLib.Parser.Internal.Fused
import all BSmtLib.Parser.Internal.Fused.Basic
import all BSmtLib.Parser.Internal.Fused.Category
import all BSmtLib.Parser.Script
import all BSmtLib.Token.SyntaxToken

@[expose] public section

/-!
# The fused command step against the port's

The fused step of a token at the command level, in every command state, is the port's script step
followed by what the parse adapter does with its result (`commandStep_eq`): the states it fuses by
the same handler calls in the same order, the others by the port's step itself.
-/

namespace BSmtLib.Facts.Proofs.Parser.Fused.Command

open BSmtLib.Traits
open BSmtLib.Parser (Parse PM Input Step Flow call syntaxError ParseErrorCause)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Parser.Category.Term (TermLevelOf TermStateOf)
open BSmtLib.Parser.Command (CommandStateOf)
open BSmtLib.Parser.Internal.Fused
open BSmtLib.Parser.Internal.Fused.Basic
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Token (BatchTag BatchCursor Produce VersionPosture)
open BSmtLib.Facts.Proofs.Parser.Fused.Loop
open BSmtLib.Facts.Proofs.Parser.Fused.Run
open BSmtLib.Facts.Proofs.Parser.Fused.Category

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [CommandHandler H m]

/-! ## Commands -/

/-- How the port's script step goes on, as the fused command step's continuation. -/
def scriptCont (posture : VersionPosture) {batch : BatchTag} (next : BatchCursor batch)
    {β : Type} (k : OutcomeOf H next → m β) :
    Except (Cause H) (Flow (PM H) (ScriptParser H) Unit) × H → m β
  | (.error e, h) => k <| .stop (.error e) (ScriptParser.new posture) next (.refl _) h
  | (.ok (.more p), h) => k <| .command h p.declarations p.command
  | (.ok (.done r), h) => k <| .stop (.ok (.break r)) (ScriptParser.new posture) next (.refl _) h
  | (.ok (.switchVersion declared resume), h) =>
    match switch : next.setVersion declared with
    | .error _ =>
      k <| .stop (.error (.syntax .unsupportedVersion)) (ScriptParser.new posture) next (.refl _) h
    | .ok switched => do
      let follows := Token.BatchCursor.setVersion_follows switch
      match ← runParser resume h with
      | (.error e, h) => k <| .stop (.error e) (ScriptParser.new posture) switched follows h
      | (.ok (.more p), h) => k <| .stop (.ok .continue) p switched follows h
      | (.ok (.done r), h) =>
        k <| .stop (.ok (.break r)) (ScriptParser.new posture) switched follows h
  | (.ok (.discardRest resume), h) => do
    let discarded := next.discardRest
    let follows := Token.BatchCursor.discardRest_follows next
    match ← runParser resume h with
    | (.error e, h) => k <| .stop (.error e) (ScriptParser.new posture) discarded follows h
    | (.ok (.more p), h) => k <| .stop (.ok .continue) p discarded follows h
    | (.ok (.done r), h) =>
      k <| .stop (.ok (.break r)) (ScriptParser.new posture) discarded follows h

omit [LawfulMonad m] in
theorem portStep_eq (posture : VersionPosture) {batch : BatchTag} (h : H) (declarations : Nat)
    (command : CommandStateOf H) (token : Token batch) (next : BatchCursor batch) {β : Type}
    (k : OutcomeOf H next → m β) :
    portStep posture h declarations command token next k =
      (ScriptParser.arrive { posture, command, declarations } (inputOf next.version next token) >>=
          fun _ => ScriptParser.step next.version { posture, command, declarations }
            (inputOf next.version next token)).run.run h
        >>= scriptCont posture next k := by
  unfold portStep runParser
  rfl

theorem commandStep_eq (posture : VersionPosture) {batch : BatchTag}
    {origin next : BatchCursor batch} (h : H) (declarations : Nat) (command : CommandStateOf H)
    (token : Token batch) (consumed : next.Consumed origin) {β : Type}
    (k : PortOut H origin → m β) :
    Parser.Internal.Fused.commandStep posture h declarations command token next
        (fun out => k (toPort posture consumed out)) =
      portStep posture h declarations command token next
        (fun out => k (toPort posture consumed out)) := by
  unfold Parser.Internal.Fused.commandStep
  cases command with
  | awaiting =>
    rw [portStep_eq]
    simp only [ScriptParser.arrive, Parser.Command.commandArrive, ScriptParser.step,
      Parser.Command.commandStep, inputOf]
    cases next.category token <;> simp only [Token.SyntaxToken.fromParts, Input.ofSyntax] <;>
      (try rcases Token.Reserved.fromBytes? (next.content token) next.version with _ | (w | w)) <;>
      simp [scriptCont, fail, syntaxError]
  | opened =>
    rw [portStep_eq]
    simp only [ScriptParser.arrive, Parser.Command.commandArrive, ScriptParser.step,
      Parser.Command.commandStep, inputOf, Reserved.contentOf_eq, Reserved.reservedAt_eq]
    cases next.category token <;> simp only [Token.SyntaxToken.fromParts, Input.ofSyntax] <;>
      (try rcases Token.Reserved.fromBytes? (next.content token) next.version with _ | (w | w)) <;>
      simp [scriptCont, fail, syntaxError]
    all_goals (cases w <;> simp [startTerm, toPort, assemble, withTerm,
      Parser.Command.Standard.Payload.init, Parser.Category.Term.TermState.init])
  | payload p =>
    cases p with
    | closing final =>
      simp only [closingStep]
      rw [portStep_eq]
      simp only [ScriptParser.arrive, Parser.Command.commandArrive,
        Parser.Command.Standard.payloadArrive, ScriptParser.step, Parser.Command.commandStep,
        Parser.Command.Standard.payloadStep, inputOf]
      cases next.category token <;> simp only [Token.SyntaxToken.fromParts, Input.ofSyntax] <;>
        (try rcases Token.Reserved.fromBytes? (next.content token) next.version with
          _ | (w | w)) <;>
        simp [scriptCont, fail, syntaxError, Parser.Category.Token.expectClose, runParser,
          run_bind_eq]
      all_goals (congr 1; funext ⟨r, h'⟩; cases r <;> (try cases final) <;>
        simp [scriptCont, toPort, runParser])
    | named named =>
      rw [portStep_eq]
      simp only [ScriptParser.arrive, Parser.Command.commandArrive,
        Parser.Command.Standard.payloadArrive, ScriptParser.step, Parser.Command.commandStep,
        Parser.Command.Standard.payloadStep, inputOf, Category.symbolOf?, Reserved.contentOf_eq,
        Reserved.reservedAt_eq]
      cases next.category token <;> simp only [Token.SyntaxToken.fromParts, Input.ofSyntax] <;>
        (try rcases Token.Reserved.fromBytes? (next.content token) next.version with
          _ | (w | w)) <;>
        simp [scriptCont, fail, syntaxError, Parser.Category.Token.expectSymbol,
          run_bind_eq]
      all_goals (cases named <;> simp [scriptCont, toPort, closing])
    | declareConst symbol state =>
      rw [portStep_eq]
      simp only [ScriptParser.arrive, Parser.Command.commandArrive,
        Parser.Command.Standard.payloadArrive, ScriptParser.step, Parser.Command.commandStep,
        Parser.Command.Standard.payloadStep, run_bind_eq, bind_assoc, Category.sortStepOutlined]
      simp only [ExceptT.run_pure, StateT.run_pure, pure_bind]
      rw [sortStep_run]
      simp only [bind_assoc, bind_map_left]
      congr 1
      funext o
      cases o <;> simp [HandledOutcome.toRun, scriptCont, toPort, fail, closing]
    | declareFunParameters symbol state =>
      rw [portStep_eq]
      simp only [ScriptParser.arrive, Parser.Command.commandArrive,
        Parser.Command.Standard.payloadArrive, ScriptParser.step, Parser.Command.commandStep,
        Parser.Command.Standard.payloadStep, run_bind_eq, bind_assoc, Category.sortsStepOutlined]
      simp only [ExceptT.run_pure, StateT.run_pure, pure_bind]
      rw [sortsStep_run]
      simp only [bind_assoc, bind_map_left]
      congr 1
      funext o
      cases o <;> simp [HandledOutcome.toRun, scriptCont, toPort, fail]
    | declareFunResult symbol parameters state =>
      rw [portStep_eq]
      simp only [ScriptParser.arrive, Parser.Command.commandArrive,
        Parser.Command.Standard.payloadArrive, ScriptParser.step, Parser.Command.commandStep,
        Parser.Command.Standard.payloadStep, run_bind_eq, bind_assoc, Category.sortStepOutlined]
      simp only [ExceptT.run_pure, StateT.run_pure, pure_bind]
      rw [sortStep_run]
      simp only [bind_assoc, bind_map_left]
      congr 1
      funext o
      cases o <;> simp [HandledOutcome.toRun, scriptCont, toPort, fail, closing]
    | defineConstSort symbol state =>
      rw [portStep_eq]
      simp only [ScriptParser.arrive, Parser.Command.commandArrive,
        Parser.Command.Standard.payloadArrive, ScriptParser.step, Parser.Command.commandStep,
        Parser.Command.Standard.payloadStep, run_bind_eq, bind_assoc, Category.sortStepOutlined]
      simp only [ExceptT.run_pure, StateT.run_pure, pure_bind]
      rw [sortStep_run]
      simp only [bind_assoc, bind_map_left]
      congr 1
      funext o
      cases o <;> simp [HandledOutcome.toRun, scriptCont, toPort, fail, startTerm, assemble,
        withTerm, Parser.Category.Term.TermState.init]
    | defineSignature definition state =>
      rw [portStep_eq]
      simp only [ScriptParser.arrive, Parser.Command.commandArrive,
        Parser.Command.Standard.payloadArrive, ScriptParser.step, Parser.Command.commandStep,
        Parser.Command.Standard.payloadStep, run_bind_eq, bind_assoc,
        Category.signatureStepOutlined]
      simp only [ExceptT.run_pure, StateT.run_pure, pure_bind]
      rw [signatureStep_run]
      simp only [bind_assoc, bind_map_left]
      congr 1
      funext o
      cases o with
      | more h' state => simp [HandledOutcome.toRun, scriptCont, toPort]
      | error h' cause => simp [HandledOutcome.toRun, scriptCont, toPort, fail]
      | done h' signature =>
        cases definition <;> simp only [HandledOutcome.toRun] <;>
          rw [run_call_bind] <;> simp only [bind_assoc] <;> unfold runHandler <;> congr 1 <;>
          funext ⟨r, h''⟩ <;> cases r <;>
          simp [scriptCont, toPort, fail, startTerm, assemble, withTerm,
            Parser.Category.Term.TermState.init]
    | push =>
      rw [portStep_eq]
      simp only [ScriptParser.arrive, Parser.Command.commandArrive,
        Parser.Command.Standard.payloadArrive, ScriptParser.step, Parser.Command.commandStep,
        Parser.Command.Standard.payloadStep, inputOf, Reserved.contentOf_eq]
      cases next.category token <;> simp only [Token.SyntaxToken.fromParts, Input.ofSyntax] <;>
        (try rcases Token.Reserved.fromBytes? (next.content token) next.version with
          _ | (w | w)) <;>
        simp [scriptCont, fail, syntaxError, Parser.Category.Token.expectNumeral, toPort, closing]
    | pop =>
      rw [portStep_eq]
      simp only [ScriptParser.arrive, Parser.Command.commandArrive,
        Parser.Command.Standard.payloadArrive, ScriptParser.step, Parser.Command.commandStep,
        Parser.Command.Standard.payloadStep, inputOf, Reserved.contentOf_eq]
      cases next.category token <;> simp only [Token.SyntaxToken.fromParts, Input.ofSyntax] <;>
        (try rcases Token.Reserved.fromBytes? (next.content token) next.version with
          _ | (w | w)) <;>
        simp [scriptCont, fail, syntaxError, Parser.Category.Token.expectNumeral, toPort, closing]
    | _ => rfl

end BSmtLib.Facts.Proofs.Parser.Fused.Command
