module

public import BSmtLib.Facts.Proofs.Parser.Fused.Category
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Command
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Parser.Internal.Fused
import all BSmtLib.Parser.Internal.Fused.Basic
import all BSmtLib.Parser.Internal.Fused.Category
import all BSmtLib.Parser.Script
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor

@[expose] public section

/-!
# The fused command step against the port's

The fused step of a token at the command level, in every command state, is the port's script step
followed by what the parse adapter does with its result (`commandStep_eq`): the states it fuses by
the same handler calls in the same order, the others by the port's step itself.
-/

namespace BSmtLib.Facts.Proofs.Parser.Fused.Command

open BSmtLib.Handler
open BSmtLib.Parser (Parse ParseError ParseErrorKind)
open BSmtLib.Parser.Internal (PM call syntaxError)
open BSmtLib.Parser.Command.Internal (CommandStateOf)
open BSmtLib.Parser.Internal.Fused
open BSmtLib.Parser.Internal.Fused.Basic
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Token (BatchTag Cursor)
open BSmtLib.Lexer.Cursor (LexerCursor LexerToken)
open BSmtLib.Version (VersionPosture)
open BSmtLib.Facts.Proofs.Parser.Fused.Loop
open BSmtLib.Facts.Proofs.Parser.Fused.Run
open BSmtLib.Facts.Proofs.Parser.Fused.Category

/- The script parser's constructor and readers, which `simp` unfolds here. -/
attribute [local simp] ScriptParser.Internal.mk ScriptParser.Internal.command
  ScriptParser.Internal.posture ScriptParser.Internal.declarations

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [CommandHandler H m]

/-! ## Commands -/

/-- How the port's script step goes on, as the fused command step's continuation. -/
def scriptCont (posture : VersionPosture) {batch : BatchTag} (next : LexerCursor batch)
    {β : Type} (k : OutcomeOf H next → m β) :
    Except (Cause H) (Parser.Internal.Flow (PM H) (ScriptParser H) Unit) × H → m β
  | (.error e, h) =>
    k <| .stop (.error (ParseError.Internal.new e)) (ScriptParser.new posture) next (.refl _) h
  | (.ok (.more p), h) =>
    k <| .command h (ScriptParser.Internal.declarations p) (ScriptParser.Internal.command p)
  | (.ok (.done r), h) => k <| .stop (.ok (.break r)) (ScriptParser.new posture) next (.refl _) h
  | (.ok (.switchVersion declared resume), h) =>
    match switch : next.setVersion declared with
    | .error _ =>
      k <| .stop (.error (ParseError.Internal.new (.version .unsupported)))
        (ScriptParser.new posture) next (.refl _) h
    | .ok switched => do
      let follows := Lexer.Cursor.LexerCursor.setVersion_follows switch
      match ← runParser resume h with
      | (.error e, h) =>
        k <| .stop (.error (ParseError.Internal.new e)) (ScriptParser.new posture) switched
          follows h
      | (.ok (.more p), h) => k <| .resume h p switched follows
      | (.ok (.done r), h) =>
        k <| .stop (.ok (.break r)) (ScriptParser.new posture) switched follows h
  | (.ok (.discardRest resume), h) => do
    let discarded := next.discardRest
    let follows := Lexer.Cursor.LexerCursor.discardRest_follows next
    match ← runParser resume h with
    | (.error e, h) =>
      k <| .stop (.error (ParseError.Internal.new e)) (ScriptParser.new posture) discarded follows h
    | (.ok (.more p), h) => k <| .resume h p discarded follows
    | (.ok (.done r), h) =>
      k <| .stop (.ok (.break r)) (ScriptParser.new posture) discarded follows h

omit [LawfulMonad m] in
theorem portStep_eq (posture : VersionPosture) {batch : BatchTag} (h : H) (declarations : Nat)
    (command : CommandStateOf H) (token : LexerToken batch) (next : LexerCursor batch) {β : Type}
    (k : OutcomeOf H next → m β) :
    portStep posture h declarations command token next k =
      (ScriptParser.Internal.arrive (ScriptParser.Internal.mk posture command declarations)
          (inputOf next.version next token) >>=
          fun _ => ScriptParser.Internal.step next.version
            (ScriptParser.Internal.mk posture command declarations)
            (inputOf next.version next token)).run.run h
        >>= scriptCont posture next k := by
  unfold portStep runParser
  rfl

set_option maxHeartbeats 400000 in
theorem commandStep_eq (posture : VersionPosture) {batch : BatchTag}
    {origin next : LexerCursor batch} (h : H) (declarations : Nat) (command : CommandStateOf H)
    (token : LexerToken batch) (consumed : next.Consumed origin) {β : Type}
    (k : PortOut H origin → m β) :
    Parser.Internal.Fused.commandStep posture h declarations command token next
        (fun out => k (toPort posture consumed out)) =
      portStep posture h declarations command token next
        (fun out => k (toPort posture consumed out)) := by
  unfold Parser.Internal.Fused.commandStep
  cases command with
  | awaiting =>
    rw [portStep_eq]
    simp only [ScriptParser.Internal.command_mk, ScriptParser.Internal.posture_mk,
        ScriptParser.Internal.declarations_mk, ScriptParser.Internal.arrive,
        Parser.Command.Internal.commandArrive,
        ScriptParser.Internal.step,
      Parser.Command.Internal.commandStep, inputOf]
    cases next.category token <;> simp only [Token.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Lexicon.Reserved.fromBytes? (next.content token) next.version with
        _ | (w | w)) <;>
      simp [scriptCont, fail, syntaxError]
  | opened =>
    rw [portStep_eq]
    simp only [ScriptParser.Internal.command_mk, ScriptParser.Internal.posture_mk,
        ScriptParser.Internal.declarations_mk, ScriptParser.Internal.arrive,
        Parser.Command.Internal.commandArrive,
        ScriptParser.Internal.step,
      Parser.Command.Internal.commandStep, inputOf, Reserved.contentOf_eq, Reserved.reservedAt_eq]
    cases next.category token <;> simp only [Token.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Lexicon.Reserved.fromBytes? (next.content token) next.version with
        _ | (w | w)) <;>
      simp [scriptCont, fail, syntaxError]
    all_goals first
      | (simp only [startNonstandard, runHandler]
         rw [run_call, bind_map_left]
         congr 1
         funext ⟨r, h'⟩
         cases r <;> simp [toPort, fail, Except.mapError, Except.map])
      | (cases w <;> simp [startTerm, toPort, assemble, withTerm,
          Parser.Command.Internal.Standard.Payload.init,
          Parser.Category.Term.Internal.TermState.init])
  | payload p =>
    cases p with
    | closing final =>
      simp only [closingStep]
      rw [portStep_eq]
      simp only [ScriptParser.Internal.command_mk, ScriptParser.Internal.posture_mk,
          ScriptParser.Internal.declarations_mk, ScriptParser.Internal.arrive,
          Parser.Command.Internal.commandArrive,
        Parser.Command.Internal.Standard.payloadArrive, ScriptParser.Internal.step,
            Parser.Command.Internal.commandStep,
        Parser.Command.Internal.Standard.payloadStep, inputOf]
      cases next.category token <;> simp only [Token.Internal.fromParts,
          Parser.Internal.Input.ofSyntax] <;>
        (try rcases Lexicon.Reserved.fromBytes? (next.content token) next.version with
          _ | (w | w)) <;>
        simp [scriptCont, fail, syntaxError, Parser.Category.Token.Internal.expectClose, runParser,
          run_bind_eq]
      all_goals (congr 1; funext ⟨r, h'⟩; cases r <;> (try cases final) <;>
        simp [scriptCont, toPort, runParser])
    | named named =>
      rw [portStep_eq]
      simp only [ScriptParser.Internal.command_mk, ScriptParser.Internal.posture_mk,
          ScriptParser.Internal.declarations_mk, ScriptParser.Internal.arrive,
          Parser.Command.Internal.commandArrive,
        Parser.Command.Internal.Standard.payloadArrive, ScriptParser.Internal.step,
            Parser.Command.Internal.commandStep,
        Parser.Command.Internal.Standard.payloadStep, inputOf, Category.symbolOf?,
            Reserved.contentOf_eq,
        Reserved.reservedAt_eq]
      cases next.category token <;> simp only [Token.Internal.fromParts,
          Parser.Internal.Input.ofSyntax] <;>
        (try rcases Lexicon.Reserved.fromBytes? (next.content token) next.version with
          _ | (w | w)) <;>
        simp [scriptCont, fail, syntaxError, Parser.Category.Token.Internal.expectSymbol,
          run_bind_eq]
      all_goals (cases named <;> simp [scriptCont, toPort, closing])
    | declareConst symbol state =>
      rw [portStep_eq]
      simp only [ScriptParser.Internal.command_mk, ScriptParser.Internal.posture_mk,
          ScriptParser.Internal.declarations_mk, ScriptParser.Internal.arrive,
          Parser.Command.Internal.commandArrive,
        Parser.Command.Internal.Standard.payloadArrive, ScriptParser.Internal.step,
            Parser.Command.Internal.commandStep,
        Parser.Command.Internal.Standard.payloadStep, run_bind_eq, bind_assoc,
            Category.sortStepOutlined]
      simp only [ExceptT.run_pure, StateT.run_pure, pure_bind]
      rw [sortStep_run]
      simp only [bind_assoc, bind_map_left]
      congr 1
      funext o
      cases o <;> simp [HandledOutcome.toRun, scriptCont, toPort, fail, closing]
    | declareFunParameters symbol state =>
      rw [portStep_eq]
      simp only [ScriptParser.Internal.command_mk, ScriptParser.Internal.posture_mk,
          ScriptParser.Internal.declarations_mk, ScriptParser.Internal.arrive,
          Parser.Command.Internal.commandArrive,
        Parser.Command.Internal.Standard.payloadArrive, ScriptParser.Internal.step,
            Parser.Command.Internal.commandStep,
        Parser.Command.Internal.Standard.payloadStep, run_bind_eq, bind_assoc,
            Category.sortsStepOutlined]
      simp only [ExceptT.run_pure, StateT.run_pure, pure_bind]
      rw [sortsStep_run]
      simp only [bind_assoc, bind_map_left]
      congr 1
      funext o
      cases o <;> simp [HandledOutcome.toRun, scriptCont, toPort, fail]
    | declareFunResult symbol parameters state =>
      rw [portStep_eq]
      simp only [ScriptParser.Internal.command_mk, ScriptParser.Internal.posture_mk,
          ScriptParser.Internal.declarations_mk, ScriptParser.Internal.arrive,
          Parser.Command.Internal.commandArrive,
        Parser.Command.Internal.Standard.payloadArrive, ScriptParser.Internal.step,
            Parser.Command.Internal.commandStep,
        Parser.Command.Internal.Standard.payloadStep, run_bind_eq, bind_assoc,
            Category.sortStepOutlined]
      simp only [ExceptT.run_pure, StateT.run_pure, pure_bind]
      rw [sortStep_run]
      simp only [bind_assoc, bind_map_left]
      congr 1
      funext o
      cases o <;> simp [HandledOutcome.toRun, scriptCont, toPort, fail, closing]
    | defineConstSort symbol state =>
      rw [portStep_eq]
      simp only [ScriptParser.Internal.command_mk, ScriptParser.Internal.posture_mk,
          ScriptParser.Internal.declarations_mk, ScriptParser.Internal.arrive,
          Parser.Command.Internal.commandArrive,
        Parser.Command.Internal.Standard.payloadArrive, ScriptParser.Internal.step,
            Parser.Command.Internal.commandStep,
        Parser.Command.Internal.Standard.payloadStep, run_bind_eq, bind_assoc,
            Category.sortStepOutlined]
      simp only [ExceptT.run_pure, StateT.run_pure, pure_bind]
      rw [sortStep_run]
      simp only [bind_assoc, bind_map_left]
      congr 1
      funext o
      cases o <;> simp [HandledOutcome.toRun, scriptCont, toPort, fail, startTerm, assemble,
        withTerm, Parser.Category.Term.Internal.TermState.init]
    | defineSignature definition state =>
      rw [portStep_eq]
      simp only [ScriptParser.Internal.command_mk, ScriptParser.Internal.posture_mk,
          ScriptParser.Internal.declarations_mk, ScriptParser.Internal.arrive,
          Parser.Command.Internal.commandArrive,
        Parser.Command.Internal.Standard.payloadArrive, ScriptParser.Internal.step,
            Parser.Command.Internal.commandStep,
        Parser.Command.Internal.Standard.payloadStep, run_bind_eq, bind_assoc,
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
            Parser.Category.Term.Internal.TermState.init]
    | push =>
      rw [portStep_eq]
      simp only [ScriptParser.Internal.command_mk, ScriptParser.Internal.posture_mk,
          ScriptParser.Internal.declarations_mk, ScriptParser.Internal.arrive,
          Parser.Command.Internal.commandArrive,
        Parser.Command.Internal.Standard.payloadArrive, ScriptParser.Internal.step,
            Parser.Command.Internal.commandStep,
        Parser.Command.Internal.Standard.payloadStep, inputOf, Reserved.contentOf_eq]
      cases next.category token <;> simp only [Token.Internal.fromParts,
          Parser.Internal.Input.ofSyntax] <;>
        (try rcases Lexicon.Reserved.fromBytes? (next.content token) next.version with
          _ | (w | w)) <;>
        simp [scriptCont, fail, syntaxError, Parser.Category.Token.Internal.expectNumeral, toPort,
            closing]
    | pop =>
      rw [portStep_eq]
      simp only [ScriptParser.Internal.command_mk, ScriptParser.Internal.posture_mk,
          ScriptParser.Internal.declarations_mk, ScriptParser.Internal.arrive,
          Parser.Command.Internal.commandArrive,
        Parser.Command.Internal.Standard.payloadArrive, ScriptParser.Internal.step,
            Parser.Command.Internal.commandStep,
        Parser.Command.Internal.Standard.payloadStep, inputOf, Reserved.contentOf_eq]
      cases next.category token <;> simp only [Token.Internal.fromParts,
          Parser.Internal.Input.ofSyntax] <;>
        (try rcases Lexicon.Reserved.fromBytes? (next.content token) next.version with
          _ | (w | w)) <;>
        simp [scriptCont, fail, syntaxError, Parser.Category.Token.Internal.expectNumeral, toPort,
            closing]
    | _ => rfl
  | nonstandard parser => rfl

end BSmtLib.Facts.Proofs.Parser.Fused.Command
