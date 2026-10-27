module

public import BSmtLib.Facts.Proofs.Parser.Fused.Category
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Internal.Fused
import all BSmtLib.Parser.Internal.Fused.Basic
import all BSmtLib.Parser.Internal.Fused.Category
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor

@[expose] public section

/-!
# The fused term step against the port's

The fused step of a command's term, in every mode and on every token, is the port's term step
followed by what the loop does with its result (`termStep_eq`): the modes it fuses by the same
handler calls in the same order, the others by the port's step itself.
-/

namespace BSmtLib.Facts.Proofs.Parser.Fused.Term

open BSmtLib.Handler
open BSmtLib.Parser (Parse ParseError ParseErrorKind)
open BSmtLib.Parser.Internal (PM call syntaxError)
open BSmtLib.Parser.Category.Term.Internal (TermLevelOf TermStateOf)
open BSmtLib.Parser.Internal.Fused
open BSmtLib.Parser.Internal.Fused.Basic
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Token (BatchTag Cursor)
open BSmtLib.Lexer.Cursor (LexerCursor LexerToken)
open BSmtLib.Version (VersionPosture)
open BSmtLib.Facts.Proofs.Parser.Fused.Run
open BSmtLib.Facts.Proofs.Parser.Fused.Category

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [CommandHandler H m]

/-! ## Terms -/

/-- How the port's term step goes on, as the fused term step's continuation. -/
def termCont (posture : VersionPosture) (declarations : Nat)
    (context : TermContext (Handler.«Sort» H)) {batch : BatchTag} (next : LexerCursor batch)
    {β : Type} (k : OutcomeOf H next → m β) :
    Except (Cause H) (Parser.Internal.Step (TermStateOf H) (Handler.Term H)) × H → m β
  | (.error e, h) => fail posture next h e k
  | (.ok (.more term), h) => k (.term h declarations context term.mode term.levels)
  | (.ok (.done term), h) => k (.command h declarations (finishTerm context term))

omit [LawfulMonad m] in
theorem portTermStep_eq (posture : VersionPosture) {batch : BatchTag} (h : H)
    (declarations : Nat) (context : TermContext (Handler.«Sort» H)) (term : TermStateOf H)
    (token : LexerToken batch) (next : LexerCursor batch) {β : Type} (k : OutcomeOf H next → m β) :
    portTermStep posture h declarations context term token next k =
      (Parser.Category.Term.Internal.termStep next.version term
          (inputOf next.version next token)).run.run h
        >>= termCont posture declarations context next k := by
  unfold portTermStep runParser
  rfl
theorem termComplete_eq (posture : VersionPosture) {batch : BatchTag} (next : LexerCursor batch)
    (h : H) (declarations : Nat) (context : TermContext (Handler.«Sort» H))
    (levels : List (TermLevelOf H)) (term : Handler.Term H) {β : Type}
    (k : OutcomeOf H next → m β) :
    (Parser.Category.Term.Internal.termComplete levels term).run.run h >>=
        termCont posture declarations context next k =
      Parser.Internal.Fused.termComplete posture next h declarations context levels term k := by
  unfold Parser.Category.Term.Internal.termComplete Parser.Internal.Fused.termComplete
  rcases levels with _ | ⟨level, outer⟩
  · simp [termCont]
  · cases level with
    | matchScrutinee =>
      simp only []
      rw [run_call_bind, bind_assoc]
      unfold runHandler
      congr 1
      funext ⟨r, h'⟩
      cases r <;> simp [termCont, fail]
    | _ => simp [termCont]

theorem handleTerm_eq (posture : VersionPosture) {batch : BatchTag} (next : LexerCursor batch)
    (h : H) (declarations : Nat) (context : TermContext (Handler.«Sort» H))
    (levels : List (TermLevelOf H)) (node : Grammar.Nodes.Term (Handler.«Sort» H) (Handler.Term H))
    {β : Type} (k : OutcomeOf H next → m β) :
    (call (Handler.handleTerm node) >>= fun term =>
          Parser.Category.Term.Internal.termComplete levels term).run.run h >>=
        termCont posture declarations context next k =
      Parser.Internal.Fused.handleTerm posture next h declarations context levels node k := by
  unfold Parser.Internal.Fused.handleTerm runHandler
  rw [run_call_bind, bind_assoc]
  congr 1
  funext ⟨r, h'⟩
  cases r <;> simp [termCont, fail, termComplete_eq]

theorem termStep_eq (posture : VersionPosture) {batch : BatchTag} (h : H) (declarations : Nat)
    (context : TermContext (Handler.«Sort» H)) (mode : TermModeOf H)
    (levels : List (TermLevelOf H)) (token : LexerToken batch) (next : LexerCursor batch) {β : Type}
    (k : OutcomeOf H next → m β) :
    Parser.Internal.Fused.termStep posture h declarations context mode levels token next k =
      portTermStep posture h declarations context { mode, levels } token next k := by
  unfold Parser.Internal.Fused.termStep
  cases mode with
  | letBindingsOpen =>
    rw [portTermStep_eq]
    unfold Parser.Category.Term.Internal.termStep
    simp only [inputOf]
    cases next.category token <;> simp only [Token.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Lexicon.Reserved.fromBytes? (next.content token) next.version with
        _ | (w | w)) <;>
      simp [termCont, fail, Parser.Category.Token.Internal.expectOpen, syntaxError]
  | letBindingClose bindings =>
    rw [portTermStep_eq]
    unfold Parser.Category.Term.Internal.termStep
    simp only [inputOf]
    cases next.category token <;> simp only [Token.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Lexicon.Reserved.fromBytes? (next.content token) next.version with
        _ | (w | w)) <;>
      simp [termCont, fail, Parser.Category.Token.Internal.expectClose, syntaxError]
  | letBindingSymbol bindings =>
    rw [portTermStep_eq]
    unfold Parser.Category.Term.Internal.termStep
    simp only [Category.symbolOf?, Reserved.contentOf_eq, Reserved.reservedAt_eq, inputOf]
    cases next.category token <;> simp only [Token.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Lexicon.Reserved.fromBytes? (next.content token) next.version with
        _ | (w | w)) <;>
      simp [termCont, fail, Parser.Category.Token.Internal.expectSymbol, syntaxError]
  | letBindingOpen bindings =>
    rw [portTermStep_eq]
    unfold Parser.Category.Term.Internal.termStep
    simp only [inputOf]
    cases next.category token <;> simp only [Token.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Lexicon.Reserved.fromBytes? (next.content token) next.version with
        _ | (w | w)) <;>
      simp [termCont, fail, syntaxError]
    all_goals
      by_cases hb : bindings = #[]
      · simp [hb, termCont, fail]
      · simp only [hb, ite_false]
        rw [run_call_map, bind_assoc]
        unfold runHandler
        congr 1
        funext ⟨r, h'⟩
        cases r <;> simp [termCont, fail]
  | binderClose kind scope body =>
    rw [portTermStep_eq]
    unfold Parser.Category.Term.Internal.termStep
    simp only [inputOf]
    cases next.category token <;> simp only [Token.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Lexicon.Reserved.fromBytes? (next.content token) next.version with
        _ | (w | w)) <;>
      simp [termCont, fail, syntaxError, Parser.Category.Token.Internal.expectClose]
    all_goals
      rcases kind with _ | (_ | _) <;>
        simp only [Parser.Category.Term.Internal.endBinder] <;>
        rw [run_call_bind, bind_assoc] <;>
        unfold runHandler <;>
        congr 1 <;>
        funext ⟨r, h'⟩ <;>
        cases r <;> simp [termCont, fail, termComplete_eq]
  | start =>
    rw [portTermStep_eq]
    unfold Parser.Category.Term.Internal.termStep
    simp only [Reserved.contentOf_eq, Reserved.reservedAt_eq, inputOf]
    cases next.category token <;> simp only [Token.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Lexicon.Reserved.fromBytes? (next.content token) next.version with
        _ | (w | w)) <;>
      simp [termCont, fail, syntaxError, constantOf, ← handleTerm_eq]
    all_goals
      (rcases levels with _ | ⟨level, outer⟩ <;> (try cases level) <;> simp [termCont, fail])
    all_goals (split <;> simp_all [termCont, fail])
  | opened =>
    rw [portTermStep_eq]
    unfold Parser.Category.Term.Internal.termStep Parser.Category.Term.Internal.termOpened
    simp only [Reserved.contentOf_eq, Reserved.reservedAt_eq, inputOf]
    cases next.category token <;> simp only [Token.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Lexicon.Reserved.fromBytes? (next.content token) next.version with
        _ | (w | w)) <;>
      simp [termCont, fail, syntaxError]
    all_goals (cases w <;> simp [termCont, fail])
  | qualIdent state =>
    simp only []
    cases hq : Category.qualIdentStep next.version state (next.category token) next token with
    | none => simp only []
    | some r =>
      rw [portTermStep_eq]
      unfold Parser.Category.Term.Internal.termStep
      simp only []
      rw [run_bind_eq, qualIdentStep_run next.version state next token h r hq]
      cases r <;> simp [qualToRun, termCont, fail, ← handleTerm_eq]
  | applicationHead state =>
    simp only []
    cases hq : Category.qualIdentStep next.version state (next.category token) next token with
    | none => simp only []
    | some r =>
      rw [portTermStep_eq]
      unfold Parser.Category.Term.Internal.termStep
      simp only []
      rw [run_bind_eq, qualIdentStep_run next.version state next token h r hq]
      cases r <;> simp [qualToRun, termCont, fail]
  | sortedVars binder state =>
    rw [portTermStep_eq]
    unfold Parser.Category.Term.Internal.termStep
    simp only [Category.sortedVarsStepOutlined]
    rw [run_bind_eq, sortedVarsStep_run, bind_map_left, bind_assoc]
    congr 1
    funext o
    cases o with
    | more h' state => simp [HandledOutcome.toRun, termCont]
    | error h' cause => simp [HandledOutcome.toRun, termCont, fail]
    | done h' variables =>
      by_cases hv : variables.isEmpty = true
      · cases binder <;> simp [HandledOutcome.toRun, termCont, fail, hv, syntaxError]
      · cases binder <;>
          simp only [HandledOutcome.toRun, hv, Bool.false_eq_true, ite_false,
            Parser.Category.Term.Internal.startBinder] <;>
          rw [run_call_bind, bind_assoc] <;> unfold runHandler <;> congr 1 <;>
          funext ⟨r, h''⟩ <;> cases r <;> simp [termCont, fail]
  | _ => rfl

end BSmtLib.Facts.Proofs.Parser.Fused.Term
