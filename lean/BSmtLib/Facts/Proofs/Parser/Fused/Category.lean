module

public import BSmtLib.Facts.Proofs.Parser.Fused.Run
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Category.Ident
import all BSmtLib.Parser.Category.QualifiedIdent
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Category.SortedVar
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Command.Internal.Function
import all BSmtLib.Parser.Internal.Fused.Basic
import all BSmtLib.Parser.Internal.Fused.Category
import all BSmtLib.Token.SyntaxToken

@[expose] public section

/-!
# The fused category steps against the port's

Each category step of the fused reader, on the token's category, gives what the port's step gives
on the token as the port views it, run on the handler: identifiers, sorts, lists of sorts, sorted
variables and their lists, signatures, and qualified identifiers in parentheses without `as`. The
proofs go by the state, then by the token's category and the reserved word it spells.
-/

namespace BSmtLib.Facts.Proofs.Parser.Fused.Category

open BSmtLib.Traits
open BSmtLib.Parser (Parse ParseErrorCause)
open BSmtLib.Parser.Internal (PM call syntaxError)
open BSmtLib.Parser.Internal.Fused
open BSmtLib.Parser.Internal.Fused.Basic
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Token (BatchTag BatchCursor Produce VersionPosture)
open BSmtLib.Facts.Proofs.Parser.Fused.Run

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [CommandHandler H m]

omit [LawfulMonad m] in
theorem identStep_run {batch : BatchTag} (version : Token.Version)
    (s : Parser.Category.Ident.Internal.IdentState)
    (next : BatchCursor batch) (token : Token batch) (h : H) :
    (Parser.Category.Ident.Internal.IdentState.step (H := H) version s
        (inputOf version next token)).run.run h =
      pure (PureOutcome.toRun (Category.identStep version s (next.category token) next token),
        h) := by
  simp only [Category.identStep, Category.symbolOf?, Category.isWord,
    Reserved.contentOf_eq, Reserved.reservedAt_eq, inputOf]
  generalize next.category token = cat
  generalize next.content token = c
  cases s <;> cases cat <;> simp only [Token.SyntaxToken.Internal.fromParts,
      Parser.Internal.Input.ofSyntax] <;>
    (try rcases Token.Reserved.fromBytes? c version with _ | (w | w)) <;>
    simp [Parser.Category.Ident.Internal.IdentState.step,
      PureOutcome.toRun, syntaxError, Parser.Internal.Input.isWord]
  all_goals (split <;> simp_all)

theorem sortComplete_run
    (levels : List (Parser.Category.Sort.Internal.SortLevel (Handler.«Sort» H)))
    (head : Nodes.Identifier) (arguments : Array (Handler.«Sort» H)) (h : H) :
    (Parser.Category.Sort.Internal.sortComplete levels head arguments).run.run h =
      HandledOutcome.toRun <$> Category.sortComplete h levels head arguments := by
  unfold Parser.Category.Sort.Internal.sortComplete Category.sortComplete runHandler
  rw [run_call_bind, map_bind]
  congr 1
  funext ⟨r, h'⟩
  cases r with
  | error e => simp [HandledOutcome.toRun]
  | ok sort => cases levels <;> simp [HandledOutcome.toRun]

theorem sortStep_run {batch : BatchTag} (version : Token.Version)
    (s : Parser.Category.Sort.Internal.SortState (Handler.«Sort» H))
    (next : BatchCursor batch) (token : Token batch) (h : H) :
    (Parser.Category.Sort.Internal.sortStep version s (inputOf version next token)).run.run h =
      HandledOutcome.toRun <$> Category.sortStep version h s (next.category token) next token := by
  obtain ⟨mode, levels⟩ := s
  unfold Parser.Category.Sort.Internal.sortStep Category.sortStep
  cases mode with
  | identOnly ident =>
    simp only []
    rw [run_bind_eq, identStep_run]
    cases Category.identStep version ident (next.category token) next token <;>
      simp [PureOutcome.toRun, HandledOutcome.toRun, sortComplete_run]
  | startingIdent ident =>
    simp only []
    rw [run_bind_eq, identStep_run]
    cases Category.identStep version ident (next.category token) next token <;>
      simp [PureOutcome.toRun, HandledOutcome.toRun]
  | start =>
    simp only [Category.symbolOf?, Reserved.contentOf_eq, Reserved.reservedAt_eq,
      inputOf]
    generalize next.category token = cat
    generalize next.content token = c
    cases cat <;> simp only [Token.SyntaxToken.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Token.Reserved.fromBytes? c version with _ | (w | w)) <;>
      simp [HandledOutcome.toRun, sortComplete_run, syntaxError]
    all_goals (cases levels <;> simp [HandledOutcome.toRun]) <;>
      (split <;> simp_all [HandledOutcome.toRun, sortComplete_run])
  | opened =>
    simp only [Category.symbolOf?, Category.isWord, Reserved.contentOf_eq, Reserved.reservedAt_eq,
      inputOf]
    generalize next.category token = cat
    generalize next.content token = c
    cases cat <;> simp only [Token.SyntaxToken.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Token.Reserved.fromBytes? c version with _ | (w | w)) <;>
      simp [HandledOutcome.toRun, syntaxError, Parser.Internal.Input.isWord]
    all_goals (split <;> simp_all [HandledOutcome.toRun])

theorem sortsStep_run {batch : BatchTag} (version : Token.Version)
    (s : Parser.Category.Combinator.Internal.ListState (Category.SortStateOf H) (Handler.«Sort» H))
    (next : BatchCursor batch) (token : Token batch) (h : H) :
    (Parser.Category.Combinator.Internal.ListState.step .init
        (Parser.Category.Sort.Internal.sortStep version) none s
        (inputOf version next token)).run.run h =
      HandledOutcome.toRun <$> Category.sortsStep version h s (next.category token) next token := by
  obtain ⟨opened, outside, inner, items⟩ := s
  unfold Parser.Category.Combinator.Internal.ListState.step Category.sortsStep
  cases opened with
  | false =>
    simp only [inputOf]
    generalize next.category token = cat
    cases cat <;> simp only [Token.SyntaxToken.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Token.Reserved.fromBytes? (next.content token) version with _ | (w | w)) <;>
      simp [HandledOutcome.toRun, Parser.Category.Token.Internal.expectOpen, syntaxError]
  | true =>
    by_cases hc : next.category token = .parenClose
    · cases outside with
      | true =>
        have := (inputOf_parenClose version next token).mpr hc
        simp [this, hc, HandledOutcome.toRun, beq_parenClose]
      | false =>
        simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.false_and]
        rw [run_bind_eq, sortStep_run, bind_map_left, map_bind]
        congr 1
        funext o
        cases o <;> simp [HandledOutcome.toRun]
    · cases outside with
      | true =>
        have hne := fun e => hc ((inputOf_parenClose version next token).mp e)
        simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true, beq_parenClose_of_ne hc,
          Bool.true_and]
        rw [run_bind_eq, sortStep_run, bind_map_left, map_bind]
        congr 1
        funext o
        cases o <;> simp [HandledOutcome.toRun]
      | false =>
        simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.false_and]
        rw [run_bind_eq, sortStep_run, bind_map_left, map_bind]
        congr 1
        funext o
        cases o <;> simp [HandledOutcome.toRun]

theorem sortedVarStep_run {batch : BatchTag} (version : Token.Version)
    (s : Category.SortedVarOf H) (next : BatchCursor batch) (token : Token batch) (h : H) :
    (Parser.Category.SortedVar.Internal.sortedVarStep version s
        (inputOf version next token)).run.run h =
      HandledOutcome.toRun <$>
        Category.sortedVarStep version h s (next.category token) next token := by
  unfold Parser.Category.SortedVar.Internal.sortedVarStep Category.sortedVarStep
  cases s with
  | sort symbol sort =>
    simp only []
    rw [run_bind_eq, sortStep_run, bind_map_left, map_bind]
    congr 1
    funext o
    cases o <;> simp [HandledOutcome.toRun]
  | _ =>
    simp only [Category.symbolOf?, Reserved.contentOf_eq, Reserved.reservedAt_eq, inputOf]
    generalize next.category token = cat
    cases cat <;> simp only [Token.SyntaxToken.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Token.Reserved.fromBytes? (next.content token) version with _ | (w | w)) <;>
      simp [HandledOutcome.toRun, Parser.Category.Token.Internal.expectOpen,
        Parser.Category.Token.Internal.expectClose, Parser.Category.Token.Internal.expectSymbol,
            syntaxError]
theorem sortedVarsStep_run {batch : BatchTag} (version : Token.Version)
    (s : Category.SortedVarsOf H)
    (next : BatchCursor batch) (token : Token batch) (h : H) :
    (Parser.Category.Combinator.Internal.ListState.step .start
        (Parser.Category.SortedVar.Internal.sortedVarStep version) none s
        (inputOf version next token)).run.run h =
      HandledOutcome.toRun <$>
        Category.sortedVarsStep version h s (next.category token) next token := by
  obtain ⟨opened, outside, inner, items⟩ := s
  unfold Parser.Category.Combinator.Internal.ListState.step Category.sortedVarsStep
  cases opened with
  | false =>
    simp only [inputOf]
    generalize next.category token = cat
    cases cat <;> simp only [Token.SyntaxToken.Internal.fromParts,
        Parser.Internal.Input.ofSyntax] <;>
      (try rcases Token.Reserved.fromBytes? (next.content token) version with _ | (w | w)) <;>
      simp [HandledOutcome.toRun, Parser.Category.Token.Internal.expectOpen, syntaxError]
  | true =>
    by_cases hc : next.category token = .parenClose
    · cases outside with
      | true =>
        have := (inputOf_parenClose version next token).mpr hc
        simp [this, hc, HandledOutcome.toRun, beq_parenClose]
      | false =>
        simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.false_and]
        rw [run_bind_eq, sortedVarStep_run, bind_map_left, map_bind]
        congr 1
        funext o
        cases o <;> simp [HandledOutcome.toRun]
    · cases outside with
      | true =>
        have hne := fun e => hc ((inputOf_parenClose version next token).mp e)
        simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true, beq_parenClose_of_ne hc,
          Bool.true_and]
        rw [run_bind_eq, sortedVarStep_run, bind_map_left, map_bind]
        congr 1
        funext o
        cases o <;> simp [HandledOutcome.toRun]
      | false =>
        simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.false_and]
        rw [run_bind_eq, sortedVarStep_run, bind_map_left, map_bind]
        congr 1
        funext o
        cases o <;> simp [HandledOutcome.toRun]

theorem signatureStep_run {batch : BatchTag} (version : Token.Version)
    (s : Parser.Command.Internal.Function.SignatureState (Handler.«Sort» H))
    (next : BatchCursor batch)
    (token : Token batch) (h : H) :
    (Parser.Command.Internal.Function.signatureStep version s
        (inputOf version next token)).run.run h =
      HandledOutcome.toRun <$>
        Category.signatureStep version h s (next.category token) next token := by
  unfold Parser.Command.Internal.Function.signatureStep Category.signatureStep
  cases s with
  | start =>
    simp only [Category.symbolOf?, Reserved.contentOf_eq, Reserved.reservedAt_eq, inputOf]
    cases next.category token <;>
      simp only [Token.SyntaxToken.Internal.fromParts, Parser.Internal.Input.ofSyntax] <;>
      (try rcases Token.Reserved.fromBytes? (next.content token) version with _ | (w | w)) <;>
      simp [HandledOutcome.toRun, Parser.Category.Token.Internal.expectSymbol, syntaxError]
  | parameters symbol state =>
    simp only []
    rw [run_bind_eq, sortedVarsStep_run, bind_map_left, map_bind]
    congr 1
    funext o
    cases o <;> simp [HandledOutcome.toRun]
  | result symbol parameters state =>
    simp only []
    rw [run_bind_eq, sortStep_run, bind_map_left, map_bind]
    congr 1
    funext o
    cases o <;> simp [HandledOutcome.toRun]

theorem qualIdentStep_run {batch : BatchTag} (version : Token.Version)
    (s : Parser.Category.QualifiedIdent.Internal.QualIdentState (Handler.«Sort» H))
    (next : BatchCursor batch) (token : Token batch) (h : H)
    (r : Category.PureOutcome
        (Parser.Category.QualifiedIdent.Internal.QualIdentState (Handler.«Sort» H))
      Nodes.Identifier)
    (fused : Category.qualIdentStep (H := H) version s (next.category token) next token = some r) :
    (Parser.Category.QualifiedIdent.Internal.qualIdentStep (H := H) version s
        (inputOf version next token)).run.run h = pure (qualToRun (H := H) r, h) := by
  unfold Parser.Category.QualifiedIdent.Internal.qualIdentStep
  unfold Category.qualIdentStep at fused
  cases s with
  | opened =>
    simp only [] at fused ⊢
    rw [inputOf_isWord, inputOf_isWord]
    revert fused
    cases Category.isWord version (next.category token) next token .underscore <;>
      cases Category.isWord version (next.category token) next token .as <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, Option.some.injEq] <;>
      intro e <;> subst e <;> simp [qualToRun, syntaxError]
  | indexed ident =>
    simp only [] at fused ⊢
    rw [run_bind_eq, identStep_run]
    revert fused
    cases Category.identStep version ident (next.category token) next token <;>
      intro e <;> simp only [Option.some.injEq] at e <;> subst e <;>
      simp [PureOutcome.toRun, qualToRun]
  | _ => cases fused

end BSmtLib.Facts.Proofs.Parser.Fused.Category
