module

public import BSmtLib.Facts.Proofs.Parser.Fused.Loop
public import BSmtLib.Facts.Proofs.Parser.Fused.Reserved
import all BSmtLib.Parser
import all BSmtLib.Parser.Internal.Fused.Category
import all BSmtLib.Token
import all BSmtLib.Token.SyntaxToken

@[expose] public section

/-!
# Runs of the port's parser calls

What the proofs of the fused reader share: a parser program of the port run on the handler, bound
to what follows it (`run_bind_eq`, `run_call_bind`, `run_call_map`); the fused category steps'
outcomes read as the port's results (`PureOutcome.toRun`, `HandledOutcome.toRun`, `qualToRun`);
and the token as the port views it, by its category and content (`inputOf`), with the facts about
it that the fused steps read from the category alone.
-/

namespace BSmtLib.Facts.Proofs.Parser.Fused.Run

open BSmtLib.Traits
open BSmtLib.Parser (Parse ParseError ParseErrorCause)
open BSmtLib.Parser.Internal (PM call syntaxError)
open BSmtLib.Parser.Internal.Fused
open BSmtLib.Parser.Internal.Fused.Basic
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Token (BatchTag BatchCursor Produce VersionPosture)

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [CommandHandler H m]

omit [LawfulMonad m] in
theorem run_bind_eq {α γ : Type} (x : PM H α) (f : α → PM H γ) (h : H) :
    (x >>= f).run.run h = x.run.run h >>= fun p => match p.1 with
      | .ok a => (f a).run.run p.2
      | .error e => pure (.error e, p.2) := by
  simp only [ExceptT.run_bind, StateT.run_bind]
  congr 1
  funext ⟨r, h'⟩
  cases r <;> simp

/-! ## The category parsers -/

/-- A pure outcome of a fused category step, as the port's step gives it. -/
def PureOutcome.toRun {σ ρ ε : Type} :
    Category.PureOutcome σ ρ → Except (ParseErrorCause ε) (Parser.Internal.Step σ ρ)
  | .more state => .ok (.more state)
  | .done result => .ok (.done result)
  | .error kind => .error (.syntax kind)

/-- A handled outcome of a fused category step, as the port's step gives it. -/
def HandledOutcome.toRun {σ ρ ε : Type} :
    Category.HandledOutcome H σ ρ ε → Except ε (Parser.Internal.Step σ ρ) × H
  | .more h state => (.ok (.more state), h)
  | .done h result => (.ok (.done result), h)
  | .error h cause => (.error cause, h)

/-- The token as the port views it, by its category and content. -/
abbrev inputOf {batch : BatchTag} (version : Token.Version) (next : BatchCursor batch)
    (token : Token batch) : Parser.Internal.Input :=
  Parser.Internal.Input.ofSyntax (Token.SyntaxToken.Internal.fromParts (next.category token)
      (next.content token) version)

theorem run_call {α : Type} (x : ExceptT (Handler.Error H) (StateT H m) α) (h : H) :
    (call x).run.run h = (fun p => (p.1.mapError .handler, p.2)) <$> x.run.run h := by
  simp only [call, ExceptT.adapt, ExceptT.run_mk, StateT.run_map]
  rfl

theorem run_call_bind {α γ : Type} (x : ExceptT (Handler.Error H) (StateT H m) α)
    (f : α → PM H γ) (h : H) :
    (call x >>= f).run.run h = x.run.run h >>= fun p => match p.1 with
      | .ok a => (f a).run.run p.2
      | .error e => pure (.error (.handler e), p.2) := by
  simp only [call, ExceptT.adapt, ExceptT.run_bind, ExceptT.run_mk, StateT.run_bind]
  rw [StateT.run_map, bind_map_left]
  congr 1
  funext ⟨r, h'⟩
  cases r <;> simp [Except.mapError]

omit [Monad m] [LawfulMonad m] [CommandHandler H m] in
theorem inputOf_parenClose {batch : BatchTag} (version : Token.Version) (next : BatchCursor batch)
    (token : Token batch) :
    inputOf version next token = .parenClose ↔ next.category token = .parenClose := by
  simp only [inputOf]
  generalize next.category token = cat
  cases cat <;> simp only [Token.SyntaxToken.Internal.fromParts, Parser.Internal.Input.ofSyntax] <;>
    (try rcases Token.Reserved.fromBytes? (next.content token) version with _ | (w | w)) <;>
    simp

omit [Monad m] [LawfulMonad m] [CommandHandler H m] in
theorem beq_parenClose_of_ne {category : Token.TokenCategory} (hc : category ≠ .parenClose) :
    (category == .parenClose) = false := by
  cases category <;> first | rfl | exact absurd rfl hc

omit [Monad m] [LawfulMonad m] [CommandHandler H m] in
theorem beq_parenClose : (Token.TokenCategory.parenClose == .parenClose) = true := (rfl)

omit [Monad m] [LawfulMonad m] [CommandHandler H m] in
theorem inputOf_isWord {batch : BatchTag} (version : Token.Version) (next : BatchCursor batch)
    (token : Token batch) (word : Token.Reserved.GeneralReserved) :
    (inputOf version next token).isWord word =
      Category.isWord version (next.category token) next token word := by
  simp only [Category.isWord, Reserved.reservedAt_eq, inputOf]
  cases next.category token <;> simp only [Token.SyntaxToken.Internal.fromParts,
      Parser.Internal.Input.ofSyntax] <;>
    (try rcases Token.Reserved.fromBytes? (next.content token) version with _ | (w | w)) <;>
    rfl

/-- A pure outcome of the fused step of a qualified identifier, as the port's step gives it. -/
def qualToRun {σ ε : Type} :
    Category.PureOutcome σ Nodes.Identifier →
      Except (ParseErrorCause ε) (Parser.Internal.Step σ (Nodes.Identifier × Option
          (Handler.«Sort» H)))
  | .more state => .ok (.more state)
  | .done identifier => .ok (.done (identifier, none))
  | .error kind => .error (.syntax kind)

theorem run_call_map {α γ : Type} (x : ExceptT (Handler.Error H) (StateT H m) α)
    (f : α → γ) (h : H) :
    (f <$> call x : PM H γ).run.run h = x.run.run h >>= fun p => match p.1 with
      | .ok a => pure (.ok (f a), p.2)
      | .error e => pure (.error (.handler e), p.2) := by
  rw [map_eq_pure_bind, run_call_bind]
  simp only [ExceptT.run_pure, StateT.run_pure]

end BSmtLib.Facts.Proofs.Parser.Fused.Run
