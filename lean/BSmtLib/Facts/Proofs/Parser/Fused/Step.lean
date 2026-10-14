module

public import BSmtLib.Facts.Proofs.Parser.Fused.Adapter
public import BSmtLib.Facts.Proofs.Parser.Fused.Term
public import BSmtLib.Facts.Proofs.Parser.Fused.Command
import all BSmtLib.Parser.Internal.Fused

@[expose] public section

/-!
# The fused reader's step and consumer

The fused step of every token simulates the parse adapter's (`stepSimulates`), from the term step
and the command step; so the fused reader's consumer is the parse adapter's (`consume_eq`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Fused.Step

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
open BSmtLib.Facts.Proofs.Parser.Fused.Adapter
open BSmtLib.Facts.Proofs.Parser.Fused.Term
open BSmtLib.Facts.Proofs.Parser.Fused.Command

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [CommandHandler H m]

/-! ## The step -/

/-- The fused step of every token simulates the adapter's. -/
theorem stepSimulates : StepSimulates H m := by
  intro posture batch origin next h declarations command inTerm context mode levels token
    consumed β k
  cases inTerm with
  | true =>
    simp only [step, ite_true]
    rw [termStep_eq, ← portStep_withTerm, takeOne_eq_portStep]
    rfl
  | false =>
    simp only [step, Bool.false_eq_true, ite_false]
    rw [commandStep_eq, takeOne_eq_portStep]
    rfl

/-! ## The consumer -/

/-- The fused reader's consumer is the parse adapter's: the same answer, cursor, parser and
handler, in every lawful monad, with every handler, on every cursor. -/
theorem consume_eq {batch : BatchTag} (producer : BatchCursor batch)
    (hp : Produce.HasNext producer) (adapter : ParseAdapter H (ScriptParser H)) :
    (Token.ConsumeFrom.consume (H := ScriptAdapter H) (m := m) producer hp).run ⟨adapter⟩ =
      (fun (out, adapter) => (out, (⟨adapter⟩ : ScriptAdapter H))) <$>
        (Token.ConsumeFrom.consume (H := ParseAdapter H (ScriptParser H)) (m := m) producer
          hp).run adapter :=
  Loop.consume_eq stepSimulates producer hp adapter

end BSmtLib.Facts.Proofs.Parser.Fused.Step
