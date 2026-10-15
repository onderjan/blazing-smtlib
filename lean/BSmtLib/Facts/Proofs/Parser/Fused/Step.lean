module

public import BSmtLib.Facts.Proofs.Parser.Fused.Adapter
public import BSmtLib.Facts.Proofs.Parser.Fused.Term
public import BSmtLib.Facts.Proofs.Parser.Fused.Command
import all BSmtLib.Parser.Internal.Fused

@[expose] public section

/-!
# The fused reader's step and consumer

The fused step of every token simulates the step of the script parser's loop over single tokens
(`stepSimulates`), from the term step and the command step; so the script parser's `parse` on a
batch cursor, the fused reader, is that loop (`parse_eq`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Fused.Step

open BSmtLib.Traits
open BSmtLib.Parser (Parse PM call syntaxError ParseErrorCause)
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

/-! ## The parse -/

/-- The fused reader parses a batch cursor as the script parser's loop over single tokens does:
the same answer, parser, parse state, cursor and handler, in every lawful monad, with every
handler, on every cursor. -/
theorem parse_eq {batch : BatchTag} (parser : ScriptParser H) (state : Parser.ParseState H)
    (producer : BatchCursor batch) :
    Parse.parse
        (m := m) parser state producer = Parser.Internal.parseByToken parser state producer :=
  Loop.parse_eq stepSimulates parser state producer

end BSmtLib.Facts.Proofs.Parser.Fused.Step
