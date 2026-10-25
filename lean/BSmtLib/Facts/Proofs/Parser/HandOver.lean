module

public import BSmtLib.Facts.Parser.Adapters.Handler
import all BSmtLib.Parser
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# The loop over single tokens of a parser that does not hand its cursor over

A parser stepped by single tokens may, in a state, hand its cursor to a parser it holds
(`Parser.Internal.ParseByToken.handOver?`). Where it does not, the loop over single tokens takes
the cursor's next token (`rest_of_none`, `parseByToken_of_none`); a parser that does in no state
(`NoHandOver`) is taken token by token throughout.
-/

namespace BSmtLib.Facts.Proofs.Parser.HandOver

open BSmtLib.Parser (ParseError ParseState)
open BSmtLib.Parser.Internal (ParseByToken takeOne rest parseByToken not_hasNext)

/-- The parser hands its cursor over in no state, on no cursor. -/
def NoHandOver (P : Type) {H : Type} {m : Type → Type} {E R : Type}
    [ParseByToken P H m E R] : Prop :=
  ∀ {Z : Type} [Token.Cursor Z] (parser : P) (cursor : Z),
    ParseByToken.handOver? parser cursor = none

variable {H P R E : Type} {m : Type → Type} [Monad m] [ParseByToken P H m E R]
variable {Z : Type} [Token.Cursor Z]

/-- The loop, from a parser that does not hand the cursor over: it takes the next token. -/
theorem rest_of_none {origin : Z} {parser : P} {cursor : Z}
    (consumed : Token.Cursor.Consumed cursor origin)
    (h : ParseByToken.handOver? parser cursor = none) :
    rest (m := m) origin parser cursor consumed =
      match Token.Cursor.next? cursor with
      | none => return (.ok .continue, parser, ⟨cursor, consumed⟩)
      | some (token, ⟨next, step⟩) => do
        match ← takeOne parser cursor token next step with
        | (.goOn parser, ⟨later, taken⟩) =>
          rest origin parser later (Token.Cursor.consumed_trans taken consumed)
        | (.stop answer parser, ⟨later, taken⟩) =>
          return (answer, parser, ⟨later, Token.Cursor.consumed_trans taken consumed⟩) := by
  rw [rest, h]
  rfl

/-- The parse, from a parser that does not hand the cursor over: it takes the next token. -/
theorem parseByToken_of_none {parser : P} (state : ParseState H) {cursor : Z}
    (h : ParseByToken.handOver? parser cursor = none) :
    parseByToken (m := m) parser state cursor =
      match hn : Token.Cursor.next? cursor with
      | none =>
        return (.ok .continue, parser, state, ⟨cursor, fun has => absurd has (not_hasNext hn)⟩)
      | some (token, ⟨next, consumed⟩) => do
        match ← takeOne parser cursor token next consumed with
        | (.goOn parser, ⟨later, taken⟩) =>
          let (answer, parser, ⟨done, hd⟩) ← rest cursor parser later taken
          return (answer, parser, state, ⟨done, fun _ => hd⟩)
        | (.stop answer parser, ⟨later, taken⟩) =>
          return (answer, parser, state, ⟨later, fun _ => taken⟩) := by
  rw [parseByToken, h]
  rfl

/-- The script parser of a handler that has no parser of a non-standard command hands no cursor
over. -/
theorem script_noHandOver {H : Type} {m : Type → Type} [Monad m] [Handler.CommandHandler H m]
    (empty : Handler.CommandHandler.NonstandardParser H → False) :
    NoHandOver (Parser.Script.ScriptParser H) := by
  intro Z _ parser cursor
  show Parser.Script.ScriptParser.Internal.handOver? parser cursor = none
  unfold Parser.Script.ScriptParser.Internal.handOver?
  split
  · rename_i nonstandard _
    exact (empty nonstandard).elim
  · rfl

/-- A script parser not in a non-standard command hands no cursor over. -/
theorem script_handOver_none {H : Type} {m : Type → Type} [Monad m] [Handler.CommandHandler H m]
    {parser : Parser.Script.ScriptParser H}
    (h : ∀ nonstandard,
      Parser.Script.ScriptParser.Internal.command parser ≠ .nonstandard nonstandard)
    (cursor : Z) : ParseByToken.handOver? parser cursor = none := by
  show Parser.Script.ScriptParser.Internal.handOver? parser cursor = none
  unfold Parser.Script.ScriptParser.Internal.handOver?
  split
  · rename_i nonstandard heq
    exact (h nonstandard heq).elim
  · rfl

/-- The recording handler has no parser of a non-standard command, so its script parser takes
every cursor token by token. -/
theorem recording_noHandOver :
    NoHandOver (Parser.Script.ScriptParser (List BSmtLibSpec.Parser.Properties.Event)) :=
  script_noHandOver fun e => Empty.elim e

end BSmtLib.Facts.Proofs.Parser.HandOver
