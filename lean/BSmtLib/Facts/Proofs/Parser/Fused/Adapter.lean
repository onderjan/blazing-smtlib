module

public import BSmtLib.Facts.Proofs.Parser.Fused.Run
import all BSmtLib.Parser
import all BSmtLib.Parser
import all BSmtLib.Parser.Command
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Parser.Internal.Fused
import all BSmtLib.Parser.Internal.Fused.Basic
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# The parse adapter's token and the port's step

The parse adapter takes a token of the script parser as the fused reader's fallback does
(`takeOne_eq_portStep`), read through the loop's continuation (`toPort`): the step of the parser
keeps its posture whenever it goes on, which the loop holds as an argument of its own. In a
command's term, the port's script step is its term step (`portStep_withTerm`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Fused.Adapter

open BSmtLib.Handler
open BSmtLib.Parser (Parse ParseError ParseErrorCause)
open BSmtLib.Parser.Internal (PM call versionError)
open BSmtLib.Parser.Category.Term.Internal (TermLevelOf TermStateOf)
open BSmtLib.Parser.Internal.Fused
open BSmtLib.Parser.Internal.Fused.Basic
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Token (BatchTag Cursor)
open BSmtLib.Lexer.Cursor (LexerCursor LexerToken)
open BSmtLib.Version (VersionPosture)
open BSmtLib.Facts.Proofs.Parser.Fused.Loop
open BSmtLib.Facts.Proofs.Parser.Fused.Run

/- The script parser's constructor and readers, which `simp` unfolds here. -/
attribute [local simp] ScriptParser.Internal.mk ScriptParser.Internal.command
  ScriptParser.Internal.posture ScriptParser.Internal.declarations

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [CommandHandler H m]

theorem takeOne_eq_portStep (parser : ScriptParser H) {batch : BatchTag}
    {origin next : LexerCursor batch} (h : H) (token : LexerToken batch)
    (consumed : next.Consumed origin) {β : Type} (k : PortOut H origin → m β) :
    ((Parser.Internal.takeOne parser origin token next consumed).run h >>= k) =
      portStep (ScriptParser.Internal.posture parser) h (ScriptParser.Internal.declarations parser)
        (ScriptParser.Internal.command parser) token next
        (fun out => k (toPort (ScriptParser.Internal.posture parser) consumed out)) := by
  obtain ⟨posture, command, declarations⟩ := parser
  unfold Parser.Internal.takeOne portStep runParser
  simp only [StateT.run_bind, bind_assoc, Parser.Internal.ParseByToken.arrive,
      Parser.Internal.ParseByToken.step, Parser.Internal.ParseByToken.reset]
  unfold ScriptParser.Internal.step
  simp only [ScriptParser.Internal.posture, ScriptParser.Internal.command,
    ScriptParser.Internal.declarations, ScriptParser.Internal.mk,
    Parser.ParseError.Internal.new]
  simp only [run_bind_eq, bind_assoc]
  congr 1
  funext ⟨r, h'⟩
  cases r with
  | error e => simp [toPort]
  | ok u =>
    simp only [bind_assoc]
    congr 1
    funext ⟨r, h''⟩
    cases r with
    | error e => simp [toPort]
    | ok s =>
      cases s with
      | more c => simp [toPort]
      | done outcome =>
        cases outcome with
        | command => simp [toPort]
        | endOfFile => simp [toPort]
        | exit => simp [toPort, Parser.Internal.resumed]; rfl
        | setVersion declared =>
          cases hc : Parser.Script.Internal.VersionPosture.check posture declarations declared with
          | some kind => simp [toPort, versionError, hc]
          | none =>
            simp only [hc, ExceptT.run_pure, StateT.run_pure, pure_bind]
            split
            · split
              · simp [toPort]
              · rename_i a e1 s e2
                exact absurd (e1.symm.trans e2) (by simp)
            · split
              · rename_i s e1 a e2
                exact absurd (e1.symm.trans e2) (by simp)
              · rename_i s e1 s' e2
                have := Except.ok.inj (e1.symm.trans e2)
                subst this
                simp only [StateT.run_bind, bind_assoc]
                congr 1
                funext ⟨r, h'''⟩
                cases r with
                | error e => simp [toPort]
                | ok st => cases st <;> simp [toPort, Parser.Internal.resumed]

theorem portStep_withTerm (posture : VersionPosture) {batch : BatchTag}
    {origin next : LexerCursor batch} (h : H) (declarations : Nat)
    (context : TermContext (Handler.«Sort» H)) (term : TermStateOf H) (token : LexerToken batch)
    (consumed : next.Consumed origin) {β : Type} (k : PortOut H origin → m β) :
    portStep posture h declarations (withTerm context term) token next
        (fun out => k (toPort posture consumed out)) =
      portTermStep posture h declarations context term token next
        (fun out => k (toPort posture consumed out)) := by
  unfold portStep portTermStep runParser
  cases context with
  | assert =>
    simp only [withTerm, ScriptParser.Internal.arrive, Parser.Command.Internal.commandArrive,
      Parser.Command.Internal.Standard.payloadArrive, ScriptParser.Internal.step,
          Parser.Command.Internal.commandStep,
      Parser.Command.Internal.Standard.payloadStep, run_bind_eq, bind_assoc, pure_bind,
      ScriptParser.Internal.command_mk, ScriptParser.Internal.posture_mk,
      ScriptParser.Internal.declarations_mk]
    congr 1
    funext ⟨r, h'⟩
    cases r with
    | error e => simp [fail]
    | ok s => cases s <;> simp [toPort, finishTerm, withTerm, assemble, closing]
  | definition d =>
    simp only [withTerm, ScriptParser.Internal.arrive, Parser.Command.Internal.commandArrive,
      Parser.Command.Internal.Standard.payloadArrive, ScriptParser.Internal.step,
          Parser.Command.Internal.commandStep,
      Parser.Command.Internal.Standard.payloadStep, run_bind_eq, bind_assoc, pure_bind,
      ScriptParser.Internal.command_mk, ScriptParser.Internal.posture_mk,
      ScriptParser.Internal.declarations_mk]
    congr 1
    funext ⟨r, h'⟩
    cases r with
    | error e => simp [fail]
    | ok s => cases s <;> cases d <;> simp [toPort, finishTerm, withTerm, assemble, closing]

end BSmtLib.Facts.Proofs.Parser.Fused.Adapter
