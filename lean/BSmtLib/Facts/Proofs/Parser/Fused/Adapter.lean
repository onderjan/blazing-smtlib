module

public import BSmtLib.Facts.Proofs.Parser.Fused.Run
import all BSmtLib.Parser
import all BSmtLib.Parser
import all BSmtLib.Parser.Command
import all BSmtLib.Parser.Command.Standard
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

open BSmtLib.Traits
open BSmtLib.Parser (Parse PM call syntaxError ParseErrorCause)
open BSmtLib.Parser.Category.Term (TermLevelOf TermStateOf)
open BSmtLib.Parser.Command (CommandStateOf)
open BSmtLib.Parser.Internal.Fused
open BSmtLib.Parser.Internal.Fused.Basic
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Token (BatchTag BatchCursor Produce VersionPosture)
open BSmtLib.Facts.Proofs.Parser.Fused.Loop
open BSmtLib.Facts.Proofs.Parser.Fused.Run

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [CommandHandler H m]

theorem takeOne_eq_portStep (parser : ScriptParser H) {batch : BatchTag}
    {origin next : BatchCursor batch} (h : H) (token : Token batch)
    (consumed : next.Consumed origin) {β : Type} (k : PortOut H origin → m β) :
    ((Parser.Internal.takeOne parser origin token next consumed).run h >>= k) =
      portStep parser.posture h parser.declarations parser.command token next
        (fun out => k (toPort parser.posture consumed out)) := by
  obtain ⟨posture, command, declarations⟩ := parser
  unfold Parser.Internal.takeOne portStep runParser
  simp only [StateT.run_bind, bind_assoc, Parser.Internal.ParseByToken.arrive,
      Parser.Internal.ParseByToken.step, Parser.Internal.ParseByToken.reset]
  unfold ScriptParser.step
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
        | endOfInput => simp [toPort]
        | exit => simp [toPort, Parser.Internal.resumed]; rfl
        | setVersion declared =>
          cases hc : Parser.Script.VersionPosture.check posture declarations declared with
          | some kind => simp [toPort, syntaxError, hc]
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
    {origin next : BatchCursor batch} (h : H) (declarations : Nat)
    (context : TermContext (Handler.«Sort» H)) (term : TermStateOf H) (token : Token batch)
    (consumed : next.Consumed origin) {β : Type} (k : PortOut H origin → m β) :
    portStep posture h declarations (withTerm context term) token next
        (fun out => k (toPort posture consumed out)) =
      portTermStep posture h declarations context term token next
        (fun out => k (toPort posture consumed out)) := by
  unfold portStep portTermStep runParser
  cases context with
  | assert =>
    simp only [withTerm, ScriptParser.arrive, Parser.Command.commandArrive,
      Parser.Command.Standard.payloadArrive, ScriptParser.step, Parser.Command.commandStep,
      Parser.Command.Standard.payloadStep, run_bind_eq, bind_assoc, pure_bind]
    congr 1
    funext ⟨r, h'⟩
    cases r with
    | error e => simp [fail]
    | ok s => cases s <;> simp [toPort, finishTerm, withTerm, assemble, closing]
  | definition d =>
    simp only [withTerm, ScriptParser.arrive, Parser.Command.commandArrive,
      Parser.Command.Standard.payloadArrive, ScriptParser.step, Parser.Command.commandStep,
      Parser.Command.Standard.payloadStep, run_bind_eq, bind_assoc, pure_bind]
    congr 1
    funext ⟨r, h'⟩
    cases r with
    | error e => simp [fail]
    | ok s => cases s <;> cases d <;> simp [toPort, finishTerm, withTerm, assemble, closing]

end BSmtLib.Facts.Proofs.Parser.Fused.Adapter
