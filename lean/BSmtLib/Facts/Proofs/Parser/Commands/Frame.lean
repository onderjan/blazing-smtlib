module

public import BSmtLib.Facts.Proofs.Parser.Commands.Datatypes
import all BSmtLib.Parser.Command

@[expose] public section

/-!
# The frame of a command

The command parser takes a command's `(`, the calls due at its arrival made between its arrival
and its processing, and its name; then it runs the payload parser of the command, which ends at
the command's `)`. `command_of_payload` is that frame: given what the payload parser does over
the tokens after the name, the command parser does the traversal's command.
-/

namespace BSmtLib.Facts.Proofs.Parser.Commands.Frame

open BSmtLibSpec.Grammar
open BSmtLib.Parser (PM)
open BSmtLib.Parser.Command (CommandState CommandOutcome commandStep)
open BSmtLib.Parser.Command.Standard (Payload FinalCall payloadStep finalCall)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Lemmas
open BSmtLib.Facts.Proofs.Parser.Reserved BSmtLib.Facts.Proofs.Parser.Tokens

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.CommandHandler H m]
variable {points : Points (StateT H m)} {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

omit [LawfulMonad m] in
/-- The command parser in a payload mode steps as the payload parser. -/
theorem commandStep_payload (payload : Parser.Command.Standard.PayloadOf H)
    (token : Parser.Internal.Input) :
    commandStep version (.payload payload) token =
      payloadStep version payload token >>=
        Parser.Internal.Step.wrap CommandState.payload fun outcome => pure (.done outcome) := by
  simp only [commandStep]
  congr 1
  funext step
  cases step <;> rfl

omit [LawfulMonad m] in
/-- The command parser in a payload mode has the payload parser's calls due at an arrival. -/
theorem commandArrive_payload (payload : Parser.Command.Standard.PayloadOf H)
    (token : Parser.Internal.Input) :
    Parser.Command.commandArrive (.payload payload) token = Parser.Command.Standard.payloadArrive
        payload token := (rfl)

variable (points version) in
/-- `Runs` of the payload parser, with its calls due at a token's arrival. -/
abbrev PayloadRuns {α : Type} (state : Parser.Command.Standard.PayloadOf H)
    (tokens : List Parser.Internal.Input)
    (program : PM H α) (next : α → PM H (Parser.Internal.Step (Parser.Command.Standard.PayloadOf H)
    CommandOutcome)) : Prop :=
  Runs points (payloadStep version) state tokens program next Parser.Command.Standard.payloadArrive

/-- A token standing for a command's name is that name. -/
theorem Parser.Internal.Input.received_commandName {token : Parser.Internal.Input}
    {name : Token.Reserved.CommandNameReserved}
    {s : String}
    (hname : Bridge.reserved (.commandName name) = BSmtLibSpec.Regex.chars s)
    (h : Bridge.received token = some (.token (word s))) :
    token = .reserved (.commandName name) := by
  apply Parser.Internal.Input.received_word
  rw [hname]
  exact h

/--
The frame of a command: if the payload parser, from the command's initial payload, reads the
tokens after the name with the effects of `program`, the command parser reads the whole command
with the opening's ticks, then `program`.
-/
theorem command_frame {name : Token.Reserved.CommandNameReserved} {s : String}
    (hname : Bridge.reserved (.commandName name) = BSmtLibSpec.Regex.chars s)
    {payload : List Parser.Internal.Input} {program : PM H Unit} {outcome : CommandOutcome}
    (hruns : PayloadRuns points version (Payload.init name version) payload program
      fun _ => pure (.done outcome))
    (rest : List Parser.Internal.Input) :
    drive points (commandStep version) .awaiting
        (.parenOpen :: .reserved (.commandName name) :: (payload ++ rest))
            Parser.Command.commandArrive =
      (do
        adaptRun (opening points s)
        program
        pure (some (outcome, rest))) := by
  have hembed := drive_embedA (points := points) (inner := payloadStep version)
    (outer := commandStep version) CommandState.payload (fun outcome => pure (.done outcome))
    commandStep_payload commandArrive_payload (Payload.init name version) (payload ++ rest)
  simp only [drive_cons', arrivalTick, Parser.Command.commandArrive, commandStep, resume_more,
      hembed,
    hruns rest]
  simp [opening, adaptRun_take (token := .reserved (.commandName name))
    (syntaxToken := word s) (by simp [Bridge.received, hname, word]),
    adaptRun_take (token := .parenOpen) rfl, tick, arriveAt, processAt, Bridge.received]

/--
A command against the traversal, from what its payload parser does: the command's tokens are
`(`, its name and the payload's tokens, then `)`; the traversal's command is the opening, then
the rest; and the payload parser, from the command's initial payload, reads the tokens standing
for the payload's and the `)` with the rest's effects.
-/
theorem command_of_payload (command : Tree.Command) {name : Token.Reserved.CommandNameReserved}
    {s : String}
    (hname : Bridge.reserved (.commandName name) = BSmtLibSpec.Regex.chars s)
    {payloadSyntax : List BSmtLibSpec.Grammar.SyntaxToken}
    (htokens : command.tokens = commandTokens s payloadSyntax)
    {rest : Run (StateT H m) (Traits.Handler.Error H) Unit}
    (hcommand : Traversal.command points h command = (do opening points s; rest))
    (hpayload : ∀ {payload : List Parser.Internal.Input}, Stands payload payloadSyntax →
      PayloadRuns points version (Payload.init name version) (payload ++ [.parenClose])
        (adaptRun rest) fun _ => pure (.done (outcomeOf command)))
    {tokens : List Parser.Internal.Input} (hs : Stands tokens command.tokens)
        (following : List Parser.Internal.Input) :
    drive points (commandStep version) .awaiting (tokens ++ following) Parser.Command.commandArrive
        =
      (do
        adaptRun (Traversal.command points h command)
        pure (some (outcomeOf command, following))) := by
  rw [htokens] at hs
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
  obtain ⟨nameToken, payload, rfl, hnameToken, hpayloadTokens⟩ := Stands.split_cons hinner
  rw [Parser.Internal.Input.received_commandName hname hnameToken, hcommand, adaptRun_bind]
  have := command_frame (points := points) hname (hpayload hpayloadTokens) following
  simp only [List.cons_append, List.append_assoc] at this ⊢
  rw [this]
  simp

end

end BSmtLib.Facts.Proofs.Parser.Commands.Frame
