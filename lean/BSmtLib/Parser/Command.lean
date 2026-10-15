module

public import BSmtLib.Parser.Command.Standard

public section

/-!
# The command parser

A state machine stepped by single tokens over one command: its `(`, its name, then the payload
parser of the command, which finishes at the command's `)`. A command's parts are parsed into
values the parser holds, and handed over at the handler call; every command's last call comes
at its `)`.
-/

namespace BSmtLib.Parser.Command

open BSmtLib.Traits BSmtLib.Parser.Command.Standard
open BSmtLib.Token (Version)

/-- The state of the command parser. -/
inductive CommandState (HandledSExpr HandledAttribute HandledSort HandledTerm Scope : Type) where
  /-- Before a command, or the end of the input. -/
  | awaiting
  /-- After the `(` of a command, before its name. -/
  | opened
  | payload (state : Payload HandledSExpr HandledAttribute HandledSort HandledTerm Scope)

/-- The command parser state of the handler. -/
abbrev CommandStateOf (H : Type) {m : Type → Type} [Handler H m] :=
  CommandState (Handler.SExpr H) (Handler.Attribute H) (Handler.«Sort» H) (Handler.Term H)
    (Handler.Scope H)

/--
The parser of one command (`SmtCommandParser`). It finishes after every command, and after the
end of the input while it awaits a command.

A version declaration switches nothing: the version is a mode of a script. The parser reports
the declaration in its outcome, and its caller decides; `exit` likewise.
-/
structure CommandParser (H : Type) {m : Type → Type} [Handler H m] where
  state : CommandStateOf H

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- The command parser before a command. -/
def CommandParser.new : CommandParser H := ⟨.awaiting⟩

end

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/--
A step of the command parser: `(`, the command's name, its payload up to its `)`; or the end of
the input between commands. A symbol as the name, even one spelled as a standard command's
name, names a non-standard command.
-/
def commandStep (version : Version) (self : CommandStateOf H) (token : Internal.Input) :
    PM H (Internal.Step (CommandStateOf H) CommandOutcome) := do
  match self with
  | .awaiting =>
    match token with
    | .parenOpen => return .more .opened
    | .endOfInput => return .done .endOfInput
    | _ => syntaxError .expectedCommand
  | .opened =>
    match token with
    | .reserved (.commandName name) => return .more (.payload (Payload.init name version))
    | .symbol name => throw (.handler (CommandHandler.nonstandardCommand (H := H) name))
    | _ => syntaxError .expectedCommandName
  | .payload payload =>
    match ← payloadStep version payload token with
    | .more payload => return .more (.payload payload)
    | .done outcome => return .done outcome

/-- The calls due when a token arrives at the command parser: those of its payload parser. -/
def commandArrive (self : CommandStateOf H) (token : Internal.Input) : PM H Unit :=
  match self with
  | .payload payload => payloadArrive payload token
  | _ => pure ()

instance : Internal.ParseByToken (CommandParser H) H m (Handler.Error H) CommandOutcome where
  arrive parser token := commandArrive parser.state token
  step version parser token := do
    match ← commandStep version parser.state token with
    | .more state => return .more ⟨state⟩
    | .done result => return .done result
  reset _ := .new

instance : Parse (CommandParser H) H m (Handler.Error H) CommandOutcome where
  parse := Internal.parseByToken

end

end BSmtLib.Parser.Command
