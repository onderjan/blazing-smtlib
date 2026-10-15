module

public import BSmtLib.Parser.Command

public section

/-!
# The script parser

The parser of an SMT-LIB script: a sequence of commands, each handed to the command handler as
it is parsed, under a version posture that restricts the version declarations.
-/

namespace BSmtLib.Parser.Script

open BSmtLib.Parser.Command BSmtLib.Traits
open BSmtLib.Parser.Command.Internal
open BSmtLib.Parser.Internal (PM call syntaxError)

/--
The parser of a script (`SmtScriptParser`).

It finishes at the end of the input: between commands, or after `exit`, after which its producer
discards the rest of the input. A version declaration, at its `)`, is handled as `set-info`;
then it is checked against the posture, then the producer switches to the version (it may
refuse), then the handler; the new version holds from the next command. At the `)` of `exit`
the handler is told of the command, then the producer discards the rest, and the script goes on
to the end of the input.
-/
structure ScriptParser (H : Type) {m : Type → Type} [Handler H m] where
  posture : Token.VersionPosture
  /-- The state of the command parser. -/
  command : CommandStateOf H
  /-- The number of version declarations made so far. -/
  declarations : Nat

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/-- The script parser before a script, under the posture. -/
def ScriptParser.new (posture : Token.VersionPosture) : ScriptParser H :=
  { posture, command := .awaiting, declarations := 0 }

/--
The check of a version declaration against the posture, given the number of declarations the
script made before it: first the number, then the version.
-/
def Internal.VersionPosture.check (self : Token.VersionPosture) (declarations : Nat)
    (version : Token.Version) :
    Option SyntaxErrorKind :=
  match self.maxDeclarations with
  | some limit =>
    if limit ≤ declarations then some (.tooManyVersionDeclarations limit)
    else if self.allowed.contains version then none else some .unsupportedVersion
  | none => if self.allowed.contains version then none else some .unsupportedVersion

/-- The step of the script parser. -/
@[inline]
def ScriptParser.Internal.step (version : Token.Version) (parser : ScriptParser H)
    (token : Internal.Input) :
    PM H (Internal.Flow (PM H) (ScriptParser H) Unit) := do
  match ← Internal.commandStep version parser.command token with
  | .more command => return .more { parser with command }
  | .done .command => return .more { parser with command := .awaiting }
  | .done (.setVersion declared) =>
    match (Internal.VersionPosture.check parser.posture) parser.declarations declared with
    | some kind => syntaxError kind
    | none =>
      return .switchVersion declared (do
        ExceptT.lift (Handler.setVersion (H := H) declared)
        return .more
          { parser with command := .awaiting, declarations := parser.declarations + 1 })
  -- the producer discards the rest of the input, and the script goes on to its end
  | .done .exit => return .discardRest (pure (.more { parser with command := .awaiting }))
  | .done .endOfInput => return .done ()

/-- The calls due when a token arrives at the script parser: those of its command parser. -/
def ScriptParser.Internal.arrive (parser : ScriptParser H) (token : Internal.Input) : PM H Unit :=
  Internal.commandArrive parser.command token

/- LEAN: the script parser's `Parse` instance is in `Parser.Internal.Fused`: its `parse` runs the
fused reader on the library's batch cursors, which needs this module, and this loop on every
other producer. -/
instance : Internal.ParseByToken (ScriptParser H) H m (Handler.Error H) Unit where
  arrive := ScriptParser.Internal.arrive
  step := ScriptParser.Internal.step
  reset parser := .new parser.posture

end

end BSmtLib.Parser.Script
