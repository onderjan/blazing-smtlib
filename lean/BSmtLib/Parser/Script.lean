import BSmtLib.Parser.Parse

/-!
# The script parser

The parser of an SMT-LIB script: a sequence of commands, each handed to the command handler as
it is parsed, under a version posture that restricts the version declarations.
-/

namespace BSmtLib.Parser

/--
Which versions a script may declare, and how many declarations it may make, without a limit if
there is none (`SmtVersionPosture`).
-/
/- LEAN: Rust builds a posture with `SmtVersionPostureBuilder`; here the fields are public. -/
structure VersionPosture where
  allowed : Array Version
  maxDeclarations : Option Nat

/-- The default posture: 2.5, 2.6 and 2.7, one declaration. -/
def VersionPosture.default : VersionPosture :=
  { allowed := #[.v2_5, .v2_6, .v2_7], maxDeclarations := some 1 }

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
  posture : VersionPosture
  /-- The state of the command parser. -/
  command : CommandStateOf H
  /-- The number of version declarations made so far. -/
  declarations : Nat

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/-- The script parser before a script, under the posture. -/
def ScriptParser.new (posture : VersionPosture) : ScriptParser H :=
  { posture, command := .awaiting, declarations := 0 }

/--
The check of a version declaration against the posture, given the number of declarations the
script made before it: first the number, then the version.
-/
def VersionPosture.check (self : VersionPosture) (declarations : Nat) (version : Version) :
    Option SyntaxErrorKind :=
  match self.maxDeclarations with
  | some limit =>
    if limit ≤ declarations then some (.tooManyVersionDeclarations limit)
    else if self.allowed.contains version then none else some .unsupportedVersion
  | none => if self.allowed.contains version then none else some .unsupportedVersion

/-- The step of the script parser. -/
@[inline]
def ScriptParser.step (version : Version) (parser : ScriptParser H) (token : Input) :
    PM H (Flow (PM H) (ScriptParser H) Unit) := do
  match ← commandStep version parser.command token with
  | .more command => return .more { parser with command }
  | .done .command => return .more { parser with command := .awaiting }
  | .done (.setVersion declared) =>
    match parser.posture.check parser.declarations declared with
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
def ScriptParser.arrive (parser : ScriptParser H) (token : Input) : PM H Unit :=
  commandArrive parser.command token

instance : Parse (ScriptParser H) H m (Handler.Error H) Unit where
  arrive := ScriptParser.arrive
  step := ScriptParser.step
  reset parser := .new parser.posture

end

end BSmtLib.Parser
