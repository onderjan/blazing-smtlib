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
open BSmtLib.Parser.Internal (PM call syntaxError versionError)

/--
The parser of a script (`SmtScriptParser`).

It finishes at the end of the input: between commands, or after `exit`, after which its producer
discards the rest of the input. A version declaration, at its `)`, is handled as `set-info`;
then it is checked against the posture, then the producer switches to the version (it may
refuse), then the handler; the new version holds from the next command. At the `)` of `exit`
the handler is told of the command, then the producer discards the rest, and the script goes on
to the end of the input.
-/
/- LEAN: the constructor and the fields are private, as Rust's are; the library builds and reads
the parser through `ScriptParser.Internal`. -/
structure ScriptParser (H : Type) {m : Type → Type} [CommandHandler H m] where
  private mk ::
  private posture : Token.VersionPosture
  /-- The state of the command parser. -/
  private command : CommandStateOf H
  /-- The number of version declarations made so far. -/
  private declarations : Nat

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/-- The script parser before a script, under the posture. -/
def ScriptParser.new (posture : Token.VersionPosture) : ScriptParser H :=
  { posture, command := .awaiting, declarations := 0 }

/- LEAN: `Inhabited` gives the default value, Rust's `Default`: the parser under the default
posture. -/
instance : Inhabited (ScriptParser H) := ⟨.new default⟩

end

namespace ScriptParser.Internal

variable {H : Type} {m : Type → Type} [CommandHandler H m]

/-- The script parser with the given posture, command parser state and number of version
declarations. -/
@[inline]
def mk (posture : Token.VersionPosture) (command : CommandStateOf H) (declarations : Nat) :
    ScriptParser H :=
  { posture, command, declarations }

/-- The posture of the script parser. -/
@[inline]
def posture (self : ScriptParser H) : Token.VersionPosture :=
  self.posture

/-- The state of the command parser. -/
@[inline]
def command (self : ScriptParser H) : CommandStateOf H :=
  self.command

/-- The number of version declarations made so far. -/
@[inline]
def declarations (self : ScriptParser H) : Nat :=
  self.declarations

@[simp]
theorem posture_mk (posture : Token.VersionPosture) (command : CommandStateOf H)
    (declarations : Nat) : Internal.posture (mk posture command declarations) = posture :=
  (rfl)

@[simp]
theorem command_mk (posture : Token.VersionPosture) (command : CommandStateOf H)
    (declarations : Nat) : Internal.command (mk posture command declarations) = command :=
  (rfl)

@[simp]
theorem declarations_mk (posture : Token.VersionPosture) (command : CommandStateOf H)
    (declarations : Nat) :
    Internal.declarations (mk posture command declarations) = declarations :=
  (rfl)

/-- A script parser is the one built from its fields. -/
@[simp]
theorem mk_eta (self : ScriptParser H) :
    mk (Internal.posture self) (Internal.command self) (Internal.declarations self) = self :=
  (rfl)

/-- Two script parsers built from the same fields are equal. -/
theorem mk_inj {posture posture' : Token.VersionPosture} {command command' : CommandStateOf H}
    {declarations declarations' : Nat} :
    mk posture command declarations = mk posture' command' declarations' ↔
      posture = posture' ∧ command = command' ∧ declarations = declarations' := by
  constructor
  · intro h
    exact ⟨congrArg Internal.posture h, congrArg Internal.command h,
      congrArg Internal.declarations h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

end ScriptParser.Internal

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

omit [Monad m] in
/-- The script parser before a script. -/
theorem ScriptParser.Internal.new_eq (posture : Token.VersionPosture) :
    (ScriptParser.new posture : ScriptParser H) = mk posture .awaiting 0 :=
  (rfl)

/--
The check of a version declaration against the posture, given the number of declarations the
script made before it: first the number, then the version.
-/
def Internal.VersionPosture.check (self : Token.VersionPosture) (declarations : Nat)
    (version : Token.Version) :
    Option VersionErrorKind :=
  match self.maxDeclarations with
  | some limit =>
    if limit ≤ declarations then some (.tooManyDeclarations limit)
    else if self.allowed.contains version then none else some .unsupported
  | none => if self.allowed.contains version then none else some .unsupported

/-- The step of the script parser. -/
@[inline]
def ScriptParser.Internal.step (version : Token.Version) (parser : ScriptParser H)
    (token : Internal.Input) :
    PM H (Internal.Flow (PM H) (ScriptParser H) Unit) := do
  match ← Internal.commandStep version (command parser) token with
  | .more command => return .more (mk (posture parser) command (declarations parser))
  | .done .command => return .more (mk (posture parser) .awaiting (declarations parser))
  | .done (.setVersion declared) =>
    match (Internal.VersionPosture.check (posture parser)) (declarations parser) declared with
    | some kind => versionError kind
    | none =>
      return .switchVersion declared (do
        ExceptT.lift (Handler.setVersion (H := H) declared)
        return .more (mk (posture parser) .awaiting (declarations parser + 1)))
  -- the producer discards the rest of the input, and the script goes on to its end
  | .done .exit =>
    return .discardRest (pure (.more (mk (posture parser) .awaiting (declarations parser))))
  | .done .endOfFile => return .done ()

/-- The calls due when a token arrives at the script parser: those of its command parser. -/
def ScriptParser.Internal.arrive (parser : ScriptParser H) (token : Internal.Input) : PM H Unit :=
  Internal.commandArrive (command parser) token

/--
In a non-standard command, the script parser hands the cursor to the handler's parser of the
command's payload; after the command, it awaits the next one.
-/
@[inline]
def ScriptParser.Internal.handOver? {Z : Type} [Token.Cursor Z] (parser : ScriptParser H)
    (cursor : Z) :
    Option (StateT H m (Internal.After (ScriptParser H) Unit (Handler.Error H) ×
      { next : Z // Token.Cursor.HasNext cursor → Token.Cursor.Consumed next cursor })) :=
  match command parser with
  | .nonstandard nonstandard => some do
    let (answer, next) ← Command.Internal.nonstandardParse nonstandard cursor
    match answer with
    | .error error => return (.stop (.error error) (.new (posture parser)), next)
    | .ok (some nonstandard) =>
      return (.goOn (mk (posture parser) (.nonstandard nonstandard) (declarations parser)), next)
    -- a non-standard command cannot be the exit command
    | .ok none => return (.goOn (mk (posture parser) .awaiting (declarations parser)), next)
  | _ => none

/- LEAN: the script parser's `Parse` instance is in `Parser.Internal.Fused`: its `parse` runs the
fused reader on the library's batch cursors, which needs this module, and this loop on every
other producer. -/
@[no_expose]
instance Internal.instParseByTokenScriptParser :
    Internal.ParseByToken (ScriptParser H) H m (Handler.Error H) Unit where
  arrive := ScriptParser.Internal.arrive
  step := ScriptParser.Internal.step
  reset parser := .new (ScriptParser.Internal.posture parser)
  handOver? := ScriptParser.Internal.handOver?

end

end BSmtLib.Parser.Script
