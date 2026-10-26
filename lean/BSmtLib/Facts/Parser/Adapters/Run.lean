module

public import BSmtLib.Facts.Parser.Adapters.Handler

@[expose] public section

/-!
# Running the library's parser as the formalism runs a parser

- `drive` runs a parser stepped by single tokens over a list of tokens. Before the step that takes a
  token, it marks the token's arrival with the `Points` of the specification formalism
  (`BSmtLibSpec`), makes the parser's calls due at the token's arrival (`arrival`, none by default),
  and marks the token's processing.
- `driveParse` runs a parser that steps by single tokens (an instance of
  `Parser.Internal.ParseByToken`) over a list of tokens, as its loop over single tokens runs it
  over a producer's tokens. What the parser asks of the producer, the formalism's producer does.
- `driveInput` tells the handler the version first, as the adapter does at the start of every
  input, and then runs `driveParse`.
- `parserRecord` is the recording run of the script parser, under the posture that restricts
  nothing.
- `Rejection.libraryParser` is that run as a recording parser of the formalism
  (`BSmtLibSpec.Parser.Properties.RecordingParser`).
- `switchOf` and `discardOf` read what a recording run asks of its producer after its last
  processing.

These definitions are adapters: the root theorems of `BSmtLib.Facts.Parser` and
`BSmtLib.Facts.Reader` are stated with them, so they are trusted, and are to be read with the
formalism.
-/

open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Bridge.Rejection
open BSmtLib.Parser.Script

namespace BSmtLib.Facts.Parser.Adapters.Run

section

open BSmtLib.Parser
open BSmtLib.Parser.Internal (PM call syntaxError)
open BSmtLibSpec.Parser.Traversal

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m] {σ ρ τ χ α β : Type}
variable (points : Points (StateT H m))

/-- The traversal's run as a run of the parser: its failures as the parser's. -/
def adaptRun (run : Run (StateT H m) (Handler.Error H) α) : PM H α :=
  ExceptT.adapt causeOf run

/-- The arrival of the token, if it stands for something in the formalism. -/
def arriveAt (token : Parser.Internal.Input) : StateT H m Unit :=
  match Bridge.received token with
  | some received => points.arrive received
  | none => pure ()

/-- The processing of the token, if it stands for something in the formalism. -/
def processAt (token : Parser.Internal.Input) : StateT H m Unit :=
  match Bridge.received token with
  | some received => points.process received
  | none => pure ()

/-- A token arrives at the parser in the state, the calls due then are made, and it is
processed. -/
def arrivalTick (arrival : σ → Parser.Internal.Input → PM H Unit) (state : σ)
    (token : Parser.Internal.Input) : PM H Unit := do
  ExceptT.lift (arriveAt points token)
  arrival state token
  ExceptT.lift (processAt points token)

/-- A parser with no call due at any token's arrival. -/
def noArrival : σ → Parser.Internal.Input → PM H Unit := fun _ _ => pure ()

/--
Runs the parser from the state over the tokens. Each token arrives, the calls due at its arrival
are made, it is processed, and then the step processes it. Gives the result and the tokens after
the parser's end, or `none` if the tokens run out before the parser ends.
-/
def drive (step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)) :
    σ → List Parser.Internal.Input →
        (arrival : σ → Parser.Internal.Input → PM H Unit := noArrival) →
      PM H (Option (ρ × List Parser.Internal.Input))
  | _, [], _ => pure none
  | state, token :: tokens, arrival => do
    arrivalTick points arrival state token
    match ← step state token with
    | .more state => drive step state tokens arrival
    | .done result => pure (some (result, tokens))

end

section

open BSmtLib.Parser
open BSmtLib.Parser.Internal (PM call syntaxError)
open BSmtLibSpec.Parser.Traversal

variable {H P R : Type} {m : Type → Type} [Monad m] [Handler H m]
variable [Parser.Internal.ParseByToken P H m (Handler.Error H) R]
variable (points : Points (StateT H m)) (producer : Producer (StateT H m))

/--
Runs the parser in the version from its state over the tokens. Gives the result and the tokens
after the parser's end, or `none` if the tokens run out before it ends.
-/
def driveParse : Version → P → List Parser.Internal.Input → PM H (Option
    (R × List Parser.Internal.Input))
  | _, _, [] => pure none
  | version, parser, token :: tokens => do
    ExceptT.lift (arriveAt points token)
    Parser.Internal.ParseByToken.arrive parser token
    ExceptT.lift (processAt points token)
    match ← Parser.Internal.ParseByToken.step version parser token with
    | .more parser => driveParse version parser tokens
    | .done result => pure (some (result, tokens))
    | .switchVersion declared resume =>
      match ← ExceptT.lift (producer.setVersion (Bridge.version declared)).run with
      | .error _ => throw (.version .unsupported)
      | .ok () =>
        match ← resume with
        | .more parser => driveParse declared parser tokens
        | .done result => pure (some (result, tokens))
    | .discardRest resume => do
      ExceptT.lift producer.discardRest
      match ← resume with
      | .more parser => driveParse version parser tokens
      | .done result => pure (some (result, tokens))

/--
The parser over an input with the initial version, as the parse adapter runs it: the handler is
told the version first, then the parser takes the tokens.
-/
def driveInput (version : Version) (parser : P) (tokens : List Parser.Internal.Input) :
    PM H (Option (R × List Parser.Internal.Input)) := do
  ExceptT.lift (Handler.setVersion (H := H) version)
  driveParse points producer version parser tokens

end

section

open BSmtLibSpec.Parser.Properties
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Version (VersionPosture)

/-- The event is a processing. -/
def isProcessing : Event → Bool
  | .process _ => true
  | _ => false

/-- The events of a recording run of the script parser over the items, from the events before
it, in order. -/
def recordedRun (version : Version) (parser : ScriptParser (List Event))
    (items : List Parser.Internal.Input) (events : List Event) : List Event :=
  ((driveParse recordingPoints recordingProducer version parser items).run.run events).2.reverse

/-- The posture that restricts nothing: every version, any number of declarations. -/
def unrestrictedPosture : VersionPosture :=
  (Version.VersionPostureBuilder.new.clearAllowed.addAllowed .v2_0 |>.addAllowed .v2_5
    |>.addAllowed .v2_6 |>.addAllowed .v2_7 |>.setMaxDeclarations none).build

/-- The events a recording run starts with, with the initial version: the handler's switch to it. -/
abbrev startEvents (version : Version) : List Event :=
  [.handlerSwitch (Bridge.version version)]

/-- The events of a recording run of the script parser over the items: what `record` is for the
traversal. The parser has the posture that restricts nothing and starts in the initial version,
and the handler is told the version first. -/
def parserRecord (version : Version) (items : List Parser.Internal.Input) : List Event :=
  recordedRun version (ScriptParser.new unrestrictedPosture) items (startEvents version)

end

section

open BSmtLibSpec
open BSmtLibSpec.Parser.Properties

/-- The events after the last processing. -/
def afterLastProcess (events : List Event) : List Event :=
  (events.reverse.takeWhile fun e => !isProcessing e).reverse

/-- The version the producer is asked to switch to after the last processing, if it is. -/
def switchOf (events : List Event) : Option Lexicon.Version :=
  (afterLastProcess events).findSome? fun
    | .producerSwitch version => some version
    | _ => none

/-- Whether the producer is asked to discard after the last processing. -/
def discardOf (events : List Event) : Bool :=
  (afterLastProcess events).any fun
    | .producerDiscard => true
    | _ => false

end

namespace Rejection

open BSmtLibSpec.Parser.Properties
open BSmtLib.Parser.Script (ScriptParser)

/-- How the library's run ends, by its result. -/
def libEnding : Except (Parser.ParseErrorCause Unit) (Option
    (Unit × List Parser.Internal.Input)) → Ending
  | .ok none => .waiting
  | .ok (some _) => .finished
  | .error (.version .unsupported) => .failed .unsupportedVersion
  | .error (.version (.tooManyDeclarations limit)) => .failed (.tooManyDeclarations limit)
  | .error _ => .rejected

/-- The parser's tokens other than whitespace and comments. -/
abbrev LibItem : Type := {token : Parser.Internal.Input // Bridge.received token ≠ none}

/-- The library's script parser as a recording parser. -/
def libraryParser : RecordingParser where
  Item := LibItem
  stands token := rcv token.1
  parse version items :=
    let run := (driveInput recordingPoints recordingProducer (Bridge.libVersion version)
      (ScriptParser.new (H := List Event) unrestrictedPosture) (items.map Subtype.val)).run.run []
    (run.2.reverse, libEnding run.1)

end Rejection

end BSmtLib.Facts.Parser.Adapters.Run
