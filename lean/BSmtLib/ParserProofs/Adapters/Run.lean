import BSmtLib.ParserProofs.Adapters.Handler

/-!
# Running the library's parser as the spec runs a parser

`drive` runs a parser stepped by single tokens over a list of tokens, marking each token's
arrival and processing with the spec's `Points` before the step that takes it, and making the
parser's calls due at the token's arrival (`arrival`, none unless given) between the two.
`driveParse` runs a parser (an instance of `Parser.Parse`) over a list of tokens as the parse
adapter runs it over a producer's tokens, what the parser asks of the producer done by the
spec's producer; `driveInput` tells the handler the version first, as the adapter does at the
start of every input.

`parserRecord` is the recording run of the script parser, under the posture that restricts
nothing, and `Rejection.libraryParser` is that run as a recording parser of the spec
(`BSmtLibSpec.Parser.Properties.RecordingParser`). `switchOf` and `discardOf` read what a recording run asks of
its producer after its last processing.

These definitions are adapters: the root theorems of `BSmtLib.ParserProofs` and
`BSmtLib.EndToEnd` are stated with them, so they are trusted, and are to be read with the spec.
-/

namespace BSmtLib.ParserProofs

section

open BSmtLib.Parser
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal

variable {H : Type} {m : Type → Type} [Monad m] [Parser.Handler H m] {σ ρ τ χ α β : Type}
variable (points : Points (StateT H m))

/-- The traversal's run as a run of the parser: its failures as the parser's. -/
def adaptRun (run : Run (StateT H m) (Parser.Handler.Error H) α) : PM H α :=
  ExceptT.adapt causeOf run

/-- The arrival of the token, if it stands for something in the spec. -/
def arriveAt (token : Input) : StateT H m Unit :=
  match Bridge.received token with
  | some received => points.arrive received
  | none => pure ()

/-- The processing of the token, if it stands for something in the spec. -/
def processAt (token : Input) : StateT H m Unit :=
  match Bridge.received token with
  | some received => points.process received
  | none => pure ()

/-- A token arrives at the parser in the state, the calls due then are made, and it is
processed. -/
def arrivalTick (arrival : σ → Input → PM H Unit) (state : σ) (token : Input) : PM H Unit := do
  ExceptT.lift (arriveAt points token)
  arrival state token
  ExceptT.lift (processAt points token)

/-- A parser with no call due at any token's arrival. -/
def noArrival : σ → Input → PM H Unit := fun _ _ => pure ()

/--
The parser, from the state, over the tokens: each token arrives, the calls due at its arrival
are made, it is processed, then the step processes it. The result and the tokens after the
parser's end, or `none` if the tokens run out before the parser ends.
-/
def drive (step : σ → Input → PM H (Step σ ρ)) :
    σ → List Input → (arrival : σ → Input → PM H Unit := noArrival) →
      PM H (Option (ρ × List Input))
  | _, [], _ => pure none
  | state, token :: tokens, arrival => do
    arrivalTick points arrival state token
    match ← step state token with
    | .more state => drive step state tokens arrival
    | .done result => pure (some (result, tokens))

end

section

open BSmtLib.Parser
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal

variable {H P R : Type} {m : Type → Type} [Monad m] [Parser.Handler H m]
variable [Parse P H m (Parser.Handler.Error H) R]
variable (points : Points (StateT H m)) (producer : Producer (StateT H m))

/--
The parser in the version, from its state, over the tokens: the result and the tokens after
the parser's end, or `none` if the tokens run out before it ends.
-/
def driveParse : Version → P → List Input → PM H (Option (R × List Input))
  | _, _, [] => pure none
  | version, parser, token :: tokens => do
    ExceptT.lift (arriveAt points token)
    Parse.arrive parser token
    ExceptT.lift (processAt points token)
    match ← Parse.step version parser token with
    | .more parser => driveParse version parser tokens
    | .done result => pure (some (result, tokens))
    | .switchVersion declared resume =>
      match ← ExceptT.lift (producer.setVersion (Bridge.version declared)).run with
      | .error _ => throw (.syntax .unsupportedVersion)
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
The parser over an input read from the version, as the parse adapter runs it: the handler is
told the version first, then the parser takes the tokens.
-/
def driveInput (version : Version) (parser : P) (tokens : List Input) :
    PM H (Option (R × List Input)) := do
  ExceptT.lift (Parser.Handler.setVersion (H := H) version)
  driveParse points producer version parser tokens

end

section

open BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser (Input PM Step Flow Parse ScriptParser VersionPosture)

/-- The event is a processing. -/
def isProcessing : Event → Bool
  | .process _ => true
  | _ => false

/-- The events of a recording run of the script parser over the items, from the events before
it, in order. -/
def recordedRun (version : BSmtLib.Version) (parser : ScriptParser (List Event))
    (items : List Input) (events : List Event) : List Event :=
  ((driveParse recordingPoints recordingProducer version parser items).run.run events).2.reverse

/-- The posture that restricts nothing: every version, any number of declarations. -/
def unrestrictedPosture : VersionPosture :=
  { allowed := #[.v2_0, .v2_5, .v2_6, .v2_7], maxDeclarations := none }

/-- The events a recording run starts with, read from the version: the handler's switch to it. -/
abbrev startEvents (version : BSmtLib.Version) : List Event :=
  [.handlerSwitch (Bridge.version version)]

/-- The events of a recording run of the script parser over the items, under the posture that
restricts nothing, read from the version, the handler told the version first: what `record` is
for the traversal. -/
def parserRecord (version : BSmtLib.Version) (items : List Input) : List Event :=
  recordedRun version (ScriptParser.new unrestrictedPosture) items (startEvents version)

end

section

open BSmtLibSpec BSmtLibSpec.Lexicon BSmtLibSpec.Grammar BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLibSpec.Lexicon.Properties
open BSmtLibSpec.Regex (Chars chars)
open BSmtLibSpec.Parser.Traversal

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

open BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser (Input ScriptParser)

/-- How the library's run ends, by its result. -/
def libEnding : Except (Parser.ParseErrorCause Unit) (Option (Unit × List Input)) → Ending
  | .ok none => .waiting
  | .ok (some _) => .finished
  | .error (.syntax .unsupportedVersion) => .failed .unsupportedVersion
  | .error (.syntax (.tooManyVersionDeclarations limit)) => .failed (.tooManyDeclarations limit)
  | .error _ => .rejected

/-- The parser's tokens other than whitespace and comments. -/
abbrev LibItem : Type := {token : Input // Bridge.received token ≠ none}

/-- The library's script parser as a recording parser. -/
def libraryParser : RecordingParser where
  Item := LibItem
  stands token := rcv token.1
  parse version items :=
    let run := (driveInput recordingPoints recordingProducer (Bridge.libVersion version)
      (ScriptParser.new (H := List Event) unrestrictedPosture) (items.map Subtype.val)).run.run []
    (run.2.reverse, libEnding run.1)

end Rejection

end BSmtLib.ParserProofs
