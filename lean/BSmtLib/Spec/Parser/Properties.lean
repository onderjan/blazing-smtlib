import BSmtLib.Spec.Parser.Traversal

/-!
# Properties of the traversal

Properties of the handler contract alone: that the traversal takes exactly the tokens a script
is written as, that its calls determine the script, and that what it has done before a token
arrives depends only on the tokens before it. `BSmtLib.SpecChecks` proves them.

They are stated on a recording run (`record`): the traversal of a script with a handler and
token points that write down every event, in order, and a handler that returns as each handled
value the number of calls before it, so that a call names the earlier calls whose results it
receives. A recording run never fails: the policy restricts nothing, the producer never
refuses, and the handler never fails.

A recording stands for the run with every other handler: the traversal never looks at a value
a handler returns, it only hands it on to later calls, so the run with any handler makes the
recorded calls with that handler's values in place of the numbers.
-/

namespace BSmtLib.Spec.Parser

open BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar Traversal

/-! ## A recording run -/

/-- The values of a recording run: every handled value is the number of calls before it. -/
def Recorded : Values := ⟨Nat, Nat, Nat, Nat, Nat⟩

/-- What happens in a run of the traversal, in the order it happens. -/
inductive Event where
  | arrive (received : Received)
  | process (received : Received)
  | call (returns : Returns) (request : Call Recorded returns)
  | startScript
  | endScript
  /-- The producer's switch of the version. -/
  | producerSwitch (version : Version)

/-- The event is a call of the handler. -/
def Event.isCall : Event → Bool
  | .call _ _ | .startScript | .endScript => true
  | _ => false

/-- What arrived, if the event is an arrival. -/
def Event.arrived : Event → Option Received
  | .arrive received => some received
  | _ => none

/-- What was processed, if the event is a processing. -/
def Event.processed : Event → Option Received
  | .process received => some received
  | _ => none

/-- A run that writes down its events, the latest first. -/
abbrev Recording := StateM (List Event)

/-- Write down the event. -/
def emit (event : Event) : Recording Unit :=
  modify (event :: ·)

/-- The value a recording handler returns for a call: the number of calls before it. -/
def recordedValue : (returns : Returns) → Nat → Recorded.of returns
  | .sExpr, count => count
  | .attribute, count => count
  | .sort, count => count
  | .term, count => count
  | .scope, count => count
  | .nothing, _ => ()

/-- The token points of a recording run. -/
def recordingPoints : Points Recording where
  arrive received := emit (.arrive received)
  process received := emit (.process received)

/-- The handler of a recording run, which never fails. -/
def recordingHandler : Handler Recording Empty Recorded where
  call {returns} request := ExceptT.lift do
    let count := (← get).countP Event.isCall
    emit (.call returns request)
    pure (recordedValue returns count)
  startScript := emit .startScript
  endScript := emit .endScript

/-- The producer's switch of the version in a recording run, which never refuses. -/
def recordingSwitch (version : Version) : ExceptT VersionRefused Recording Unit :=
  ExceptT.lift (emit (.producerSwitch version))

/--
The events of the traversal of a script, in order, under the policy that restricts nothing.
-/
def record (commands : List Tree.Command) : List Event :=
  let run := script recordingPoints recordingHandler recordingSwitch VersionPolicy.unrestricted
    commands
  (Id.run ((ExceptT.run run).run [])).2.reverse

/-! ## What a parser of a script receives -/

/--
What a parser receives for the commands: the tokens each is written as, then the end of the
input, unless the commands end with `exit`, after which nothing is read.
-/
def received : List Tree.Command → List Received
  | [] => [.endOfInput]
  | .exit :: _ => Tree.Command.exit.tokens.map .token
  | first :: rest => first.tokens.map .token ++ received rest

/--
The events before the arrival of the item at the position `count` (from zero) of what a parser
receives: what a parser has done when no further item comes.
-/
def eventsBefore : Nat → List Event → List Event
  | _, [] => []
  | 0, .arrive _ :: _ => []
  | count + 1, .arrive item :: rest => .arrive item :: eventsBefore count rest
  | count, event :: rest => event :: eventsBefore count rest

/--
The events before the processing of the item at the position `count` (from zero) of what a
parser receives, without the arrival of that item itself: what a parser has done when it rejects
the item. The calls due at the item's arrival are among them; the item is left out, as it is the
one item that two inputs agreeing up to it need not share.
-/
def eventsBeforeProcessing : Nat → List Event → List Event
  | _, [] => []
  | 0, .process _ :: _ => []
  | 0, .arrive _ :: rest => eventsBeforeProcessing 0 rest
  | count + 1, .process item :: rest => .process item :: eventsBeforeProcessing count rest
  | count, event :: rest => event :: eventsBeforeProcessing count rest

/-! ## Properties -/

/--
Property: the traversal of a script takes exactly what a parser receives for it, each item
arriving and then processed, in order.

So the traversal places its calls among the very tokens the grammar writes the script as, and
nothing in the traversal repeats the grammar without the grammar checking it.
-/
def TakesItsTokens : Prop :=
  ∀ version (commands : List Tree.Command), Script version commands →
    (record commands).filterMap Event.arrived = received commands ∧
      (record commands).filterMap Event.processed = received commands

/--
Property: two scripts from the same version whose traversals make the same calls are the same
script.

So the calls lose nothing: a handler is told every construct of the script, in a form from which
the script can be rebuilt. Only the whitespace between the tokens is not told.
-/
def CallsDetermineScript : Prop :=
  ∀ version (commands commands' : List Tree.Command), Script version commands →
    Script version commands' →
    (record commands).filter Event.isCall = (record commands').filter Event.isCall →
    commands = commands'

/--
Property: what the traversal of a script has done before an item arrives, and before it is
processed, depends only on the items before it.

So what a parser has done is well defined where its input stops: when its producer has no
further token, it is what the traversal of any script that continues the input does before the
next item arrives; when it rejects an item, what that traversal does before the item is
processed. Without this, a parser could not know which calls to make before the tokens that
decide them, and would have to guess.
-/
def PlacementDetermined : Prop :=
  ∀ version (commands commands' : List Tree.Command) count, Script version commands →
    Script version commands' →
    (received commands).take count = (received commands').take count →
    eventsBefore count (record commands) = eventsBefore count (record commands') ∧
      eventsBeforeProcessing count (record commands) =
        eventsBeforeProcessing count (record commands')

end BSmtLib.Spec.Parser
