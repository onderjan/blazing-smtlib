import BSmtLib.Spec.Parser.Traversal

/-!
# Properties of the traversal

Properties of the handler contract alone: that the traversal takes exactly the tokens a script
is written as, that its calls determine the script, and that what it has done before a token
arrives depends only on the tokens before it. `BSmtLib.SpecChecks` proves them.

They are stated on a recording run (`record`): the traversal of a script with a handler, token
points and a producer that write down every event, in order, and a handler that returns as each handled
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
  /-- The handler's switch of the version. -/
  | handlerSwitch (version : Version)
  /-- The producer's switch of the version. -/
  | producerSwitch (version : Version)
  /-- The producer's discarding of the rest of the input. -/
  | producerDiscard

/-- The event is a call of the handler. -/
def Event.isCall : Event → Bool
  | .call _ _ | .handlerSwitch _ => true
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
  setVersion version := emit (.handlerSwitch version)

/--
The producer of a recording run, which never refuses to switch the version and writes down its
switches and its discarding.
-/
def recordingProducer : Producer Recording where
  setVersion version := ExceptT.lift (emit (.producerSwitch version))
  discardRest := emit .producerDiscard

/--
The events of the traversal of a script read from the version, in order, under the policy that
restricts nothing.
-/
def record (version : Version) (commands : List Tree.Command) : List Event :=
  let run := script recordingPoints recordingHandler recordingProducer VersionPolicy.unrestricted
    version commands
  (Id.run ((ExceptT.run run).run [])).2.reverse

/-! ## What a parser of a script receives -/

/--
What a parser receives for the commands: the tokens each is written as, then the end of the
input. After `exit`, the rest of the input is discarded, so the end of the input comes right
after the tokens of `exit`.
-/
def received : List Tree.Command → List Received
  | [] => [.endOfInput]
  | .exit :: _ => Tree.Command.exit.tokens.map .token ++ [.endOfInput]
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

/--
The events before the processing of the item at the position `count` (from zero), when the item
that arrives there is `item`, without its arrival: what a parser has done when it rejects that
item. They are those before the processing of the item at that position (`eventsBeforeProcessing`),
except that a `)` gets none of the calls due at its arrival, as it begins nothing: for a `)`, they
are those before the arrival (`eventsBefore`).
-/
def eventsBeforeProcessingOf (item : Received) (count : Nat) (events : List Event) : List Event :=
  match item with
  | .token .parenClose => eventsBefore count events
  | _ => eventsBeforeProcessing count events

/-! ## Properties -/

/--
Property: the traversal of a script takes exactly what a parser receives for it, each item
arriving and then processed, in order.

So the traversal places its calls among the very tokens the grammar writes the script as, and
nothing in the traversal repeats the grammar without the grammar checking it.
-/
def TakesItsTokens : Prop :=
  ∀ version (commands : List Tree.Command), Script version commands →
    (record version commands).filterMap Event.arrived = received commands ∧
      (record version commands).filterMap Event.processed = received commands

/--
Property: two scripts from the same version whose traversals make the same calls are the same
script.

So the calls lose nothing: a handler is told every construct of the script, in a form from which
the script can be rebuilt. Only the whitespace between the tokens is not told.
-/
def CallsDetermineScript : Prop :=
  ∀ version (commands commands' : List Tree.Command), Script version commands →
    Script version commands' →
    (record version commands).filter Event.isCall = (record version commands').filter Event.isCall →
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
    eventsBefore count (record version commands) = eventsBefore count (record version commands') ∧
      eventsBeforeProcessing count (record version commands) =
        eventsBeforeProcessing count (record version commands')

/-! ## Where a parser rejects its input

The properties above are about scripts. The two below are about a parser on any input that a
producer can hand it: it takes what a parser takes for a script as the traversal does, and it
rejects the first item that no script continues with.

A declaration of a version that is not supported is no command of a script, but a parser takes
it as `set-info` up to its `)` and only then fails, as on a version its policy does not allow
(`Traversal.commands`). So what a parser takes is a script, or commands that such a declaration
ends (`Takes`).
-/

/-- How a parser's run over the items it is given ends. -/
inductive Ending where
  /-- The parser took every item and waits for the next. -/
  | waiting
  /-- The script ended: the parser finished, and takes no item after it. -/
  | finished
  /-- The parser rejected the last item it took: no script continues with it. -/
  | rejected
  /-- The parser failed after the last item it took, on a version declaration. -/
  | failed (error : VersionError)

/--
`Takes version commands items ending`: read from the version, a parser takes the items for the
commands, and then ends as `ending` says. Either the commands are a script, the items what a
parser receives for it (`received`), and the parser finishes; or the commands are valid up to a
version declaration that names no supported version, which ends them, the items are their tokens
up to that declaration's `)`, and the parser fails there with `unsupportedVersion`.

Standard: 2.7 §3.11 Scripts. Readings M1, M2 and M3, as `Tree.Command.modeAfter`.
-/
inductive Takes : Version → List Tree.Command → List Received → Ending → Prop
  /-- The end of the input. -/
  | done : Takes version [] [.endOfInput] .finished
  /-- A command after which the commands go on in a version. -/
  | command {first : Tree.Command} : first.Valid version →
      first.modeAfter version = some (.read next) → Takes next rest items ending →
      Takes version (first :: rest) (first.tokens.map .token ++ items) ending
  /-- A command after which nothing is read: `exit`, then the end of the input. -/
  | stop {last : Tree.Command} : last.Valid version → last.modeAfter version = some .unparsed →
      Takes version [last] (last.tokens.map .token ++ [.endOfInput]) .finished
  /-- A version declaration that names no supported version, at whose `)` a parser fails. -/
  | refused {last : Tree.Command} : last.Valid version → last.modeAfter version = none →
      Takes version [last] (last.tokens.map .token) (.failed .unsupportedVersion)

/--
A parser can go on after the items: they are the start of what a parser takes for a script or
for commands that a declaration of a version that is not supported ends.
-/
def Viable (version : Version) (items : List Received) : Prop :=
  ∃ commands taken ending, Takes version commands taken ending ∧ items <+: taken

/--
The version in force at the item at position `count` (from zero) of what a parser takes for the
commands, read from the version: the version a declaration declares holds from the item after
its `)` on.

Reading M1: a version declaration changes the mode after its `)`.
-/
def versionAt (version : Version) : List Tree.Command → Nat → Version
  | [], _ => version
  | first :: rest, count =>
    if count < first.tokens.length then version
    else versionAt (first.declaredVersion.getD version) rest (count - first.tokens.length)

/--
The item is one that a lexer of the version can hand over, as far as a parser can tell: a
reserved word is a reserved word of the version.

Standard: 2.7 §3.1 Reserved words; ⟨reserved⟩ of each version.
-/
def Traversal.Received.OfVersion (version : Version) : Received → Prop
  | .token (.reserved word) => word ∈ (basicReservedWords version ++ commandNames version).map chars
  | _ => True

/--
A parser as its recording runs show it. It takes items of its own type, each of which stands for
a token or the end of the input (`stands`); from the version to start in and the items it is
given, it records the events of its run, with a handler, token points and a producer that write
them down as in `record`, and ends as `Ending` says.
-/
structure RecordingParser where
  Item : Type
  stands : Item → Received
  parse : Version → List Item → List Event × Ending

/--
Property: a parser takes what a parser takes for a script, or for commands that a declaration of
a version that is not supported ends, as the traversal does. On items that stand for those
items, given any start of them, it has made the traversal's events before the next item
arrives; when it has all of them, it ends as `Takes` says, and otherwise it waits for the next
item.

So a parser rejects no item that some script continues with, and it rejects a declaration of a
version that is not supported after its `set-info`, as it rejects a version that its policy does
not allow.
-/
def FollowsTheTraversal (parser : RecordingParser) : Prop :=
  ∀ version commands taken ending (all : List parser.Item),
    Takes version commands taken ending → all.map parser.stands = taken →
    ∀ count ≤ taken.length,
      parser.parse version (all.take count) =
        (eventsBefore count (record version commands),
          if count < taken.length then .waiting else ending)

/--
Property: a parser rejects the first item that no script continues with. On items that stand,
before the item at position `count`, for what a parser takes for a script, or for commands that a
declaration of a version that is not supported ends, where the items have an item there that no
script continues with, the parser takes the items up to that one and rejects it, having made the
traversal's events before the item's processing, where a `)` gets none of the calls due at its
arrival (`eventsBeforeProcessingOf`); processing the item makes no call, so the item's processing
is the last event of the run.

A lexer hands over a reserved word only if it is one of the version in force, and a parser
relies on that; so the rejected item is taken to be such. The items before it are such, as they
stand for items of a valid script.

After `exit`, a parser asks its producer to discard the rest of the input, and relies on that
too: a producer that honours the request hands over nothing after it but the end of the input. So
where the traversal has asked for the discarding before the rejected item, that item is taken to
be the end of the input.
-/
def RejectsFirstUnviable (parser : RecordingParser) : Prop :=
  ∀ version commands taken ending (items : List parser.Item) count rejected,
    Takes version commands taken ending →
    count < taken.length → items[count]? = some rejected →
    (items.map parser.stands).take count = taken.take count →
    (∀ item, (items.map parser.stands)[count]? = some item →
      item.OfVersion (versionAt version commands count)) →
    (.producerDiscard ∈ eventsBefore count (record version commands) →
      (items.map parser.stands)[count]? = some .endOfInput) →
    ¬ Viable version ((items.map parser.stands).take (count + 1)) →
    (parser.parse version items).2 = .rejected ∧
      (parser.parse version items).1.filterMap Event.processed =
        (items.map parser.stands).take (count + 1) ∧
      (parser.parse version items).1.getLast? = ((items.map parser.stands)[count]?).map .process ∧
      eventsBeforeProcessing count (parser.parse version items).1 =
        eventsBeforeProcessingOf (parser.stands rejected) count (record version commands)

end BSmtLib.Spec.Parser
