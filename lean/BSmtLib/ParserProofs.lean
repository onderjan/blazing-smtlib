import BSmtLib.Trusted
import BSmtLib.ParserProofs.Term
import BSmtLib.ParserProofs.Command
import BSmtLib.ParserProofs.Script
import BSmtLib.ParserProofs.Link
import BSmtLib.ParserProofs.Cut
import BSmtLib.ParserProofs.Rejection.Discard

/-!
# The parser against the specification's traversal

Proofs that the library's parser (`BSmtLib.Parser`) makes the calls of the specification's
traversal (`BSmtLibSpec.Parser.Traversal`), at the places among the tokens that the traversal states.

- The handler: a library handler is a class instance, the spec's handler a structure. `Agrees h`
  says that the instance answers every call as the spec's handler `h` answers it, the views and
  arrays handed over turned into the spec's characters and lists. Every spec handler, in any
  monad, has a library handler that agrees with it (`every_handler_linked`), so the theorems
  below hold for every spec handler.
- The tokens: a list of the parser's tokens stands for the spec's tokens when each turns into
  the spec's (`Stands`, `Bridge.received`). The parser is run as its adapter runs it over a
  producer (`driveInput`, which first tells the handler the version, then `driveParse`): each
  token arrives, the calls due at its arrival are made, it is processed and the parser takes it;
  what the parser asks of the producer, the spec's producer does. The spec's token points mark each arrival and processing.
- Valid input: on the tokens of a valid term, of a valid command, and of a valid script, the
  parser does exactly what the traversal does, in every monad, with every handler, token points,
  producer and posture (`term_follows_traversal`, `command_follows_traversal`,
  `script_follows_traversal`). Failures are the traversal's failures, as the parser's causes.
- Placement: in a recording run, the parser's events on any input that agrees with what a parser
  receives for a valid script up to an item are the traversal's before that item arrives, and
  before it is processed, its arrival left out (`placement_before_arrival`,
  `placement_before_processing`); where the input stops, they are the traversal's before the
  next item arrives (`placement_where_input_stops`). The last of these is what the parser has
  done when its producer has no further token; the second, what it has done when it rejects the
  item.
- Rejection: the parser as a recording parser of the spec (`Rejection.libraryParser`) takes what
  a parser takes for a script, or for commands that a declaration of a version that is not
  supported ends, as the traversal does (`follows_the_traversal`), and rejects the first item
  that no script continues with, where its producer hands over nothing but the end of the input
  after `exit` (`rejects_first_unviable`). The second rests on the parser's every step keeping
  what it has taken viable, the first on that and on the valid input above. After `exit`, the
  parser goes back to reading commands; only the end of the input keeps what it has taken
  viable there, and the traversal asks for the discarding exactly there.
-/

/-!
## What holds

Each theorem below is proved in the modules imported above. Each is followed by the axioms its
proof uses: only those of Lean's standard library, no `sorry` and no axiom of its own. The build
fails if that changes.
-/

namespace BSmtLib.ParserProofs

open BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal

/-- Every spec handler, in any monad, is answered alike by a library handler. -/
theorem every_handler_linked {m : Type → Type} [Monad m] {ε : Type} {values : Values}
    (h₀ : Traversal.Handler m ε values) (nonstandard : ε) :
    Agrees (H := Bridged h₀ nonstandard) (m := m) (liftHandler h₀ nonstandard) :=
  agrees_liftHandler

/--
info: 'BSmtLib.ParserProofs.every_handler_linked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms every_handler_linked

/--
On the tokens of a valid term, the term parser from its start makes the traversal's calls among
the traversal's token points, and ends with the handled term.
-/
theorem term_follows_traversal {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    [Parser.Handler H m] {points : Points (StateT H m)} {version : BSmtLib.Version}
    {h : Traversal.Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H)}
    (hA : TermAgrees h) (term : Tree.Term) (hvalid : term.Valid (Bridge.version version))
    {tokens : List Parser.Input} (hs : Stands tokens term.tokens) (rest : List Parser.Input) :
    drive points (Parser.termStep version) Parser.TermState.init (tokens ++ rest) =
      (do
        let handled ← adaptRun (Traversal.term points h term)
        pure (some (handled, rest))) := by
  rw [term_runs_init (points := points) hA term hvalid hs rest]
  simp

/--
info: 'BSmtLib.ParserProofs.term_follows_traversal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms term_follows_traversal

/--
On the tokens of a valid command, the command parser makes the traversal's calls among the
traversal's token points, the calls due at a token's arrival made at that arrival, and ends
with the command's outcome.
-/
theorem command_follows_traversal {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    [Parser.CommandHandler H m] {points : Points (StateT H m)} {version : BSmtLib.Version}
    {h : Traversal.Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H)}
    (hA : Agrees h) (command : Tree.Command) (hvalid : command.Valid (Bridge.version version))
    (hmode : command.modeAfter (Bridge.version version) ≠ none) {tokens : List Parser.Input}
    (hs : Stands tokens command.tokens) (rest : List Parser.Input) :
    drive points (Parser.commandStep version) .awaiting (tokens ++ rest) Parser.commandArrive =
      (do
        adaptRun (Traversal.command points h command)
        pure (some (outcomeOf command, rest))) :=
  command_runs hA command hvalid hmode hs rest

/--
info: 'BSmtLib.ParserProofs.command_follows_traversal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms command_follows_traversal

/--
On the tokens a parser receives for a valid script read from the version, followed by anything,
the script parser run as the parse adapter runs it, the handler told the version first, makes the
traversal's calls among the traversal's token points, under the policy of its posture, with the
same producer, and finishes at the end of the input, before the rest.
-/
theorem script_follows_traversal {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    [Parser.CommandHandler H m] {points : Points (StateT H m)}
    {h : Traversal.Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H)} (hA : Agrees h)
    (producer : Producer (StateT H m)) (posture : Parser.VersionPosture)
    {version : BSmtLib.Version} {commands : List Tree.Command}
    (hscript : Script (Bridge.version version) commands) {inputs : List Parser.Input}
    (hs : inputs.map Bridge.received = (BSmtLibSpec.Parser.Properties.received commands).map some)
    (rest : List Parser.Input) :
    driveInput points producer version (Parser.ScriptParser.new (H := H) posture)
        (inputs ++ rest) =
      (do
        adaptRun (Traversal.script points h producer (policyOf posture) (Bridge.version version)
          commands)
        pure (some ((), rest))) :=
  script_correct hA producer posture hscript hs rest

/--
info: 'BSmtLib.ParserProofs.script_follows_traversal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms script_follows_traversal

/-- The parser's recording run on what a parser receives for a valid script is `record`. -/
theorem recording_is_record {version : BSmtLib.Version} {commands : List Tree.Command}
    (hscript : Script (Bridge.version version) commands) {inputs : List Parser.Input}
    (hs : inputs.map Bridge.received = (BSmtLibSpec.Parser.Properties.received commands).map some) :
    parserRecord version inputs = record (Bridge.version version) commands :=
  parserRecord_script hscript hs

/--
info: 'BSmtLib.ParserProofs.recording_is_record' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms recording_is_record

/--
On any input that agrees with what a parser receives for a valid script before the item at
position `k`, the parser's recording run has written, before that item arrives, what the
traversal of the script has.
-/
theorem placement_before_arrival {version : BSmtLib.Version} {commands : List Tree.Command}
    (hscript : Script (Bridge.version version) commands) {inputs : List Parser.Input}
    (hs : inputs.map Bridge.received = (BSmtLibSpec.Parser.Properties.received commands).map some)
    {items : List Parser.Input} (hlayout : NoLayout items) (k : Nat)
    (htake : items.take k = inputs.take k) :
    eventsBefore k (parserRecord version items) =
      eventsBefore k (record (Bridge.version version) commands) :=
  placement_arrival hscript hs hlayout k htake

/--
info: 'BSmtLib.ParserProofs.placement_before_arrival' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms placement_before_arrival

/--
On any input that agrees with what a parser receives for a valid script before the item at
position `k` and has an item there, the parser's recording run has written, before that item is
processed and its arrival left out, what the traversal of the script has, where a `)` gets none
of the calls due at its arrival.
-/
theorem placement_before_processing {version : BSmtLib.Version} {commands : List Tree.Command}
    (hscript : Script (Bridge.version version) commands) {inputs : List Parser.Input}
    (hs : inputs.map Bridge.received = (BSmtLibSpec.Parser.Properties.received commands).map some)
    {items : List Parser.Input} (hlayout : NoLayout items) (k : Nat) {item : Parser.Input}
    (hitem : items[k]? = some item) {stands : Received}
    (hstands : Bridge.received item = some stands) (hk : k < inputs.length)
    (htake : items.take k = inputs.take k) :
    eventsBeforeProcessing k (parserRecord version items) =
      eventsBeforeProcessingOf stands k (record (Bridge.version version) commands) :=
  Rejection.placement_processingOf hscript hs hlayout k hitem hstands hk htake

/--
info: 'BSmtLib.ParserProofs.placement_before_processing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms placement_before_processing

/--
Where its input stops before the item at position `k` of what a parser receives for a valid
script, the parser's recording run has written what the traversal of the script has before that
item arrives.
-/
theorem placement_where_input_stops {version : BSmtLib.Version} {commands : List Tree.Command}
    (hscript : Script (Bridge.version version) commands) {inputs : List Parser.Input}
    (hs : inputs.map Bridge.received = (BSmtLibSpec.Parser.Properties.received commands).map some) (k : Nat) :
    parserRecord version (inputs.take k) =
      eventsBefore k (record (Bridge.version version) commands) :=
  placement_prefix hscript hs k

/--
info: 'BSmtLib.ParserProofs.placement_where_input_stops' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms placement_where_input_stops

/--
The parser takes what a parser takes for a script, or for commands that a declaration of a
version that is not supported ends, as the traversal does: on any start of it, its recording run
has the traversal's events before the next item, and ends as `Takes` says.
-/
theorem follows_the_traversal : FollowsTheTraversal Rejection.libraryParser :=
  Rejection.library_follows

/--
info: 'BSmtLib.ParserProofs.follows_the_traversal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms follows_the_traversal

/--
The parser rejects the first item that no script continues with: it takes the items before it,
rejects it with a cause that is no version's, has made the traversal's events before the item's
processing, and makes no call at the item: its processing is the last event of the run. After
`exit`, it relies on its producer to hand over nothing but the end of the input.
-/
theorem rejects_first_unviable : RejectsFirstUnviable Rejection.libraryParser :=
  Rejection.library_rejects

/--
info: 'BSmtLib.ParserProofs.rejects_first_unviable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rejects_first_unviable

/-! ## What is trusted

A reader of the theorems above trusts the specification (`BSmtLibSpec`), the statements in this
file, and the definitions in `BSmtLib.ParserProofs.Adapters` and the modules below it, which put
the parser and its handlers into the spec's shapes: the adapters. Everything else Lean checks.
The check below lists the adapters, every definition that the statements of the theorems in this
file rest on outside the specification, the library and Lean (`BSmtLib.Trusted`), and fails the
build if one of them is declared outside `BSmtLib.ParserProofs.Adapters`.
-/

/--
info: 10 theorems, stated with 61 adapters:
BSmtLib.ParserProofs.Adapters.Bridge:
  BSmtLib.ParserProofs.Agrees
  BSmtLib.ParserProofs.Bridge.attributeValue
  BSmtLib.ParserProofs.Bridge.callAttribute
  BSmtLib.ParserProofs.Bridge.callSExpr
  BSmtLib.ParserProofs.Bridge.callScope
  BSmtLib.ParserProofs.Bridge.callSort
  BSmtLib.ParserProofs.Bridge.callTerm
  BSmtLib.ParserProofs.Bridge.callUnit
  BSmtLib.ParserProofs.Bridge.chars
  BSmtLib.ParserProofs.Bridge.constant
  BSmtLib.ParserProofs.Bridge.constructor
  BSmtLib.ParserProofs.Bridge.identifier
  BSmtLib.ParserProofs.Bridge.index
  BSmtLib.ParserProofs.Bridge.keyword
  BSmtLib.ParserProofs.Bridge.libVersion
  BSmtLib.ParserProofs.Bridge.pairs
  BSmtLib.ParserProofs.Bridge.pattern
  BSmtLib.ParserProofs.Bridge.quantifier
  BSmtLib.ParserProofs.Bridge.received
  BSmtLib.ParserProofs.Bridge.reserved
  BSmtLib.ParserProofs.Bridge.sExprNode
  BSmtLib.ParserProofs.Bridge.signature
  BSmtLib.ParserProofs.Bridge.symbol
  BSmtLib.ParserProofs.Bridge.symbolOrWildcard
  BSmtLib.ParserProofs.Bridge.termNode
  BSmtLib.ParserProofs.Bridge.version
  BSmtLib.ParserProofs.NoLayout
  BSmtLib.ParserProofs.Rejection.rcv
  BSmtLib.ParserProofs.Stands
  BSmtLib.ParserProofs.TermAgrees
  BSmtLib.ParserProofs.causeOf
  BSmtLib.ParserProofs.outcomeOf
  BSmtLib.ParserProofs.policyOf
  BSmtLib.ParserProofs.valuesOf
BSmtLib.ParserProofs.Adapters.Handler:
  BSmtLib.ParserProofs.Bridged
  BSmtLib.ParserProofs.attributeValueOf
  BSmtLib.ParserProofs.bridgedCall
  BSmtLib.ParserProofs.instCommandHandlerBridged
  BSmtLib.ParserProofs.instHandlerBridged
  BSmtLib.ParserProofs.liftCall
  BSmtLib.ParserProofs.liftHandler
  BSmtLib.ParserProofs.recordingCall
  BSmtLib.ParserProofs.recordingLibrary
  BSmtLib.ParserProofs.recordingLibraryTerms
  BSmtLib.ParserProofs.sExprNodeOf
  BSmtLib.ParserProofs.termNodeOf
BSmtLib.ParserProofs.Adapters.Run:
  BSmtLib.ParserProofs.Rejection.LibItem
  BSmtLib.ParserProofs.Rejection.libEnding
  BSmtLib.ParserProofs.Rejection.libraryParser
  BSmtLib.ParserProofs.adaptRun
  BSmtLib.ParserProofs.arrivalTick
  BSmtLib.ParserProofs.arriveAt
  BSmtLib.ParserProofs.drive
  BSmtLib.ParserProofs.driveInput
  BSmtLib.ParserProofs.driveParse
  BSmtLib.ParserProofs.noArrival
  BSmtLib.ParserProofs.parserRecord
  BSmtLib.ParserProofs.processAt
  BSmtLib.ParserProofs.recordedRun
  BSmtLib.ParserProofs.startEvents
  BSmtLib.ParserProofs.unrestrictedPosture
-/
#guard_msgs in
#adapters within BSmtLib.ParserProofs.Adapters

end BSmtLib.ParserProofs
