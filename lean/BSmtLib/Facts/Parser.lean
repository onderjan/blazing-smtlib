module

public import BSmtLib.Facts.Trusted
public import BSmtLib.Facts.Proofs.Parser.Term
public import BSmtLib.Facts.Proofs.Parser.Command
public import BSmtLib.Facts.Proofs.Parser.Script
public import BSmtLib.Facts.Proofs.Parser.Link
public import BSmtLib.Facts.Proofs.Parser.Cut
public import BSmtLib.Facts.Proofs.Parser.Rejection.Discard
public import BSmtLib.Facts.Proofs.Parser.Fused.Step

@[expose] public section

/-!
# The parser against the specification's traversal

Proofs that the library's parser (`BSmtLib.Parser`) makes the calls of the specification's
traversal (`BSmtLibSpec.Parser.Traversal`), at the places among the tokens that the traversal
states.

- The handler: a library handler is a class instance, the spec's handler a structure. `Agrees h`
  says that the instance answers every call as the spec's handler `h` answers it, the views and
  arrays handed over turned into the spec's characters and lists. Every spec handler, in any
  monad, has a library handler that agrees with it (`every_handler_linked`), so the theorems
  below hold for every spec handler.
- The tokens: a list of the parser's tokens stands for the spec's tokens when each turns into
  the spec's (`Stands`, `Bridge.received`). The parser is run as its adapter runs it over a
  producer (`driveInput`, which first tells the handler the version, then `driveParse`): each
  token arrives, the calls due at its arrival are made, it is processed and the parser takes it;
  what the parser asks of the producer, the spec's producer does. The spec's token points mark each
  arrival and processing.
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
- The fused reader: the script parser's `parse` on a batch cursor is the fused script reader
  (`Parser.Internal.Fused`), which runs the script parser in one loop over the cursor and falls
  back to the parser's own steps for rare constructs; it parses the cursor as the parser's loop
  over single tokens does, in every lawful monad and with every handler
  (`fused_parses_as_port`). So what holds of that loop holds of the script parser's `parse`.
-/

/-!
## What holds

Each theorem below is proved in the modules imported above. Each is followed by the axioms its
proof uses: only those of Lean's standard library, no `sorry` and no axiom of its own. The build
fails if that changes.
-/

namespace BSmtLib.Facts.Parser

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Facts.Proofs.Parser.Command BSmtLib.Facts.Proofs.Parser.Cut
open BSmtLib.Facts.Proofs.Parser.Link BSmtLib.Facts.Proofs.Parser.Script
open BSmtLib.Facts.Proofs.Parser.Term

/-- Every spec handler, in any monad, is answered alike by a library handler. -/
theorem every_handler_linked {m : Type → Type} [Monad m] {ε : Type} {values : Values}
    (h₀ : Traversal.Handler m ε values) (nonstandard : ε) :
    Adapters.Bridge.Agrees (H := Adapters.Handler.Bridged h₀ nonstandard) (m := m)
        (Adapters.Handler.liftHandler h₀ nonstandard) :=
  agrees_liftHandler

/--
info: 'BSmtLib.Facts.Parser.every_handler_linked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms every_handler_linked

/--
On the tokens of a valid term, the term parser from its start makes the traversal's calls among
the traversal's token points, and ends with the handled term.
-/
theorem term_follows_traversal {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    [Traits.Handler H m] {points : Points (StateT H m)} {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (Adapters.Bridge.valuesOf H)}
    (hA : Adapters.Bridge.TermAgrees h) (term : Tree.Term)
    (hvalid : term.Valid (Adapters.Bridge.Bridge.version version))
    {tokens : List Parser.Internal.Input} (hs : Adapters.Bridge.Stands tokens term.tokens)
    (rest : List Parser.Internal.Input) :
    Adapters.Run.drive points (Parser.Category.Term.termStep version)
        Parser.Category.Term.TermState.init (tokens ++ rest) =
      (do
        let handled ← Adapters.Run.adaptRun (Traversal.term points h term)
        pure (some (handled, rest))) := by
  rw [term_runs_init (points := points) hA term hvalid hs rest]
  simp

/--
info: 'BSmtLib.Facts.Parser.term_follows_traversal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms term_follows_traversal

/--
On the tokens of a valid command, the command parser makes the traversal's calls among the
traversal's token points, the calls due at a token's arrival made at that arrival, and ends
with the command's outcome.
-/
theorem command_follows_traversal {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    [Traits.CommandHandler H m] {points : Points (StateT H m)} {version : Token.Version}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (Adapters.Bridge.valuesOf H)}
    (hA : Adapters.Bridge.Agrees h) (command : Tree.Command)
    (hvalid : command.Valid (Adapters.Bridge.Bridge.version version))
    (hmode : command.modeAfter (Adapters.Bridge.Bridge.version version) ≠ none)
    {tokens : List Parser.Internal.Input}
    (hs : Adapters.Bridge.Stands tokens command.tokens) (rest : List Parser.Internal.Input) :
    Adapters.Run.drive points (Parser.Command.commandStep version) .awaiting
        (tokens ++ rest) Parser.Command.commandArrive =
      (do
        Adapters.Run.adaptRun (Traversal.command points h command)
        pure (some (Adapters.Bridge.outcomeOf command, rest))) :=
  command_runs hA command hvalid hmode hs rest

/--
info: 'BSmtLib.Facts.Parser.command_follows_traversal' depends on axioms: [propext, Classical.choice, Quot.sound]
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
    [Traits.CommandHandler H m] {points : Points (StateT H m)}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (Adapters.Bridge.valuesOf H)}
    (hA : Adapters.Bridge.Agrees h)
    (producer : Producer (StateT H m)) (posture : Token.VersionPosture)
    {version : Token.Version} {commands : List Tree.Command}
    (hscript : Script (Adapters.Bridge.Bridge.version version) commands)
    {inputs : List Parser.Internal.Input}
    (hs : inputs.map Adapters.Bridge.Bridge.received =
    (BSmtLibSpec.Parser.Properties.received commands).map some)
    (rest : List Parser.Internal.Input) :
    Adapters.Run.driveInput points producer version
        (Parser.Script.ScriptParser.new (H := H) posture)
        (inputs ++ rest) =
      (do
        Adapters.Run.adaptRun (Traversal.script points h producer
            (Adapters.Bridge.policyOf posture) (Adapters.Bridge.Bridge.version version)
          commands)
        pure (some ((), rest))) :=
  script_correct hA producer posture hscript hs rest

/--
info: 'BSmtLib.Facts.Parser.script_follows_traversal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms script_follows_traversal

/-- The parser's recording run on what a parser receives for a valid script is `record`. -/
theorem recording_is_record {version : Token.Version} {commands : List Tree.Command}
    (hscript : Script (Adapters.Bridge.Bridge.version version) commands)
    {inputs : List Parser.Internal.Input}
    (hs : inputs.map Adapters.Bridge.Bridge.received =
    (BSmtLibSpec.Parser.Properties.received commands).map some) :
    Adapters.Run.parserRecord version inputs = record
        (Adapters.Bridge.Bridge.version version) commands :=
  parserRecord_script hscript hs

/--
info: 'BSmtLib.Facts.Parser.recording_is_record' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms recording_is_record

/--
On any input that agrees with what a parser receives for a valid script before the item at
position `k`, the parser's recording run has written, before that item arrives, what the
traversal of the script has.
-/
theorem placement_before_arrival {version : Token.Version} {commands : List Tree.Command}
    (hscript : Script (Adapters.Bridge.Bridge.version version) commands)
    {inputs : List Parser.Internal.Input}
    (hs : inputs.map Adapters.Bridge.Bridge.received =
    (BSmtLibSpec.Parser.Properties.received commands).map some)
    {items : List Parser.Internal.Input} (hlayout : Adapters.Bridge.NoLayout items) (k : Nat)
    (htake : items.take k = inputs.take k) :
    eventsBefore k (Adapters.Run.parserRecord version items) =
      eventsBefore k (record (Adapters.Bridge.Bridge.version version) commands) :=
  placement_arrival hscript hs hlayout k htake

/--
info: 'BSmtLib.Facts.Parser.placement_before_arrival' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms placement_before_arrival

/--
On any input that agrees with what a parser receives for a valid script before the item at
position `k` and has an item there, the parser's recording run has written, before that item is
processed and its arrival left out, what the traversal of the script has, where a `)` gets none
of the calls due at its arrival.
-/
theorem placement_before_processing {version : Token.Version} {commands : List Tree.Command}
    (hscript : Script (Adapters.Bridge.Bridge.version version) commands)
    {inputs : List Parser.Internal.Input}
    (hs : inputs.map Adapters.Bridge.Bridge.received =
    (BSmtLibSpec.Parser.Properties.received commands).map some)
    {items : List Parser.Internal.Input} (hlayout : Adapters.Bridge.NoLayout items) (k : Nat)
    {item : Parser.Internal.Input}
    (hitem : items[k]? = some item) {stands : Received}
    (hstands : Adapters.Bridge.Bridge.received item = some stands) (hk : k < inputs.length)
    (htake : items.take k = inputs.take k) :
    eventsBeforeProcessing k (Adapters.Run.parserRecord version items) =
      eventsBeforeProcessingOf stands k (record (Adapters.Bridge.Bridge.version version) commands)
          :=
  Proofs.Parser.Rejection.Library.placement_processingOf hscript hs hlayout k hitem hstands hk htake

/--
info: 'BSmtLib.Facts.Parser.placement_before_processing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms placement_before_processing

/--
Where its input stops before the item at position `k` of what a parser receives for a valid
script, the parser's recording run has written what the traversal of the script has before that
item arrives.
-/
theorem placement_where_input_stops {version : Token.Version} {commands : List Tree.Command}
    (hscript : Script (Adapters.Bridge.Bridge.version version) commands)
    {inputs : List Parser.Internal.Input}
    (hs : inputs.map Adapters.Bridge.Bridge.received =
    (BSmtLibSpec.Parser.Properties.received commands).map some) (k : Nat) :
    Adapters.Run.parserRecord version (inputs.take k) =
      eventsBefore k (record (Adapters.Bridge.Bridge.version version) commands) :=
  placement_prefix hscript hs k

/--
info: 'BSmtLib.Facts.Parser.placement_where_input_stops' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms placement_where_input_stops

/--
The parser takes what a parser takes for a script, or for commands that a declaration of a
version that is not supported ends, as the traversal does: on any start of it, its recording run
has the traversal's events before the next item, and ends as `Takes` says.
-/
theorem follows_the_traversal : FollowsTheTraversal Adapters.Run.Rejection.libraryParser :=
  Proofs.Parser.Rejection.Library.library_follows

/--
info: 'BSmtLib.Facts.Parser.follows_the_traversal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms follows_the_traversal

/--
The parser rejects the first item that no script continues with: it takes the items before it,
rejects it with a cause that is no version's, has made the traversal's events before the item's
processing, and makes no call at the item: its processing is the last event of the run. After
`exit`, it relies on its producer to hand over nothing but the end of the input.
-/
theorem rejects_first_unviable : RejectsFirstUnviable Adapters.Run.Rejection.libraryParser :=
  Proofs.Parser.Rejection.Discard.library_rejects

/--
info: 'BSmtLib.Facts.Parser.rejects_first_unviable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rejects_first_unviable

/--
The script parser parses a batch cursor of the library's lexer, by the fused script reader
(`Parser.Internal.Fused`), as its loop over single tokens does (`Parser.Internal.parseByToken`):
from every parser and handler, it gives the same answer, parser, parse state and cursor, and leaves
the same handler, in every lawful monad and with every handler. So every theorem about that loop
holds of the script parser's `parse` on the lexer's cursors.
-/
theorem fused_parses_as_port {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    [Traits.CommandHandler H m] {batch : Token.BatchTag}
    (parser : BSmtLib.Parser.Script.ScriptParser H) (state : BSmtLib.Parser.ParseState H)
    (cursor : Token.BatchCursor batch) :
    BSmtLib.Parser.Parse.parse (m := m) parser state cursor =
      BSmtLib.Parser.Internal.parseByToken parser state cursor :=
  Proofs.Parser.Fused.Step.parse_eq parser state cursor

/--
info: 'BSmtLib.Facts.Parser.fused_parses_as_port' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fused_parses_as_port

/-! ## What is trusted

A reader of the theorems above trusts the specification (`BSmtLibSpec`), the statements in this
file, and the definitions in `BSmtLib.Facts.Parser.Adapters` and the modules below it, which put
the parser and its handlers into the spec's shapes: the adapters. Everything else Lean checks.
The check below lists the adapters, every definition that the statements of the theorems in this
file rest on outside the specification, the library and Lean (`BSmtLib.Facts.Trusted`), and fails
the build if one of them is declared outside `BSmtLib.Facts.Parser.Adapters`.
-/

/--
info: 11 theorems, stated with 61 adapters:
BSmtLib.Facts.Parser.Adapters.Bridge:
  BSmtLib.Facts.Parser.Adapters.Bridge.Agrees
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.attributeValue
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.callAttribute
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.callSExpr
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.callScope
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.callSort
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.callTerm
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.callUnit
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.chars
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.constant
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.constructor
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.identifier
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.index
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.keyword
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.libVersion
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.pairs
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.pattern
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.quantifier
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.received
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.reserved
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.sExprNode
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.signature
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.symbol
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.symbolOrWildcard
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.termNode
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.version
  BSmtLib.Facts.Parser.Adapters.Bridge.NoLayout
  BSmtLib.Facts.Parser.Adapters.Bridge.Rejection.rcv
  BSmtLib.Facts.Parser.Adapters.Bridge.Stands
  BSmtLib.Facts.Parser.Adapters.Bridge.TermAgrees
  BSmtLib.Facts.Parser.Adapters.Bridge.causeOf
  BSmtLib.Facts.Parser.Adapters.Bridge.outcomeOf
  BSmtLib.Facts.Parser.Adapters.Bridge.policyOf
  BSmtLib.Facts.Parser.Adapters.Bridge.valuesOf
BSmtLib.Facts.Parser.Adapters.Handler:
  BSmtLib.Facts.Parser.Adapters.Handler.Bridged
  BSmtLib.Facts.Parser.Adapters.Handler.attributeValueOf
  BSmtLib.Facts.Parser.Adapters.Handler.bridgedCall
  BSmtLib.Facts.Parser.Adapters.Handler.instCommandHandlerBridged
  BSmtLib.Facts.Parser.Adapters.Handler.instHandlerBridged
  BSmtLib.Facts.Parser.Adapters.Handler.liftCall
  BSmtLib.Facts.Parser.Adapters.Handler.liftHandler
  BSmtLib.Facts.Parser.Adapters.Handler.recordingCall
  BSmtLib.Facts.Parser.Adapters.Handler.recordingLibrary
  BSmtLib.Facts.Parser.Adapters.Handler.recordingLibraryTerms
  BSmtLib.Facts.Parser.Adapters.Handler.sExprNodeOf
  BSmtLib.Facts.Parser.Adapters.Handler.termNodeOf
BSmtLib.Facts.Parser.Adapters.Run:
  BSmtLib.Facts.Parser.Adapters.Run.Rejection.LibItem
  BSmtLib.Facts.Parser.Adapters.Run.Rejection.libEnding
  BSmtLib.Facts.Parser.Adapters.Run.Rejection.libraryParser
  BSmtLib.Facts.Parser.Adapters.Run.adaptRun
  BSmtLib.Facts.Parser.Adapters.Run.arrivalTick
  BSmtLib.Facts.Parser.Adapters.Run.arriveAt
  BSmtLib.Facts.Parser.Adapters.Run.drive
  BSmtLib.Facts.Parser.Adapters.Run.driveInput
  BSmtLib.Facts.Parser.Adapters.Run.driveParse
  BSmtLib.Facts.Parser.Adapters.Run.noArrival
  BSmtLib.Facts.Parser.Adapters.Run.parserRecord
  BSmtLib.Facts.Parser.Adapters.Run.processAt
  BSmtLib.Facts.Parser.Adapters.Run.recordedRun
  BSmtLib.Facts.Parser.Adapters.Run.startEvents
  BSmtLib.Facts.Parser.Adapters.Run.unrestrictedPosture
-/
#guard_msgs in
#adapters within BSmtLib.Facts.Parser.Adapters

end BSmtLib.Facts.Parser
