import BSmtLib.Trusted
import BSmtLib.Proofs
import BSmtLib.EndToEnd.Valid
import BSmtLib.EndToEnd.Session
import BSmtLib.EndToEnd.Param.Final
import BSmtLib.EndToEnd.Reader
import BSmtLib.EndToEnd.Lexes.Reader

/-!
# From characters to the calls of the traversal

The composition of the lexer proofs (`BSmtLib.Proofs`) with the parser proofs
(`BSmtLib.ParserProofs`) at the level of the specification.

- The consumer: `EndToEnd.scriptConsumer version` is the library's script parser as a consumer of
  the lexer spec (`Spec.Lexer.Consumer`): after each token it answers as the parser's recording
  run (`Rejection.libraryParser`) on the tokens taken so far ends, each token read as the parser's
  token that stands for it, and it asks for the switch of the version and the discarding that the
  run asks of its producer after the last token's processing.
- The lexer: `Proofs.Lexer.correctWithConsumers` states that the library's lexer, fed by the
  adapter with every consumer of the spec, does what `Spec.Lexer.Runs` states, relative to what it
  hands over to the collector, which is `Spec.Lexer.Correct`.
- The file: `Spec.Grammar.File` reads the characters of a file as commands, each in the version
  in force, from its version declarations on (Reading M1) up to `exit` (Reading M2).

So the library's lexer, fed the characters of a file cut into any slices and then the end of the
input, with that consumer, takes the tokens of the commands, switching the version after every
version declaration and discarding after `exit`, and returns the parser's result at the end of the
input; and the parser's recording run on what the lexer handed it is the traversal's
(`library_lexes_file`). The proof (`EndToEnd.lexing_file`) holds for every lexer that is correct
with every consumer.

With the library's parse adapter (`Parser.ParseAdapter`) as the lexer's consumer, the same is
proved on files: the library's lexer depends on its consumer only through each call's answer and
cursor (`Param.lexSliceStep_sim`, `Param.lexEofStep_sim`), and on the tokens of a script the
parse adapter with the recording handler answers as the consumer above does
(`Param.feed_agree`); so the lexer's public calls, and the library's reader built on them, tell
the handler the traversal's calls on a file and finish (`library_parses_file`,
`reader_reads_files`).

On every input, the parse adapter and the consumer above are related too, as long as the tokens
taken stand for a start of what a parser takes or for such a start and the first item that no
script continues with (`Param.link_consumersG`): where the consumer above fails at a token, the
parse adapter fails at it too, at whitespace or a comment because no parser takes it. As the
lexer with the consumer above takes only such tokens, the lexer with the parse adapter returns a
result at the end of the input only where the lexer with the consumer above does, which is only
on a file; and so the reader finishes only on files (`reader_finishes_only_on_files`).

The relation goes on after the call at which the consumer above fails: the parse adapter then
stands where the parser's recording run over the tokens taken leaves it, as the library's lexer
hands no whitespace or comment to a consumer that does not take them (`Param.noLayout`, from the
chain of lexers). The library's parser, as a consumer of the specification, answers as the
consumer above does (`Param.consumer_agrees`). So on every input, ended or not, the reader tells
the handler the parser's calls on the tokens the lexer hands over, nothing before the first, and
finishes where the lexer does (`reader_lexes_then_parses`).
-/

/-!
## What holds

Each theorem below is proved in the modules imported above, and followed by the axioms its proof
uses: only those of Lean's standard library, no `sorry` and no axiom of its own. The build fails if
that changes.
-/

namespace BSmtLib.EndToEnd

open BSmtLib.Spec BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.ParserProofs.Rejection (libraryParser rcv)

/--
The library's lexer, fed the characters of a file of commands, read from the version, cut into any
slices, and then the end of the input, with the library's script parser as a consumer of the lexer
spec: the input ends with the parser's result returned; the tokens the parser took stand for what a
parser receives for the script, version switches and `exit` included; and the parser's recording
run on them has the traversal's events.
-/
theorem library_lexes_file (version : Lexicon.Version) (slices : List Lexicon.Chars)
    {commands : List Tree.Command} (hfile : File version slices.flatten commands) :
    (Proofs.Adapter.lexing Proofs.Adapter.Lexer.lexOps (scriptConsumer version) version [] slices
        true).outcome.isFinished = true ∧
      (Proofs.Adapter.lexing Proofs.Adapter.Lexer.lexOps (scriptConsumer version) version []
        slices true).taken.map (rcv ∘ itemOf) = received commands ∧
      (libraryParser.parse version ((Proofs.Adapter.lexing Proofs.Adapter.Lexer.lexOps
        (scriptConsumer version) version [] slices true).taken.map libItem)).1 =
        record version commands :=
  lexing_file _ Proofs.Lexer.correctWithConsumers version slices hfile

/--
info: 'BSmtLib.EndToEnd.library_lexes_file' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms library_lexes_file

/--
The library's lexer, fed the characters of any input, read from the version, cut into any slices,
and then the end of the input, with the library's script parser as a consumer of the lexer spec,
ends in one of four ways, with the parser's recording run on the tokens taken as the specification
gives it:

- the input reads as a file of commands; the input ends with the parser's result returned, the
  tokens taken stand for what a parser receives for the script, and the run has the traversal's
  events and finishes;
- the tokens taken stand for commands that a declaration naming no supported version ends; the
  parser fails there with `unsupportedVersion`, its run having the traversal's events, the last of
  which is the call of that `set-info`;
- the last token taken is the first that no script continues with (`RejectsFirstUnviable`), an end
  of the input that comes too early among them; the parser rejects it, having made the
  traversal's events before its processing, where a `)` gets none of the calls due at its
  arrival, and no call at it;
- the lexer fails with a lexical error after handing over tokens that stand for a start of what a
  parser takes, the parser waiting with the traversal's events before the next item: read from
  the end of the last version declaration on, in its version, the input has no tokenisation, and
  the tokens taken from there are those maximal to hand over on its longest viable start
  (`Spec.Lexer.Correct`).
-/
theorem library_session (version : Lexicon.Version) (slices : List Lexicon.Chars) :
    let session := Proofs.Adapter.lexing Proofs.Adapter.Lexer.lexOps (scriptConsumer version)
      version [] slices true
    let input := slices.flatten
    let items := session.taken.map (rcv ∘ itemOf)
    let run := libraryParser.parse version (session.taken.map libItem)
    (session.outcome.isFinished = true ∧
        ∃ commands, File version input commands ∧ items = received commands ∧
          run = (record version commands, .finished)) ∨
      (session.outcome = .failed (.consumer (.failed .unsupportedVersion)) ∧
        ∃ commands, Takes version commands items (.failed .unsupportedVersion) ∧
          run = (record version commands, .failed .unsupportedVersion) ∧
          ∃ handled, run.1.getLast? = some (.call .nothing (.commandSetInfo handled))) ∨
      (session.outcome = .failed (.consumer .rejected) ∧
        ∃ commands taken ending, Takes version commands taken ending ∧
          items.dropLast <+: taken ∧ items.dropLast.length < taken.length ∧
          ¬ Parser.Viable version items ∧
          run.2 = .rejected ∧ run.1.filterMap Event.processed = items ∧
          run.1.getLast? = items.getLast?.map .process ∧
          ∃ last, items.getLast? = some last ∧
            eventsBeforeProcessing items.dropLast.length run.1 =
              eventsBeforeProcessingOf last items.dropLast.length (record version commands)) ∨
      (session.outcome = .failed .lexical ∧
        ∃ commands taken ending, Takes version commands taken ending ∧
          items <+: taken ∧ items.length < taken.length ∧
          run = (eventsBefore items.length (record version commands), .waiting) ∧
          session.version = versionAt version commands items.length ∧
          ∃ offset before current, session.taken = before ++ current ∧
            (before = [] ∧ offset = 0 ∨ before.getLast?.map (·.«end».offset) = some offset) ∧
            (¬ ∃ tokens, Lexicon.Tokenization session.version (input.drop offset) tokens) ∧
            ∀ start, Lexer.LongestViableStart session.version (input.drop offset) start →
              ∃ tokens, Lexer.HandoverMaximal session.version start tokens ∧
                current = tokens.map fun token =>
                  (token.handed session.version (input.drop offset)).after
                    (input.take offset)) :=
  lexing_session _ Proofs.Lexer.correctWithConsumers version slices

/--
info: 'BSmtLib.EndToEnd.library_session' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms library_session

/--
The library's lexer, fed the characters of an input that does not read as a file, cut into any
slices, and then the end of the input, with the library's script parser as a consumer of the
lexer spec: the session fails, on a declaration that names no supported version, at the first
token that no script continues with, or with a lexical error, as `library_session` states.
-/
theorem library_fails (version : Lexicon.Version) (slices : List Lexicon.Chars)
    (hnot : ¬ ∃ commands, File version slices.flatten commands) :
    let session := Proofs.Adapter.lexing Proofs.Adapter.Lexer.lexOps (scriptConsumer version)
      version [] slices true
    let input := slices.flatten
    let items := session.taken.map (rcv ∘ itemOf)
    let run := libraryParser.parse version (session.taken.map libItem)
    (session.outcome = .failed (.consumer (.failed .unsupportedVersion)) ∧
        ∃ commands, Takes version commands items (.failed .unsupportedVersion) ∧
          run = (record version commands, .failed .unsupportedVersion) ∧
          ∃ handled, run.1.getLast? = some (.call .nothing (.commandSetInfo handled))) ∨
      (session.outcome = .failed (.consumer .rejected) ∧
        ∃ commands taken ending, Takes version commands taken ending ∧
          items.dropLast <+: taken ∧ items.dropLast.length < taken.length ∧
          ¬ Parser.Viable version items ∧
          run.2 = .rejected ∧ run.1.filterMap Event.processed = items ∧
          run.1.getLast? = items.getLast?.map .process ∧
          ∃ last, items.getLast? = some last ∧
            eventsBeforeProcessing items.dropLast.length run.1 =
              eventsBeforeProcessingOf last items.dropLast.length (record version commands)) ∨
      (session.outcome = .failed .lexical ∧
        ∃ commands taken ending, Takes version commands taken ending ∧
          items <+: taken ∧ items.length < taken.length ∧
          run = (eventsBefore items.length (record version commands), .waiting) ∧
          session.version = versionAt version commands items.length ∧
          ∃ offset before current, session.taken = before ++ current ∧
            (before = [] ∧ offset = 0 ∨ before.getLast?.map (·.«end».offset) = some offset) ∧
            (¬ ∃ tokens, Lexicon.Tokenization session.version (input.drop offset) tokens) ∧
            ∀ start, Lexer.LongestViableStart session.version (input.drop offset) start →
              ∃ tokens, Lexer.HandoverMaximal session.version start tokens ∧
                current = tokens.map fun token =>
                  (token.handed session.version (input.drop offset)).after
                    (input.take offset)) :=
  lexing_fails _ Proofs.Lexer.correctWithConsumers version slices hnot

/--
info: 'BSmtLib.EndToEnd.library_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms library_fails

/--
The library's lexer, with the library's script parser as a consumer of the lexer spec, returns the
parser's result at the end of an input, however cut into slices, exactly when the input reads as a
file.
-/
theorem library_finishes_iff_file (version : Lexicon.Version) (slices : List Lexicon.Chars) :
    (Proofs.Adapter.lexing Proofs.Adapter.Lexer.lexOps (scriptConsumer version) version [] slices
        true).outcome.isFinished = true ↔
      ∃ commands, File version slices.flatten commands :=
  lexing_finishes_iff _ Proofs.Lexer.correctWithConsumers version slices

/--
info: 'BSmtLib.EndToEnd.library_finishes_iff_file' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms library_finishes_iff_file

/--
The library's lexer with the library's parse adapter as its consumer, over the recording handler
and the script parser that allows every version, fed the characters of a file of commands, read
from the version, cut into any slices, by its public calls (`Param.paFeed`: `Lexer.lexSlice` for
each slice, then `Lexer.lexEof`): no call fails, the end of the input returns the parser's
result, and the handler has recorded the calls of the traversal of the script, in order.
-/
theorem library_parses_file (version : Lexicon.Version) (slices : List Lexicon.Chars)
    {commands : List Tree.Command} (hfile : File version slices.flatten commands) :
    ∃ result lexer,
      Param.paFeed (Lexer.new Param.recordingAdapter (Proofs.Adapter.toVersion version)) slices =
        .ok (some result, lexer) ∧
      (Lexer.Internal.handler lexer).handler.reverse = (record version commands).filter Event.isCall :=
  Param.adapter_feed_file version slices hfile

/--
info: 'BSmtLib.EndToEnd.library_parses_file' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms library_parses_file

/-! ### The reader -/

/--
The library's script reader (`Reader.script`), with the recording handler and the posture that
allows every version, fed a file in any slices by `Reader.readSlice` and then the end of the input
by `Reader.readEof`, tells the handler the calls for the file's commands and finishes.
-/
theorem reader_reads_files : Spec.Reader.ReadsFiles libraryReader :=
  libraryReader_readsFiles

/--
info: 'BSmtLib.EndToEnd.reader_reads_files' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reader_reads_files

/--
The library's script reader (`Reader.script`), with the recording handler and the posture that
allows every version, fed an input in any slices by `Reader.readSlice` and then the end of the
input by `Reader.readEof`, finishes only if the input is a file.
-/
theorem reader_finishes_only_on_files : Spec.Reader.FinishesOnlyOnFiles libraryReader :=
  libraryReader_finishesOnlyOnFiles

/--
info: 'BSmtLib.EndToEnd.reader_finishes_only_on_files' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reader_finishes_only_on_files

/--
The library's script reader (`Reader.script`), with the recording handler and the posture that
allows every version, fed an input in any slices by `Reader.readSlice` and then, if the input has
ended, the end of the input by `Reader.readEof`, does what the library's lexer, which is correct
with every consumer, does with the library's script parser as its consumer: it tells the handler
the parser's calls on the tokens the lexer hands over, nothing before the first token, and
finishes exactly where the lexer does.
-/
theorem reader_lexes_then_parses : Spec.Reader.LexesThenParses libraryReader :=
  libraryReader_lexesThenParses

/--
info: 'BSmtLib.EndToEnd.reader_lexes_then_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reader_lexes_then_parses

/-! ## What is trusted

A reader of the theorems above trusts the specification (`BSmtLib.Spec`), the statements in this
file, and the definitions in `BSmtLib.EndToEnd.Adapters`, `BSmtLib.ParserProofs.Adapters` and
`BSmtLib.Proofs.Adapters`, which put the lexer, the parser, the parse adapter and the reader into
the spec's shapes: the adapters. Everything else Lean checks. The check below lists the adapters,
every definition that the statements of the theorems in this file rest on outside the
specification, the library and Lean (`BSmtLib.Trusted`), and fails the build if one of them is
declared outside those modules.

One adapter reads the library from inside: where a call of the reader fails, the library gives no
reader back, so `readerRun` takes the calls the handler holds from the reader's lexer after the
failed step (`sliceStepped`, `eofStepped`, `lexerCalls`).
-/

/--
info: 8 theorems, stated with 79 adapters:
BSmtLib.EndToEnd.Adapters:
  BSmtLib.EndToEnd.Param.PLexer
  BSmtLib.EndToEnd.Param.RecAdapter
  BSmtLib.EndToEnd.Param.paFeed
  BSmtLib.EndToEnd.Param.recordingAdapter
  BSmtLib.EndToEnd.RecReader
  BSmtLib.EndToEnd.ScriptError
  BSmtLib.EndToEnd.answerOf
  BSmtLib.EndToEnd.eofStepped
  BSmtLib.EndToEnd.itemOf
  BSmtLib.EndToEnd.lexerCalls
  BSmtLib.EndToEnd.libItem
  BSmtLib.EndToEnd.libraryReader
  BSmtLib.EndToEnd.readerOf
  BSmtLib.EndToEnd.readerRun
  BSmtLib.EndToEnd.scriptConsumer
  BSmtLib.EndToEnd.sliceStepped
BSmtLib.ParserProofs.Adapters.Bridge:
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
  BSmtLib.ParserProofs.Bridge.signature
  BSmtLib.ParserProofs.Bridge.symbol
  BSmtLib.ParserProofs.Bridge.symbolOrWildcard
  BSmtLib.ParserProofs.Bridge.version
  BSmtLib.ParserProofs.Rejection.bytesOf
  BSmtLib.ParserProofs.Rejection.rcv
  BSmtLib.ParserProofs.allReserved
  BSmtLib.ParserProofs.decodeReserved
  BSmtLib.ParserProofs.valuesOf
BSmtLib.ParserProofs.Adapters.Handler:
  BSmtLib.ParserProofs.attributeValueOf
  BSmtLib.ParserProofs.recordingCall
  BSmtLib.ParserProofs.recordingLibrary
  BSmtLib.ParserProofs.recordingLibraryTerms
  BSmtLib.ParserProofs.sExprNodeOf
  BSmtLib.ParserProofs.termNodeOf
BSmtLib.ParserProofs.Adapters.Run:
  BSmtLib.ParserProofs.Rejection.LibItem
  BSmtLib.ParserProofs.Rejection.libEnding
  BSmtLib.ParserProofs.Rejection.libraryParser
  BSmtLib.ParserProofs.afterLastProcess
  BSmtLib.ParserProofs.arriveAt
  BSmtLib.ParserProofs.discardOf
  BSmtLib.ParserProofs.driveInput
  BSmtLib.ParserProofs.driveParse
  BSmtLib.ParserProofs.isProcessing
  BSmtLib.ParserProofs.processAt
  BSmtLib.ParserProofs.switchOf
  BSmtLib.ParserProofs.unrestrictedPosture
BSmtLib.Proofs.Adapters:
  BSmtLib.Proofs.Adapter.AnswerM
  BSmtLib.Proofs.Adapter.Answering
  BSmtLib.Proofs.Adapter.Answering.consume
  BSmtLib.Proofs.Adapter.Answering.entry
  BSmtLib.Proofs.Adapter.Answering.requests
  BSmtLib.Proofs.Adapter.Answering.switched
  BSmtLib.Proofs.Adapter.LexOps
  BSmtLib.Proofs.Adapter.LexOps.next
  BSmtLib.Proofs.Adapter.LexOps.runInput
  BSmtLib.Proofs.Adapter.LexOps.standing
  BSmtLib.Proofs.Adapter.Lexer.lexOps
  BSmtLib.Proofs.Adapter.eofResult
  BSmtLib.Proofs.Adapter.failureOf
  BSmtLib.Proofs.Adapter.fromVersion
  BSmtLib.Proofs.Adapter.instConsumeAnsweringResultOptionError
  BSmtLib.Proofs.Adapter.instConsumeFromAnsweringBatchCursorAnswerMResultOptionError
  BSmtLib.Proofs.Adapter.lexing
  BSmtLib.Proofs.Adapter.toContent
  BSmtLib.Proofs.Adapter.toHanded
  BSmtLib.Proofs.Adapter.toLayout
  BSmtLib.Proofs.Adapter.toLocation
  BSmtLib.Proofs.Adapter.toReservedKind
  BSmtLib.Proofs.Adapter.toTokenType
  BSmtLib.Proofs.Adapter.toVersion
-/
#guard_msgs in
#adapters within BSmtLib.EndToEnd.Adapters BSmtLib.ParserProofs.Adapters
    BSmtLib.Proofs.Adapters

end BSmtLib.EndToEnd
