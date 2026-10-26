module

public import BSmtLib.Facts.Trusted
public import BSmtLib.Facts.Lexer
public import BSmtLib.Facts.Proofs.Reader.Valid
public import BSmtLib.Facts.Proofs.Reader.Session
public import BSmtLib.Facts.Proofs.Reader.Param.Final
public import BSmtLib.Facts.Proofs.Reader.Reader
public import BSmtLib.Facts.Proofs.Reader.Lexes.Reader

@[expose] public section

/-!
# From characters to the calls of the traversal

The composition of the lexer proofs (`BSmtLib.Facts.Lexer`) with the parser proofs
(`BSmtLib.Facts.Parser`) at the level of the specification.

- The consumer: `Adapters.scriptConsumer version` is the library's script parser as a consumer of
  the lexer spec (`BSmtLibSpec.Lexer.Consumer`): after each token it answers as the parser's
  recording run (`Rejection.libraryParser`) on the tokens taken so far ends, each token read as the
  parser's token that stands for it, and it asks for the version switch and the discarding
  that the run asks of its producer after the last token's processing.
- The lexer: `Facts.Lexer.correctWithConsumers` states that the library's lexer, fed by the
  adapter with every consumer of the spec, does what `BSmtLibSpec.Lexer.Runs` states, relative to
  what it hands over to the collector, which is `BSmtLibSpec.Lexer.Correct`.
- The file: `BSmtLibSpec.Grammar.File` reads the characters of a file as commands, each in the
  version in force, from its version declarations on (Reading M1) up to `exit` (Reading M2).

So the library's lexer, fed the characters of a file cut into any slices and then the end of the
input, with that consumer, takes the tokens of the commands, switching the version after every
version declaration and discarding after `exit`, and returns the parser's result at the end of the
input; and the parser's recording run on what the lexer handed it is the traversal's
(`library_lexes_file`). The proof (`Facts.Proofs.Reader.Valid.lexing_file`) holds for every lexer
that is correct with every consumer.

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

namespace BSmtLib.Facts.Reader

open BSmtLibSpec BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLib.Facts.Parser.Adapters.Run.Rejection (libraryParser)
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection (rcv)
open BSmtLib.Facts.Proofs.Reader.Lexes.Reader BSmtLib.Facts.Proofs.Reader.Reader
open BSmtLib.Facts.Proofs.Reader.Session BSmtLib.Facts.Proofs.Reader.Valid

/--
The library's lexer, fed the characters of a file of commands, with the initial version, cut into
any slices, and then the end of the input, with the library's script parser as a consumer of the
lexer spec: the input ends with the parser's result returned; the tokens the parser took stand for
what a parser receives for the script, version switches and `exit` included; and the parser's
recording run on them has the traversal's events.
-/
theorem library_lexes_file (version : Lexicon.Version) (slices : List Regex.Chars)
    {commands : List Tree.Command} (hfile : File version slices.flatten commands) :
    (Lexer.Adapters.lexing Lexer.Adapters.Lexer.lexOps
    (Adapters.scriptConsumer version) version [] slices
        true).outcome.isFinished = true ∧
      (Lexer.Adapters.lexing Lexer.Adapters.Lexer.lexOps
          (Adapters.scriptConsumer version) version []
        slices true).taken.map (rcv ∘ Adapters.itemOf) = received commands ∧
      (libraryParser.parse version ((Lexer.Adapters.lexing Lexer.Adapters.Lexer.lexOps
        (Adapters.scriptConsumer version) version [] slices true).taken.map Adapters.libItem)).1 =
        record version commands :=
  lexing_file _ Facts.Lexer.correctWithConsumers version slices hfile

/--
info: 'BSmtLib.Facts.Reader.library_lexes_file' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms library_lexes_file

/--
The library's lexer, fed the characters of any input, with the initial version, cut into any slices,
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
  (`BSmtLibSpec.Lexer.Correct`).
-/
theorem library_session (version : Lexicon.Version) (slices : List Regex.Chars) :
    let session := Lexer.Adapters.lexing Lexer.Adapters.Lexer.lexOps
        (Adapters.scriptConsumer version)
      version [] slices true
    let input := slices.flatten
    let items := session.taken.map (rcv ∘ Adapters.itemOf)
    let run := libraryParser.parse version (session.taken.map Adapters.libItem)
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
          ¬ Parser.Properties.Viable version items ∧
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
  lexing_session _ Facts.Lexer.correctWithConsumers version slices

/--
info: 'BSmtLib.Facts.Reader.library_session' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms library_session

/--
The library's lexer, fed the characters of an input that does not read as a file, cut into any
slices, and then the end of the input, with the library's script parser as a consumer of the
lexer spec: the session fails, on a declaration that names no supported version, at the first
token that no script continues with, or with a lexical error, as `library_session` states.
-/
theorem library_fails (version : Lexicon.Version) (slices : List Regex.Chars)
    (hnot : ¬ ∃ commands, File version slices.flatten commands) :
    let session := Lexer.Adapters.lexing Lexer.Adapters.Lexer.lexOps
        (Adapters.scriptConsumer version)
      version [] slices true
    let input := slices.flatten
    let items := session.taken.map (rcv ∘ Adapters.itemOf)
    let run := libraryParser.parse version (session.taken.map Adapters.libItem)
    (session.outcome = .failed (.consumer (.failed .unsupportedVersion)) ∧
        ∃ commands, Takes version commands items (.failed .unsupportedVersion) ∧
          run = (record version commands, .failed .unsupportedVersion) ∧
          ∃ handled, run.1.getLast? = some (.call .nothing (.commandSetInfo handled))) ∨
      (session.outcome = .failed (.consumer .rejected) ∧
        ∃ commands taken ending, Takes version commands taken ending ∧
          items.dropLast <+: taken ∧ items.dropLast.length < taken.length ∧
          ¬ Parser.Properties.Viable version items ∧
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
  lexing_fails _ Facts.Lexer.correctWithConsumers version slices hnot

/--
info: 'BSmtLib.Facts.Reader.library_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms library_fails

/--
The library's lexer, with the library's script parser as a consumer of the lexer spec, returns the
parser's result at the end of an input, however cut into slices, exactly when the input reads as a
file.
-/
theorem library_finishes_iff_file (version : Lexicon.Version) (slices : List Regex.Chars) :
    (Lexer.Adapters.lexing Lexer.Adapters.Lexer.lexOps
    (Adapters.scriptConsumer version) version [] slices
        true).outcome.isFinished = true ↔
      ∃ commands, File version slices.flatten commands :=
  lexing_finishes_iff _ Facts.Lexer.correctWithConsumers version slices

/--
info: 'BSmtLib.Facts.Reader.library_finishes_iff_file' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms library_finishes_iff_file

/--
The library's lexer with the library's parse adapter as its consumer, over the recording handler
and the script parser that allows every version, fed the characters of a file of commands, with
the initial version, cut into any slices, by its public calls (`Param.paFeed`: `Lexer.lexSlice` for
each slice, then `Lexer.lexEof`): no call fails, the end of the input returns the parser's
result, and the handler has recorded the calls of the traversal of the script, in order.
-/
theorem library_parses_file (version : Lexicon.Version) (slices : List Regex.Chars)
    {commands : List Tree.Command} (hfile : File version slices.flatten commands) :
    ∃ result lexer,
      Adapters.paFeed (Lexer.new Adapters.recordingAdapter (Lexer.Adapters.toVersion version))
          slices =
        .ok (some result, lexer) ∧
      (Lexer.Internal.handler lexer).handler.reverse =
          (record version commands).filter Event.isCall :=
  Proofs.Reader.Param.Final.adapter_feed_file version slices hfile

/--
info: 'BSmtLib.Facts.Reader.library_parses_file' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms library_parses_file

/-! ### The reader -/

/--
The library's script reader (`Reader.script`), with the recording handler and the posture that
allows every version, fed a file in any slices by `Reader.readSlice` and then the end of the input
by `Reader.readEof`, tells the handler the calls for the file's commands and finishes.
-/
theorem reader_reads_files : BSmtLibSpec.Reader.ReadsFiles Adapters.libraryReader :=
  libraryReader_readsFiles

/--
info: 'BSmtLib.Facts.Reader.reader_reads_files' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reader_reads_files

/--
The library's script reader (`Reader.script`), with the recording handler and the posture that
allows every version, fed an input in any slices by `Reader.readSlice` and then the end of the
input by `Reader.readEof`, finishes only if the input is a file.
-/
theorem reader_finishes_only_on_files : BSmtLibSpec.Reader.FinishesOnlyOnFiles
    Adapters.libraryReader :=
  libraryReader_finishesOnlyOnFiles

/--
info: 'BSmtLib.Facts.Reader.reader_finishes_only_on_files' depends on axioms: [propext, Classical.choice, Quot.sound]
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
theorem reader_lexes_then_parses : BSmtLibSpec.Reader.LexesThenParses Adapters.libraryReader :=
  libraryReader_lexesThenParses

/--
info: 'BSmtLib.Facts.Reader.reader_lexes_then_parses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reader_lexes_then_parses

/-! ## What is trusted

A reader of the theorems above trusts the specification (`BSmtLibSpec`), the statements in this
file, and the definitions in `BSmtLib.Facts.Reader.Adapters`, `BSmtLib.Facts.Parser.Adapters` and
`BSmtLib.Facts.Lexer.Adapters`, which put the lexer, the parser, the parse adapter and the reader
into the spec's shapes: the adapters. Everything else Lean checks. The check below lists the
adapters, every definition that the statements of the theorems in this file rest on outside the
specification, the library and Lean (`BSmtLib.Facts.Trusted`), and fails the build if one of them is
declared outside those modules.
-/

/--
info: 8 theorems, stated with 76 adapters:
BSmtLib.Facts.Lexer.Adapters:
  BSmtLib.Facts.Lexer.Adapters.AnswerM
  BSmtLib.Facts.Lexer.Adapters.Answering
  BSmtLib.Facts.Lexer.Adapters.Answering.consume
  BSmtLib.Facts.Lexer.Adapters.Answering.entry
  BSmtLib.Facts.Lexer.Adapters.Answering.requests
  BSmtLib.Facts.Lexer.Adapters.Answering.switched
  BSmtLib.Facts.Lexer.Adapters.LexOps
  BSmtLib.Facts.Lexer.Adapters.LexOps.next
  BSmtLib.Facts.Lexer.Adapters.LexOps.runInput
  BSmtLib.Facts.Lexer.Adapters.LexOps.standing
  BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps
  BSmtLib.Facts.Lexer.Adapters.eofResult
  BSmtLib.Facts.Lexer.Adapters.failureOf
  BSmtLib.Facts.Lexer.Adapters.fromVersion
  BSmtLib.Facts.Lexer.Adapters.instConsumeAnsweringResultOptionError
  BSmtLib.Facts.Lexer.Adapters.instConsumeFromAnsweringLexerCursorAnswerMResultOptionError
  BSmtLib.Facts.Lexer.Adapters.lexing
  BSmtLib.Facts.Lexer.Adapters.toContent
  BSmtLib.Facts.Lexer.Adapters.toHanded
  BSmtLib.Facts.Lexer.Adapters.toLayout
  BSmtLib.Facts.Lexer.Adapters.toLocation
  BSmtLib.Facts.Lexer.Adapters.toReservedKind
  BSmtLib.Facts.Lexer.Adapters.toTokenType
  BSmtLib.Facts.Lexer.Adapters.toVersion
BSmtLib.Facts.Parser.Adapters.Bridge:
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
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.signature
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.symbol
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.symbolOrWildcard
  BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.version
  BSmtLib.Facts.Parser.Adapters.Bridge.Rejection.bytesOf
  BSmtLib.Facts.Parser.Adapters.Bridge.Rejection.rcv
  BSmtLib.Facts.Parser.Adapters.Bridge.allReserved
  BSmtLib.Facts.Parser.Adapters.Bridge.decodeReserved
  BSmtLib.Facts.Parser.Adapters.Bridge.valuesOf
BSmtLib.Facts.Parser.Adapters.Handler:
  BSmtLib.Facts.Parser.Adapters.Handler.attributeValueOf
  BSmtLib.Facts.Parser.Adapters.Handler.recordingCall
  BSmtLib.Facts.Parser.Adapters.Handler.recordingLibrary
  BSmtLib.Facts.Parser.Adapters.Handler.recordingLibraryTerms
  BSmtLib.Facts.Parser.Adapters.Handler.sExprNodeOf
  BSmtLib.Facts.Parser.Adapters.Handler.termNodeOf
BSmtLib.Facts.Parser.Adapters.Run:
  BSmtLib.Facts.Parser.Adapters.Run.Rejection.LibItem
  BSmtLib.Facts.Parser.Adapters.Run.Rejection.libEnding
  BSmtLib.Facts.Parser.Adapters.Run.Rejection.libraryParser
  BSmtLib.Facts.Parser.Adapters.Run.afterLastProcess
  BSmtLib.Facts.Parser.Adapters.Run.arriveAt
  BSmtLib.Facts.Parser.Adapters.Run.discardOf
  BSmtLib.Facts.Parser.Adapters.Run.driveInput
  BSmtLib.Facts.Parser.Adapters.Run.driveParse
  BSmtLib.Facts.Parser.Adapters.Run.isProcessing
  BSmtLib.Facts.Parser.Adapters.Run.processAt
  BSmtLib.Facts.Parser.Adapters.Run.switchOf
  BSmtLib.Facts.Parser.Adapters.Run.unrestrictedPosture
BSmtLib.Facts.Reader.Adapters:
  BSmtLib.Facts.Reader.Adapters.PLexer
  BSmtLib.Facts.Reader.Adapters.RecAdapter
  BSmtLib.Facts.Reader.Adapters.RecReader
  BSmtLib.Facts.Reader.Adapters.ScriptError
  BSmtLib.Facts.Reader.Adapters.answerOf
  BSmtLib.Facts.Reader.Adapters.itemOf
  BSmtLib.Facts.Reader.Adapters.libItem
  BSmtLib.Facts.Reader.Adapters.libraryReader
  BSmtLib.Facts.Reader.Adapters.paFeed
  BSmtLib.Facts.Reader.Adapters.readerOf
  BSmtLib.Facts.Reader.Adapters.readerRun
  BSmtLib.Facts.Reader.Adapters.recordingAdapter
  BSmtLib.Facts.Reader.Adapters.scriptConsumer
-/
#guard_msgs in
#adapters within BSmtLib.Facts.Reader.Adapters BSmtLib.Facts.Parser.Adapters
    BSmtLib.Facts.Lexer.Adapters

end BSmtLib.Facts.Reader
