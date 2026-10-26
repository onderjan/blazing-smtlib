module

public import BSmtLibSpec.Lexer
public import BSmtLibSpec.Parser

@[expose] public section

/-!
# Readers

A reader is a lexer whose consumer is a parser. It is fed an input in slices, and then the end
of the input, and tells its handler what the input holds.

- On every input, a reader does what a correct lexer does with a correct parser as its consumer
  (`LexesThenParses`).
- On a file, the handler is told the traversal's calls for the file's commands, and the reader
  finishes (`ReadsFiles`).
- On any other input, the reader does not finish (`FinishesOnlyOnFiles`).
- The calls on a file determine the file's initial version and commands
  (`CallsDetermineCommands`).

A reader can have a parser of any syntactic category; only the reader of scripts is specified
here. It reads under the policy that allows every version, and is seen through a recording
handler, as in `Parser.Properties.record`. Where its tokens are located, and where the discarding
after `exit` began, are stated by the lexer (`Lexer.Runs`) and not again here.
-/

namespace BSmtLibSpec.Reader

open BSmtLibSpec.Lexicon BSmtLibSpec.Grammar BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open Regex (Chars)

/-! ## Reading an input -/

/--
The calls a handler is told for the commands with the initial version, in order: the switch to
that version, then the traversal's calls.
-/
def calls (version : Version) (commands : List Tree.Command) : List Event :=
  (record version commands).filter Event.isCall

/--
A reader as its recording runs show it: given the initial version, the input in slices and
whether the input has ended, the calls its handler was told, in order, and whether it finished.
-/
structure RecordingReader where
  read : Version → List Chars → Bool → List Event × Bool

/-! ## Reading files -/

/--
Property: a reader reads a file to its end: it tells the handler the calls for the file's
commands, and finishes.

The reader is fed the file in any slices, and then the end of the input.
-/
def ReadsFiles (reader : RecordingReader) : Prop :=
  ∀ version slices commands, File version slices.flatten commands →
    reader.read version slices true = (calls version commands, true)

/--
Property: a reader finishes only if its input is a file.

The reader is fed the input in any slices, and then the end of the input.
-/
def FinishesOnlyOnFiles (reader : RecordingReader) : Prop :=
  ∀ version slices, (reader.read version slices true).2 = true →
    ∃ commands, File version slices.flatten commands

/--
Property: the calls for the commands of a file determine the file's initial version and its
commands.

So the handler is told the whole file but for three things that no call carries: the whitespace
and the comments; everything after `exit`, which is not read, and which a caller takes from the
input where the lexer began to discard; and, in 2.0, how a string literal is spelled, since two
spellings can stand for the same characters (`"\a"` and `"\\a"`). `BSmtLibSpec.Facts.Reader`
proves it.
-/
def CallsDetermineCommands : Prop :=
  ∀ version version' input input' commands commands',
    File version input commands → File version' input' commands' →
    calls version commands = calls version' commands' →
    version = version' ∧ commands = commands'

/-! ## A lexer with a parser as its consumer -/

/--
What a parser receives for a token that a lexer hands over, if anything: the end of the input
for the end-of-file token, nothing for whitespace and comments, and the syntax token it stands
for for every other token.
-/
def _root_.BSmtLibSpec.Lexer.Handed.received (handed : Lexer.Handed) : Option Received :=
  match handed.type with
  | .parenOpen => some (.token .parenOpen)
  | .parenClose => some (.token .parenClose)
  | .numeral => some (.token (.numeral handed.content))
  | .decimal => some (.token (.decimal handed.content))
  | .hexadecimal => some (.token (.hexadecimal handed.content))
  | .binary => some (.token (.binary handed.content))
  | .string => some (.token (.string handed.content))
  | .keyword => some (.token (.keyword handed.content))
  | .unquotedSymbol =>
    some (.token (if handed.reserved.isSome then .reserved handed.content
      else .symbol ⟨handed.content, false⟩))
  | .quotedSymbol => some (.token (.symbol ⟨handed.content, true⟩))
  | .whitespace | .comment => none
  | .endOfFile => some .endOfInput

/--
The requests a parser's run made of its producer after the last item it processed: the version
switch, if any, the last one counting, and whether it had the rest discarded.
-/
def requestsAfterLast (events : List Event) : Option Version × Bool :=
  (events.reverse.takeWhile fun event => event.processed.isNone).foldr
    (fun event requests => match event with
      | .producerSwitch version => (some version, requests.2)
      | .producerDiscard => (requests.1, true)
      | _ => requests)
    (none, false)

/--
A parser as a plain consumer of a lexer, given the item it takes for each token handed over.
After each token, it answers by how its run on the tokens so far ends: it breaks when the run
has finished, fails when the run has rejected an item or failed, and continues otherwise; at the
end of the input it fails rather than wait. It asks for the version switch and the discarding
that its run asked of its producer after the last token.
-/
def consumer (parser : RecordingParser)
    (item : Lexer.Handed → parser.Item) (version : Version) : Lexer.Consumer where
  Result := Unit
  Error := Unit
  concrete := false
  answer taken :=
    match (parser.parse version (taken.map item)).2 with
    | .finished => .break ()
    | .waiting =>
      if taken.getLast?.map (·.type) = some .endOfFile then .fail () else .continue
    | .rejected | .failed _ => .fail ()
  switchTo taken := (requestsAfterLast (parser.parse version (taken.map item)).1).1
  discards taken := (requestsAfterLast (parser.parse version (taken.map item)).1).2

/--
Property: on every input, ended or not, a reader does what a correct lexer does with a correct
parser as its consumer.

The lexer is correct with every consumer (`Lexer.CorrectWithConsumers`). The parser follows the
traversal and rejects the first item that no script continues with (`FollowsTheTraversal`,
`RejectsFirstUnviable`); it takes each token that a lexer can hand over in some version for what
the token stands for. The handler is told the parser's calls on the tokens the lexer handed
over, and the reader finishes when the lexer does. Until the lexer hands over the first token,
the handler is told nothing, not even the version.
-/
def LexesThenParses (reader : RecordingReader) : Prop :=
  ∃ (lexing : Lexer.Lexing) (parser : RecordingParser) (item : Lexer.Handed → parser.Item),
    Lexer.CorrectWithConsumers lexing ∧ FollowsTheTraversal parser ∧
    RejectsFirstUnviable parser ∧
    (∀ handed received version, handed.received = some received →
      received.OfVersion version → parser.stands (item handed) = received) ∧
    ∀ version slices ended,
      let session := lexing (consumer parser item version) version [] slices ended
      reader.read version slices ended =
        (if session.taken = [] then []
          else (parser.parse version (session.taken.map item)).1.filter Event.isCall,
          session.outcome.isFinished)

end BSmtLibSpec.Reader
