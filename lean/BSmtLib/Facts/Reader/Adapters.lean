module

public import BSmtLib.Reader
public import BSmtLibSpec.Reader
public import BSmtLib.Facts.Lexer.Adapters
public import BSmtLib.Facts.Parser.Adapters

@[expose] public section

/-!
# The adapters of the composition

The definitions that the root theorems of `BSmtLib.Facts.Reader` are stated with, beside the
specification, the library, and the adapters of the lexer proofs (`BSmtLib.Facts.Lexer.Adapters`)
and of the parser proofs (`BSmtLib.Facts.Parser.Adapters`), and nothing else:

- `scriptConsumer`: the library's script parser as a consumer of the lexer spec, each token a
  lexer hands over read as the parser's token that stands for it (`itemOf`).
- `Param.recordingAdapter` and `Param.paFeed`: the library's parse adapter with the recording
  handler, and the library's lexer with it fed by its public calls.
- `libraryReader`: the library's script reader as a recording reader of the reader spec.

A theorem stated with a wrong adapter is a theorem about the wrong thing, so these definitions are
trusted: they are to be read with the specification. `#adapters` in `BSmtLib.Facts.Reader` checks
that the root theorems need no other definition outside the specification, the library, the
lexers of the chain and Lean.
-/

open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Bridge.Rejection
open BSmtLib.Facts.Parser.Adapters.Run BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Lexer.Error BSmtLib.Plain

namespace BSmtLib.Facts.Reader.Adapters

open BSmtLibSpec
open BSmtLibSpec.Parser.Properties
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)

/-- The parse adapter with the recording handler and the script parser. -/
abbrev RecAdapter := ParseAdapter (List Event) (ScriptParser (List Event))

/-- The lexer with the parse adapter. -/
abbrev PLexer := BSmtLib.Lexer RecAdapter

/-- The parse adapter with the recording handler, nothing recorded yet, not told the version,
and the script parser with the posture that allows every version. -/
def recordingAdapter : RecAdapter :=
  ParseAdapter.new [] (ScriptParser.new unrestrictedPosture)

/-- The library's lexer with the parse adapter, fed the slices and then the end of the input by
its public calls: the result at the end of the input and the lexer, or the first error. -/
def paFeed (lexer : PLexer) :
    List Regex.Chars →
      Except (LexError (Parser.ParseError Unit)) (Option (Span.Located Unit) × PLexer)
  | [] =>
    match (Lexer.lexEof lexer : Id _) with
    | .ok result => .ok result
    | .error (error, _) => .error error
  | slice :: slices =>
    match (Lexer.lexSlice lexer slice.toByteArray.toByteSlice : Id _) with
    | .ok next => paFeed next slices
    | .error (error, _) => .error error

end BSmtLib.Facts.Reader.Adapters

namespace BSmtLib.Facts.Reader.Adapters

open BSmtLibSpec BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Lexer (Handed Consumer Answer)

/-! ## The parser's token for a handed token -/

/-- The parser's token that stands for a token as a lexer hands it over: by its type, its
content and whether it is a reserved word. -/
def itemOf (handed : Handed) : Parser.Internal.Input :=
  match handed.type with
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral => .constant (.numeral (Numeral.Internal.newUnchecked (bytesOf handed.content)))
  | .decimal => .constant (.decimal (Decimal.Internal.newUnchecked (bytesOf handed.content)))
  | .hexadecimal =>
    .constant (.hexadecimal (HexDigits.Internal.newUnchecked (bytesOf handed.content)))
  | .binary => .constant (.binary (BinDigits.Internal.newUnchecked (bytesOf handed.content)))
  | .string => .constant (.string (StringContent.Internal.newUnchecked (bytesOf handed.content)))
  | .keyword => .keyword (Keyword.Internal.newUnchecked (bytesOf handed.content))
  | .unquotedSymbol =>
    match handed.reserved, decodeReserved handed.content with
    | some _, some word => .reserved word
    | _, _ => .symbol (Symbol.Internal.newUnchecked false (bytesOf handed.content))
  | .quotedSymbol => .symbol (Symbol.Internal.newUnchecked true (bytesOf handed.content))
  -- whitespace and comments are handed over only to a concrete consumer, which the script
  -- consumer is not; they stand for nothing the parser reads, and are given a symbol of their
  -- content only so that every entry has an item
  | .whitespace | .comment =>
    .symbol (Symbol.Internal.newUnchecked false (bytesOf handed.content))
  | .endOfFile => .endOfInput

/-- The parser's item for a handed token. -/
def libItem (handed : Handed) : LibItem :=
  ⟨itemOf handed, by unfold itemOf; split <;> (try split) <;> simp [Bridge.received]⟩

/-! ## The consumer -/

/-- How the script consumer fails: the parser rejected the token, or failed on a version
declaration. -/
inductive ScriptError where
  /-- The parser rejected the token. -/
  | rejected
  /-- The parser failed on a version declaration, with the error. -/
  | failed (error : VersionPolicy.Error)

/-- The answer to a parser's run that ends as given, at a token that is or is not the end of the
input. -/
def answerOf (atEnd : Bool) : Ending → Answer Unit ScriptError
  | .waiting => if atEnd then .fail .rejected else .continue
  | .finished => .break ()
  | .rejected => .fail .rejected
  | .failed error => .fail (.failed error)

/- The consumer fails where the parser waits for more after the end of the input, which the
library's parser does not do; that makes the consumer's obligation at the end of the input hold
by its definition. -/
/--
The library's script parser, from the version, as a consumer of the lexer spec: after each token
it answers as the parser's recording run on the tokens taken so far ends, and asks for the switch
and the discarding that run asks for after the last token's processing.
-/
def scriptConsumer (version : Lexicon.Version) : Consumer where
  Result := Unit
  Error := ScriptError
  concrete := false
  answer taken := answerOf (taken.getLast?.map (·.type) = some .endOfFile)
    (libraryParser.parse version (taken.map libItem)).2
  switchTo taken := switchOf (libraryParser.parse version (taken.map libItem)).1
  discards taken := discardOf (libraryParser.parse version (taken.map libItem)).1

end BSmtLib.Facts.Reader.Adapters

namespace BSmtLib.Facts.Reader.Adapters

open BSmtLibSpec
open BSmtLibSpec.Parser.Properties
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Facts.Lexer.Adapters (toVersion)
open BSmtLib.Facts.Reader.Adapters (PLexer RecAdapter recordingAdapter paFeed)

/-- The script reader with the recording handler. -/
abbrev RecReader := Reader (List Event) (ScriptParser (List Event))

/-- The script reader with the recording handler, nothing recorded yet, and the posture that
allows every version, starting in the version. -/
def readerOf (version : Lexicon.Version) : RecReader :=
  Reader.script [] unrestrictedPosture (toVersion version)

/-- The reader fed the slices by `Reader.readSlice`, and then the end of the input by
`Reader.readEof` if the input has ended: the calls its handler holds afterwards, in order, and
whether the end of the input returned a result. Where a call fails, the handler is the one the
failure carries. -/
def readerRun : RecReader → List Regex.Chars → Bool → List Event × Bool
  | reader, [], false => (reader.handler.reverse, false)
  | reader, [], true =>
    match (reader.readEof : Id _) with
    | .ok (result, reader') => (reader'.handler.reverse, result.isSome)
    | .error failure => (failure.handler.reverse, false)
  | reader, slice :: slices, ended =>
    match (reader.readSlice slice.toByteArray.toByteSlice : Id _) with
    | .ok reader' => readerRun reader' slices ended
    | .error failure => (failure.handler.reverse, false)

/-- The library's script reader, with the recording handler and the posture that allows every
version, as a recording reader. -/
def libraryReader : BSmtLibSpec.Reader.RecordingReader where
  read version slices ended := readerRun (readerOf version) slices ended

end BSmtLib.Facts.Reader.Adapters
