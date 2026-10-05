import BSmtLib.Proofs.Lexer.V1Naive
import BSmtLib.Token.Syntax
import BSmtLib.Spec.Lexer

/-!
# The naive lexer as the spec sees it

`lex` runs the naive lexer on an input cut into slices and gives what the lexer hands over in
the spec's form, `Spec.Lexer.Handed`. It is the lexer of which `Spec.Lexer.LexerCorrect` is
stated.

The consumer takes every token it is handed and records it. It does not take whitespace and
comments, never finishes and never switches the version. Each field of a recorded token is
read from the cursor the lexer hands it over in, and is only converted from the library's
types to the spec's: nothing is computed but the kind of reserved word, which the library
gives through `BatchCursor.syntax`.
-/

namespace BSmtLib.Proofs.Lexer.V1Spec

open BSmtLib.Proofs.Lexer.V1Naive
open BSmtLib.Spec.Lexer (Handed TokenType ReservedKind)

/-- The library's version for a version of the spec. -/
def toVersion : Spec.Lexicon.Version → Version
  | .v2_0 => .v2_0
  | .v2_5 => .v2_5
  | .v2_6 => .v2_6
  | .v2_7 => .v2_7

/-- The spec's location for a location of the library. -/
def toLocation (location : Location) : Spec.Lexer.Location :=
  { offset := location.offset, line := location.line, column := location.column }

/-- The spec's token type for a category of the library; none for whitespace and comments,
which the spec does not hand over. -/
def toTokenType : TokenCategory → Option TokenType
  | .parenOpen => some .parenOpen
  | .parenClose => some .parenClose
  | .numeral => some .numeral
  | .decimal => some .decimal
  | .hexadecimal => some .hexadecimal
  | .binary => some .binary
  | .string => some .string
  | .keyword => some .keyword
  | .unquotedSymbol => some .unquotedSymbol
  | .quotedSymbol => some .quotedSymbol
  | .whitespace | .comment => none
  | .endOfFile => some .endOfFile

/-- The kind of reserved word a syntax token is, if it is one. -/
def toReservedKind : SyntaxToken → Option ReservedKind
  | .reserved word => some (if word.isCommandName then .command else .general)
  | _ => none

/-- A token as the cursor reports it, in the spec's form; none for whitespace and comments. -/
def toHanded (cursor : BatchCursor) (token : Token) : Option Handed :=
  (toTokenType (cursor.category token)).map fun type =>
    { type
      start := toLocation (cursor.span token).start
      «end» := toLocation (cursor.span token).end
      reserved := toReservedKind (cursor.syntax token cursor.version)
      content := (cursor.content token).toByteArray.toList }

/-- A consumer that records every token it is handed, in the spec's form. -/
structure Collector where
  /-- The tokens handed over so far, in order. -/
  handed : List Handed

/--
The consumer takes the next token of the cursor, records it and continues. It does not take
whitespace and comments, and fails if it is handed one.
-/
instance : Consume Collector Id Empty Unit where
  consumesWhitespaceAndComments := false
  consume cursor h := do
    let (token, rest) := cursor.next h
    match toHanded cursor token with
    | some handed =>
      modify fun collector => { handed := collector.handed ++ [handed] }
      return (.ok .continue, rest)
    | none => return (.error (), rest)

/--
Feeds the lexer the slices and then the end of the input, and gives what the consumer has
recorded, or none if a call fails. The consumer never finishes, so no call breaks.
-/
def feed (lexer : V1Naive.Lexer Collector) : List Spec.Lexicon.Chars → Option (List Handed)
  | [] =>
    match lexer.lexEof with
    | .ok (.continue, lexer) => some lexer.handler.handed
    | .ok (.break finished, _) => finished.value.elim
    | .error _ => none
  | slice :: slices =>
    match lexer.lexSlice slice.toByteArray.toByteSlice with
    | .ok (.continue, lexer) => feed lexer slices
    | .ok (.break finished, _) => finished.value.elim
    | .error _ => none

/--
What the naive lexer hands over when fed the slices and then the end of the input, under the
version, or none if a call fails.
-/
def lex (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars) :
    Option (List Handed) :=
  feed (V1Naive.Lexer.new { handed := [] } (toVersion version)) slices

end BSmtLib.Proofs.Lexer.V1Spec
