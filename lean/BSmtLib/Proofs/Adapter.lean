import BSmtLib.Proofs.Lexer.V1Naive
import BSmtLib.Proofs.Lexer.V2Batched
import BSmtLib.Proofs.Lexer.V3Runs
import BSmtLib.Proofs.Lexer.V4FastPaths
import BSmtLib.Proofs.Lexer.WRustPort
import BSmtLib.Proofs.Lexer.X1BatchInCore
import BSmtLib.Proofs.Lexer.X2Contents
import BSmtLib.Token.Syntax
import BSmtLib.Spec.Lexer

/-!
# The adapter from the lexers to the spec

This module is trusted, as the spec is. `Spec.Lexer.LexerCorrect` is a property of a function
that gives what a lexer hands over in the spec's form; `handed` is that function for each lexer
of the chain. A theorem stated through `handed` says only what `handed` makes of the lexer, so
it is to be read like the spec: `handed` has to run the lexer as a consumer would, and record
what the lexer hands over as it is, or the theorem says nothing about the lexer.

So `handed` fixes nothing up. It feeds the slices and then the end of the input, with a
consumer that takes every token of each cursor and records it. The consumer does not take
whitespace and comments, never finishes and never switches the version. Each field of a
recorded token is read from the cursor the lexer hands it over in, and is only converted from
the library's types to the spec's, by one small function per type. Each lexer is given to
`handed` by its operations alone (`Ops`), which name the lexer's own functions and do nothing
else.
-/

namespace BSmtLib.Proofs.Adapter

open BSmtLib.Spec.Lexer (Handed TokenType ReservedKind)

/-! ## Conversions to the spec's types -/

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

/-- The spec's content for the content of a token of the library. -/
def toContent (content : ByteSlice) : Spec.Lexicon.Chars :=
  content.toByteArray.toList

/-! ## The consumer -/

/-- A token as the cursor reports it, in the spec's form; none for whitespace and comments. -/
def toHanded (cursor : BatchCursor) (token : Token) : Option Handed :=
  (toTokenType (cursor.category token)).map fun type =>
    { type
      start := toLocation (cursor.span token).start
      «end» := toLocation (cursor.span token).end
      reserved := toReservedKind (cursor.syntax token cursor.version)
      content := toContent (cursor.content token) }

/-- A consumer that records every token it is handed, in the spec's form. -/
structure Collector where
  /-- The tokens handed over so far, in order. -/
  handed : List Handed

/--
Takes the tokens of the cursor from the next one on, in order, and gives them in the spec's
form, with the cursor after the last one taken. Taking stops at a token that is whitespace or a
comment, which is taken, and then gives none.
-/
def takeRest (cursor : BatchCursor) :
    Option (List Handed) × { c : BatchCursor // c.Follows cursor } :=
  if h : cursor.HasNext then
    match cursor.next h with
    | (token, ⟨next, consumed⟩) =>
      match toHanded cursor token with
      | none => (none, ⟨next, consumed.follows⟩)
      | some handed =>
        match takeRest next with
        | (rest, ⟨last, follows⟩) =>
          (rest.map (handed :: ·), ⟨last, follows.trans consumed.follows⟩)
  else
    (some [], ⟨cursor, .refl cursor⟩)
termination_by cursor.remaining
decreasing_by exact consumed.remaining_lt

/--
The consumer takes every token of the cursor, records them and continues. It does not take
whitespace and comments, and fails at the first one it is handed.
-/
instance : Consume Collector Id Empty Unit where
  consumesWhitespaceAndComments := false
  consume cursor h := do
    match cursor.next h with
    | (token, ⟨next, consumed⟩) =>
      match toHanded cursor token with
      | none => return (.error (), ⟨next, consumed⟩)
      | some handed =>
        match takeRest next with
        | (none, ⟨last, follows⟩) => return (.error (), ⟨last, follows.trans_consumed consumed⟩)
        | (some rest, ⟨last, follows⟩) =>
          modify fun collector => { handed := collector.handed ++ handed :: rest }
          return (.ok .continue, ⟨last, follows.trans_consumed consumed⟩)

/-! ## Running a lexer -/

/-- The operations of a lexer, with the consumer `Collector`, that `handed` runs. -/
structure Ops where
  /-- The lexer with its consumer. -/
  Lexer : Type
  /-- What a failed lexing of a slice gives back besides the error. -/
  AfterError : Type
  /-- What a failed lexing of the end of the input gives back besides the error. -/
  AfterEofError : Type
  /-- Constructs the lexer, which stops at its first error. -/
  new : Collector → Version → Lexer
  lexSlice : Lexer → ByteSlice →
    Id (Except (LexError Unit × AfterError) (ControlFlow (Located Empty) × Lexer))
  lexEof : Lexer → Id (Except (LexError Unit × AfterEofError) (ControlFlow (Located Empty) × Lexer))
  /-- The consumer of the lexer. -/
  handler : Lexer → Collector

/--
Feeds the lexer the slices and then the end of the input, and gives what the consumer has
recorded, or none if a call fails. The consumer never finishes, so no call breaks.
-/
def feed (ops : Ops) (lexer : ops.Lexer) : List Spec.Lexicon.Chars → Option (List Handed)
  | [] =>
    match ops.lexEof lexer with
    | .ok (.continue, lexer) => some (ops.handler lexer).handed
    | .ok (.break finished, _) => finished.value.elim
    | .error _ => none
  | slice :: slices =>
    match ops.lexSlice lexer slice.toByteArray.toByteSlice with
    | .ok (.continue, lexer) => feed ops lexer slices
    | .ok (.break finished, _) => finished.value.elim
    | .error _ => none

/--
What the lexer hands over when fed the slices and then the end of the input, under the
version, or none if a call fails.
-/
def handed (ops : Ops) (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars) :
    Option (List Handed) :=
  feed ops (ops.new { handed := [] } (toVersion version)) slices

/-! ## The lexers -/

/-- The naive lexer `Lexer.V1Naive`. -/
def V1Naive.ops : Ops where
  Lexer := Lexer.V1Naive.Lexer Collector
  AfterError := Lexer.V1Naive.Lexer.AfterError Collector .failFast
  AfterEofError := Lexer.V1Naive.Lexer.AfterEofError Collector .failFast
  new := Lexer.V1Naive.Lexer.new
  lexSlice := Lexer.V1Naive.Lexer.lexSlice
  lexEof := Lexer.V1Naive.Lexer.lexEof
  handler := Lexer.V1Naive.Lexer.handler

/-- The batched lexer `Lexer.V2Batched`. -/
def V2Batched.ops : Ops where
  Lexer := Lexer.V1Naive.Lexer Collector
  AfterError := Lexer.V1Naive.Lexer.AfterError Collector .failFast
  AfterEofError := Lexer.V1Naive.Lexer.AfterEofError Collector .failFast
  new := Lexer.V1Naive.Lexer.new
  lexSlice := Lexer.V2Batched.lexSlice
  lexEof := Lexer.V1Naive.Lexer.lexEof
  handler := Lexer.V1Naive.Lexer.handler

/-- The lexer over runs `Lexer.V3Runs`. -/
def V3Runs.ops : Ops where
  Lexer := Lexer.V1Naive.Lexer Collector
  AfterError := Lexer.V1Naive.Lexer.AfterError Collector .failFast
  AfterEofError := Lexer.V1Naive.Lexer.AfterEofError Collector .failFast
  new := Lexer.V1Naive.Lexer.new
  lexSlice := Lexer.V3Runs.lexSlice
  lexEof := Lexer.V1Naive.Lexer.lexEof
  handler := Lexer.V1Naive.Lexer.handler

/-- The lexer with fast paths `Lexer.V4FastPaths`. -/
def V4FastPaths.ops : Ops where
  Lexer := Lexer.V1Naive.Lexer Collector
  AfterError := Lexer.V1Naive.Lexer.AfterError Collector .failFast
  AfterEofError := Lexer.V1Naive.Lexer.AfterEofError Collector .failFast
  new := Lexer.V1Naive.Lexer.new
  lexSlice := Lexer.V4FastPaths.lexSlice
  lexEof := Lexer.V1Naive.Lexer.lexEof
  handler := Lexer.V1Naive.Lexer.handler

/-- The Rust lexer ported to Lean `Lexer.WRustPort`. -/
def WRustPort.ops : Ops where
  Lexer := Lexer.WRustPort.Lexer Collector
  AfterError := Lexer.WRustPort.Lexer.AfterError Collector .failFast
  AfterEofError := Lexer.WRustPort.Lexer.AfterEofError Collector .failFast
  new := Lexer.WRustPort.Lexer.new
  lexSlice := Lexer.WRustPort.Lexer.lexSlice
  lexEof := Lexer.WRustPort.Lexer.lexEof
  handler := Lexer.WRustPort.Lexer.handler

/-- The lexer with the batch kept in its state `Lexer.X1BatchInCore`. -/
def X1BatchInCore.ops : Ops where
  Lexer := Lexer.X1BatchInCore.Lexer Collector
  AfterError := Lexer.X1BatchInCore.Lexer.AfterError Collector .failFast
  AfterEofError := Lexer.X1BatchInCore.Lexer.AfterEofError Collector .failFast
  new := Lexer.X1BatchInCore.Lexer.new
  lexSlice := Lexer.X1BatchInCore.Lexer.lexSlice
  lexEof := Lexer.X1BatchInCore.Lexer.lexEof
  handler := Lexer.X1BatchInCore.Lexer.handler

/-- The lexer with the content buffer `Lexer.X2Contents`. -/
def X2Contents.ops : Ops where
  Lexer := Lexer.X2Contents.Lexer Collector
  AfterError := Lexer.X2Contents.Lexer.AfterError Collector .failFast
  AfterEofError := Lexer.X2Contents.Lexer.AfterEofError Collector .failFast
  new := Lexer.X2Contents.Lexer.new
  lexSlice := Lexer.X2Contents.Lexer.lexSlice
  lexEof := Lexer.X2Contents.Lexer.lexEof
  handler := Lexer.X2Contents.Lexer.handler

/-- The library's lexer `BSmtLib.Lexer`. -/
def Lexer.ops : Ops where
  Lexer := BSmtLib.Lexer Collector
  AfterError := BSmtLib.Lexer.AfterError Collector .failFast
  AfterEofError := BSmtLib.Lexer.AfterEofError Collector .failFast
  new := BSmtLib.Lexer.new
  lexSlice := BSmtLib.Lexer.lexSlice
  lexEof := BSmtLib.Lexer.lexEof
  handler := BSmtLib.Lexer.Internal.handler

end BSmtLib.Proofs.Adapter
