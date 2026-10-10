import BSmtLib.Proofs.Lexer.VNaive
import BSmtLib.Proofs.Lexer.WRustPort
import BSmtLib.Proofs.Lexer.X1BatchInCore
import BSmtLib.Token.Syntax
import BSmtLib.Spec.Lexer

/-!
# The adapter from the lexers to the spec

This module is trusted, as the spec is. `Spec.Lexer.Correct` is a property of a function that
gives what a lexer has done in the spec's form; `fedInput` is that function for each lexer of the
chain: what the lexer has handed over after being fed slices and then, if the input has ended,
the end of the input, and whether a call failed. A theorem stated through it says only what it
makes of the lexer, so it is to be read like the spec: it has to run the lexer as a consumer
would, and record what the lexer hands over as it is, or the theorem says nothing about the
lexer.

So `fedInput` fixes nothing up. It feeds the slices and then, if the input has ended and no call
has failed, the end of the input, with a consumer that takes every token of each cursor and
records it. The consumer does not take whitespace and comments, never finishes and never
switches the version. Each field of a recorded token is read from the cursor the lexer hands it
over in, and is only converted from the library's types to the spec's, by one small function per
type. Each lexer is given to `fedInput` by its operations alone (`Ops`), which name the lexer's
own functions and do nothing else.

A lexer that stops at its first error does not give itself back from a call that fails, so its
consumer cannot be read after it from the public calls. `fedInput` feeds the slices and the end
of the input by the steps that the public calls run (`Ops.lexSliceStep`, `Ops.lexEofStep`),
through the lexer's own entry point that gives the lexer back also when the step fails; each
public call is its step followed by dropping the lexer on an error.
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
def toHanded {batch : BatchTag} (cursor : BatchCursor batch) (token : Token batch) :
    Option Handed :=
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
def takeRest {batch : BatchTag} (cursor : BatchCursor batch) :
    Option (List Handed) × { c : BatchCursor batch // c.Follows cursor } :=
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

/-- The operations of a lexer, with the consumer `Collector`. `fedInput` runs the steps
(`lexSliceStep`, `lexEofStep`); the public calls (`lexSlice`, `lexEof`) are those that run
them. -/
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
  /-- The step that `lexSlice` runs, run by the lexer's entry point that gives the lexer back
  also when the step fails. -/
  lexSliceStep : Lexer → ByteSlice →
    Id (Except (LexError Unit) (ControlFlow (Located Empty)) × Lexer)
  /-- The step that `lexEof` runs, run by the lexer's entry point that gives the lexer back
  also when the step fails. -/
  lexEofStep : Lexer → Id (Except (LexError Unit) (ControlFlow (Located Empty)) × Lexer)
  /-- The consumer of the lexer. -/
  handler : Lexer → Collector

/--
Feeds the lexer the end of the input, by the step of `lexEof`, and gives the consumer and
whether the call failed, with the consumer as the call left it. The consumer never finishes, so
the call does not break.
-/
def feedEnd (ops : Ops) (lexer : ops.Lexer) : Collector × Bool :=
  match ops.lexEofStep lexer with
  | (.ok .continue, lexer) => (ops.handler lexer, false)
  | (.ok (.break finished), _) => finished.value.elim
  | (.error _, lexer) => (ops.handler lexer, true)

/--
Feeds the lexer the slices by the step of `lexSlice`, and then, if the input has ended, the end
of the input by the step of `lexEof`, and gives the consumer and whether a call failed. The
feeding stops at the first call that fails, with the consumer as that call left it. The
consumer never finishes, so no call breaks.
-/
def feedInput (ops : Ops) (lexer : ops.Lexer) (ended : Bool) :
    List Spec.Lexicon.Chars → Collector × Bool
  | [] => if ended then feedEnd ops lexer else (ops.handler lexer, false)
  | slice :: slices =>
    match ops.lexSliceStep lexer slice.toByteArray.toByteSlice with
    | (.ok .continue, lexer) => feedInput ops lexer ended slices
    | (.ok (.break finished), _) => finished.value.elim
    | (.error _, lexer) => (ops.handler lexer, true)

/--
What the lexer has done after being fed the slices under the version and then, if the input has
ended, the end of the input: what it has handed over, and whether a call failed.
-/
def fedInput (ops : Ops) (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars)
    (ended : Bool) : Spec.Lexer.Fed :=
  let (collector, failed) :=
    feedInput ops (ops.new { handed := [] } (toVersion version)) ended slices
  { handed := collector.handed, failed }

/-! ## The lexers -/

/-- The naive lexer `Lexer.VNaive`. -/
def VNaive.ops : Ops where
  Lexer := Lexer.VNaive.Lexer Collector
  AfterError := Lexer.VNaive.Lexer.AfterError Collector .failFast
  AfterEofError := Lexer.VNaive.Lexer.AfterEofError Collector .failFast
  new := Lexer.VNaive.Lexer.new
  lexSlice := Lexer.VNaive.Lexer.lexSlice
  lexEof := Lexer.VNaive.Lexer.lexEof
  lexSliceStep lexer slice :=
    lexer.run (Lexer.VNaive.lexSliceStep (Recovery.failFast == .recovering)
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast) slice)
  lexEofStep lexer :=
    lexer.run (Lexer.VNaive.lexEofStep (Recovery.failFast == .recovering)
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast))
  handler := Lexer.VNaive.Lexer.handler

/-- The Rust lexer ported to Lean `Lexer.WRustPort`. -/
def WRustPort.ops : Ops where
  Lexer := Lexer.WRustPort.Lexer Collector
  AfterError := Lexer.WRustPort.Lexer.AfterError Collector .failFast
  AfterEofError := Lexer.WRustPort.Lexer.AfterEofError Collector .failFast
  new := Lexer.WRustPort.Lexer.new
  lexSlice := Lexer.WRustPort.Lexer.lexSlice
  lexEof := Lexer.WRustPort.Lexer.lexEof
  lexSliceStep lexer slice :=
    lexer.run (Lexer.WRustPort.lexSliceStep (ops := Lexer.WRustPort.Rust.ops)
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast) slice)
  lexEofStep lexer :=
    lexer.run (Lexer.WRustPort.lexEofStep (ops := Lexer.WRustPort.Rust.ops)
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast))
  handler := Lexer.WRustPort.Lexer.handler

/-- The lexer with the batch kept in its state `Lexer.X1BatchInCore`, which has the type of the
Rust lexer ported to Lean and lexes by functions of its own. -/
def X1BatchInCore.ops : Ops where
  Lexer := Lexer.WRustPort.Lexer Collector
  AfterError := Lexer.WRustPort.Lexer.AfterError Collector .failFast
  AfterEofError := Lexer.WRustPort.Lexer.AfterEofError Collector .failFast
  new := Lexer.WRustPort.Lexer.new
  lexSlice := Lexer.X1BatchInCore.Lexer.lexSlice
  lexEof := Lexer.X1BatchInCore.Lexer.lexEof
  lexSliceStep lexer slice :=
    lexer.run (Lexer.WRustPort.lexSliceStep (ops := Lexer.X1BatchInCore.ops)
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast) slice)
  lexEofStep lexer :=
    lexer.run (Lexer.WRustPort.lexEofStep (ops := Lexer.X1BatchInCore.ops)
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast))
  handler := Lexer.WRustPort.Lexer.handler

/-- The library's lexer `BSmtLib.Lexer`. -/
def Lexer.ops : Ops where
  Lexer := BSmtLib.Lexer Collector
  AfterError := BSmtLib.Lexer.AfterError Collector .failFast
  AfterEofError := BSmtLib.Lexer.AfterEofError Collector .failFast
  new := BSmtLib.Lexer.new
  lexSlice := BSmtLib.Lexer.lexSlice
  lexEof := BSmtLib.Lexer.lexEof
  lexSliceStep lexer slice :=
    BSmtLib.Lexer.Internal.run lexer (BSmtLib.Lexer.Internal.lexSliceStep
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast) slice)
  lexEofStep lexer :=
    BSmtLib.Lexer.Internal.run lexer (BSmtLib.Lexer.Internal.lexEofStep
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast))
  handler := BSmtLib.Lexer.Internal.handler

end BSmtLib.Proofs.Adapter
