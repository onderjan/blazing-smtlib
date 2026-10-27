module

public import BSmtLib.Lexer.Internal.VNaive
public import BSmtLib.Lexer.Internal.X1BatchInCore
public import BSmtLibSpec.Lexer

@[expose] public section

/-!
# The adapters of the lexer proofs

The definitions that the root theorems of `BSmtLib.Facts.Lexer` are stated with, beside the
specification formalism (`BSmtLibSpec`), the library and the lexers of the chain, and nothing else;
the root theorems of `BSmtLib.Facts.Reader` use some of them too. A theorem stated with a wrong
adapter is a theorem about the wrong thing, so these definitions are trusted: they are to be read
with the formalism. `#adapters` in `BSmtLib.Facts.Lexer` checks that the root theorems need no other
definition outside the formalism, the library, the lexers of the chain and Lean.

`BSmtLibSpec.Lexer.CorrectWithConsumers` is a property of a function that gives what a lexer has
done with a consumer of the formalism, in the formalism's form (`BSmtLibSpec.Lexer.Lexing`);
`lexing` is that function for each lexer of the chain. A theorem stated through it says only what it
makes of the lexer, so it has to run the lexer as a consumer would, and record what the lexer hands
over and how its calls end as they are, or the theorem says nothing about the lexer.

So `lexing` fixes nothing up. It runs the lexer with one consumer, `Answering consumer`, which
answers as the formalism's consumer does. It takes the entries of each cursor one at a time,
and for each:

- records it;
- answers, switches the version and asks for discarding as the formalism's consumer does
  after it.

Each field of a recorded entry is read from the cursor the lexer hands it over in, and is only
converted from the library's types to the formalism's, by one small function per type.

`lexing` feeds the earlier inputs, then the slices and then, if the input has ended, the end of
the input. It gives:

- the entries the consumer has taken;
- where the lexer stands;
- the version and the discarding of the lexer after the last call.

Each lexer is given to `lexing` by its operations alone (`LexOps`), which name the lexer's own
functions and do nothing else.

A lexer that stops at its first error does not give itself back from a call that fails, so its
state cannot be read after it from the public calls. `lexing` feeds the slices and the end of
the input by the steps that the public calls run (`LexOps.lexSliceStep`, `LexOps.lexEofStep`),
through the lexer's own entry point that gives the lexer back also when the step fails, and keeps
the held result as the public calls do; each public call is its step followed by keeping the held
result, and by dropping the lexer on an error.
-/

open BSmtLib.Lexer.Cursor (LexerCursor LexerToken)

namespace BSmtLib.Facts.Lexer.Adapters

open BSmtLibSpec.Lexer (Handed TokenType ReservedKind)
open BSmtLib.Lexer.Cursor.LexerCursor.Internal (remaining Follows)
open BSmtLib.Lexer.Error

/-! ## Conversions to the formalism's types -/

/-- The library's version for a version of the formalism. -/
def toVersion : BSmtLibSpec.Lexicon.Version → Version
  | .v2_0 => .v2_0
  | .v2_5 => .v2_5
  | .v2_6 => .v2_6
  | .v2_7 => .v2_7

/-- The formalism's location for a location of the library. -/
def toLocation (location : Span.Location) : BSmtLibSpec.Lexer.Location :=
  { offset := location.offset, line := location.line, column := location.column }

/-- The formalism's token type for a category of the library; none for whitespace and comments,
which the formalism does not hand over. -/
def toTokenType : Token.TokenCategory → Option TokenType
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
def toReservedKind : Token → Option ReservedKind
  | .reserved word => some (if word.isCommandName then .command else .general)
  | _ => none

/-- The formalism's content for the content of a token of the library. -/
def toContent (content : ByteSlice) : BSmtLibSpec.Regex.Chars :=
  content.toByteArray.toList

/-- A token as the cursor reports it, in the formalism's form; none for whitespace and comments.
-/
def toHanded {batch : Token.BatchTag} (cursor : LexerCursor batch) (token : LexerToken batch) :
    Option Handed :=
  (toTokenType (cursor.category token)).map fun type =>
    { type
      start := toLocation (cursor.span token).start
      «end» := toLocation (cursor.span token).end
      reserved := toReservedKind (cursor.syntax token)
      content := toContent (cursor.content token) }

/-- A piece of whitespace or a comment as the cursor reports it, in the formalism's form. -/
def toLayout {batch : Token.BatchTag} (cursor : LexerCursor batch)
    (token : LexerToken batch) : Handed :=
  { type := if cursor.category token == .comment then .comment else .whitespace
    start := toLocation (cursor.span token).start
    «end» := toLocation (cursor.span token).end
    reserved := none
    content := toContent (cursor.content token) }

/-! ## The consumer

`BSmtLibSpec.Lexer.Consumer` is a consumer as the formalism states it: what it answers and asks
for after each entry, given the entries it has taken in the input so far. `Answering consumer` is
that consumer as a consumer of the library: it takes the entries of a cursor one at a time, records
each in the formalism's form, and answers and asks as the formalism's consumer does, until
it breaks, fails or makes a request. The entries taken so far are the state of its monad `AnswerM`,
which `lexing` starts empty for each input. It is handed whitespace and comments only if the
formalism's consumer is concrete, and then takes them as entries like the tokens. A consumer
that is not concrete fails at the first one it is handed, with the error `none`, which is no error
of the formalism's consumer.
-/

/-- The monad of the consumer `Answering`: its state is the entries it has taken in the input so
far, in the formalism's form. -/
abbrev AnswerM := StateM (List Handed)

/-- The consumer that answers as the formalism's consumer does. It has no state of its own; the
entries it has taken are the state of its monad `AnswerM`. -/
structure Answering (consumer : BSmtLibSpec.Lexer.Consumer) : Type where

/-- `Answering consumer` is a consumer of the library with the formalism's consumer's result and,
as its error, the formalism's consumer's error or `none`; it is concrete if the formalism's
consumer is. -/
instance (consumer : BSmtLibSpec.Lexer.Consumer) : Token.Consume
    (Answering consumer) consumer.Result
    (Option consumer.Error) where
  isConcrete := consumer.concrete

/-- The entry the consumer takes for the token of the cursor, in the formalism's form: the
token, or a piece of whitespace or a comment if the consumer is concrete; none for whitespace or a
comment handed to a consumer that is not concrete. -/
def Answering.entry (consumer : BSmtLibSpec.Lexer.Consumer) {batch : Token.BatchTag}
    (cursor : LexerCursor batch) (token : LexerToken batch) : Option Handed :=
  match toHanded cursor token with
  | some handed => some handed
  | none => if consumer.concrete then some (toLayout cursor token) else none

/-- The cursor after the version switch that the consumer asks for at the last of the
entries `taken`, if it asks for one. The lexer's cursor never refuses a version. -/
def Answering.switched (consumer : BSmtLibSpec.Lexer.Consumer) {batch : Token.BatchTag}
    (taken : List Handed) (cursor : LexerCursor batch) :
    {c : LexerCursor batch // Follows c cursor} :=
  match consumer.switchTo taken with
  | none => ⟨cursor, .refl cursor⟩
  | some version =>
    match h : cursor.setVersion (toVersion version) with
    | .ok next => ⟨next, Lexer.Cursor.LexerCursor.setVersion_follows h⟩
    | .error _ => ⟨cursor, .refl cursor⟩

/-- The cursor after the requests of the consumer at the last of the entries `taken`: the version
it switches to, and then discarding. -/
def Answering.requests (consumer : BSmtLibSpec.Lexer.Consumer) {batch : Token.BatchTag}
    (taken : List Handed) (cursor : LexerCursor batch) :
    {c : LexerCursor batch // Follows c cursor} :=
  let switched := Answering.switched consumer taken cursor
  if consumer.discards taken then
    ⟨switched.val.discardRest, (Lexer.Cursor.LexerCursor.discardRest_follows _).trans switched.property⟩
  else
    switched

/--
Takes the entries of the cursor from the next one on, one at a time, and answers as the
formalism's consumer does. At each entry, given the entries taken so far and this one, it fails,
breaks or goes on, and makes the requests that the formalism's consumer makes at it. It stops
taking at an entry where it asks for a version or for discarding, and when the cursor has no
entry left.
-/
def Answering.consume (consumer : BSmtLibSpec.Lexer.Consumer) {batch : Token.BatchTag}
    (cursor : LexerCursor batch) (h : cursor.HasNext) :
    AnswerM (Except (Option consumer.Error) (ControlFlow consumer.Result) ×
      {c : LexerCursor batch // c.Consumed cursor}) :=
  match cursor.next h with
  | (token, ⟨next, consumed⟩) =>
    match Answering.entry consumer cursor token with
    | none =>
      -- whitespace or a comment, handed to a consumer that is not concrete
      return (.error none, ⟨next, consumed⟩)
    | some handed => do
      let taken := (← get) ++ [handed]
      set taken
      match consumer.answer taken with
      | .fail error =>
        let after := Answering.requests consumer taken next
        return (.error (some error), ⟨after.val, after.property.trans_consumed consumed⟩)
      | .break result =>
        let after := Answering.requests consumer taken next
        return (.ok (.break result), ⟨after.val, after.property.trans_consumed consumed⟩)
      | .continue =>
        if (consumer.switchTo taken).isSome || consumer.discards taken then
          let after := Answering.requests consumer taken next
          return (.ok .continue, ⟨after.val, after.property.trans_consumed consumed⟩)
        else if h' : next.HasNext then do
          let (answer, ⟨last, consumed'⟩) ← Answering.consume consumer next h'
          return (answer, ⟨last, consumed'.trans consumed⟩)
        else
          return (.ok .continue, ⟨next, consumed⟩)
termination_by remaining cursor
decreasing_by exact consumed.remaining_lt

/-- `Answering consumer` takes the entries of a cursor by `Answering.consume`. -/
instance (consumer : BSmtLibSpec.Lexer.Consumer) {batch : Token.BatchTag} :
    Token.ConsumeFrom (Answering consumer) (LexerCursor batch) AnswerM where
  consume cursor h := Answering.consume consumer cursor h

/-! ## Running a lexer -/

/-- The formalism's version for a version of the library. -/
def fromVersion : Version → BSmtLibSpec.Lexicon.Version
  | .v2_0 => .v2_0
  | .v2_5 => .v2_5
  | .v2_6 => .v2_6
  | .v2_7 => .v2_7

/-- How a lexer call failed, in the formalism's form: with `UnexpectedTrailingToken`, at the
start of its span, with another lexical error, or with the consumer's error. The adapter's own error
`none`, which its consumer raises if it is handed whitespace or a comment it does not take, is
given as a lexical error. -/
def failureOf {ε : Type} (error : LexerError (Option ε)) : BSmtLibSpec.Lexer.Failure ε :=
  match error.kind with
  | .lexical kind =>
    if kind == .unexpectedTrailingToken then .trailing (toLocation error.span.start)
    else .lexical
  | .consumer (some error) => .consumer error
  | .consumer none => .lexical

/-- The result that the public call at the end of the input returns: the held one, else the one
the consumer broke with at the end of the input; none if the consumer continued there. -/
def eofResult {α : Type} (held : Option (Span.Located α)) (flow : ControlFlow (Span.Located α)) :
    Option (Span.Located α) :=
  match held, flow with
  | some held, _ => some held
  | none, .break located => some located
  | none, .continue => none

/-- The operations of a lexer with the consumer `Answering consumer`, for every consumer of the
formalism. `lexing` runs the steps (`lexSliceStep`, `lexEofStep`) and keeps the held result as
the public calls (`lexSlice`, `lexEof`) do. -/
structure LexOps where
  /-- The lexer with the consumer. -/
  Lexer : BSmtLibSpec.Lexer.Consumer → Type
  /-- What a failed lexing of a slice gives back besides the error. -/
  AfterError : BSmtLibSpec.Lexer.Consumer → Type
  /-- What a failed lexing of the end of the input gives back besides the error. -/
  AfterEofError : BSmtLibSpec.Lexer.Consumer → Type
  /-- Constructs the lexer, which stops at its first error. -/
  new : (consumer : BSmtLibSpec.Lexer.Consumer) → Answering consumer → Version → Lexer
      consumer
  lexSlice : {consumer : BSmtLibSpec.Lexer.Consumer} → Lexer consumer → ByteSlice →
    AnswerM (Except (LexerError (Option consumer.Error) × AfterError consumer) (Lexer consumer))
  lexEof : {consumer : BSmtLibSpec.Lexer.Consumer} → Lexer consumer →
    AnswerM (Except (LexerError (Option consumer.Error) × AfterEofError consumer)
      (Option (Span.Located consumer.Result) × Lexer consumer))
  /-- The step that `lexSlice` runs, run by the lexer's entry point that gives the lexer back
  also when the step fails. -/
  lexSliceStep : {consumer : BSmtLibSpec.Lexer.Consumer} → Lexer consumer → ByteSlice →
    AnswerM (Except (LexerError (Option consumer.Error)) (Option (Span.Located consumer.Result)) ×
      Lexer consumer)
  /-- The step that `lexEof` runs, run by the lexer's entry point that gives the lexer back
  also when the step fails. -/
  lexEofStep : {consumer : BSmtLibSpec.Lexer.Consumer} → Lexer consumer →
    AnswerM (Except (LexerError (Option consumer.Error))
        (ControlFlow (Span.Located consumer.Result)) ×
      Lexer consumer)
  /-- The result the lexer holds. -/
  held : {consumer : BSmtLibSpec.Lexer.Consumer} → Lexer consumer → Option
      (Span.Located consumer.Result)
  /-- The lexer with the held result. -/
  withHeld : {consumer : BSmtLibSpec.Lexer.Consumer} → Lexer consumer →
    Option (Span.Located consumer.Result) → Lexer consumer
  /-- The version in force. -/
  version : {consumer : BSmtLibSpec.Lexer.Consumer} → Lexer consumer → Version
  /-- Where the lexer began to discard, if it discards. -/
  discardedFrom : {consumer : BSmtLibSpec.Lexer.Consumer} → Lexer consumer → Option Span.Location

/-- Where the lexer stands, in the formalism's form, after the slices if no call failed: holding
the result it holds, or waiting. -/
def LexOps.standing (ops : LexOps) {consumer : BSmtLibSpec.Lexer.Consumer}
    (lexer : ops.Lexer consumer) :
    BSmtLibSpec.Lexer.Outcome consumer.Result consumer.Error :=
  match ops.held lexer with
  | some held => .holding held.value (toLocation held.location)
  | none => .running

/--
Feeds the lexer the slices and then, if the input has ended, the end of the input, by the steps
of the public calls, and keeps the held result as they do; the feeding stops at the first call
that fails. Gives where the lexer stands, in the formalism's form, and the lexer, also after a
failed call.
-/
def LexOps.runInput (ops : LexOps) {consumer : BSmtLibSpec.Lexer.Consumer}
    (lexer : ops.Lexer consumer)
    (ended : Bool) :
    List BSmtLibSpec.Regex.Chars →
      AnswerM (BSmtLibSpec.Lexer.Outcome consumer.Result consumer.Error × ops.Lexer consumer)
  | [] =>
    if ended then do
      match ← ops.lexEofStep lexer with
      | (.ok flow, lexer) =>
        let result := eofResult (ops.held lexer) flow
        let lexer := ops.withHeld lexer none
        match result with
        | some result => return (.finished result.value (toLocation result.location), lexer)
        | none => return (.running, lexer)
      | (.error error, lexer) => return (.failed (failureOf error), lexer)
    else
      return (ops.standing lexer, lexer)
  | slice :: slices => do
    match ← ops.lexSliceStep lexer slice.toByteArray.toByteSlice with
    | (.ok held, lexer) => ops.runInput (ops.withHeld lexer (held.or (ops.held lexer))) ended slices
    | (.error error, lexer) => return (.failed (failureOf error), lexer)

/--
The lexer that the next input is fed to after an earlier input, which is fed as slices and then
the end of the input. It is the lexer the last call gave back or, if a call failed, a lexer
constructed anew with the version, since a lexer that stops at its first error is gone after a
failed call.
-/
def LexOps.next (ops : LexOps) (consumer : BSmtLibSpec.Lexer.Consumer) (version : Version)
    (lexer : ops.Lexer consumer) (input : List BSmtLibSpec.Regex.Chars) : ops.Lexer consumer :=
  match ((ops.runInput lexer true input).run []).1 with
  | (.failed _, _) => ops.new consumer {} version
  | (_, lexer) => lexer

/--
What the lexer has done with a consumer of the formalism, in the formalism's form
(`BSmtLibSpec.Lexer.Lexing`).

The lexer has the consumer `Answering consumer`. It is constructed with the version and fed each
earlier input as slices and then the end of the input (`LexOps.next`). It is then fed the slices
and, if the input has ended, the end of the input. The entries taken are those the consumer has
taken in the last input; the version and where the discarding began are the lexer's after the
last call.
-/
def lexing (ops : LexOps) : BSmtLibSpec.Lexer.Lexing := fun consumer version earlier slices ended =>
  let lexer := earlier.foldl (ops.next consumer (toVersion version))
    (ops.new consumer {} (toVersion version))
  let ((outcome, lexer), taken) := (ops.runInput lexer ended slices).run []
  { taken, outcome, version := fromVersion (ops.version lexer)
    discardedFrom := (ops.discardedFrom lexer).map toLocation }

/-! ## The lexers -/

/-- The naive lexer `Lexer.Internal.VNaive`. -/
def VNaive.lexOps : LexOps where
  Lexer consumer := Lexer.Internal.VNaive.Lexer (Answering consumer)
  AfterError consumer := Lexer.Internal.VNaive.Lexer.AfterError
      (Answering consumer) Lexer.Recovery.FailFast
  AfterEofError consumer := Lexer.Internal.VNaive.Lexer.AfterEofError
      (Answering consumer) Lexer.Recovery.FailFast
  new _ := Lexer.Internal.VNaive.Lexer.new
  lexSlice := Lexer.Internal.VNaive.Lexer.lexSlice
  lexEof := Lexer.Internal.VNaive.Lexer.lexEof
  lexSliceStep lexer slice :=
    lexer.run (Lexer.Internal.VNaive.lexSliceStep
      (Lexer.Recovery.Recovers.recovers Lexer.Recovery.FailFast)
      (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
          (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) slice)
  lexEofStep lexer :=
    lexer.run (Lexer.Internal.VNaive.lexEofStep
      (Lexer.Recovery.Recovers.recovers Lexer.Recovery.FailFast)
      (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
          (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast))
  held lexer := lexer.held
  withHeld lexer held := { lexer with held }
  version := Lexer.Internal.VNaive.Lexer.version
  discardedFrom := Lexer.Internal.VNaive.Lexer.discardedFrom

/-- The Rust lexer ported to Lean `Lexer.Internal.WRustPort`. -/
def WRustPort.lexOps : LexOps where
  Lexer consumer := Lexer.Internal.WRustPort.Lexer (Answering consumer)
  AfterError consumer := Lexer.Internal.WRustPort.Lexer.AfterError
      (Answering consumer) Lexer.Recovery.FailFast
  AfterEofError consumer := Lexer.Internal.WRustPort.Lexer.AfterEofError
      (Answering consumer) Lexer.Recovery.FailFast
  new _ := Lexer.Internal.WRustPort.Lexer.new
  lexSlice := Lexer.Internal.WRustPort.Lexer.lexSlice
  lexEof := Lexer.Internal.WRustPort.Lexer.lexEof
  lexSliceStep lexer slice :=
    lexer.run (Lexer.Internal.WRustPort.lexSliceStep (ops := Lexer.Internal.WRustPort.Rust.ops)
      (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
          (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) slice)
  lexEofStep lexer :=
    lexer.run (Lexer.Internal.WRustPort.lexEofStep (ops := Lexer.Internal.WRustPort.Rust.ops)
      (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
          (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast))
  held lexer := lexer.held
  withHeld lexer held := { lexer with held }
  version := Lexer.Internal.WRustPort.Lexer.version
  discardedFrom := Lexer.Internal.WRustPort.Lexer.discardedFrom

/-- The lexer with the batch kept in its state `Lexer.Internal.X1BatchInCore`, which has the type of
the Rust lexer ported to Lean and lexes by functions of its own. -/
def X1BatchInCore.lexOps : LexOps where
  Lexer consumer := Lexer.Internal.WRustPort.Lexer (Answering consumer)
  AfterError consumer := Lexer.Internal.WRustPort.Lexer.AfterError
      (Answering consumer) Lexer.Recovery.FailFast
  AfterEofError consumer := Lexer.Internal.WRustPort.Lexer.AfterEofError
      (Answering consumer) Lexer.Recovery.FailFast
  new _ := Lexer.Internal.WRustPort.Lexer.new
  lexSlice := Lexer.Internal.X1BatchInCore.Lexer.lexSlice
  lexEof := Lexer.Internal.X1BatchInCore.Lexer.lexEof
  lexSliceStep lexer slice :=
    lexer.run (Lexer.Internal.WRustPort.lexSliceStep (ops := Lexer.Internal.X1BatchInCore.ops)
      (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
          (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) slice)
  lexEofStep lexer :=
    lexer.run (Lexer.Internal.WRustPort.lexEofStep (ops := Lexer.Internal.X1BatchInCore.ops)
      (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
          (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast))
  held lexer := lexer.held
  withHeld lexer held := { lexer with held }
  version := Lexer.Internal.WRustPort.Lexer.version
  discardedFrom := Lexer.Internal.WRustPort.Lexer.discardedFrom

/-- The library's lexer `BSmtLib.Lexer`. -/
def Lexer.lexOps : LexOps where
  Lexer consumer := BSmtLib.Lexer (Answering consumer)
  AfterError consumer := BSmtLib.Lexer.AfterError
      (Answering consumer) Lexer.Recovery.FailFast
  AfterEofError consumer := BSmtLib.Lexer.AfterEofError
      (Answering consumer) Lexer.Recovery.FailFast
  new _ := BSmtLib.Lexer.new
  lexSlice := BSmtLib.Lexer.lexSlice
  lexEof := BSmtLib.Lexer.lexEof
  lexSliceStep lexer slice :=
    BSmtLib.Lexer.Internal.run lexer (BSmtLib.Lexer.Internal.lexSliceStep
      (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
          (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) slice)
  lexEofStep lexer :=
    BSmtLib.Lexer.Internal.run lexer (BSmtLib.Lexer.Internal.lexEofStep
      (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
          (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast))
  held := BSmtLib.Lexer.Internal.held
  withHeld := BSmtLib.Lexer.Internal.withHeld
  version := BSmtLib.Lexer.version
  discardedFrom := BSmtLib.Lexer.discardedFrom

end BSmtLib.Facts.Lexer.Adapters
