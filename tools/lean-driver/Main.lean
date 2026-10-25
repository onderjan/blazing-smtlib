/-
The driver protocol, answered by the Lean lexer and parser, see `lean/driver-protocol.md`.
The Rust tests run their lexer inputs, and their parser and reader inputs, through it to check the
Lean port.

Reads one request per line from the standard input and writes the response
to the standard output, until the input ends. The lexer requests (`lex`, `lex-from` and
`lex-file`) are answered here; the writer requests (`write`) are answered by `WriteRequests`
(`Write.lean`); the parser requests are answered by `ParseRequests` (`Parse.lean`), which also
reads the answers to the handler's calls from the standard input while it answers a request, and
keeps the reader of `reader` for the requests after it.

The environment variable `BLAZING_SMTLIB_LEAN_LEXER` chooses the lexer that answers: `z`, the
library's lexer `BSmtLib.Lexer`, which is the one when the variable is unset, `v`, the naive
lexer `BSmtLib.Lexer.Internal.VNaive`, `w`, the Rust lexer ported to Lean
`BSmtLib.Lexer.Internal.WRustPort`, or `x1`, the lexer with the batch kept in its state
`BSmtLib.Lexer.Internal.X1BatchInCore`. Any other value makes the driver exit at once with an
error.
-/
module

import BSmtLib
import BSmtLib.Lexer.Internal.VNaive
import BSmtLib.Lexer.Internal.WRustPort
import BSmtLib.Lexer.Internal.X1BatchInCore
import Protocol
import Write
import Parse

open BSmtLib
open BSmtLib.Token (BatchTag Consume ConsumeFrom Cursor)
open BSmtLib.Lexer.Error (LexerError LexerReadError LexicalErrorKind)
open BSmtLib.Lexer.Cursor (LexerCursor LexerToken)
open BSmtLib.Lexer (Recover)
open BSmtLib.Span (Location Located)

/- The loops over a cursor's tokens end as each step consumes a token: they descend by the
producer's consumption, which is well-founded. -/
local instance {batch : BatchTag} : WellFoundedRelation (LexerCursor batch) :=
  ⟨Cursor.Consumed, Cursor.consumed_wf⟩

/-- The response line of a token of the cursor, under the version. -/
def tokenLine {batch : BatchTag} (cursor : LexerCursor batch) (token : LexerToken batch)
    (version : Version) : String :=
  let reserved := match Token.fromLexerToken cursor token version with
    | .reserved (.general _) => "general"
    | .reserved (.commandName _) => "command"
    | _ => "-"
  let span := cursor.span token
  s!"t {tokenTypeName (cursor.category token)} {location span.start} {location span.end} \
    {reserved} x{hex (cursor.content token)}\n"

/-- What the consumer of a request does with one hand-over, by its plan. -/
inductive Reply where
  /-- Take every token and continue. -/
  | takeAll
  /-- Take this many tokens and continue: the rest is handed over again. -/
  | leave (count : Nat)
  /-- Take this many tokens and finish. -/
  | finish (count : Nat)
  /-- Take this many tokens and fail. -/
  | fail (count : Nat)
  /-- Take this many tokens, set the version and continue. -/
  | switch (count : Nat) (version : Version)
  /-- Take this many tokens, set the version and finish. -/
  | switchAndFinish (count : Nat) (version : Version)
  deriving BEq

/-- How the consumer of a request behaves. -/
inductive Behaviour where
  /-- It takes every token and always continues. -/
  | takeAll
  /-- It answers the hand-overs in order by the replies, and takes every
  token once they have run out. -/
  | plan (replies : Array Reply)
  /-- It takes every token and fails by what the tokens are: on the symbol
  `bad`, on a closing parenthesis that closes nothing, and on the
  end-of-file token inside a parenthesis, or on every end-of-file token
  if `refuseEnd` is set. The symbol `to-2.0` makes it set the version. -/
  | rules (refuseEnd : Bool)
  /-- It takes every token and continues, and has the cursor discard the
  rest of the input once it has taken `after` tokens, the end-of-file
  token not counted. -/
  | discard (after : Nat)
  deriving BEq

/-- What a `lex-from` or a `lex-file` request lexes as a whole input. -/
inductive ReadInput where
  /-- A buffered reader that hands out the bytes `size` at a time, and then ends or, if `fails`,
  fails. -/
  | reader (size : Nat) (bytes : ByteArray) (fails : Bool)
  /-- The file at the path. -/
  | file (path : System.FilePath)

/-- A request, read from its line. A feed is a slice, or `none` for the end of the input. -/
structure Request where
  version : Version
  whitespace : Bool
  recover : Bool
  behaviour : Behaviour
  /-- The feeds of a `lex` request. -/
  feeds : Array (Option ByteArray)
  /-- The input of a `lex-from` or a `lex-file` request, `none` for a `lex` request. -/
  read : Option ReadInput

def readReply (word : String) : Except String Reply := do
  let bad := s!"unknown reply {repr word}"
  if word == "t" then
    return .takeAll
  if word.isEmpty then
    throw bad
  let letter := (word.take 1).toString
  let rest := (word.drop 1).toString
  -- the version follows the first colon, if there is one
  let (count, version) ← match rest.splitOn ":" with
    | [count] => pure (count, none)
    | count :: version => pure (count, some (← readVersion (":".intercalate version)))
    | [] => throw bad
  let some count := count.toNat?
    | throw bad
  if count == 0 then
    throw s!"a reply must take a token: {repr word}"
  match letter, version with
  | "l", none => return .leave count
  | "f", none => return .finish count
  | "x", none => return .fail count
  | "v", some version => return .switch count version
  | "w", some version => return .switchAndFinish count version
  | _, _ => throw bad

/-- The request with the word read as an option into it, or `none` if the word is none. -/
def readOption (word : String) (request : Request) : Except String (Option Request) := do
  if word == "ws" then
    return some { request with whitespace := true }
  if word == "recover" then
    return some { request with recover := true }
  -- at most one of the options that script the consumer
  if request.behaviour != .takeAll then
    return none
  if word == "rules" then
    return some { request with behaviour := .rules false }
  if word == "rules=refuse-end" then
    return some { request with behaviour := .rules true }
  if word.startsWith "plan=" then
    let replies := (word.drop 5).toString
    -- no replies at all are a plan too: every token is taken,
    -- and the hand-overs are reported
    let replies ← if replies.isEmpty then pure #[]
      else (replies.splitOn ",").toArray.mapM readReply
    return some { request with behaviour := .plan replies }
  if word.startsWith "discard=" then
    let some after := (word.drop 8).toString.toNat?
      | throw s!"unknown option {repr word}"
    if after == 0 then
      throw s!"the consumer must take a token first: {repr word}"
    return some { request with behaviour := .discard after }
  return none

/-- The input of a `lex-from` request, of its operands: the buffer size, the bytes and how the
reader ends. -/
def readReader (operands : Array String) : Except String ReadInput := do
  let #[size, bytes, ending] := operands
    | throw "lex-from takes a size, bytes and an ending"
  let some size := size.toNat?
    | throw s!"bad buffer size {repr size}"
  if size == 0 then
    throw s!"bad buffer size {repr size}"
  unless bytes.startsWith "s" do
    throw s!"bad bytes {repr bytes}"
  let bytes ← unhex (bytes.drop 1).toString
  let fails ← match ending with
    | "end" => pure false
    | "fail" => pure true
    | _ => throw s!"unknown ending {repr ending}"
  return .reader size bytes fails

def readRequest (line : String) : Except String Request := do
  let words := line.splitOn " "
  let some kind := words.head?
    | throw "unknown request"
  unless ["lex", "lex-from", "lex-file"].contains kind do
    throw "unknown request"
  let some version := words[1]?
    | throw "no version"
  let mut request : Request := {
    version := ← readVersion version
    whitespace := false
    recover := false
    behaviour := .takeAll
    feeds := #[]
    read := none }
  -- the options come before the other operands
  let mut operands : Array String := #[]
  for word in words.drop 2 do
    if operands.isEmpty then
      if let some next ← readOption word request then
        request := next
        continue
    operands := operands.push word
  match kind with
  | "lex" =>
    for word in operands do
      if word == "e" then
        request := { request with feeds := request.feeds.push none }
      else if word.startsWith "s" then
        let bytes ← unhex (word.drop 1).toString
        request := { request with feeds := request.feeds.push (some bytes) }
      else
        throw s!"unknown operation {repr word}"
  | "lex-from" =>
    request := { request with read := some (← readReader operands) }
  | _ =>
    let #[digits] := operands
      | throw "lex-file takes a path"
    let some path := String.fromUTF8? (← unhex digits)
      | throw s!"the path {digits} is not UTF-8"
    request := { request with read := some (.file path) }
  if request.recover && request.read.isSome then
    throw "only lex takes recover"
  return request

/- LEAN: the Rust driver collects the lines in a `RefCell<String>` shared with the consumer;
`IO.Ref` is Lean's counterpart, so the consumer runs in `IO`. `whitespace` is the Rust const
parameter `WHITESPACE`. -/
/--
The consumer of a request: writes what it is called with as response
lines. `whitespace` says whether it takes whitespace and comments.
-/
structure Scripted (whitespace : Bool) where
  behaviour : Behaviour
  /-- The number of hand-overs answered by the plan. -/
  handed : Nat
  /-- The number of tokens taken, the end-of-file token not counted, for the consumer that
  discards. -/
  taken : Nat := 0
  /-- The number of parentheses left open by the tokens taken by the rules. -/
  opened : Nat
  out : IO.Ref String

/- LEAN: a consumer cannot look at tokens without consuming them. Rust reports the tokens a
reply does not take through an attempt that takes every token and then fails; a Lean cursor
is a value, so this walks a copy of it instead, which leaves the cursor itself untouched. -/
/-- The lines of every token remaining in the cursor, and their number. -/
def describeAll {batch : BatchTag} (cursor : LexerCursor batch) (version : Version) :
    String × Nat :=
  match cursor.next? with
  | none => ("", 0)
  | some (token, ⟨next, _⟩) =>
    let (lines, count) := describeAll next version
    (tokenLine cursor token version ++ lines, count + 1)
termination_by cursor
decreasing_by assumption

/-- Takes every token remaining in the cursor, which has one, writing a line for each. -/
def takeAll {batch : BatchTag} (out : IO.Ref String) (version : Version)
    (cursor : LexerCursor batch)
    (h : cursor.HasNext) : IO { c : LexerCursor batch // c.Consumed cursor } := do
  let (token, ⟨next, consumed⟩) := cursor.next h
  out.modify (· ++ tokenLine cursor token version)
  if h : next.HasNext then
    let ⟨last, taken⟩ ← takeAll out version next h
    return ⟨last, taken.trans consumed⟩
  else
    return ⟨next, consumed⟩
termination_by cursor
decreasing_by exact consumed

/-- Takes the next token, which there is, and then up to `more` further ones. -/
def takeSome {batch : BatchTag} (cursor : LexerCursor batch) (h : cursor.HasNext) (more : Nat) :
    { c : LexerCursor batch // c.Consumed cursor } :=
  let (_, ⟨next, consumed⟩) := cursor.next h
  match more with
  | more + 1 =>
    if h : next.HasNext then
      let ⟨last, taken⟩ := takeSome next h more
      ⟨last, taken.trans consumed⟩
    else
      ⟨next, consumed⟩
  | 0 => ⟨next, consumed⟩

/-- The cursor after a switch of the version, which the lexer's cursor never refuses; a refusal
would leave it as it is. -/
def switchVersion {batch : BatchTag} {origin : LexerCursor batch}
    (next : { c : LexerCursor batch // c.Consumed origin }) (version : Version) :
    { c : LexerCursor batch // c.Consumed origin } :=
  match h : next.1.setVersion version with
  | .ok switched => ⟨switched, (LexerCursor.setVersion_follows h).trans_consumed next.2⟩
  | .error _ => next

/--
Takes the tokens of the cursor, which has one, by the rules: fails on the symbol `bad`, on
a closing parenthesis that closes nothing, and on the end-of-file token inside a parenthesis,
or on every one if `refuseEnd` is set; the symbol `to-2.0` sets the version.
-/
def takeByRules {batch : BatchTag} (refuseEnd : Bool) (version : Version)
    (cursor : LexerCursor batch) (h : cursor.HasNext) :
    StateT (Scripted whitespace) IO
      (Except String (ControlFlow Bool) × { c : LexerCursor batch // c.Consumed cursor }) := do
  let (token, ⟨next, consumed⟩) := cursor.next h
  let state : Scripted whitespace ← get
  state.out.modify (· ++ tokenLine cursor token version)
  let content := cursor.content token
  let mut next : { c : LexerCursor batch // c.Consumed cursor } := ⟨next, consumed⟩
  match cursor.category token with
  | .parenOpen => set ({ state with opened := state.opened + 1 } : Scripted whitespace)
  | .parenClose =>
    if state.opened == 0 then
      return (.error "unmatched", next)
    set ({ state with opened := state.opened - 1 } : Scripted whitespace)
  | .endOfFile =>
    if refuseEnd || state.opened > 0 then
      return (.error "unexpected-end", next)
  | .unquotedSymbol =>
    if content == "bad".toUTF8.toByteSlice then
      return (.error "bad", next)
    if content == "to-2.0".toUTF8.toByteSlice then
      next := switchVersion next .v2_0
  | _ => pure ()
  if h : next.1.HasNext then
    let (result, ⟨last, taken⟩) ← takeByRules refuseEnd version next.1 h
    return (result, ⟨last, taken.trans next.2⟩)
  else
    return (.ok .continue, next)
termination_by cursor
decreasing_by exact next.2

/--
Takes every token of the cursor, which has one, writing a line for each, and has the cursor
discard the rest of the input once the consumer has taken `after` tokens, the end-of-file token
not counted.
-/
def takeDiscarding {batch : BatchTag} {whitespace : Bool} (after : Nat) (version : Version)
    (cursor : LexerCursor batch) (h : cursor.HasNext) :
    StateT (Scripted whitespace) IO { c : LexerCursor batch // c.Consumed cursor } := do
  let (token, ⟨next, consumed⟩) := cursor.next h
  let state : Scripted whitespace ← get
  state.out.modify (· ++ tokenLine cursor token version)
  let mut next : { c : LexerCursor batch // c.Consumed cursor } := ⟨next, consumed⟩
  if cursor.category token != .endOfFile then
    let taken := state.taken + 1
    set ({ state with taken } : Scripted whitespace)
    if taken == after then
      next := ⟨next.1.discardRest, (LexerCursor.discardRest_follows next.1).trans_consumed next.2⟩
  if h : next.1.HasNext then
    let ⟨last, taken⟩ ← takeDiscarding after version next.1 h
    return ⟨last, taken.trans next.2⟩
  else
    return next
termination_by cursor
decreasing_by exact next.2

/- LEAN: the Rust error type is `&'static str`, the name of what made the consumer fail. The
result says whether the consumer finished by its script (`true`) or only because it was handed
the end of the input (`false`): every consumer breaks there at the latest, and the second kind
is not reported. -/
instance : Consume (Scripted whitespace) Bool String where
  isConcrete := whitespace

/-- The answer of the consumer, which breaks on the end-of-file token where it would continue. -/
def breakAtEnd {batch : BatchTag} (cursor : LexerCursor batch) (h : cursor.HasNext)
    (result : Except String (ControlFlow Bool)) : Except String (ControlFlow Bool) :=
  match result with
  | .ok .continue =>
    -- the end-of-file token is handed over alone
    if cursor.category (cursor.peek h) == .endOfFile then .ok (.break false) else result
  | _ => result

instance {batch : BatchTag} : ConsumeFrom (Scripted whitespace) (LexerCursor batch) IO where
  consume cursor h := do
    let state : Scripted whitespace ← get
    -- the version the tokens of this hand-over were lexed under
    let version := cursor.version
    let (result, next) ← match state.behaviour with
      | .takeAll =>
        pure (.ok .continue, ← takeAll state.out version cursor h)
      | .plan replies => do
        let reply := replies[state.handed]?.getD .takeAll
        set ({ state with handed := state.handed + 1 } : Scripted whitespace)

        -- report every token of the hand-over, also those the reply will not take
        let (lines, count) := describeAll cursor version
        state.out.modify (· ++ s!"h {versionName version} {count}\n" ++ lines)

        let taken := match reply with
          | .takeAll => count
          | .leave taken | .finish taken | .fail taken | .switch taken _
          | .switchAndFinish taken _ => min taken count
        -- every reply takes a token, and the cursor has one
        let ⟨next, consumed⟩ := takeSome cursor h (taken - 1)
        let switched (version : Version) : { c : LexerCursor _ // c.Consumed cursor } :=
          switchVersion ⟨next, consumed⟩ version
        pure <| match reply with
          | .takeAll | .leave _ => (.ok .continue, ⟨next, consumed⟩)
          | .finish _ => (.ok (.break true), ⟨next, consumed⟩)
          | .fail _ => (.error "plan", ⟨next, consumed⟩)
          | .switch _ version => (.ok .continue, switched version)
          | .switchAndFinish _ version => (.ok (.break true), switched version)
      | .rules refuseEnd => takeByRules refuseEnd version cursor h
      | .discard after => pure (.ok .continue, ← takeDiscarding after version cursor h)
    return (breakAtEnd cursor h result, next)

instance : Recover (Scripted whitespace) IO where
  abandon place := do
    let state : Scripted whitespace ← get
    state.out.modify (· ++ s!"ab {location place}\n")
    -- nothing is open any more
    set ({ state with opened := 0 } : Scripted whitespace)
  recover place := do
    let state : Scripted whitespace ← get
    state.out.modify (· ++ s!"rc {location place}\n")

/--
The line of the error. With `recover`, it ends with where the input continues from, if it
does.
-/
def errorLine (err : LexerError String) (recover : Bool) : Except String String := do
  let line ← match err.cause with
    | .lexical kind => pure s!"err {errorKindName kind} {location err.span.start} \
        {location err.span.end}"
    | .consumer name => pure s!"cerr {name}"
  if !recover then
    return line ++ "\n"
  -- where the input continues from, if it does
  let continues := match err.continuesFrom with
    | some continues => location continues
    | none => "-"
  return s!"{line} {continues}\n"

/-- The line of the result the lexer returned at the end of the input, if it has one: the
consumer finished by its script. -/
def resultLine (result : Option (Located Bool)) : String :=
  match result with
  | some located => if located.value then s!"fin {location located.location}\n" else ""
  | _ => ""

/-- The lines that end the feed: where the lexer is, and its version if the consumer is scripted. -/
def feedLines (request : Request) (lexer : Lexer (Scripted whitespace) recovery) : String :=
  let scripted := request.behaviour != .takeAll
  s!"at {location lexer.currentLocation}\n" ++
    if scripted then s!"v {versionName lexer.version}\n" else ""

/--
Applies the feeds of the request to the lexer that stops at its first error and writes the
lines of the feeds themselves. Returns whether every feed was applied.
-/
/- LEAN: a recursion over the feeds rather than a loop, so that each lexer is handed on once:
a lexer still referred to while it lexes would be copied by every change of its state. -/
def drive (request : Request) (lines : IO.Ref String) :
    List (Option ByteArray) → Lexer (Scripted whitespace) → ExceptT String IO Bool
  | [], _ => return true
  | feed :: feeds, lexer => do
    let result ← match feed with
      | some slice => (·.map (("", ·))) <$> lexer.lexSlice slice.toByteSlice
      | none => (·.map fun (result, lexer) => (resultLine result, lexer)) <$> lexer.lexEof
    match result with
    | .ok (line, lexer) =>
      lines.modify (· ++ line ++ feedLines request lexer)
      drive request lines feeds lexer
    | .error (err, _) =>
      lines.modify (· ++ (← errorLine err false))
      -- the lexer has stopped for good, and the response with it
      return false

/- LEAN: Rust's `drive` serves both kinds of lexer; here the recovering one has its own, as its
calls give back different things. -/
/--
Applies the feeds of the request to the recovering lexer and writes the lines of the feeds
themselves. After an error on a slice, the rest of that slice is applied again, from where
the input continues; after an error on the end of the input that continues, the end of the
input is applied again.
-/
def driveRecovering (request : Request) (lines : IO.Ref String)
    (lexer : Lexer (Scripted whitespace) Lexer.Recovering) : ExceptT String IO Unit := do
  let mut lexer := lexer
  for feed in request.feeds do
    match feed with
    | some slice =>
      -- the part of a slice that the lexer has not taken yet
      let mut from_ := 0
      repeat
        let before := lexer.currentLocation.offset
        match ← lexer.lexSlice (slice.toByteSlice from_) with
        | .ok next =>
          lexer := next
          break
        | .error (err, next) =>
          lexer := next
          lines.modify (· ++ (← errorLine err true))
          match err.continuesFrom with
          -- the rest of the feed is applied again from there
          | some continues => from_ := from_ + (continues.offset - before)
          -- the input has ended with the error, the feed is done
          | none => break
    | none =>
      match ← lexer.lexEof with
      | .ok (result, next) =>
        lexer := next
        lines.modify (· ++ resultLine result)
      | .error (err, after) =>
        lines.modify (· ++ (← errorLine err true))
        match after with
        | .lexer next => lexer := next
        | .pending pending =>
          -- the end of the input continues, apply it again
          match ← pending.lexEof with
          | .ok (result, next) =>
            lexer := next
            lines.modify (· ++ resultLine result)
          | .error (err, next) =>
            lexer := next
            lines.modify (· ++ (← errorLine err true))
    lines.modify (· ++ feedLines request lexer)

/-! The same for the naive lexer V, `BSmtLib.Lexer.Internal.VNaive`, which has the operations of
the library's lexer on a lexer type of its own. -/

namespace V

/-- The naive lexer. -/
abbrev NaiveLexer (H : Type) {R E : Type} [Consume H R E] (recovery : Type := Lexer.FailFast) :=
  Lexer.Internal.VNaive.Lexer H recovery

/-- The lines that end the feed: where the lexer is, and its version if the consumer is scripted. -/
def feedLines (request : Request) (lexer : NaiveLexer (Scripted whitespace) recovery) : String :=
  let scripted := request.behaviour != .takeAll
  s!"at {location lexer.currentLocation}\n" ++
    if scripted then s!"v {versionName lexer.version}\n" else ""

/--
Applies the feeds of the request to the lexer that stops at its first error and writes the
lines of the feeds themselves. Returns whether every feed was applied.
-/
def drive (request : Request) (lines : IO.Ref String) :
    List (Option ByteArray) → NaiveLexer (Scripted whitespace) → ExceptT String IO Bool
  | [], _ => return true
  | feed :: feeds, lexer => do
    let result ← match feed with
      | some slice => (·.map (("", ·))) <$> lexer.lexSlice slice.toByteSlice
      | none => (·.map fun (result, lexer) => (resultLine result, lexer)) <$> lexer.lexEof
    match result with
    | .ok (line, lexer) =>
      lines.modify (· ++ line ++ feedLines request lexer)
      drive request lines feeds lexer
    | .error (err, _) =>
      lines.modify (· ++ (← errorLine err false))
      -- the lexer has stopped for good, and the response with it
      return false

/--
Applies the feeds of the request to the recovering lexer and writes the lines of the feeds
themselves. After an error on a slice, the rest of that slice is applied again, from where
the input continues; after an error on the end of the input that continues, the end of the
input is applied again.
-/
def driveRecovering (request : Request) (lines : IO.Ref String)
    (lexer : NaiveLexer (Scripted whitespace) Lexer.Recovering) : ExceptT String IO Unit := do
  let mut lexer := lexer
  for feed in request.feeds do
    match feed with
    | some slice =>
      -- the part of a slice that the lexer has not taken yet
      let mut from_ := 0
      repeat
        let before := lexer.currentLocation.offset
        match ← lexer.lexSlice (slice.toByteSlice from_) with
        | .ok next =>
          lexer := next
          break
        | .error (err, next) =>
          lexer := next
          lines.modify (· ++ (← errorLine err true))
          match err.continuesFrom with
          -- the rest of the feed is applied again from there
          | some continues => from_ := from_ + (continues.offset - before)
          -- the input has ended with the error, the feed is done
          | none => break
    | none =>
      match ← lexer.lexEof with
      | .ok (result, next) =>
        lexer := next
        lines.modify (· ++ resultLine result)
      | .error (err, after) =>
        lines.modify (· ++ (← errorLine err true))
        match after with
        | .lexer next => lexer := next
        | .pending pending =>
          -- the end of the input continues, apply it again
          match ← pending.lexEof with
          | .ok (result, next) =>
            lexer := next
            lines.modify (· ++ resultLine result)
          | .error (err, next) =>
            lexer := next
            lines.modify (· ++ (← errorLine err true))
    lines.modify (· ++ feedLines request lexer)

end V

/-! The same for the lexers of the chain that have a lexer type of their own, as the library's
lexer has: `BSmtLib.Lexer.Internal.WRustPort`, and `X1BatchInCore`, which has the type of
`WRustPort`. Each is given to the driver by its operations (`Ops`). -/

namespace Own

/-- The operations of a lexer with a lexer type of its own, with the scripted consumer. -/
structure Ops (whitespace : Bool) where
  /-- The lexer that stops at its first error. -/
  Lexer : Type
  /-- The recovering lexer. -/
  Recovering : Type
  /-- What a recovering lexer gives back after its end of the input failed. -/
  AfterEof : Type
  new : Scripted whitespace → Version → Lexer
  newRecovering : Scripted whitespace → Version → Recovering
  lexSlice : Lexer → ByteSlice →
    IO (Except (LexerError String × Scripted whitespace) Lexer)
  lexEof : Lexer →
    IO (Except (LexerError String × Scripted whitespace) (Option (Located Bool) × Lexer))
  currentLocation : Lexer → Location
  version : Lexer → Version
  recoveringLexSlice : Recovering → ByteSlice →
    IO (Except (LexerError String × Recovering) Recovering)
  recoveringLexEof : Recovering →
    IO (Except (LexerError String × AfterEof) (Option (Located Bool) × Recovering))
  /-- The lexer after its end of the input failed, or the end of the input to lex again. -/
  afterEof : AfterEof → Sum Recovering
    (IO (Except (LexerError String × Recovering) (Option (Located Bool) × Recovering)))
  recoveringLocation : Recovering → Location
  recoveringVersion : Recovering → Version
  /-- Where the lexer that stops at its first error discards the input from, if it does. -/
  discardedFrom : Lexer → Option Location

/-- The lines that end the feed: where the lexer is, and its version if the consumer is scripted. -/
def feedLines (request : Request) (location : Location) (version : Version) : String :=
  let scripted := request.behaviour != .takeAll
  s!"at {location.offset}:{location.line}:{location.column}\n" ++
    if scripted then s!"v {versionName version}\n" else ""

/--
Applies the feeds of the request to the lexer that stops at its first error and writes the
lines of the feeds themselves. Returns whether every feed was applied.
-/
def drive (ops : Ops whitespace) (request : Request) (lines : IO.Ref String) :
    List (Option ByteArray) → ops.Lexer → ExceptT String IO Bool
  | [], _ => return true
  | feed :: feeds, lexer => do
    let result ← match feed with
      | some slice => (·.map (("", ·))) <$> ops.lexSlice lexer slice.toByteSlice
      | none => (·.map fun (result, lexer) => (resultLine result, lexer)) <$> ops.lexEof lexer
    match result with
    | .ok (line, lexer) =>
      lines.modify (· ++ line ++
        feedLines request (ops.currentLocation lexer) (ops.version lexer))
      drive ops request lines feeds lexer
    | .error (err, _) =>
      lines.modify (· ++ (← errorLine err false))
      -- the lexer has stopped for good, and the response with it
      return false

/--
Applies the feeds of the request to the recovering lexer and writes the lines of the feeds
themselves. After an error on a slice, the rest of that slice is applied again, from where
the input continues; after an error on the end of the input that continues, the end of the
input is applied again.
-/
def driveRecovering (ops : Ops whitespace) (request : Request) (lines : IO.Ref String)
    (lexer : ops.Recovering) : ExceptT String IO Unit := do
  let mut lexer := lexer
  for feed in request.feeds do
    match feed with
    | some slice =>
      -- the part of a slice that the lexer has not taken yet
      let mut from_ := 0
      repeat
        let before := (ops.recoveringLocation lexer).offset
        match ← ops.recoveringLexSlice lexer (slice.toByteSlice from_) with
        | .ok next =>
          lexer := next
          break
        | .error (err, next) =>
          lexer := next
          lines.modify (· ++ (← errorLine err true))
          match err.continuesFrom with
          -- the rest of the feed is applied again from there
          | some continues => from_ := from_ + (continues.offset - before)
          -- the input has ended with the error, the feed is done
          | none => break
    | none =>
      match ← ops.recoveringLexEof lexer with
      | .ok (result, next) =>
        lexer := next
        lines.modify (· ++ resultLine result)
      | .error (err, after) =>
        lines.modify (· ++ (← errorLine err true))
        match ops.afterEof after with
        | .inl next => lexer := next
        | .inr pending =>
          -- the end of the input continues, apply it again
          match ← pending with
          | .ok (result, next) =>
            lexer := next
            lines.modify (· ++ resultLine result)
          | .error (err, next) =>
            lexer := next
            lines.modify (· ++ (← errorLine err true))
    lines.modify (· ++
      feedLines request (ops.recoveringLocation lexer) (ops.recoveringVersion lexer))

/-- Answers one request line with the lexer, giving the response lines. -/
def answer (ops : (whitespace : Bool) → Ops whitespace) (request : Request) :
    ExceptT String IO String := do
  -- the consumer writes into the response while the lexer owns it
  let lines ← IO.mkRef ""
  let version := request.version
  let behaviour := request.behaviour
  let complete ← match request.whitespace, request.recover with
    | false, false =>
      drive (ops false) request lines request.feeds.toList ((ops false).new
        ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted false) version)
    | true, false =>
      drive (ops true) request lines request.feeds.toList ((ops true).new
        ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted true) version)
    | false, true =>
      driveRecovering (ops false) request lines ((ops false).newRecovering
        ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted false) version)
      pure true
    | true, true =>
      driveRecovering (ops true) request lines ((ops true).newRecovering
        ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted true) version)
      pure true

  let mut response ← lines.get
  if complete then
    response := response ++ "ok\n"
  return response

/-- The Rust lexer ported to Lean, `BSmtLib.Lexer.Internal.WRustPort`. -/
def w (whitespace : Bool) : Ops whitespace :=
  { Lexer := Lexer.Internal.WRustPort.Lexer (Scripted whitespace)
    Recovering := Lexer.Internal.WRustPort.Lexer (Scripted whitespace) Lexer.Recovering
    AfterEof := Lexer.Internal.WRustPort.Lexer.AfterEof (Scripted whitespace)
    new := Lexer.Internal.WRustPort.Lexer.new
    newRecovering := Lexer.Internal.WRustPort.Lexer.newRecovering
    lexSlice := fun lexer slice => Lexer.Internal.WRustPort.Lexer.lexSlice lexer slice
    lexEof := fun lexer => Lexer.Internal.WRustPort.Lexer.lexEof lexer
    currentLocation := Lexer.Internal.WRustPort.Lexer.currentLocation
    version := Lexer.Internal.WRustPort.Lexer.version
    recoveringLexSlice := fun lexer slice => Lexer.Internal.WRustPort.Lexer.lexSlice lexer slice
    recoveringLexEof := fun lexer => Lexer.Internal.WRustPort.Lexer.lexEof lexer
    afterEof := fun
      | .lexer lexer => .inl lexer
      | .pending pending => .inr pending.lexEof
    recoveringLocation := Lexer.Internal.WRustPort.Lexer.currentLocation
    recoveringVersion := Lexer.Internal.WRustPort.Lexer.version
    discardedFrom := Lexer.Internal.WRustPort.Lexer.discardedFrom }

/-- The lexer with the batch kept in its state, `BSmtLib.Lexer.Internal.X1BatchInCore`, which has
the Rust port's type and lexes by functions of its own. -/
def x1 (whitespace : Bool) : Ops whitespace :=
  { Lexer := Lexer.Internal.WRustPort.Lexer (Scripted whitespace)
    Recovering := Lexer.Internal.WRustPort.Lexer (Scripted whitespace) Lexer.Recovering
    AfterEof := Lexer.Internal.WRustPort.Lexer.AfterEof (Scripted whitespace)
    new := Lexer.Internal.WRustPort.Lexer.new
    newRecovering := Lexer.Internal.WRustPort.Lexer.newRecovering
    lexSlice := fun lexer slice => Lexer.Internal.X1BatchInCore.Lexer.lexSlice lexer slice
    lexEof := fun lexer => Lexer.Internal.X1BatchInCore.Lexer.lexEof lexer
    currentLocation := Lexer.Internal.WRustPort.Lexer.currentLocation
    version := Lexer.Internal.WRustPort.Lexer.version
    recoveringLexSlice := fun lexer slice =>
      Lexer.Internal.X1BatchInCore.Lexer.lexSlice lexer slice
    recoveringLexEof := fun lexer => Lexer.Internal.X1BatchInCore.Lexer.lexEof lexer
    afterEof := fun
      | .lexer lexer => .inl lexer
      | .pending pending => .inr (Lexer.Internal.X1BatchInCore.Lexer.PendingEof.lexEof pending)
    recoveringLocation := Lexer.Internal.WRustPort.Lexer.currentLocation
    recoveringVersion := Lexer.Internal.WRustPort.Lexer.version
    discardedFrom := Lexer.Internal.WRustPort.Lexer.discardedFrom }

end Own

/--
Answers one request line with the naive lexer, giving the response lines.
-/
def answerNaive (request : Request) : ExceptT String IO String := do
  -- the consumer writes into the response while the lexer owns it
  let lines ← IO.mkRef ""
  let version := request.version
  let behaviour := request.behaviour
  let complete ← match request.whitespace, request.recover with
    | false, false =>
      V.drive request lines request.feeds.toList (Lexer.Internal.VNaive.Lexer.new
        ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted false) version)
    | true, false =>
      V.drive request lines request.feeds.toList (Lexer.Internal.VNaive.Lexer.new
        ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted true) version)
    | false, true =>
      V.driveRecovering request lines
        (Lexer.Internal.VNaive.Lexer.newRecovering
          ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted false) version)
      pure true
    | true, true =>
      V.driveRecovering request lines
        (Lexer.Internal.VNaive.Lexer.newRecovering
          ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted true) version)
      pure true

  let mut response ← lines.get
  if complete then
    response := response ++ "ok\n"
  return response

/-! Lexing a whole input from a buffered reader or a file, for `lex-from` and `lex-file`. -/

/-- The message of the failure of the buffered reader of a `lex-from` request that fails after
its bytes. -/
def READER_FAILURE : String := "the test reader fails after its input"

/-- The buffered reader of a `lex-from` request: hands out its bytes `size` at a time, and then
ends or, if `fails`, fails. -/
structure Chunks where
  bytes : ByteArray
  /-- The number of the bytes consumed. -/
  consumed : Nat
  size : Nat
  fails : Bool

instance : Reader.BufRead Chunks IO where
  fillBuf self := do
    if self.consumed ≥ self.bytes.size && self.fails then
      return .error (IO.userError READER_FAILURE)
    let stop := min (self.consumed + self.size) self.bytes.size
    return .ok (self.bytes.toByteSlice self.consumed stop, self)
  consume self amount := { self with consumed := self.consumed + amount }

/-- The operations of a lexer that stops at its first error, which lexing a whole input from a
buffered reader needs. -/
structure ReadOps (L : Type) where
  lexSlice : L → ByteSlice → IO (Except (LexerError String) L)
  lexEof : L → IO (Except (LexerError String) (Option (Located Bool) × L))
  currentLocation : L → Location
  discardedFrom : L → Option Location

/- LEAN: the lexers of the chain have no `lexFrom` of their own; this does what the library's
`Lexer.lexFrom` does, step for step. It is `partial`, as `Lexer.lexFrom` is. -/
/-- `Lexer.lexFrom` over the lexer of the operations. -/
partial def emulatedLexFrom {L B : Type} [Reader.BufRead B IO] (ops : ReadOps L) (lexer : L)
    (buf : B) : IO (Except (LexerReadError String) (Option (Located Bool)) × B) := do
  let lexRest (lexer : L) : IO (Except (LexerReadError String) (Option (Located Bool))) := do
    return ((← ops.lexEof lexer).map (·.1)).mapError LexerReadError.ofLex
  if (ops.discardedFrom lexer).isSome then
    -- the consumer does not care about any subsequent bytes
    return (← lexRest lexer, buf)
  match ← Reader.BufRead.fillBuf buf with
  | .error err =>
    let span := Span.Internal.newEmpty (ops.currentLocation lexer)
    return (.error (LexerReadError.Internal.new (.io err) span), buf)
  | .ok (buffer, buf) =>
    if buffer.size == 0 then
      return (← lexRest lexer, buf)
    -- consume the bytes lexed, which are fewer than the buffer holds when discarding begins
    -- inside it
    let startOffset := (ops.currentLocation lexer).offset
    match ← ops.lexSlice lexer buffer with
    | .error err => return (.error (LexerReadError.ofLex err), buf)
    | .ok lexer =>
      let len := (ops.currentLocation lexer).offset - startOffset
      emulatedLexFrom ops lexer (Reader.BufRead.consume (n := IO) buf len)

/-- `Lexer.lexFile` over the lexer of the operations. -/
def emulatedLexFile {L : Type} (ops : ReadOps L) (lexer : L) (path : System.FilePath) :
    IO (Except (LexerReadError String) (Option (Located Bool))) := do
  match ← (IO.FS.Handle.mk path .read).toBaseIO with
  | .error err => return .error (LexerReadError.Internal.new (.io err) Span.Internal.newZero)
  | .ok file =>
    let buf := Reader.BufReader.new (IO.FS.Stream.ofHandle file) Lexer.Internal.BUF_READER_CAPACITY
    return (← emulatedLexFrom ops lexer buf).1

/-- Lexes the input as a whole input with the lexer of the operations, giving the outcome and,
for a buffered reader, the number of its bytes not consumed. -/
def emulatedRead {L : Type} (ops : ReadOps L) (lexer : L) :
    ReadInput → IO (Except (LexerReadError String) (Option (Located Bool)) × Option Nat)
  | .reader size bytes fails => do
    let (result, reader) ← emulatedLexFrom ops lexer ({ bytes, consumed := 0, size, fails } : Chunks)
    return (result, some (bytes.size - reader.consumed))
  | .file path => do return (← emulatedLexFile ops lexer path, none)

/-- Lexes the input as a whole input with the library's lexer, giving the outcome and, for a
buffered reader, the number of its bytes not consumed. -/
def libraryRead {whitespace : Bool} (lexer : Lexer (Scripted whitespace)) :
    ReadInput → IO (Except (LexerReadError String) (Option (Located Bool)) × Option Nat)
  | .reader size bytes fails => do
    let (result, reader) ← lexer.lexFrom (n := IO) ({ bytes, consumed := 0, size, fails } : Chunks)
    return (((result.map (·.1)).mapError (·.1)), some (bytes.size - reader.consumed))
  | .file path => do
    return (((← lexer.lexFile (n := IO) path).map (·.1)).mapError (·.1), none)

/-- The lines of the outcome of lexing a whole input: the result, or the error that ended it. -/
def readLines (result : Except (LexerReadError String) (Option (Located Bool)))
    (rest : Option Nat) : String :=
  match result with
  | .ok (some located) =>
    -- only a finish by the script is reported
    let finish := if located.value then s!"fin {location located.location}\n" else ""
    let rest := match rest with
      | some rest => s!" {rest}"
      | none => ""
    s!"{finish}done {location located.location}{rest}\n"
  | .ok none => "none\n"
  | .error err =>
    match err.cause with
    | .lexical kind =>
      s!"err {errorKindName kind} {location err.span.start} {location err.span.end}\n"
    | .consumer name => s!"cerr {name}\n"
    | .io error =>
      s!"ioerr {location err.span.start} {location err.span.end} \
        x{hex (toString error).toUTF8.toByteSlice}\n"

/-- Answers a `lex-from` or a `lex-file` request with the chosen lexer, whose consumer takes
whitespace and comments if `whitespace` is set. -/
def answerReadAs (whitespace : Bool) (choice : LexerChoice) (request : Request)
    (input : ReadInput) : IO String := do
  -- the consumer writes into the response while the lexer owns it
  let lines ← IO.mkRef ""
  let consumer : Scripted whitespace :=
    { behaviour := request.behaviour, handed := 0, opened := 0, out := lines }
  let version := request.version
  let (result, rest) ← match choice with
    | .z => libraryRead (Lexer.new consumer version) input
    | .v =>
      emulatedRead
        { lexSlice := fun lexer slice => do
            return (← Lexer.Internal.VNaive.Lexer.lexSlice lexer slice).mapError (·.1)
          lexEof := fun lexer => do
            return (← Lexer.Internal.VNaive.Lexer.lexEof lexer).mapError (·.1)
          currentLocation := Lexer.Internal.VNaive.Lexer.currentLocation
          discardedFrom := Lexer.Internal.VNaive.Lexer.discardedFrom }
        (Lexer.Internal.VNaive.Lexer.new consumer version) input
    | .w | .x1 =>
      let ops := if choice matches .w then Own.w whitespace else Own.x1 whitespace
      emulatedRead
        { lexSlice := fun lexer slice => do return (← ops.lexSlice lexer slice).mapError (·.1)
          lexEof := fun lexer => do return (← ops.lexEof lexer).mapError (·.1)
          currentLocation := ops.currentLocation
          discardedFrom := ops.discardedFrom }
        (ops.new consumer version) input
  return (← lines.get) ++ readLines result rest

/-- Answers a `lex-from` or a `lex-file` request with the chosen lexer. -/
def answerRead (choice : LexerChoice) (request : Request) (input : ReadInput) : IO String :=
  answerReadAs request.whitespace choice request input

/-- Answers one request line, giving the response lines. -/
def answer (choice : LexerChoice) (line : String) : ExceptT String IO String := do
  -- decode the whole request first, so that a malformed one produces no lines
  let request ← readRequest line
  if let some input := request.read then
    return ← answerRead choice request input
  match choice with
  | .v => return ← answerNaive request
  | .w => return ← Own.answer Own.w request
  | .x1 => return ← Own.answer Own.x1 request
  | .z => pure ()

  -- the consumer writes into the response while the lexer owns it
  let lines ← IO.mkRef ""
  let version := request.version
  let behaviour := request.behaviour
  let complete ← match request.whitespace, request.recover with
    | false, false =>
      drive request lines request.feeds.toList
        (Lexer.new ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted false) version)
    | true, false =>
      drive request lines request.feeds.toList
        (Lexer.new ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted true) version)
    | false, true =>
      driveRecovering request lines (Lexer.newRecovering
        ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted false) version)
      pure true
    | true, true =>
      driveRecovering request lines (Lexer.newRecovering
        ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted true) version)
      pure true

  let mut response ← lines.get
  if complete then
    response := response ++ "ok\n"
  return response

/-- Serves the requests until the input ends, with the reader of the last `reader` request. -/
partial def serve (choice : LexerChoice) (stdin : IO.FS.Stream) (stdout : IO.FS.Stream)
    (session : Option ParseRequests.Session) : IO Unit := do
  let line ← stdin.getLine
  -- the input has ended
  if line.isEmpty then
    return
  let request := lineContent line
  let words := request.splitOn " "
  let session ← if words.head?.any (ParseRequests.requestNames.contains ·) then
      -- a parser request writes its response itself, as it talks to the Rust side meanwhile
      try
        ParseRequests.answer choice { stdin, stdout } session words
      catch err =>
        -- the message on one line
        let message := (toString err).map fun c => if c == '\n' || c == '\r' then ' ' else c
        stdout.putStr s!"fail {message}\n"
        pure session
    else
      -- the writer requests are answered by `WriteRequests` (`Write.lean`)
      let answered := if words.head? == some "write" then WriteRequests.answer request
        else answer choice request
      let out ← match ← answered.run with
        | .ok out => pure out
        | .error message => pure s!"fail {message}\n"
      stdout.putStr out
      pure session
  stdout.flush
  serve choice stdin stdout session

public def main : IO UInt32 := do
  match readLexerChoice (← IO.getEnv "BLAZING_SMTLIB_LEAN_LEXER") with
  | .ok choice =>
    serve choice (← IO.getStdin) (← IO.getStdout) none
    return 0
  | .error message =>
    IO.eprintln message
    return 1
