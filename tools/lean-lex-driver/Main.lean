/-
The lexer driver protocol, answered by the Lean lexer, see `lean/driver-protocol.md`.
The Rust tests run their lexer inputs through it to check the Lean port.

Reads one request per line from the standard input and writes the response
to the standard output, until the input ends.

The environment variable `BLAZING_SMTLIB_LEAN_LEXER` chooses the lexer that answers: `v5`, the
library's lexer `BSmtLib.Lexer`, which is the one when the variable is unset, `v1`, the naive
lexer `BSmtLib.Proofs.Lexer.V1Naive`, `w`, the Rust lexer ported to Lean
`BSmtLib.Proofs.Lexer.WRustPort`, `x1`, the lexer with the batch kept in its state
`BSmtLib.Proofs.Lexer.X1BatchInCore`, or `x2`, the lexer with the content buffer
`BSmtLib.Proofs.Lexer.X2Contents`. Any other value makes the driver exit at once with an error.
-/
import BSmtLib
import BSmtLib.Proofs

open BSmtLib

def location (location : Location) : String :=
  s!"{location.offset}:{location.line}:{location.column}"

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hex (bytes : ByteSlice) : String := Id.run do
  let mut out := ""
  for i in [0:bytes.size] do
    let byte := (bytes.get! i).toNat
    out := (out.push (hexDigit (byte / 16))).push (hexDigit (byte % 16))
  out

def versionName : Version → String
  | .v2_0 => "2.0"
  | .v2_5 => "2.5"
  | .v2_6 => "2.6"
  | .v2_7 => "2.7"

/-- The token type, spelled as the Rust variant. -/
def tokenTypeName : TokenCategory → String
  | .parenOpen => "ParenOpen"
  | .parenClose => "ParenClose"
  | .numeral => "Numeral"
  | .decimal => "Decimal"
  | .hexadecimal => "Hexadecimal"
  | .binary => "Binary"
  | .string => "String"
  | .keyword => "Keyword"
  | .unquotedSymbol => "UnquotedSymbol"
  | .quotedSymbol => "QuotedSymbol"
  | .whitespace => "Whitespace"
  | .comment => "Comment"
  | .endOfFile => "EndOfFile"

/-- The lexer error kind, spelled as the Rust variant. -/
def errorKindName : LexicalErrorKind → String
  | .unexpectedCharacter => "UnexpectedCharacter"
  | .fractionDigitExpected => "FractionDigitExpected"
  | .hexadecimalDigitExpected => "HexadecimalDigitExpected"
  | .binaryDigitExpected => "BinaryDigitExpected"
  | .baseSelectionExpected => "BaseSelectionExpected"
  | .unclosedStringLiteral => "UnclosedStringLiteral"
  | .forbiddenCharInString => "ForbiddenCharInString"
  | .forbiddenKeywordName => "ForbiddenKeywordName"
  | .backslashInQuotedSymbol => "BackslashInQuotedSymbol"
  | .forbiddenCharInQuotedSymbol => "ForbiddenCharInQuotedSymbol"
  | .unclosedQuotedSymbol => "UnclosedQuotedSymbol"
  | .numeralLeadingZero => "NumeralLeadingZero"
  | .missingDelimiter => "MissingDelimiter"

/-- The response line of a token of the cursor, under the version. -/
def tokenLine {batch : BatchTag} (cursor : BatchCursor batch) (token : Token batch)
    (version : Version) : String :=
  let reserved := match cursor.syntax token version with
    | .reserved (.general _) => "general"
    | .reserved (.commandName _) => "command"
    | _ => "-"
  let span := cursor.span token
  s!"t {tokenTypeName (cursor.category token)} {location span.start} {location span.end} \
    {reserved} x{hex (cursor.content token)}\n"

/-- Decodes the hexadecimal digits of a slice operand. -/
def unhex (digits : String) : Except String ByteArray := do
  let chars := digits.toList.toArray
  if chars.size % 2 != 0 then
    throw s!"odd number of hexadecimal digits in {repr digits}"
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else throw s!"bad hexadecimal digits in {repr digits}"
  let mut bytes := ByteArray.emptyWithCapacity (chars.size / 2)
  for i in [0:chars.size / 2] do
    let high ← digit chars[2 * i]!
    let low ← digit chars[2 * i + 1]!
    bytes := bytes.push (high * 16 + low).toUInt8
  return bytes

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
  deriving BEq

/-- A request, read from its line. A feed is a slice, or `none` for the end of the input. -/
structure Request where
  version : Version
  whitespace : Bool
  recover : Bool
  behaviour : Behaviour
  feeds : Array (Option ByteArray)

def readVersion (word : String) : Except String Version :=
  match Version.fromDecimal? word.toUTF8.toByteSlice with
  | some version => pure version
  | none => throw s!"unknown version {repr word}"

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

def readRequest (line : String) : Except String Request := do
  let words := line.splitOn " "
  if words.head? != some "lex" then
    throw "unknown request"
  let some version := words[1]?
    | throw "no version"
  let mut request : Request := {
    version := ← readVersion version
    whitespace := false
    recover := false
    behaviour := .takeAll
    feeds := #[] }
  for word in words.drop 2 do
    let scripted := request.behaviour != .takeAll
    -- the options come before the feeds
    let option := request.feeds.isEmpty
    if word == "e" then
      request := { request with feeds := request.feeds.push none }
    else if word == "ws" && option then
      request := { request with whitespace := true }
    else if word == "recover" && option then
      request := { request with recover := true }
    else if word == "rules" && option && !scripted then
      request := { request with behaviour := .rules false }
    else if word == "rules=refuse-end" && option && !scripted then
      request := { request with behaviour := .rules true }
    else if word.startsWith "plan=" && option && !scripted then
      let replies := (word.drop 5).toString
      -- no replies at all are a plan too: every token is taken,
      -- and the hand-overs are reported
      let replies ← if replies.isEmpty then pure #[]
        else (replies.splitOn ",").toArray.mapM readReply
      request := { request with behaviour := .plan replies }
    else if word.startsWith "s" then
      request := { request with feeds := request.feeds.push (some (← unhex (word.drop 1).toString)) }
    else
      throw s!"unknown operation {repr word}"
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
  /-- The number of parentheses left open by the tokens taken by the rules. -/
  opened : Nat
  out : IO.Ref String

/- LEAN: a consumer cannot look at tokens without consuming them. Rust reports the tokens a
reply does not take through an attempt that takes every token and then fails; a Lean cursor
is a value, so this walks a copy of it instead, which leaves the cursor itself untouched. -/
/-- The lines of every token remaining in the cursor, and their number. -/
def describeAll {batch : BatchTag} (cursor : BatchCursor batch) (version : Version) :
    String × Nat :=
  match cursor.next? with
  | none => ("", 0)
  | some (token, ⟨next, consumed⟩) =>
    have : next.remaining < cursor.remaining := consumed.remaining_lt
    let (lines, count) := describeAll next version
    (tokenLine cursor token version ++ lines, count + 1)
termination_by cursor.remaining

/-- Takes every token remaining in the cursor, which has one, writing a line for each. -/
def takeAll {batch : BatchTag} (out : IO.Ref String) (version : Version)
    (cursor : BatchCursor batch)
    (h : cursor.HasNext) : IO { c : BatchCursor batch // c.Consumed cursor } := do
  let (token, ⟨next, consumed⟩) := cursor.next h
  out.modify (· ++ tokenLine cursor token version)
  if h : next.HasNext then
    have : next.remaining < cursor.remaining := consumed.remaining_lt
    let ⟨last, taken⟩ ← takeAll out version next h
    return ⟨last, taken.trans consumed⟩
  else
    return ⟨next, consumed⟩
termination_by cursor.remaining

/-- Takes the next token, which there is, and then up to `more` further ones. -/
def takeSome {batch : BatchTag} (cursor : BatchCursor batch) (h : cursor.HasNext) (more : Nat) :
    { c : BatchCursor batch // c.Consumed cursor } :=
  let (_, ⟨next, consumed⟩) := cursor.next h
  match more with
  | more + 1 =>
    if h : next.HasNext then
      let ⟨last, taken⟩ := takeSome next h more
      ⟨last, taken.trans consumed⟩
    else
      ⟨next, consumed⟩
  | 0 => ⟨next, consumed⟩

/--
Takes the tokens of the cursor, which has one, by the rules: fails on the symbol `bad`, on
a closing parenthesis that closes nothing, and on the end-of-file token inside a parenthesis,
or on every one if `refuseEnd` is set; the symbol `to-2.0` sets the version.
-/
def takeByRules {batch : BatchTag} (refuseEnd : Bool) (version : Version)
    (cursor : BatchCursor batch) (h : cursor.HasNext) :
    StateT (Scripted whitespace) IO
      (Except String (ControlFlow Unit) × { c : BatchCursor batch // c.Consumed cursor }) := do
  let (token, ⟨next, consumed⟩) := cursor.next h
  let state : Scripted whitespace ← get
  state.out.modify (· ++ tokenLine cursor token version)
  let content := cursor.content token
  let mut next : { c : BatchCursor batch // c.Consumed cursor } := ⟨next, consumed⟩
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
      next := ⟨next.1.setVersion .v2_0, (next.1.setVersion_follows .v2_0).trans_consumed next.2⟩
  | _ => pure ()
  if h : next.1.HasNext then
    have : next.1.remaining < cursor.remaining := next.2.remaining_lt
    let (result, ⟨last, taken⟩) ← takeByRules refuseEnd version next.1 h
    return (result, ⟨last, taken.trans next.2⟩)
  else
    return (.ok .continue, next)
termination_by cursor.remaining

/- LEAN: the Rust error type is `&'static str`, the name of what made the consumer fail. -/
instance : Consume (Scripted whitespace) IO Unit String where
  consumesWhitespaceAndComments := whitespace
  consume cursor h := do
    let state : Scripted whitespace ← get
    -- the version the tokens of this hand-over were lexed under
    let version := cursor.version
    match state.behaviour with
    | .takeAll =>
      return (.ok .continue, ← takeAll state.out version cursor h)
    | .plan replies =>
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
      let switched (version : Version) : { c : BatchCursor _ // c.Consumed cursor } :=
        ⟨next.setVersion version, (next.setVersion_follows version).trans_consumed consumed⟩
      return match reply with
        | .takeAll | .leave _ => (.ok .continue, ⟨next, consumed⟩)
        | .finish _ => (.ok (.break ()), ⟨next, consumed⟩)
        | .fail _ => (.error "plan", ⟨next, consumed⟩)
        | .switch _ version => (.ok .continue, switched version)
        | .switchAndFinish _ version => (.ok (.break ()), switched version)
    | .rules refuseEnd => takeByRules refuseEnd version cursor h

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
def errorLine (err : LexError String) (recover : Bool) : Except String String := do
  let line ← match err.cause with
    | .lexical err => pure s!"err {errorKindName err.kind} {location err.span.start} \
        {location err.span.end}"
    | .consumer name => pure s!"cerr {name}"
  if !recover then
    return line ++ "\n"
  -- where the input continues from, if it does
  let continues := match err.continuesFrom with
    | some continues => location continues
    | none => "-"
  return s!"{line} {continues}\n"

/-- The line of the flow the lexer returned, if it has one. -/
def flowLine (flow : ControlFlow (Located Unit)) : String :=
  match flow with
  | .continue => ""
  | .break located => s!"fin {location located.location}\n"

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
      | some slice => lexer.lexSlice slice.toByteSlice
      | none => lexer.lexEof
    match result with
    | .ok (flow, lexer) =>
      lines.modify (· ++ flowLine flow ++ feedLines request lexer)
      drive request lines feeds lexer
    | .error (err, ()) =>
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
    (lexer : Lexer (Scripted whitespace) .recovering) : ExceptT String IO Unit := do
  let mut lexer := lexer
  for feed in request.feeds do
    match feed with
    | some slice =>
      -- the part of a slice that the lexer has not taken yet
      let mut from_ := 0
      repeat
        let before := lexer.currentLocation.offset
        match ← lexer.lexSlice (slice.toByteSlice from_) with
        | .ok (flow, next) =>
          lexer := next
          lines.modify (· ++ flowLine flow)
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
      | .ok (flow, next) =>
        lexer := next
        lines.modify (· ++ flowLine flow)
      | .error (err, after) =>
        lines.modify (· ++ (← errorLine err true))
        match after with
        | .lexer next => lexer := next
        | .pending pending =>
          -- the end of the input continues, apply it again
          match ← pending.lexEof with
          | .ok (flow, next) =>
            lexer := next
            lines.modify (· ++ flowLine flow)
          | .error (err, next) =>
            lexer := next
            lines.modify (· ++ (← errorLine err true))
    lines.modify (· ++ feedLines request lexer)

/-! The same for the naive lexer V1, `BSmtLib.Proofs.Lexer.V1Naive`, which has the operations of
the library's lexer on a lexer type of its own. -/

namespace V1

/-- The naive lexer. -/
abbrev NaiveLexer (H : Type) (recovery : Recovery := .failFast) :=
  Proofs.Lexer.V1Naive.Lexer H recovery

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
      | some slice => lexer.lexSlice slice.toByteSlice
      | none => lexer.lexEof
    match result with
    | .ok (flow, lexer) =>
      lines.modify (· ++ flowLine flow ++ feedLines request lexer)
      drive request lines feeds lexer
    | .error (err, ()) =>
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
    (lexer : NaiveLexer (Scripted whitespace) .recovering) : ExceptT String IO Unit := do
  let mut lexer := lexer
  for feed in request.feeds do
    match feed with
    | some slice =>
      -- the part of a slice that the lexer has not taken yet
      let mut from_ := 0
      repeat
        let before := lexer.currentLocation.offset
        match ← lexer.lexSlice (slice.toByteSlice from_) with
        | .ok (flow, next) =>
          lexer := next
          lines.modify (· ++ flowLine flow)
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
      | .ok (flow, next) =>
        lexer := next
        lines.modify (· ++ flowLine flow)
      | .error (err, after) =>
        lines.modify (· ++ (← errorLine err true))
        match after with
        | .lexer next => lexer := next
        | .pending pending =>
          -- the end of the input continues, apply it again
          match ← pending.lexEof with
          | .ok (flow, next) =>
            lexer := next
            lines.modify (· ++ flowLine flow)
          | .error (err, next) =>
            lexer := next
            lines.modify (· ++ (← errorLine err true))
    lines.modify (· ++ feedLines request lexer)

end V1

/-! The same for the lexers of the chain that have a lexer type of their own, as the library's
lexer has: `BSmtLib.Proofs.Lexer.WRustPort`, `X1BatchInCore` and `X2Contents`. Each is given to
the driver by its operations (`Ops`). -/

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
    IO (Except (LexError String × Unit) (ControlFlow (Located Unit) × Lexer))
  lexEof : Lexer → IO (Except (LexError String × Unit) (ControlFlow (Located Unit) × Lexer))
  currentLocation : Lexer → Location
  version : Lexer → Version
  recoveringLexSlice : Recovering → ByteSlice →
    IO (Except (LexError String × Recovering) (ControlFlow (Located Unit) × Recovering))
  recoveringLexEof : Recovering →
    IO (Except (LexError String × AfterEof) (ControlFlow (Located Unit) × Recovering))
  /-- The lexer after its end of the input failed, or the end of the input to lex again. -/
  afterEof : AfterEof → Sum Recovering
    (IO (Except (LexError String × Recovering) (ControlFlow (Located Unit) × Recovering)))
  recoveringLocation : Recovering → Location
  recoveringVersion : Recovering → Version

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
      | some slice => ops.lexSlice lexer slice.toByteSlice
      | none => ops.lexEof lexer
    match result with
    | .ok (flow, lexer) =>
      lines.modify (· ++ flowLine flow ++
        feedLines request (ops.currentLocation lexer) (ops.version lexer))
      drive ops request lines feeds lexer
    | .error (err, ()) =>
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
        | .ok (flow, next) =>
          lexer := next
          lines.modify (· ++ flowLine flow)
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
      | .ok (flow, next) =>
        lexer := next
        lines.modify (· ++ flowLine flow)
      | .error (err, after) =>
        lines.modify (· ++ (← errorLine err true))
        match ops.afterEof after with
        | .inl next => lexer := next
        | .inr pending =>
          -- the end of the input continues, apply it again
          match ← pending with
          | .ok (flow, next) =>
            lexer := next
            lines.modify (· ++ flowLine flow)
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

/-- The Rust lexer ported to Lean, `BSmtLib.Proofs.Lexer.WRustPort`. -/
def w (whitespace : Bool) : Ops whitespace :=
  { Lexer := Proofs.Lexer.WRustPort.Lexer (Scripted whitespace)
    Recovering := Proofs.Lexer.WRustPort.Lexer (Scripted whitespace) .recovering
    AfterEof := Proofs.Lexer.WRustPort.Lexer.AfterEof (Scripted whitespace)
    new := Proofs.Lexer.WRustPort.Lexer.new
    newRecovering := Proofs.Lexer.WRustPort.Lexer.newRecovering
    lexSlice := Proofs.Lexer.WRustPort.Lexer.lexSlice
    lexEof := Proofs.Lexer.WRustPort.Lexer.lexEof
    currentLocation := Proofs.Lexer.WRustPort.Lexer.currentLocation
    version := Proofs.Lexer.WRustPort.Lexer.version
    recoveringLexSlice := Proofs.Lexer.WRustPort.Lexer.lexSlice
    recoveringLexEof := Proofs.Lexer.WRustPort.Lexer.lexEof
    afterEof := fun
      | .lexer lexer => .inl lexer
      | .pending pending => .inr pending.lexEof
    recoveringLocation := Proofs.Lexer.WRustPort.Lexer.currentLocation
    recoveringVersion := Proofs.Lexer.WRustPort.Lexer.version }

/-- The lexer with the batch kept in its state, `BSmtLib.Proofs.Lexer.X1BatchInCore`. -/
def x1 (whitespace : Bool) : Ops whitespace :=
  { Lexer := Proofs.Lexer.X1BatchInCore.Lexer (Scripted whitespace)
    Recovering := Proofs.Lexer.X1BatchInCore.Lexer (Scripted whitespace) .recovering
    AfterEof := Proofs.Lexer.X1BatchInCore.Lexer.AfterEof (Scripted whitespace)
    new := Proofs.Lexer.X1BatchInCore.Lexer.new
    newRecovering := Proofs.Lexer.X1BatchInCore.Lexer.newRecovering
    lexSlice := Proofs.Lexer.X1BatchInCore.Lexer.lexSlice
    lexEof := Proofs.Lexer.X1BatchInCore.Lexer.lexEof
    currentLocation := Proofs.Lexer.X1BatchInCore.Lexer.currentLocation
    version := Proofs.Lexer.X1BatchInCore.Lexer.version
    recoveringLexSlice := Proofs.Lexer.X1BatchInCore.Lexer.lexSlice
    recoveringLexEof := Proofs.Lexer.X1BatchInCore.Lexer.lexEof
    afterEof := fun
      | .lexer lexer => .inl lexer
      | .pending pending => .inr pending.lexEof
    recoveringLocation := Proofs.Lexer.X1BatchInCore.Lexer.currentLocation
    recoveringVersion := Proofs.Lexer.X1BatchInCore.Lexer.version }

/-- The lexer with the content buffer, `BSmtLib.Proofs.Lexer.X2Contents`. -/
def x2 (whitespace : Bool) : Ops whitespace :=
  { Lexer := Proofs.Lexer.X2Contents.Lexer (Scripted whitespace)
    Recovering := Proofs.Lexer.X2Contents.Lexer (Scripted whitespace) .recovering
    AfterEof := Proofs.Lexer.X2Contents.Lexer.AfterEof (Scripted whitespace)
    new := Proofs.Lexer.X2Contents.Lexer.new
    newRecovering := Proofs.Lexer.X2Contents.Lexer.newRecovering
    lexSlice := Proofs.Lexer.X2Contents.Lexer.lexSlice
    lexEof := Proofs.Lexer.X2Contents.Lexer.lexEof
    currentLocation := Proofs.Lexer.X2Contents.Lexer.currentLocation
    version := Proofs.Lexer.X2Contents.Lexer.version
    recoveringLexSlice := Proofs.Lexer.X2Contents.Lexer.lexSlice
    recoveringLexEof := Proofs.Lexer.X2Contents.Lexer.lexEof
    afterEof := fun
      | .lexer lexer => .inl lexer
      | .pending pending => .inr pending.lexEof
    recoveringLocation := Proofs.Lexer.X2Contents.Lexer.currentLocation
    recoveringVersion := Proofs.Lexer.X2Contents.Lexer.version }

end Own

/-- The lexer that answers the requests. -/
inductive LexerChoice where
  /-- The naive lexer, `BSmtLib.Proofs.Lexer.V1Naive`. -/
  | v1
  /-- The Rust lexer ported to Lean, `BSmtLib.Proofs.Lexer.WRustPort`. -/
  | w
  /-- The lexer with the batch kept in its state, `BSmtLib.Proofs.Lexer.X1BatchInCore`. -/
  | x1
  /-- The lexer with the content buffer, `BSmtLib.Proofs.Lexer.X2Contents`. -/
  | x2
  /-- The library's lexer, `BSmtLib.Lexer`. -/
  | v5

/-- The lexer named by the value of `BLAZING_SMTLIB_LEAN_LEXER`, the library's if it is unset. -/
def readLexerChoice : Option String → Except String LexerChoice
  | none | some "v5" => pure .v5
  | some "v1" => pure .v1
  | some "w" => pure .w
  | some "x1" => pure .x1
  | some "x2" => pure .x2
  | some other => throw s!"unknown lexer {repr other} in BLAZING_SMTLIB_LEAN_LEXER, \
      expected v1, w, x1, x2 or v5"

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
      V1.drive request lines request.feeds.toList (Proofs.Lexer.V1Naive.Lexer.new
        ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted false) version)
    | true, false =>
      V1.drive request lines request.feeds.toList (Proofs.Lexer.V1Naive.Lexer.new
        ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted true) version)
    | false, true =>
      V1.driveRecovering request lines
        (Proofs.Lexer.V1Naive.Lexer.newRecovering
          ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted false) version)
      pure true
    | true, true =>
      V1.driveRecovering request lines
        (Proofs.Lexer.V1Naive.Lexer.newRecovering
          ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted true) version)
      pure true

  let mut response ← lines.get
  if complete then
    response := response ++ "ok\n"
  return response

/-- Answers one request line, giving the response lines. -/
def answer (choice : LexerChoice) (line : String) : ExceptT String IO String := do
  -- decode the whole request first, so that a malformed one produces no lines
  let request ← readRequest line
  match choice with
  | .v1 => return ← answerNaive request
  | .w => return ← Own.answer Own.w request
  | .x1 => return ← Own.answer Own.x1 request
  | .x2 => return ← Own.answer Own.x2 request
  | .v5 => pure ()

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

partial def serve (choice : LexerChoice) (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) :
    IO Unit := do
  let line ← stdin.getLine
  -- the input has ended
  if line.isEmpty then
    return
  let request := (line.dropEndWhile (· == '\n')).toString
  let request := (request.dropEndWhile (· == '\r')).toString
  let out ← match ← (answer choice request).run with
    | .ok out => pure out
    | .error message => pure s!"fail {message}\n"
  stdout.putStr out
  stdout.flush
  serve choice stdin stdout

def main : IO UInt32 := do
  match readLexerChoice (← IO.getEnv "BLAZING_SMTLIB_LEAN_LEXER") with
  | .ok choice =>
    serve choice (← IO.getStdin) (← IO.getStdout)
    return 0
  | .error message =>
    IO.eprintln message
    return 1
