/-
The lexer driver protocol, answered by the Lean lexer, see `lean/driver-protocol.md`.
The Rust tests run their lexer inputs through it to check the Lean port.

Reads one request per line from the standard input and writes the response
to the standard output, until the input ends.
-/
import BSmtLib

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
def tokenLine (cursor : BatchCursor) (token : Token) (version : Version) : String :=
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
def describeAll (cursor : BatchCursor) (version : Version) : String × Nat :=
  match cursor.next? with
  | none => ("", 0)
  | some (token, ⟨next, consumed⟩) =>
    have : next.remaining < cursor.remaining := consumed.remaining_lt
    let (lines, count) := describeAll next version
    (tokenLine cursor token version ++ lines, count + 1)
termination_by cursor.remaining

/-- Takes every token remaining in the cursor, which has one, writing a line for each. -/
def takeAll (out : IO.Ref String) (version : Version) (cursor : BatchCursor)
    (h : cursor.HasNext) : IO { c : BatchCursor // c.Consumed cursor } := do
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
def takeSome (cursor : BatchCursor) (h : cursor.HasNext) (more : Nat) :
    { c : BatchCursor // c.Consumed cursor } :=
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
def takeByRules (refuseEnd : Bool) (version : Version) (cursor : BatchCursor)
    (h : cursor.HasNext) :
    StateT (Scripted whitespace) IO
      (Except String (ControlFlow Unit) × { c : BatchCursor // c.Consumed cursor }) := do
  let (token, ⟨next, consumed⟩) := cursor.next h
  let state : Scripted whitespace ← get
  state.out.modify (· ++ tokenLine cursor token version)
  let content := cursor.content token
  let mut next : { c : BatchCursor // c.Consumed cursor } := ⟨next, consumed⟩
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
      let switched (version : Version) : { c : BatchCursor // c.Consumed cursor } :=
        ⟨next.setVersion version, (next.setVersion_follows version).trans_consumed consumed⟩
      return match reply with
        | .takeAll | .leave _ => (.ok .continue, ⟨next, consumed⟩)
        | .finish _ => (.ok (.break ()), ⟨next, consumed⟩)
        | .fail _ => (.error "plan", ⟨next, consumed⟩)
        | .switch _ version => (.ok .continue, switched version)
        | .switchAndFinish _ version => (.ok (.break ()), switched version)
    | .rules refuseEnd => takeByRules refuseEnd version cursor h

/--
Applies the feeds of the request to the lexer and writes the lines of
the feeds themselves. Returns whether every feed was applied.
-/
def drive (request : Request) (lines : IO.Ref String) (lexer : Lexer (Scripted whitespace)) :
    ExceptT String IO Bool := do
  let scripted := request.behaviour != .takeAll
  let mut lexer := lexer
  for feed in request.feeds do
    let (result, next) ← match feed with
      | some slice => lexer.lexSlice slice.toByteSlice
      | none => lexer.lexEof
    lexer := next
    match result with
    | .ok .continue => pure ()
    | .ok (.break located) => lines.modify (· ++ s!"fin {location located.location}\n")
    | .error err =>
      let line ← match err with
        | .lexer err => pure s!"err {errorKindName err.kind} {location err.span.start} \
            {location err.span.end}"
        | .handler name => pure s!"cerr {name}"
        -- the protocol has no line for an internal error, which must not occur
        | .internal err => throw s!"internal error: {err.message}"
      lines.modify (· ++ line ++ "\n")
      -- the lexer has stopped for good, and the response with it
      return false
    lines.modify (· ++ s!"at {location lexer.currentLocation}\n")
    if scripted then
      lines.modify (· ++ s!"v {versionName lexer.version}\n")
  return true

/-- Answers one request line, giving the response lines. -/
def answer (line : String) : ExceptT String IO String := do
  -- decode the whole request first, so that a malformed one produces no lines
  let request ← readRequest line
  -- the option that the Lean lexer cannot answer yet
  if request.recover then
    throw "the option recover is not implemented yet"

  -- the consumer writes into the response while the lexer owns it
  let lines ← IO.mkRef ""
  let version := request.version
  let behaviour := request.behaviour
  let complete ← if request.whitespace then
      drive request lines
        (Lexer.new ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted true) version)
    else
      drive request lines
        (Lexer.new ({ behaviour, handed := 0, opened := 0, out := lines } : Scripted false) version)

  let mut response ← lines.get
  if complete then
    response := response ++ "ok\n"
  return response

partial def serve (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  -- the input has ended
  if line.isEmpty then
    return
  let request := (line.dropEndWhile (· == '\n')).toString
  let request := (request.dropEndWhile (· == '\r')).toString
  let out ← match ← (answer request).run with
    | .ok out => pure out
    | .error message => pure s!"fail {message}\n"
  stdout.putStr out
  stdout.flush
  serve stdin stdout

def main : IO Unit := do
  serve (← IO.getStdin) (← IO.getStdout)
