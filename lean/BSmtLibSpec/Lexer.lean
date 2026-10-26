module

public import BSmtLibSpec.Lexicon.Properties

@[expose] public section

/-!
# Lexers

What a lexer hands over, in a form that does not depend on how a lexer represents its tokens,
and what it means for a lexer to be correct. An error named in code, such as
`UnexpectedTrailingToken`, is the error of the library's interface that the definition
specifies.
-/

namespace BSmtLibSpec.Lexer

open BSmtLibSpec.Lexicon
open Regex (Chars)

/-! ## What a lexer hands over -/

/--
A location in the input, all zero-based.
-/
structure Location where
  offset : Nat
  line : Nat
  column : Nat
  deriving DecidableEq, Repr

/--
The location of `offset` in the input: lines are counted by line feeds (10) alone, and
columns by characters.
-/
def locate (input : Chars) (offset : Nat) : Location :=
  let before := input.take offset
  { offset, line := before.count 10, column := (before.reverse.takeWhile (· ≠ 10)).length }

/--
The token types of the implementation. Whitespace and comments are handed over only to a
concrete consumer.
-/
inductive TokenType where
  | parenOpen
  | parenClose
  | numeral
  | decimal
  | hexadecimal
  | binary
  | string
  | keyword
  | unquotedSymbol
  | quotedSymbol
  | whitespace
  | comment
  | endOfFile
  deriving DecidableEq, Repr

/--
Which kind of reserved word a token is.
-/
inductive ReservedKind where
  | general
  | command
  deriving DecidableEq, Repr

/--
A token as the implementation hands it over.

The form is a set of conventions, not a restriction on a lexer: a lexer that represents its
tokens otherwise is correct when its tokens map to this form. The content is what
`Token.content` gives: what a string literal stands for, a quoted symbol without its bars, a
keyword without its colon, the digits of a hexadecimal or a binary without `#x` or `#b`, and
otherwise the characters of the token. Whitespace and comments are handed over in the same form
(`layoutFrom`). The start and the end are located by `locate`:
zero-based, with lines counted by line feeds alone; the end is the location just after the
token's last character.
-/
structure Handed where
  type : TokenType
  start : Location
  «end» : Location
  reserved : Option ReservedKind
  content : Chars
  deriving DecidableEq, Repr

end BSmtLibSpec.Lexer

/-
The three definitions below belong to the lexicon's types, so they are in the lexicon's
namespace, where dot notation finds them (`token.handed version input`). They are written here
and not in the lexicon's modules because they build the types above, and a Lean module can use
only what is declared before it.
-/
namespace BSmtLibSpec.Lexicon

open BSmtLibSpec.Lexer
open Regex (Chars chars)

/--
The type of a token of each kind; a reserved word is an unquoted symbol.
-/
def Category.type : Category → TokenType
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral => .numeral
  | .decimal => .decimal
  | .hexadecimal => .hexadecimal
  | .binary => .binary
  | .string => .string
  | .simpleSymbol | .reserved => .unquotedSymbol
  | .quotedSymbol => .quotedSymbol
  | .keyword => .keyword

/--
Which kind of reserved word a token is, if it is one.
-/
def Token.reservedKind (version : Version) (token : Token) :
    Option ReservedKind :=
  if token.category ≠ .reserved then none
  else if ∃ w ∈ basicReservedWords version, token.text = chars w then some .general
  else some .command

/--
The token as the implementation hands it over.
-/
def Token.handed (version : Version) (input : Chars) (token : Token) : Handed :=
  { type := token.category.type
    start := locate input token.offset
    «end» := locate input (token.offset + token.text.length)
    reserved := token.reservedKind version
    content := token.content version }

end BSmtLibSpec.Lexicon

namespace BSmtLibSpec.Lexer

open BSmtLibSpec.Lexicon BSmtLibSpec.Lexicon.Properties
open Regex (Chars chars)

/--
The end-of-file token after the input.
-/
def endOfFile (input : Chars) : Handed :=
  { type := .endOfFile, start := locate input input.length, «end» := locate input input.length,
    reserved := none, content := [] }

/--
The end-of-file token located at the location.
-/
def endOfFileAt (location : Location) : Handed :=
  { type := .endOfFile, start := location, «end» := location, reserved := none, content := [] }

/-! ## About a lexer

The properties are about one function that an adapter makes of a lexer, `feed`: what the lexer
has done after being fed slices and then, if the input has ended, the end of the input. The
input is the slices joined, so how it is cut into slices does not matter. Each property is
about one version, one input, and whether the input has ended; `Correct` asks for them on every
version and every input, ended or not.

They are stated for a consumer that takes every token handed over, continues on each but the
end-of-file token and breaks on that (`collector`). How a lexer answers a consumer that breaks
earlier, leaves tokens, switches the version, discards the rest or fails is stated relative to
them, in the section on consumers below.

Reading L8: the lexer does not perform the check for non-ASCII bytes.
-/

/--
What a lexer has done after being fed slices, and possibly the end of the input: the tokens it
handed over, in order, and whether it failed.

The standard knows only whole inputs; a lexer fed in slices is this library's.
-/
structure Fed where
  handed : List Handed
  failed : Bool

/--
Property: the token is a parenthesis, or the character after it is in the input.

A token other than a parenthesis needs a delimiter after it (`Tokenization.Delimited`, Reading
L1), so a lexer can tell that the token ends where it does only once it has read the character
after it. A parenthesis needs no delimiter.
-/
def DelimiterSeen (input : Chars) (token : Token) : Prop :=
  token.category = .parenOpen ∨ token.category = .parenClose ∨
    token.offset + token.text.length < input.length

/--
Property: `start` is the longest start of `input` that is viable.

Up to the end of `start`, characters may still follow that make a valid input; past it, none
can. While the input is `Viable`, `start` is all of it; once it is not, `start` ends where it
stopped being viable. Of `(a #q`, it is `(a #`: `#x1` could follow, but nothing can follow
`(a #q`.

The standard speaks only of whole inputs; a lexer fed in slices has read a start of one.
-/
def LongestViableStart (version : Version) (input start : Chars) : Prop :=
  start <+: input ∧ Viable version start ∧
    ∀ longer, longer <+: input → Viable version longer → longer.length ≤ start.length

/--
Property: no characters that follow the input can change the tokens, and the character after
each of them but a parenthesis is in the input.

These are tokens that a lexer fed the input in slices may hand over: they are `Determined`,
and their delimiter has been read (`DelimiterSeen`). After `(x |abc|`, `(` and `x` are ready,
but `|abc|` is not: it is determined, but the character after it has not been read.

Waiting for the delimiter of a token that is already determined is this library's; the standard
does not speak of a lexer fed in slices.
-/
def HandoverReady (version : Version) (input : Chars) (tokens : List Token) : Prop :=
  Determined version input tokens ∧ ∀ token ∈ tokens, DelimiterSeen input token

/--
Property: the tokens are ready to be handed over, and no longer list is.

These are all the tokens that a lexer fed the input in slices may hand over, so a lexer that
hands them over holds nothing back. On an input that is not `Viable`, every list is
determined, so no list is maximal.
-/
def HandoverMaximal (version : Version) (input : Chars) (tokens : List Token) : Prop :=
  HandoverReady version input tokens ∧
    ∀ tokens', HandoverReady version input tokens' → tokens'.length ≤ tokens.length

/--
Property: the input has ended, and it has a tokenisation.

The lexer has then read the input to its end without failing, and the end of the input
delimits the last token, so every token of the tokenisation is ready. An input that has ended
without a tokenisation of its own is not complete, even when it is `Viable`: on `(a "ab`, the
end of the input does not complete the string literal.
-/
def Complete (version : Version) (input : Chars) (ended : Bool) : Prop :=
  ended = true ∧ ∃ tokens, Tokenization version input tokens

/--
Property: a lexer fed the slices, and then the end of the input if it has ended, has failed
exactly when the input can no longer be valid.

Before the end, characters may still follow: while the input is `Viable`, they may make a valid
input of it, so the lexer must not fail; once it is not, none can, so the lexer must have
failed. After the end, nothing can follow, so the lexer must have failed exactly when the input
has no tokenisation. `"ab` is viable, so a lexer fails on it only at the end.

Reading L8: the input need not be a `SourceFile`.
-/
def FailsCorrectly (feed : Version → List Chars → Bool → Fed) (version : Version)
    (slices : List Chars) (ended : Bool) : Prop :=
  let input := slices.flatten
  (feed version slices ended).failed ↔
    if ended then ¬ ∃ tokens, Tokenization version input tokens else ¬ Viable version input

/--
Property: a lexer fed the slices and then the end of the input has handed over the tokens of
the tokenisation of the input followed by the end-of-file token.

It is what the lexer must have handed over when the input is `Complete`: the end of the input
delimits the last token, so every token is ready.

Reading L8: the input need not be a `SourceFile`.
-/
def HandsOverAll (feed : Version → List Chars → Bool → Fed) (version : Version)
    (slices : List Chars) : Prop :=
  let input := slices.flatten
  ∃ tokens, Tokenization version input tokens ∧
    (feed version slices true).handed = tokens.map (·.handed version input) ++ [endOfFile input]

/--
Property: a lexer fed the slices, and then the end of the input if it has ended, has handed
over the tokens maximal to hand over on the longest viable start of the input, and nothing else.

It is what the lexer must have handed over when the input is not `Complete`. `start` is that
longest viable start (`LongestViableStart`), all of the input while it is viable. So the lexer
holds no token back, hands none over before it is ready, and hands none over from where the
input stopped being viable on.

The end of an input that is not complete releases no token: on `(a "ab`, the lexer has handed
over `(` and `a`, at the end as before it. Nor does the end of the input delimit a token after
the input stopped being viable: on `(a bc"`, the lexer has handed over `(` and `a`, and not
`bc`, since it read `"` after `bc` and not the end.

Reading L8: the input need not be a `SourceFile`.
-/
def HandsOverMaximal (feed : Version → List Chars → Bool → Fed) (version : Version)
    (slices : List Chars) (ended : Bool) (start : Chars) : Prop :=
  let input := slices.flatten
  LongestViableStart version input start →
    ∃ tokens, HandoverMaximal version start tokens ∧
      (feed version slices ended).handed = tokens.map (·.handed version input)

open Classical in
/--
Property: a lexer fed the slices, and then the end of the input if it has ended, has handed
over the tokens that are ready, and nothing else.

It is `HandsOverAll` if the input is `Complete`, and `HandsOverMaximal` if it is not.
-/
def HandsOverCorrectly (feed : Version → List Chars → Bool → Fed) (version : Version)
    (slices : List Chars) (ended : Bool) (start : Chars) : Prop :=
  if Complete version slices.flatten ended then HandsOverAll feed version slices
  else HandsOverMaximal feed version slices ended start

/--
Property: a lexer is correct on every version and every input, ended or not.

It is `FailsCorrectly` and `HandsOverCorrectly`.
-/
def Correct (feed : Version → List Chars → Bool → Fed) : Prop :=
  ∀ version slices ended start,
    FailsCorrectly feed version slices ended ∧ HandsOverCorrectly feed version slices ended start

/-! ## Consequences of correctness

Properties that are not a part of `Correct` because they follow from it. `BSmtLibSpec.Facts.Lexer`
proves `Sequential` and `WholeInputCorrect` as consequences of `Correct`, for every lexer at
once.
-/

/--
Property: `later` has handed over what `before` had, and possibly more, and has failed if
`before` had.
-/
def Extends (before later : Fed) : Prop :=
  before.handed <+: later.handed ∧ (before.failed → later.failed)

/--
Property: what a lexer has done extends as it is fed more slices, and as it is fed the end of
the input.

What a lexer hands over is never taken back, so what a consumer has done with the tokens of a
command, a later command cannot change. The end of the input only releases what waited for it.
-/
def Sequential (feed : Version → List Chars → Bool → Fed) (version : Version)
    (slices more : List Chars) : Prop :=
  Extends (feed version slices false) (feed version (slices ++ more) false) ∧
    Extends (feed version slices false) (feed version slices true)

/--
Property: a lexer fed the slices and then the end of the input has not failed and has handed
over `handed` exactly when `handed` is the tokens of the tokenisation of the input followed by
the end-of-file token.

So it fails exactly when the input has no tokenisation. This is what the standard asks of a
whole input.

Reading L8: the input need not be a `SourceFile`.
-/
def WholeInputCorrect (feed : Version → List Chars → Bool → Fed) (version : Version)
    (slices : List Chars) (handed : List Handed) : Prop :=
  let input := slices.flatten
  (¬ (feed version slices true).failed ∧ (feed version slices true).handed = handed) ↔
    ∃ tokens, Tokenization version input tokens ∧
      handed = tokens.map (·.handed version input) ++ [endOfFile input]


/-! ## About the specification

A property of the specification alone, which `BSmtLibSpec.Facts.Lexicon` proves.
-/

/--
Property: characters whose tokenisation ends with a `)` at their end are handed over whole, and
the characters followed by more are tokenised as the two parts read on their own.

This is a property of the specification alone. A command ends with a `)`, which needs no
delimiter, so its end is a point where reading can stop and start again, possibly in another
version: a lexer fed the command holds nothing of it back, and the input after it is tokenised
as an input of its own, its tokens moved by the length of what came before.
-/
def ComposesAtClose : Prop :=
  ∀ version start tokens, Tokenization version start tokens →
    EndsWithClose tokens start.length →
      HandoverMaximal version start tokens ∧
        ∀ more tokens', Tokenization version (start ++ more) tokens' ↔
          ∃ others, tokens' = tokens ++ others.map (Token.moveBy start.length) ∧
            Tokenization version more others

/-! ## Consumers

What a lexer does with a consumer that need not take every token and continue: the consumer
breaks with a result, fails, switches the version or has the rest of the input discarded. It is
stated relative to `feed`, what the lexer hands over to the `collector`: the consumer takes the
tokens the collector would take, up to where it breaks, fails or makes a request, and what the
lexer does after that is stated here.

A consumer here decides from the entries it has taken alone (`Consumer`). A plain consumer is
handed the tokens. A concrete consumer is also handed the whitespace and comments (the layout),
each piece an entry of its own (`layoutFrom`), and decides at them as at tokens: it may
continue, break, fail, switch the version or have the rest discarded at any entry.

- **The break.** When the consumer breaks with a result, the lexer holds the result, located at
  the end of the entry the consumer broke at, and goes on lexing what it is fed. The result is
  confirmed only at the end of the input, where the lexer returns it without handing the end of
  the input over.
- **Trailing input.** While a result is held, the first entry the lexer hands over is the error
  `UnexpectedTrailingToken`, located at the start of that entry. Entries that the consumer left
  untaken when it broke count as handed over. A lexical error found before that entry is a
  lexical error, as it would be without the break.
- **Requests.** A switch of the version or discarding that the consumer asks for at an entry
  stands, whether the consumer continues, breaks or fails at that entry.
- **Discarding.** When the consumer has the rest discarded, the lexer drops everything it is fed
  after the entry, and hands over nothing more but the end of the input, which it hands over
  unless a result is held or the consumer has failed. It reports where the discarding began.
  While discarding, the location does not move: the end of the input is located there.
- **The end of the input.** Every consumer breaks at the end of the input at the latest: that is
  the consumer's obligation, not the lexer's (`Consumer.BreaksAtEnd`). After the end of the
  input, everything is reset: the version to the one the lexer was created with, the discarding,
  the held result, and any partial token (`ResetsAtEnd`).
-/

/-- What a consumer answers when it has taken an entry. -/
inductive Answer (α ε : Type) where
  /-- It goes on taking entries. -/
  | «continue»
  /-- It breaks with the result. -/
  | «break» (result : α)
  /-- It fails with the error. -/
  | fail (error : ε)

/--
A consumer as a lexer sees it: its results and errors, whether it is concrete, and what it
answers and asks for after each entry, given the entries it has taken so far, in order, the last
one among them. The entries are the tokens, and for a concrete consumer also the pieces of
whitespace and comments.

A consumer that asks for a switch of the version has the input after the entry read in that
version; one that asks for discarding has the input after the entry dropped. Both requests stand
whether the consumer continues, breaks or fails at the entry: a consumer that breaks has the
trailing input read in the version it asked for, and one that fails leaves the lexer in that
version and discarding. What a lexer that recovers from such a failure is to read next is left
to the design of recovery.
-/
structure Consumer where
  Result : Type
  Error : Type
  /-- Whether the consumer is handed the whitespace and comments. -/
  concrete : Bool
  answer : List Handed → Answer Result Error
  /-- The version the consumer switches to after the entry, if it switches. -/
  switchTo : List Handed → Option Version
  /-- Whether the consumer has the rest of the input discarded after the entry. -/
  discards : List Handed → Bool

/--
Property: the consumer does not continue on the end-of-file token.

Every consumer breaks at the end of the input at the latest, with a result, or fails. It is an
obligation on the consumer: a lexer handed a consumer that continues there owes nothing.
-/
def Consumer.BreaksAtEnd (consumer : Consumer) : Prop :=
  ∀ taken token, token.type = .endOfFile → consumer.answer (taken ++ [token]) ≠ .continue

/--
The consumer that `feed` is about: it takes every token, plain, continues on each but the
end-of-file token, breaks on that, and asks for nothing.
-/
def collector : Consumer where
  Result := Unit
  Error := Empty
  concrete := false
  answer taken := if taken.getLast?.map (·.type) = some .endOfFile then .break () else .continue
  switchTo _ := none
  discards _ := false

/-- How a lexer has failed. -/
inductive Failure (ε : Type) where
  /-- With a lexical error. -/
  | lexical
  /-- With the consumer's error. -/
  | consumer (error : ε)
  /-- With `UnexpectedTrailingToken`, at the location. -/
  | trailing (location : Location)

/-- Where a lexer stands with its consumer. -/
inductive Outcome (α ε : Type) where
  /-- It waits for more input, holding no result. -/
  | running
  /-- It holds the consumer's result, located where the consumer broke, and waits for more. -/
  | holding (result : α) (location : Location)
  /-- It has failed. -/
  | failed (failure : Failure ε)
  /-- The input has ended, and it has returned the consumer's result, located where the
  consumer broke. -/
  | finished (result : α) (location : Location)

/--
What a lexer has done with a consumer after being fed the input: the tokens the consumer took,
in order, where the lexer stands, the version in force, and where the discarding began, if the
lexer discards.
-/
structure Session (α ε : Type) where
  taken : List Handed
  outcome : Outcome α ε
  version : Version
  discardedFrom : Option Location

/-- Whether the lexer has failed. -/
def Outcome.isFailed {α ε : Type} : Outcome α ε → Bool
  | .failed _ => true
  | _ => false

/-- Whether the input has ended with the consumer's result returned. -/
def Outcome.isFinished {α ε : Type} : Outcome α ε → Bool
  | .finished _ _ => true
  | _ => false

/-- What the lexer has handed over to the consumer, and whether it has failed. -/
def Session.fed {α ε : Type} (session : Session α ε) : Fed :=
  { handed := session.taken, failed := session.outcome.isFailed }

/--
Property: the end of the input resets the version and the discarding.

The session of a lexer created with the version `start`, which reaches the outcome with the
tokens taken: if the outcome finishes the input, the version is reset to `start` and the lexer
no longer discards; otherwise the version and the discarding are as given.
-/
def settle {α ε : Type} (start : Version) (taken : List Handed) (outcome : Outcome α ε)
    (version : Version) (discardedFrom : Option Location) : Session α ε :=
  if outcome.isFinished then ⟨taken, outcome, start, none⟩
  else ⟨taken, outcome, version, discardedFrom⟩

/--
The location, located in an input on its own, as located in the input that is `before`
followed by that input.
-/
def Location.after (before : Chars) (location : Location) : Location :=
  let start := locate before before.length
  { offset := before.length + location.offset
    line := start.line + location.line
    column := if location.line = 0 then start.column + location.column else location.column }

/-- The token, handed over from an input on its own, as handed over from the input that is
`before` followed by that input. -/
def Handed.after (before : Chars) (handed : Handed) : Handed :=
  { handed with start := handed.start.after before, «end» := handed.«end».after before }

/--
Property: the input after a switch of the version is read on its own, in the new version.

What a lexer hands over to the collector from the offset of the input on, in the version: what
`feed` does with the input from the offset on, read on its own, located in the whole input.
`ReadsOnItsOwn` and `ComposesAtClose` say that reading on its own loses nothing where the switch
is at a `)`.
-/
def segment (feed : Version → List Chars → Bool → Fed) (version : Version) (input : Chars)
    (ended : Bool) (offset : Nat) : Fed :=
  let fed := feed version [input.drop offset] ended
  { handed := fed.handed.map (Handed.after (input.take offset)), failed := fed.failed }

/-- The piece of layout of the input that starts at the offset, has the length and the content,
as handed over. -/
def layoutEntry (input : Chars) (type : TokenType) (offset length : Nat) (content : Chars) :
    Handed :=
  { type, start := locate input offset, «end» := locate input (offset + length), reserved := none
    content }

open Classical in
/--
Property: the layout that a lexer hands to a concrete consumer from the offset of the input on,
up to the first character that starts no layout: each piece an entry of its own, handed over
once it is complete.

A piece is a run of white space characters, complete once a character after it is not one, or a
comment with its line-breaking character, complete once that character is read; either is
complete once the input has ended. The content of a run is its characters, that of a comment its
characters after the `;`, with the line-breaking character. Between two tokens, the pieces reach
from the one to the other.
-/
noncomputable def layoutFrom (input : Chars) (ended : Bool) (offset : Nat) : List Handed :=
  match _h : input.drop offset with
  | [] => []
  | c :: rest =>
    if whiteSpaceChar [c] then
      let run := c :: rest.takeWhile fun d => decide (whiteSpaceChar [d])
      if ended = true ∨ offset + run.length < input.length then
        layoutEntry input .whitespace offset run.length run ::
          layoutFrom input ended (offset + run.length)
      else []
    else if [c] = chars ";" then
      let body := rest.takeWhile fun d => !decide (lineBreak [d])
      match rest.dropWhile fun d => !decide (lineBreak [d]) with
      | lb :: _ =>
        layoutEntry input .comment offset (body.length + 2) (body ++ [lb]) ::
          layoutFrom input ended (offset + (body.length + 2))
      | [] => if ended then [layoutEntry input .comment offset (body.length + 1) body] else []
    else []
termination_by input.length - offset
decreasing_by
  all_goals
    have hlen := congrArg List.length _h
    simp only [List.length_drop, List.length_cons] at hlen
    try simp only [List.length_cons]
    omega

/--
Property: the entries a lexer hands to the consumer from the offset of the input on, given the
tokens it hands over from there, and whether it fails after them: the tokens, and for a concrete
consumer also the layout before the first token and after each token.
-/
noncomputable def withLayout (concrete : Bool) (input : Chars) (ended : Bool) (offset : Nat)
    (fed : Fed) : Fed :=
  if concrete then
    { handed := layoutFrom input ended offset ++
        fed.handed.flatMap fun token => token :: layoutFrom input ended token.«end».offset
      failed := fed.failed }
  else fed

/--
Property: the entries ready from the offset of the input on, when the input from there is read
on its own in the version (`segment`), and whether the lexer fails after them.
-/
noncomputable def readyFrom (feed : Version → List Chars → Bool → Fed) (concrete : Bool)
    (version : Version) (input : Chars) (ended : Bool) (offset : Nat) : Fed :=
  withLayout concrete input ended offset (segment feed version input ended offset)

/--
Property: after an entry, the lexer goes on with the entries ready after it in the version in
force after it.

The entries ready after an entry that ends at the offset, and whether the lexer fails after them:
those ready after it as before, given as `rest` and `failed`, unless the consumer switched the
version at the entry, in which case the input after the entry is read on its own in the new
version. A switch is allowed after any entry.
-/
noncomputable def following (feed : Version → List Chars → Bool → Fed) (concrete : Bool)
    (input : Chars) (ended : Bool) (offset : Nat) (switchTo : Option Version)
    (rest : List Handed) (failed : Bool) : Fed :=
  match switchTo with
  | none => ⟨rest, failed⟩
  | some version => readyFrom feed concrete version input ended offset

/--
Property: where a lexer stands after the consumer broke with the result at an entry that ends at
`location`, given the entries ready after it and whether the lexer fails after them.

The first entry handed over after the break is `UnexpectedTrailingToken`, at its start. If that
entry is the end-of-file token, the input has ended and the result is returned instead. If no
entry follows, the lexer fails if it fails after the entries, with a lexical error, and otherwise
holds the result.
-/
inductive AfterBreak {α ε : Type} (result : α) (location : Location) :
    List Handed → Bool → Outcome α ε → Prop
  /-- An entry other than the end of file follows. -/
  | trailing : next.type ≠ .endOfFile →
      AfterBreak result location (next :: ready) failed (.failed (.trailing next.start))
  /-- The end of the input follows: the result is returned. -/
  | ends : next.type = .endOfFile →
      AfterBreak result location (next :: ready) failed (.finished result location)
  /-- Nothing follows, and the lexer fails. -/
  | lexical : AfterBreak result location [] true (.failed .lexical)
  /-- Nothing follows yet. -/
  | held : AfterBreak result location [] false (.holding result location)

/--
Property: what a lexer created with the version `start`, fed the input, and then the end of the
input if it has ended, does with the consumer from the point where the consumer has taken
`taken`, the version in force is `version`, the entries ready next are `ready` and the lexer
fails after them exactly if `failed`: it ends in the session.

Each constructor is one step: the consumer takes the next ready entry and answers, or no entry
is ready. The rules of the section's documentation are the constructors' premises.
-/
inductive Runs (feed : Version → List Chars → Bool → Fed) (consumer : Consumer)
    (start : Version) (input : Chars) (ended : Bool) :
    Version → List Handed → Bool → List Handed → Session consumer.Result consumer.Error → Prop
  /-- No entry is ready, and the lexer has not failed: it waits. -/
  | waiting : Runs feed consumer start input ended version [] false taken
      (settle start taken .running version none)
  /-- No entry is ready, and the lexer has failed. -/
  | lexical : Runs feed consumer start input ended version [] true taken
      (settle start taken (.failed .lexical) version none)
  /-- The consumer fails at the entry. Its switch of the version and its discarding stand. -/
  | fails : consumer.answer (taken ++ [token]) = .fail error →
      Runs feed consumer start input ended version (token :: ready) failed taken
        (settle start (taken ++ [token]) (.failed (.consumer error))
          ((consumer.switchTo (taken ++ [token])).getD version)
          (if consumer.discards (taken ++ [token]) then some token.«end» else none))
  /-- The consumer breaks at the end-of-file token: the result is returned. -/
  | ends : token.type = .endOfFile → consumer.answer (taken ++ [token]) = .break result →
      Runs feed consumer start input ended version (token :: ready) failed taken
        (settle start (taken ++ [token]) (.finished result token.«end») version none)
  /-- The consumer continues at an entry: the lexer goes on with the entries ready after it, in
  the version the consumer switched to, if it did. -/
  | continues : token.type ≠ .endOfFile → consumer.answer (taken ++ [token]) = .continue →
      consumer.discards (taken ++ [token]) = false →
      Runs feed consumer start input ended ((consumer.switchTo (taken ++ [token])).getD version)
        (following feed consumer.concrete input ended token.«end».offset
          (consumer.switchTo (taken ++ [token])) ready failed).handed
        (following feed consumer.concrete input ended token.«end».offset
          (consumer.switchTo (taken ++ [token])) ready failed).failed
        (taken ++ [token]) session →
      Runs feed consumer start input ended version (token :: ready) failed taken session
  /-- The consumer breaks at an entry: the lexer holds the result and checks what follows. -/
  | breaks : token.type ≠ .endOfFile → consumer.answer (taken ++ [token]) = .break result →
      consumer.discards (taken ++ [token]) = false →
      AfterBreak result token.«end»
        (following feed consumer.concrete input ended token.«end».offset
          (consumer.switchTo (taken ++ [token])) ready failed).handed
        (following feed consumer.concrete input ended token.«end».offset
          (consumer.switchTo (taken ++ [token])) ready failed).failed outcome →
      Runs feed consumer start input ended version (token :: ready) failed taken
        (settle start (taken ++ [token]) outcome
          ((consumer.switchTo (taken ++ [token])).getD version) none)
  /-- The consumer breaks at an entry and has the rest discarded, before the end of the input:
  the lexer holds the result and discards. -/
  | discardsHeld : token.type ≠ .endOfFile → consumer.answer (taken ++ [token]) = .break result →
      consumer.discards (taken ++ [token]) = true → ended = false →
      Runs feed consumer start input ended version (token :: ready) failed taken
        (settle start (taken ++ [token]) (.holding result token.«end»)
          ((consumer.switchTo (taken ++ [token])).getD version) (some token.«end»))
  /-- The consumer breaks at an entry and has the rest discarded, and the input has ended: the
  end of the input is not handed over, and the result is returned. -/
  | discardsEnds : token.type ≠ .endOfFile → consumer.answer (taken ++ [token]) = .break result →
      consumer.discards (taken ++ [token]) = true → ended = true →
      Runs feed consumer start input ended version (token :: ready) failed taken
        (settle start (taken ++ [token]) (.finished result token.«end»)
          ((consumer.switchTo (taken ++ [token])).getD version) none)
  /-- The consumer continues at an entry and has the rest discarded, before the end of the
  input: the lexer discards and waits for the end of the input. -/
  | discardsWaiting : token.type ≠ .endOfFile → consumer.answer (taken ++ [token]) = .continue →
      consumer.discards (taken ++ [token]) = true → ended = false →
      Runs feed consumer start input ended version (token :: ready) failed taken
        (settle start (taken ++ [token]) .running
          ((consumer.switchTo (taken ++ [token])).getD version) (some token.«end»))
  /-- The consumer continues at an entry and has the rest discarded, and the input has ended:
  the end of the input is handed over, located where the discarding began, and the consumer
  breaks at it. -/
  | discardsToEnd : token.type ≠ .endOfFile → consumer.answer (taken ++ [token]) = .continue →
      consumer.discards (taken ++ [token]) = true → ended = true →
      consumer.answer (taken ++ [token, endOfFileAt token.«end»]) = .break result →
      Runs feed consumer start input ended version (token :: ready) failed taken
        (settle start (taken ++ [token, endOfFileAt token.«end»]) (.finished result token.«end»)
          ((consumer.switchTo (taken ++ [token])).getD version) none)
  /-- The consumer continues at an entry and has the rest discarded, and the input has ended:
  the end of the input is handed over, located where the discarding began, and the consumer
  fails at it. The discarding goes on from the entry, and a switch of the version at the end of
  the input stands. -/
  | discardsFailsAtEnd : token.type ≠ .endOfFile →
      consumer.answer (taken ++ [token]) = .continue →
      consumer.discards (taken ++ [token]) = true → ended = true →
      consumer.answer (taken ++ [token, endOfFileAt token.«end»]) = .fail error →
      Runs feed consumer start input ended version (token :: ready) failed taken
        (settle start (taken ++ [token, endOfFileAt token.«end»]) (.failed (.consumer error))
          ((consumer.switchTo (taken ++ [token, endOfFileAt token.«end»])).getD
            ((consumer.switchTo (taken ++ [token])).getD version)) (some token.«end»))

/--
What a lexer has done with a consumer, created with a version: after being fed the earlier
inputs, each as slices followed by the end of the input, then the slices, and then the end of
the input if it has ended. The consumer starts each input with no entries taken.

A lexer that stops at its first error is given only earlier inputs on which it finished.
-/
abbrev Lexing := (consumer : Consumer) → Version → List (List Chars) → List Chars → Bool →
  Session consumer.Result consumer.Error

/-- What a lexer hands over to the `collector` on one input: the `feed` of the properties
above. -/
def Lexing.fed (lexing : Lexing) (version : Version) (slices : List Chars) (ended : Bool) :
    Fed :=
  (lexing collector version [] slices ended).fed

/--
Property: a lexer fed the slices, and then the end of the input if it has ended, does with a
consumer that breaks at the end of the input what `Runs` states, from the start of the input
with nothing taken, relative to what it hands over to the collector.
-/
def HandlesConsumer (lexing : Lexing) (consumer : Consumer) (version : Version)
    (slices : List Chars) (ended : Bool) : Prop :=
  consumer.BreaksAtEnd →
    Runs lexing.fed consumer version slices.flatten ended version
      (readyFrom lexing.fed consumer.concrete version slices.flatten ended 0).handed
      (readyFrom lexing.fed consumer.concrete version slices.flatten ended 0).failed []
      (lexing consumer version [] slices ended)

/--
Property: after an input on which the lexer finished, the lexer does on what it is fed next
what a new lexer created with the same version does.

So the end of the input resets everything: the version, the discarding, the held result, the
partial token, and the locations, which start again at zero.
-/
def ResetsAtEnd (lexing : Lexing) : Prop :=
  ∀ consumer version earlier first slices ended,
    (lexing consumer version earlier first true).outcome.isFinished →
      lexing consumer version (earlier ++ [first]) slices ended =
        lexing consumer version [] slices ended

/--
Property: a lexer is correct with every consumer on every version and every input, ended or not:
it is `Correct` with the collector, handles every consumer that breaks at the end of the input,
and is reset by the end of the input.
-/
def CorrectWithConsumers (lexing : Lexing) : Prop :=
  Correct lexing.fed ∧ (∀ consumer version slices ended,
    HandlesConsumer lexing consumer version slices ended) ∧ ResetsAtEnd lexing

/-! ### A lexer that recovers from errors

A lexer that recovers from an error reports it and goes on lexing. What it hands over after an
error is not stated here; what is stated is what becomes of a held result.
-/

/--
What a lexer that recovers from errors has done with a consumer that has broken: how many errors
it has reported since the break, and the result it holds, or, once the input has ended, the one
it returned.
-/
structure Recovered (α : Type) where
  errorsSinceBreak : Nat
  held : Option α

/--
What a lexer that recovers from errors has done with a consumer, created with a version, after
being fed the slices and then the end of the input if it has ended: none while the consumer has
not broken.
-/
abbrev RecoveringLexing := (consumer : Consumer) → Version → List Chars → Bool →
  Option (Recovered consumer.Result)

/--
Property: a lexer that recovers from errors drops the held result on any error after the break,
and then returns no result at the end of the input.

A value is confirmed only at the end of the input, so an error after it, `UnexpectedTrailingToken`
among them, leaves nothing to confirm.
-/
def DropsHeldOnError (lexing : RecoveringLexing) : Prop :=
  ∀ consumer version slices ended recovered,
    lexing consumer version slices ended = some recovered → 0 < recovered.errorsSinceBreak →
      recovered.held = none

end BSmtLibSpec.Lexer
