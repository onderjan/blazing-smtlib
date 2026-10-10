import BSmtLib.Spec.Lexicon

/-!
# Lexers

What a lexer hands over, in a form that does not depend on how a lexer represents its tokens,
and what it means for a lexer to be correct. The properties are trusted as much as the spec:
a proof shows that a property holds, so the property has to say what is meant.
-/

namespace BSmtLib.Spec.Lexer

open BSmtLib.Spec.Lexicon

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
The token types of the implementation.
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
otherwise the characters of the token. The start and the end are located by `locate`:
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

end BSmtLib.Spec.Lexer

/-
The three definitions below belong to the lexicon's types, so they are in the lexicon's
namespace, where dot notation finds them (`token.handed version input`). They are written here
and not in the lexicon's modules because they build the types above, and a Lean module can use
only what is declared before it.
-/
namespace BSmtLib.Spec.Lexicon

open BSmtLib.Spec.Lexer

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

end BSmtLib.Spec.Lexicon

namespace BSmtLib.Spec.Lexer

open BSmtLib.Spec.Lexicon

/--
The end-of-file token after the input.
-/
def endOfFile (input : Chars) : Handed :=
  { type := .endOfFile, start := locate input input.length, «end» := locate input input.length,
    reserved := none, content := [] }

/-! ## About a lexer

The properties are about one function that an adapter makes of a lexer, `feed`: what the lexer
has done after being fed slices and then, if the input has ended, the end of the input. The
input is the slices joined, so how it is cut into slices does not matter. Each property is
about one version, one input, and whether the input has ended; `Correct` asks for them on every
version and every input, ended or not.

They are stated for a consumer that takes every token handed over and always continues; how a
lexer answers a consumer that finishes, leaves tokens, switches version or fails will be stated
relative to them.

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

A token other than a parenthesis needs a delimiter after it (`Delimited`, Reading L1), so a
lexer can tell that the token ends where it does only once it has read the character after it.
A parenthesis needs no delimiter.
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

Properties that are not a part of `Correct` because they follow from it. `BSmtLib.SpecChecks`
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

end BSmtLib.Spec.Lexer
