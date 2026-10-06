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
Extension: where a lexer reports a token to be; not in the standard.

A location in the input, all zero-based.
-/
structure Location where
  offset : Nat
  line : Nat
  column : Nat
  deriving DecidableEq, Repr

/--
Extension: locations are zero-based, and lines are counted by line feeds alone.

The location of `offset` in the input: lines are counted by line feeds (10) alone, and
columns by characters.
-/
def locate (input : Chars) (offset : Nat) : Location :=
  let before := input.take offset
  { offset, line := before.count 10, column := (before.reverse.takeWhile (· ≠ 10)).length }

/--
Extension: the types of the tokens a lexer hands over.

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
Extension: which kind of reserved word a handed-over token is.

Which kind of reserved word a token is.
-/
inductive ReservedKind where
  | general
  | command
  deriving DecidableEq, Repr

/--
Extension: the common form of a token a lexer hands over.

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
Extension: the type of a handed-over token of each kind.

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
Extension: as `ReservedKind`.

Which kind of reserved word a token is, if it is one.
-/
def Token.reservedKind (version : Version) (token : Token) :
    Option ReservedKind :=
  if token.category ≠ .reserved then none
  else if ∃ w ∈ basicReservedWords version, token.text = chars w then some .general
  else some .command

/--
Extension: as `Handed`.

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
Extension: a lexer hands over an end-of-file token after the input.

The end-of-file token after the input.
-/
def endOfFile (input : Chars) : Handed :=
  { type := .endOfFile, start := locate input input.length, «end» := locate input input.length,
    reserved := none, content := [] }

/-! ## About a lexer

Extension D: the properties do not require the input to be a `SourceFile`, so a lexer that
has them accepts characters from 128 on in 2.0 as 2.5 and later do. 2.0 is used mainly
to read old scripts into 2.5 and later, or to give a solver that reads 2.5 and later a legacy
mode, where accepting these characters as 2.5 does is what is wanted.
-/

/--
Property: the token is a parenthesis or ends before the last character fed so far.
Extension: when this library's lexer hands a token over; not in the standard.

A token other than a parenthesis needs a delimiter after it (`Delimited`); this states that
the character after it has been fed.
-/
def DelimiterFed (fed : Chars) (token : Token) : Prop :=
  token.category = .parenOpen ∨ token.category = .parenClose ∨
    token.offset + token.text.length < fed.length

/--
Property: the tokens are the longest list that is `Determined` by the characters fed so far
and in which every token but a parenthesis ends before the last character fed. Extension: when
this library's lexer hands a token over; not in the standard.

These are the tokens that a lexer fed an input in slices hands over. A lexer hands a token
over only once it has seen that the character after it delimits it; a parenthesis needs no
delimiter. After `(x |abc|`, the settled tokens are `(` and `x`: `|abc|` is determined, but
the character after it has not been fed yet. On characters that are not `Viable`, no list is
settled.
-/
def Settled (version : Version) (fed : Chars) (tokens : List Token) : Prop :=
  Determined version fed tokens ∧ (∀ token ∈ tokens, DelimiterFed fed token) ∧
    ∀ tokens', Determined version fed tokens' → (∀ token ∈ tokens', DelimiterFed fed token) →
      tokens'.length ≤ tokens.length

/--
Property: of a lexer, to be proved of an implementation. Extension D: the input need not be a
`SourceFile`.

A lexer is correct on whole inputs, however they are cut into slices: `lex version slices` is
what it hands over when fed the slices and then the end of the input, or `none` if it fails.
It hands over the tokens of the tokenisation of the characters fed and the end-of-file token
exactly when they have a tokenisation.

This is stated for a consumer that takes every token handed over and always continues; how a
lexer answers a consumer that finishes, leaves tokens, switches version or fails will be
stated relative to it.
-/
def LexerCorrect (lex : Version → List Chars → Option (List Handed)) : Prop :=
  ∀ version slices handed, let input := slices.flatten
    lex version slices = some handed ↔
      ∃ tokens, Tokenization version input tokens ∧
        handed = tokens.map (·.handed version input) ++ [endOfFile input]

/--
Property: of a lexer, to be proved of an implementation. Extension D: the input need not be a
`SourceFile`.

A lexer fed in slices is correct: `feed version slices` is what it handed over after the
slices, and whether it failed. It fails exactly when the characters fed stop being viable,
and it hands over the tokens settled by the longest viable part of them.

This is stated for a consumer that takes every token handed over and always continues; how a
lexer answers a consumer that finishes, leaves tokens, switches version or fails will be
stated relative to it.
-/
def StreamingCorrect (feed : Version → List Chars → List Handed × Bool) : Prop :=
  ∀ version slices, let fed := slices.flatten
    ((feed version slices).2 = true ↔ ¬ Viable version fed) ∧
    ∃ viable tokens, (∃ after, fed = viable ++ after) ∧ Viable version viable ∧
      (∀ longer after, fed = longer ++ after → Viable version longer →
        longer.length ≤ viable.length) ∧
      Settled version viable tokens ∧
      (feed version slices).1 = tokens.map (·.handed version fed)

end BSmtLib.Spec.Lexer
