import BSmtLib.Spec.Lexicon.Rules

/-!
# Tokenising an input

How an input is broken into a sequence of tokens, its tokenisation: whitespace breaks the
input into tokens, and every token is one of the lexical tokens of the version.
-/

namespace BSmtLib.Spec.Lexicon

open Regex

/--
The kinds of lexical token: the parentheses, the token categories and the reserved words.

Standard: 2.7 §3.1: the lexical tokens are the parentheses, the elements of the token
categories and the reserved words.
-/
inductive Category where
  | parenOpen
  | parenClose
  | numeral
  | decimal
  | hexadecimal
  | binary
  | string
  | simpleSymbol
  | quotedSymbol
  | keyword
  | reserved
  deriving DecidableEq, Repr

/--
The expression of each kind of token in the version.

Standard: 2.7 §3.1, as `Category`.
-/
def categoryRegex (version : Version) : Category → Regex
  | .parenOpen => lit "("
  | .parenClose => lit ")"
  | .numeral => numeral
  | .decimal => decimal
  | .hexadecimal => hexadecimal
  | .binary => binary
  | .string => if version = .v2_0 then string20 else string
  | .simpleSymbol => simpleSymbol version
  | .quotedSymbol => quotedSymbol
  | .keyword => keyword
  | .reserved => reserved version

/--
A token of an input: its kind, the offset of its first character, and its characters.

Standard: 2.7 §3.1 lexical tokens; the offset and the characters are how the spec records a
token.
-/
structure Token where
  category : Category
  offset : Nat
  text : Chars
  deriving DecidableEq, Repr

/--
The delimitation rule: a token other than a parenthesis is followed by the end of the
input, a white space character, a parenthesis or the `;` that starts a comment. The standard
does not state how adjacent tokens are separated; this is the strict reading, under which
`1.5` is one decimal rather than `1` followed by `.5`, and `"a"b` is not an input.

Reading L1: a token other than a parenthesis is followed by a delimiter.
-/
def Delimited (category : Category) (rest : Chars) : Prop :=
  category = .parenOpen ∨ category = .parenClose ∨ rest = [] ∨
    ∃ c more, rest = c :: more ∧ (whiteSpaceChar [c] ∨ oneOf "();" [c])

/--
`TokenizationFrom version offset input tokens`: in the version, the tokens are a tokenisation
of the input, whose first character is at `offset`.

Standard: 2.7 §3.1: the only lexical function of whitespace is to break the source text into
tokens. Readings L1 and L2.
-/
inductive TokenizationFrom (version : Version) : Nat → Chars → List Token → Prop
  | done : whitespaceAtEnd w → TokenizationFrom version offset w []
  | token : whitespace w → categoryRegex version category s → Delimited category rest →
      TokenizationFrom version (offset + w.length + s.length) rest tokens →
      TokenizationFrom version offset (w ++ s ++ rest) 
        (⟨category, offset + w.length, s⟩ :: tokens)

/--
`Tokenization version input tokens`: in the version, the tokens are a tokenisation of the
input.

Standard: 2.7 §3.1, as `TokenizationFrom`.
-/
def Tokenization (version : Version) (input : Chars) (tokens : List Token) : Prop :=
  TokenizationFrom version 0 input tokens

/--
The content of a token: what a string literal stands for, the name of a quoted symbol
without its bars, a keyword without its colon, the digits of a hexadecimal or binary without
`#x` or `#b`, and otherwise the characters of the token.

Standard: 2.7 §3.1 String literals and Symbols, for what a string literal and a quoted symbol
stand for. Dropping the colon of a keyword and the `#x` and `#b` of a hexadecimal and a binary
is a convention of the spec.
-/
def Token.content (version : Version) (token : Token) : Chars :=
  match token.category with
  | .string => (if version = .v2_0 then unescape20 else unescape) (token.text.drop 1).dropLast
  | .quotedSymbol => (token.text.drop 1).dropLast
  | .keyword => token.text.drop 1
  | .hexadecimal | .binary => token.text.drop 2
  | _ => token.text

/--
The token moved by `k` characters to the right: the same kind and characters, at an offset
larger by `k`.
-/
def Token.moveBy (k : Nat) (token : Token) : Token :=
  ⟨token.category, token.offset + k, token.text⟩

/--
The tokens end with a `)` whose last character is just before the offset `stop`.
-/
def EndsWithClose (tokens : List Token) (stop : Nat) : Prop :=
  ∃ last, tokens.getLast? = some last ∧ last.category = .parenClose ∧
    last.offset + last.text.length = stop

end BSmtLib.Spec.Lexicon
