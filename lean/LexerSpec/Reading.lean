import LexerSpec.Lexicon

/-!
# Reading an input

How an input is read as a sequence of tokens: whitespace breaks the input into tokens, and
every token is one of the lexical tokens of the version.
-/

namespace LexerSpec

open Regex

/-- The kinds of lexical token: the parentheses, the token categories and the reserved words. -/
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

/-- The expression of each kind of token in the version. -/
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

/-- A token of an input: its kind, the offset of its first character, and its characters. -/
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
-/
def Delimited (category : Category) (rest : Chars) : Prop :=
  category = .parenOpen ∨ category = .parenClose ∨ rest = [] ∨
    ∃ c more, rest = c :: more ∧ (whiteSpaceChar [c] ∨ oneOf "();" [c])

/--
`ReadsFrom version offset input tokens`: in the version, the input, whose first character is
at `offset`, reads as the tokens.
-/
inductive ReadsFrom (version : Version) : Nat → Chars → List Token → Prop
  | done : whitespaceAtEnd w → ReadsFrom version offset w []
  | token : whitespace w → categoryRegex version category s → Delimited category rest →
      ReadsFrom version (offset + w.length + s.length) rest tokens →
      ReadsFrom version offset (w ++ s ++ rest) (⟨category, offset + w.length, s⟩ :: tokens)

/-- `Reads version input tokens`: in the version, the input reads as the tokens. -/
def Reads (version : Version) (input : Chars) (tokens : List Token) : Prop :=
  ReadsFrom version 0 input tokens

end LexerSpec
