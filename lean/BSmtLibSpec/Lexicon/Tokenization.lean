module

public import BSmtLibSpec.Lexicon

@[expose] public section

/-!
# Tokenising an input

How an input is broken into a sequence of tokens, its tokenisation: whitespace breaks the
input into tokens, and every token is a lexical token.
-/

namespace BSmtLibSpec.Lexicon

open Regex

/--
The delimitation rule: a token other than a parenthesis is followed by the end of the
input, a white space character, a parenthesis or the `;` that starts a comment. The standard
does not state how adjacent tokens are separated; this is the strict reading, under which
`1.5` is one decimal rather than `1` followed by `.5`, and `"a"b` is not an input.

Reading L1: a token other than a parenthesis is followed by a delimiter.
-/
def Tokenization.Delimited (category : Category) (rest : Chars) : Prop :=
  category = .parenOpen ∨ category = .parenClose ∨ rest = [] ∨
    ∃ c more, rest = c :: more ∧ (whiteSpaceChar [c] ∨ oneOf "();" [c])

/--
`Tokenization.From version offset input tokens`: with the starting offset `offset`, the tokens
are a tokenisation of the input.

Standard: 2.7 §3.1: the only lexical function of whitespace is to break the source text into
tokens. Readings L1 and L2.
-/
inductive Tokenization.From (version : Version) : Nat → Chars → List Token → Prop
  | done : whitespaceAtEnd w → Tokenization.From version offset w []
  | token : whitespace w → categoryRegex version category s → Tokenization.Delimited category rest →
      Tokenization.From version (offset + w.length + s.length) rest tokens →
      Tokenization.From version offset (w ++ s ++ rest)
        (⟨category, offset + w.length, s⟩ :: tokens)

/--
`Tokenization version input tokens`: the tokens are a tokenisation of the input.

Standard: 2.7 §3.1, as `Tokenization.From`.
-/
def Tokenization (version : Version) (input : Chars) (tokens : List Token) : Prop :=
  Tokenization.From version 0 input tokens

/--
The tokens are a tokenisation of the input, which ends with the last of them: no whitespace
follows.
-/
def Tokenization.Exactly (version : Version) (offset : Nat) (input : Chars)
    (tokens : List Token) : Prop :=
  Tokenization.From version offset input tokens ∧
    ∃ last, tokens.getLast? = some last ∧ last.offset + last.text.length = offset + input.length

end BSmtLibSpec.Lexicon
