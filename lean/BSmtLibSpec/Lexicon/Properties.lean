module

public import BSmtLibSpec.Lexicon.Tokenization

@[expose] public section

/-!
# Properties of tokenisation

Each definition here formalises a property stated in words on its first line, such as "every
input has at most one tokenisation".
-/

namespace BSmtLibSpec.Lexicon.Properties

open Regex (Chars)

/-! ## About the formalism -/

/--
Property: every input has at most one tokenisation.

This is a property of the formalism alone. `BSmtLibSpec.Facts.Lexicon` proves it as
`Lexicon.unique`. If it did not hold, the formalism would let one input stand for two
different sequences of tokens, and no lexer could hand over the right one.
-/
def Unique : Prop :=
  ∀ version input tokens tokens',
    Tokenization version input tokens → Tokenization version input tokens' → tokens = tokens'

/--
Property: some input that starts with the given characters has a tokenisation.

A lexer fed an input in slices does not know the characters that follow. It can report an
error only once the characters fed are not viable: until then, the characters still to come may
yet make them the start of a valid input.
-/
def Viable (version : Version) (start : Chars) : Prop :=
  ∃ rest tokens, Tokenization version (start ++ rest) tokens

/--
Property: all tokenisations of inputs that start with the given characters start with the
given tokens.

No characters that follow can change these tokens, so a lexer fed an input in slices can hand
them over without waiting for the rest of the input. The empty list always qualifies, and if
the given characters are not `Viable`, every list does.
-/
def Determined (version : Version) (start : Chars) (tokens : List Token) : Prop :=
  ∀ rest tokens', Tokenization version (start ++ rest) tokens' → ∃ more, tokens' = tokens ++ more

/--
Property: characters read from any offset, in any version, are tokenised as they are on their
own, their tokens moved to that offset.

This is a property of the formalism alone. Where reading stops and starts again, possibly
in another version, the characters after the stop are read as an input of their own; without
this property, where they stand in the whole input could change their tokens.
-/
def ReadsOnItsOwn : Prop :=
  ∀ version offset input tokens,
    Tokenization.From version offset input tokens ↔
      ∃ tokens₀, tokens = tokens₀.map (Token.moveBy offset) ∧ Tokenization version input tokens₀

end BSmtLibSpec.Lexicon.Properties
