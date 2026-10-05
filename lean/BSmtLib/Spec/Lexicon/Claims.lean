import BSmtLib.Spec.Lexicon.Tokenization

/-!
# Claims about tokenisation

What is claimed about the tokenisation of an input. The claims are trusted as much as the
spec: a proof shows that a claim holds, so the claim has to say what is meant.
-/

namespace BSmtLib.Spec.Lexicon

/-! ## About the spec -/

/--
Claim: about the lexicon, to be proved.

Every input has at most one tokenisation.
-/
def Unique : Prop :=
  ∀ version input tokens tokens',
    Tokenization version input tokens → Tokenization version input tokens' → tokens = tokens'

/--
Claim: a definition the claims about lexers are stated with.

The characters fed so far can still be continued into an input that has a
tokenisation.
-/
def Viable (version : Version) (fed : Chars) : Prop :=
  ∃ rest tokens, Tokenization version (fed ++ rest) tokens

/--
Claim: a definition the claims about lexers are stated with.

Every tokenisation of every continuation of the characters fed so far starts with the tokens.
-/
def Determined (version : Version) (fed : Chars) (tokens : List Token) : Prop :=
  ∀ rest tokens', Tokenization version (fed ++ rest) tokens' → tokens <+: tokens'

end BSmtLib.Spec.Lexicon
