import BSmtLib.Spec.Lexicon.Reading

/-!
# Claims about the reading

What is claimed about the lexicon's reading of an input. The claims are trusted as much as the
spec: a proof shows that a claim holds, so the claim has to say what is meant.
-/

namespace BSmtLib.Spec.Lexicon

/-! ## About the spec -/

/--
Claim: about the lexicon, to be proved.

Every input has at most one reading.
-/
def Unique : Prop :=
  ∀ version input tokens tokens',
    Reads version input tokens → Reads version input tokens' → tokens = tokens'

/--
Claim: a definition the claims about lexers are stated with.

The characters fed so far can still be continued into an input that has a reading.
-/
def Viable (version : Version) (fed : Chars) : Prop :=
  ∃ rest tokens, Reads version (fed ++ rest) tokens

/--
Claim: a definition the claims about lexers are stated with.

Every reading of every continuation of the characters fed so far starts with the tokens.
-/
def Determined (version : Version) (fed : Chars) (tokens : List Token) : Prop :=
  ∀ rest tokens', Reads version (fed ++ rest) tokens' → tokens <+: tokens'

end BSmtLib.Spec.Lexicon
