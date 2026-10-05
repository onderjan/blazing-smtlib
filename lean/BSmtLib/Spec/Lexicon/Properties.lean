import BSmtLib.Spec.Lexicon.Tokenization

/-!
# Properties of tokenisation

Each definition here formalises a property stated in words on its first line, such as "every
input has at most one tokenisation". The properties of the grammar, of the lexer, and of the
parser are built from them, and proofs about this library end in them.

A proof only shows that the formal statement holds. If a definition here does not formalise
what its first line says, every property built on it, and every proof of one, establishes
something other than what its own words promise, and nothing in Lean will notice. So these
definitions are trusted as much as the rules of the standard, and are to be read with the
same care.
-/

namespace BSmtLib.Spec.Lexicon

/-! ## About the spec -/

/--
Property: every input has at most one tokenisation.

This is a property of the specification alone; `BSmtLib.SpecChecks` is to prove it. It is the
lexical half of `Grammar.ScriptsUnique`.
-/
def Unique : Prop :=
  ∀ version input tokens tokens',
    Tokenization version input tokens → Tokenization version input tokens' → tokens = tokens'

/--
Property: the characters fed so far begin some input that has a tokenisation.

This is used to state when a lexer fed an input in slices fails: `StreamingCorrect` requires
it to fail exactly when the characters fed stop being viable.
-/
def Viable (version : Version) (fed : Chars) : Prop :=
  ∃ rest tokens, Tokenization version (fed ++ rest) tokens

/--
Property: the tokens begin every tokenisation of every input that begins with the characters
fed so far.

This is used to state what a lexer fed an input in slices may hand over: `StreamingCorrect`
requires it to hand over tokens determined by the characters fed, as no later character can
change them. After `(a 12`, the tokens `(` and `a` are determined, but `12` is not, as `123`
or `12.5` may follow.
-/
def Determined (version : Version) (fed : Chars) (tokens : List Token) : Prop :=
  ∀ rest tokens', Tokenization version (fed ++ rest) tokens' → tokens <+: tokens'

end BSmtLib.Spec.Lexicon
