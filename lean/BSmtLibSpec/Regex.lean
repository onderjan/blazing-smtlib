module

@[expose] public section

/-!
# Regular expressions

The formalism the lexicon is written in. A regular expression is given directly by the
character sequences it matches: each combinator is defined in one line, and that definition
is all there is to its meaning.

The standard counts characters in an 8-bit encoding, with codes from 0 to 255, so a
character is a byte.
-/

namespace BSmtLibSpec

/-- A sequence of characters. -/
abbrev Regex.Chars := List UInt8

/-- The characters of an ASCII string. Only ASCII strings are used. -/
def Regex.chars (s : String) : Chars := s.toList.map Char.toUInt8

/-- A regular expression: the set of character sequences it matches. -/
def Regex := Regex.Chars → Prop

namespace Regex

/-- One character with a code from `lo` to `hi`. -/
def range (lo hi : Nat) : Regex := fun x => ∃ c, x = [c] ∧ lo ≤ c.toNat ∧ c.toNat ≤ hi

/-- One character with the code `n`. -/
def code (n : Nat) : Regex := range n n

/-- Any one character. -/
def anyChar : Regex := range 0 255

/-- One of the characters of the string `s`. -/
def oneOf (s : String) : Regex := fun x => ∃ c ∈ chars s, x = [c]

/-- Exactly the characters of the string `s`. -/
def lit (s : String) : Regex := fun x => x = chars s

/-- Exactly the characters of one of the strings `ws`. -/
def litOneOf (ws : List String) : Regex := fun x => ∃ w ∈ ws, x = chars w

/-- Anything, including nothing. -/
def anything : Regex := fun _ => True

/-- What `r` matches followed by what `q` matches. -/
def seq (r q : Regex) : Regex := fun x => ∃ a b, x = a ++ b ∧ r a ∧ q b

/-- What `r` or `q` matches. -/
def alt (r q : Regex) : Regex := fun x => r x ∨ q x

/-- What one of `rs` matches. -/
def altAll (rs : List Regex) : Regex := fun x => ∃ r ∈ rs, r x

/-- A sequence of zero or more parts, each matched by `r`. -/
def star (r : Regex) : Regex := fun x => ∃ parts : List Chars, x = parts.flatten ∧ ∀ p ∈ parts, r p

/-- A sequence of one or more parts, each matched by `r`. -/
def plus (r : Regex) : Regex := seq r (star r)

/-- What `r` matches, except what `q` matches. -/
def minus (r q : Regex) : Regex := fun x => r x ∧ ¬ q x

/-- A sequence starting with what `r` matches. -/
def startsWith (r : Regex) : Regex := seq r anything

end Regex

end BSmtLibSpec
