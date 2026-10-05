import BSmtLib.SpecChecks.RoundTrip.Tokens
import BSmtLib.SpecChecks.RoundTrip.Lexical
import BSmtLib.SpecChecks.RoundTrip.Trees
import BSmtLib.SpecChecks.RoundTrip.Scripts

/-!
# Printing and reading back

Printers that go back the way the specification reads:

- `RoundTrip.Tokens`: from lexicon tokens to characters, the concrete printer, which writes an
  input back exactly, and the canonical layout.
- `RoundTrip.Trees`: from syntax trees to syntax tokens, for every category of the grammar.
- `RoundTrip.Lexical`: from syntax tokens to lexicon tokens, in a version.
- `RoundTrip.Scripts`: from the commands of a script to characters, each command in the
  version in force at it.

Reading what a printer writes gives back what it was printed from, for everything the
specification can read.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Lexicon

open BSmtLib.Spec BSmtLib.Spec.Lexicon

/-! ## Examples -/

/-- The token of the category with the characters of `s`, at the offset. -/
abbrev tok (category : Category) (offset : Nat) (s : String) : Token := ⟨category, offset, chars s⟩

/-- The tokens of `(f x ;c` and a line feed, then ` 1)`. -/
abbrev exampleTokens : List Token :=
  [tok .parenOpen 0 "(", tok .simpleSymbol 1 "f", tok .simpleSymbol 3 "x", tok .numeral 9 "1",
    tok .parenClose 10 ")"]

/-- The concrete printer keeps the comment and the line feed. -/
example : printConcrete (readConcrete (chars "(f x ;c\n 1)") exampleTokens) =
    chars "(f x ;c\n 1)" := by decide

/-- The gaps the concrete reading finds. -/
example : (readConcrete (chars "(f x ;c\n 1)") exampleTokens).pieces.map Prod.fst =
    [[], [], chars " ", chars " ;c\n ", []] := by decide

/-- The canonical layout drops them. -/
example : layout exampleTokens = chars "(f x 1)" := by decide

/-- Between `)` and `(` the layout writes a space. -/
example : layout [tok .parenOpen 0 "(", tok .simpleSymbol 0 "f", tok .parenOpen 0 "(",
    tok .simpleSymbol 0 "g", tok .simpleSymbol 0 "a", tok .parenClose 0 ")",
    tok .parenOpen 0 "(", tok .simpleSymbol 0 "h", tok .simpleSymbol 0 "b",
    tok .parenClose 0 ")", tok .parenClose 0 ")"] = chars "(f (g a) (h b))" := by decide

end BSmtLib.SpecChecks.Lexicon
