module

public import BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Lexical

@[expose] public section

/-!
# Printing and reading back

Printers that go back the way the specification formalism (`BSmtLibSpec`) reads:

- `RoundTrip.Tokens`: from lexicon tokens to characters, the concrete printer, which writes an
  input back exactly, and the canonical layout.
- `RoundTrip.Lexical`: from syntax tokens to lexicon tokens, in a version.

Reading what a printer writes gives back what it was printed from, for everything the
formalism can read.

Not trusted: everything here is proved.
-/

namespace BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip

open BSmtLibSpec.Lexicon
open BSmtLibSpec.Regex (chars)

/-! ## Examples -/

/-- The token of the category with the characters of `s`, at the offset. -/
abbrev tok (category : Category) (offset : Nat) (s : String) : Token := ⟨category, offset, chars s⟩

/-- The tokens of `(f x ;c` and a line feed, then ` 1)`. -/
abbrev exampleTokens : List Token :=
  [tok .parenOpen 0 "(", tok .simpleSymbol 1 "f", tok .simpleSymbol 3 "x", tok .numeral 9 "1",
    tok .parenClose 10 ")"]

/-- The concrete printer keeps the comment and the line feed. -/
example : Facts.Proofs.Lexicon.RoundTrip.Tokens.printConcrete
    (Facts.Proofs.Lexicon.RoundTrip.Tokens.readConcrete
    (chars "(f x ;c\n 1)") Facts.Proofs.Lexicon.RoundTrip.exampleTokens) =
    chars "(f x ;c\n 1)" := by decide

/-- The gaps the concrete reading finds. -/
example : (Facts.Proofs.Lexicon.RoundTrip.Tokens.readConcrete
    (chars "(f x ;c\n 1)") Facts.Proofs.Lexicon.RoundTrip.exampleTokens).pieces.map Prod.fst =
    [[], [], chars " ", chars " ;c\n ", []] := by decide

/-- The canonical layout drops them. -/
example : Facts.Proofs.Lexicon.RoundTrip.Tokens.layout Facts.Proofs.Lexicon.RoundTrip.exampleTokens
    = chars "(f x 1)\n" := by decide

/-- Between `)` and `(` the layout writes a space. -/
example : Facts.Proofs.Lexicon.RoundTrip.Tokens.layout [Facts.Proofs.Lexicon.RoundTrip.tok
    .parenOpen 0 "(", Facts.Proofs.Lexicon.RoundTrip.tok .simpleSymbol 0 "f",
        Facts.Proofs.Lexicon.RoundTrip.tok .parenOpen 0 "(",
    Facts.Proofs.Lexicon.RoundTrip.tok .simpleSymbol 0 "g", Facts.Proofs.Lexicon.RoundTrip.tok
        .simpleSymbol 0 "a", Facts.Proofs.Lexicon.RoundTrip.tok .parenClose 0 ")",
    Facts.Proofs.Lexicon.RoundTrip.tok .parenOpen 0 "(", Facts.Proofs.Lexicon.RoundTrip.tok
        .simpleSymbol 0 "h", Facts.Proofs.Lexicon.RoundTrip.tok .simpleSymbol 0 "b",
    Facts.Proofs.Lexicon.RoundTrip.tok .parenClose 0 ")", Facts.Proofs.Lexicon.RoundTrip.tok
        .parenClose 0 ")"] = chars "(f (g a) (h b))\n" := by decide

/-- After each top-level item the layout writes a line feed: after the `)` that closes every
open parenthesis, after a token outside parentheses, and after a `)` that closes none. -/
example : Facts.Proofs.Lexicon.RoundTrip.Tokens.layout [Facts.Proofs.Lexicon.RoundTrip.tok
    .parenClose 0 ")", Facts.Proofs.Lexicon.RoundTrip.tok .simpleSymbol 0 "x",
    Facts.Proofs.Lexicon.RoundTrip.tok .parenOpen 0 "(", Facts.Proofs.Lexicon.RoundTrip.tok
        .simpleSymbol 0 "f", Facts.Proofs.Lexicon.RoundTrip.tok .parenClose 0 ")",
    Facts.Proofs.Lexicon.RoundTrip.tok .numeral 0 "42"] = chars ")\nx\n(f)\n42\n" := by decide

/-- The layout ends with a line feed also where parentheses are left open, and writes nothing
for no tokens. -/
example : Facts.Proofs.Lexicon.RoundTrip.Tokens.layout [Facts.Proofs.Lexicon.RoundTrip.tok
    .parenOpen 0 "(", Facts.Proofs.Lexicon.RoundTrip.tok .simpleSymbol 0 "a",
    Facts.Proofs.Lexicon.RoundTrip.tok .parenOpen 0 "(", Facts.Proofs.Lexicon.RoundTrip.tok
        .simpleSymbol 0 "b"] = chars "(a (b\n" ∧
    Facts.Proofs.Lexicon.RoundTrip.Tokens.layout [] = [] := by decide

end BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip
