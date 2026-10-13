import BSmtLib.SpecChecks.Lemmas

/-!
# The standard's examples

The examples the standard gives with its lexical rules, checked against the spec. Not
trusted: these are proofs.
-/

namespace BSmtLib.SpecChecks.Lexicon

open BSmtLibSpec BSmtLibSpec.Lexicon BSmtLibSpec.Regex
open BSmtLibSpec.Lexicon.Properties
open BSmtLibSpec.Regex (Chars chars)

/-! ## Hexadecimals and binaries -/

example : hexadecimal (chars "#x01Ab") :=
  seq_intro (a := chars "#x") rfl (plus_each (by simp [altAll, digit, range_one]; decide)
    (by simp [altAll, digit, range_one]; decide))

example : binary (chars "#b101011") :=
  seq_intro (a := chars "#b") rfl (plus_each (by simp [oneOf_one]; decide)
    (by simp [oneOf_one]; decide))

/-! ## Numerals and decimals -/

example : numeral (chars "0") := Or.inl rfl

example : ¬ numeral (chars "01") := by
  rintro (h | ⟨-, h⟩)
  · simp [lit_iff, chars] at h
  · exact h ((startsWith_lit_one "0" rfl).mpr rfl)

/-! ## Simple symbols, reserved words and keywords -/

example : simpleSymbol .v2_7 (chars "<adf>") :=
  simpleSymbol_of (by simp [simpleSymbolChar_one]; decide) (by decide) (by decide)

example : simpleSymbol .v2_7 (chars "*$s&6") :=
  simpleSymbol_of (by simp [simpleSymbolChar_one]; decide) (by decide) (by decide)

example : simpleSymbol .v2_7 (chars ".8") :=
  simpleSymbol_of (by simp [simpleSymbolChar_one]; decide) (by decide) (by decide)

/-- `assert` is a reserved word, so not a simple symbol. -/
example : ¬ simpleSymbol .v2_7 (chars "assert") := fun h =>
  h.2 (litOneOf_iff.mpr (by decide))

/-- `lambda` is a simple symbol in 2.6 and a reserved word in 2.7. -/
example : simpleSymbol .v2_6 (chars "lambda") ∧ reserved .v2_7 (chars "lambda") :=
  ⟨simpleSymbol_of (by simp [simpleSymbolChar_one]; decide) (by decide) (by decide),
    litOneOf_iff.mpr (by decide)⟩

example : keyword (chars ":foo-bar") :=
  seq_intro (a := chars ":") rfl
    (plus_each (by simp [simpleSymbolChar_one]; decide) (by simp [simpleSymbolChar_one]; decide))

/-- `:56`, one of the standard's examples, is a keyword. -/
example : keyword (chars ":56") :=
  seq_intro (a := chars ":") rfl
    (plus_each (by simp [simpleSymbolChar_one]; decide) (by simp [simpleSymbolChar_one]; decide))

/-- `:assert` is a keyword, although `assert` is a reserved word. -/
example : keyword (chars ":assert") :=
  seq_intro (a := chars ":") rfl
    (plus_each (by simp [simpleSymbolChar_one]; decide) (by simp [simpleSymbolChar_one]; decide))

/-- `:` alone is not a keyword. -/
example : ¬ keyword (chars ":") := by
  rintro ⟨a, b, h, rfl, ⟨c, rest, hb, hc, -⟩⟩
  have hb0 : b = [] := by simpa [chars] using h.symm
  subst hb0
  obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp hb.symm
  obtain ⟨r, hr, hrc⟩ := hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    simp [letter, digit, symbolPunctuation, alt, range, oneOf] at hrc

/-! ## Quoted symbols and string literals -/

example : quotedSymbol (chars "| \" can occur too|") :=
  seq_intro (a := chars "|") rfl (seq_intro (a := chars " \" can occur too") (b := chars "|")
    (star_each (by simp [minus, spaceOrPrintable_one, printableOrSpace_one, oneOf_one]; decide))
    rfl)

example : quotedSymbol (chars "||") :=
  seq_intro (a := chars "|") rfl (seq_intro (a := []) (star_each (by simp)) rfl)

/-- The body of a string literal, split into single characters and `""`. -/
def stringParts : Chars → List Chars
  | 34 :: 34 :: rest => [34, 34] :: stringParts rest
  | c :: rest => [c] :: stringParts rest
  | [] => []

example : string (chars "\"She said: \"\"Bye bye\"\" and left.\"") := by
  have hall : ∀ p ∈ stringParts (chars "She said: \"\"Bye bye\"\" and left."),
      stringPartOk p = true := by decide
  have hflat : (stringParts (chars "She said: \"\"Bye bye\"\" and left.")).flatten =
      chars "She said: \"\"Bye bye\"\" and left." := by decide
  have body := star_parts _ fun p hp => stringPart_of_ok (hall p hp)
  rw [hflat] at body
  rw [show chars "\"She said: \"\"Bye bye\"\" and left.\"" =
    chars "\"" ++ (chars "She said: \"\"Bye bye\"\" and left." ++ chars "\"") by decide]
  exact seq_intro rfl (seq_intro body rfl)

example : unescape (chars "She said: \"\"Bye bye\"\" and left.") =
    chars "She said: \"Bye bye\" and left." := by
  decide

/-! ## Tokenising a whole input -/

example : Tokenization .v2_7 (chars "(assert x)")
    [⟨.parenOpen, 0, chars "("⟩, ⟨.reserved, 1, chars "assert"⟩,
      ⟨.simpleSymbol, 8, chars "x"⟩, ⟨.parenClose, 9, chars ")"⟩] := by
  apply Tokenization.From.token (category := .parenOpen) (w := []) (s := chars "(")
    (rest := chars "assert x)") whitespace_nil rfl (Or.inl rfl)
  apply Tokenization.From.token (category := .reserved) (w := []) (s := chars "assert")
    (rest := chars " x)") whitespace_nil (litOneOf_iff.mpr (by decide))
    (delimited_by (Or.inl (whiteSpaceChar_one.mpr (by decide))))
  apply Tokenization.From.token (category := .simpleSymbol) (w := chars " ") (s := chars "x")
    (rest := chars ")") (whitespace_spaces (by decide))
    (simpleSymbol_of (by simp [simpleSymbolChar_one]; decide) (by decide) (by decide))
    (delimited_by (Or.inr (oneOf_one.mpr (by decide))))
  apply Tokenization.From.token (category := .parenClose) (w := []) (s := chars ")") (rest := [])
    whitespace_nil rfl (Or.inr (Or.inl rfl))
  exact Tokenization.From.done ⟨[], [], rfl, whitespace_nil, Or.inl rfl⟩

/-- A comment that runs to the end of the input, without a line feed, has a tokenisation. -/
example : Tokenization .v2_7 (chars ";c") [] :=
  Tokenization.From.done ⟨[], chars ";c", rfl, whitespace_nil,
    Or.inr (seq_intro (a := chars ";") rfl (star_each (by
      simp [minus, anyChar, lineBreak, alt, code, range_one]; decide)))⟩

/-- A tab is allowed in a 2.0 string literal. -/
example : Tokenization .v2_0 (chars "\"a\tb\"") [⟨.string, 0, chars "\"a\tb\""⟩] := by
  apply Tokenization.From.token (category := .string) (w := []) (s := chars "\"a\tb\"") (rest := [])
    whitespace_nil ?_ (Or.inr (Or.inr (Or.inl rfl)))
  · exact Tokenization.From.done ⟨[], [], rfl, whitespace_nil, Or.inl rfl⟩
  · show string20 (chars "\"" ++ (chars "a\tb" ++ chars "\""))
    refine seq_intro rfl (seq_intro (star_each fun c hc => Or.inl ⟨?_, ?_⟩) rfl)
    · simp [chars] at hc
      rcases hc with rfl | rfl | rfl <;> simp [printableOrSpace_one] <;> decide
    · simp [chars] at hc
      rcases hc with rfl | rfl | rfl <;> simp [oneOf_one, chars] <;> decide

/-- `"é"` in UTF-8, as bytes. -/
def stringE : Chars := [34, 195, 169, 34]

/-- Characters from 128 on are allowed in a 2.0 string literal. -/
example : Tokenization .v2_0 stringE [⟨.string, 0, stringE⟩] := by
  apply Tokenization.From.token (category := .string) (w := []) (s := stringE) (rest := [])
    whitespace_nil ?_ (Or.inr (Or.inr (Or.inl rfl)))
  · exact Tokenization.From.done ⟨[], [], rfl, whitespace_nil, Or.inl rfl⟩
  · show string20 (chars "\"" ++ ([195, 169] ++ chars "\""))
    refine seq_intro rfl (seq_intro (star_each fun c hc => Or.inl ⟨?_, ?_⟩) rfl)
    · simp at hc
      rcases hc with rfl | rfl <;> simp [printableOrSpace_one]
    · simp at hc
      rcases hc with rfl | rfl <;> simp [oneOf_one, chars] <;> decide

/-- The same input is not a 2.0 source file. -/
example : ¬ SourceFile .v2_0 stringE := fun h => absurd (h 195 (by decide)) (by decide)

end BSmtLib.SpecChecks.Lexicon
