import BSmtLib.SpecChecks.Lemmas
import BSmtLib.SpecChecks.Examples
import BSmtLib.SpecChecks.Reserved
import BSmtLib.SpecChecks.Unique
import BSmtLib.SpecChecks.Streaming
import BSmtLib.SpecChecks.StreamingFacts
import BSmtLib.SpecChecks.RoundTrip

/-!
# Checks of the specification

Proofs that the specification means what it says on the standard's own examples and lists,
and that every input has at most one tokenisation, with examples of what a lexer fed in slices
hands over; that what the properties of a lexer fed in slices ask for exists, and that a lexer
that has them hands over more as it is fed more; and that the tokens of an input can be printed
back, exactly with the whitespace and comments between them and in a canonical layout without
them, and are read back from what is printed.
They are not part of the specification and are not trusted.
-/

/-!
## What holds

Each theorem below proves a property of the specification, from the modules imported above.
Each is followed by the axioms its proof uses: only those of Lean's standard library, no
`sorry` and no axiom of its own. The build fails if that changes.
-/

namespace BSmtLib.SpecChecks

open BSmtLib.Spec

/-- Every input has at most one tokenisation. -/
theorem Lexicon.unique : Lexicon.Unique :=
  fun _ _ _ _ h₁ h₂ => Lexicon.tokenizationFrom_unique h₁ h₂

/--
info: 'BSmtLib.SpecChecks.Lexicon.unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.unique

/-!
### A lexer fed in slices

`Spec.Lexer.HandsOverCorrectly` asks for the tokens maximal to hand over on the longest viable
start of the input; both exist and are unique, so it is not vacuous. `Spec.Lexer.Sequential`
is not a part of `Spec.Lexer.Correct`, as it follows from `Spec.Lexer.StreamingInputCorrect`.
-/

/-- Every input has exactly one longest viable start. -/
theorem Lexer.longestViableStart_existsUnique (version : Lexicon.Version)
    (input : Lexicon.Chars) :
    ∃ start, Spec.Lexer.LongestViableStart version input start ∧
      ∀ start', Spec.Lexer.LongestViableStart version input start' → start' = start :=
  let ⟨start, h⟩ := Lexer.exists_longestViableStart version input
  ⟨start, h, fun _ h' => Lexer.longestViableStart_unique h' h⟩

/--
info: 'BSmtLib.SpecChecks.Lexer.longestViableStart_existsUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.longestViableStart_existsUnique

/-- On a viable input, exactly one list of tokens is maximal to hand over. -/
theorem Lexer.handoverMaximal_existsUnique {version : Lexicon.Version}
    {input : Lexicon.Chars} (h : Lexicon.Viable version input) :
    ∃ tokens, Spec.Lexer.HandoverMaximal version input tokens ∧
      ∀ tokens', Spec.Lexer.HandoverMaximal version input tokens' → tokens' = tokens :=
  let ⟨tokens, ht⟩ := Lexer.exists_handoverMaximal h
  ⟨tokens, ht, fun _ h' => Lexer.handoverMaximal_unique h h' ht⟩

/--
info: 'BSmtLib.SpecChecks.Lexer.handoverMaximal_existsUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.handoverMaximal_existsUnique

/-- A lexer that is `StreamingInputCorrect` on every version, slices and start is
`Sequential`: fed more slices, it has handed over what it had and possibly more, and once it
has failed, it stays failed. -/
theorem Lexer.sequential {feed : Lexicon.Version → List Lexicon.Chars → Spec.Lexer.Fed}
    (h : ∀ version slices start, Spec.Lexer.StreamingInputCorrect feed version slices start) :
    ∀ version slices more, Spec.Lexer.Sequential feed version slices more :=
  Lexer.sequential_of_streamingInputCorrect h

/--
info: 'BSmtLib.SpecChecks.Lexer.sequential' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.sequential


/-!
### Round trips

`Lexicon.readConcrete input tokens` is the concrete reading of an input: its tokens with the
whitespace and comments between them, and `Lexicon.printConcrete` writes it back. The canonical
layout `Lexicon.layout` writes tokens with a single space between two of them, except after `(`
and before `)`; `Lexicon.place` gives the offsets at which it puts them.
-/

/-- The concrete printer writes the input of a tokenisation back exactly. -/
theorem Lexicon.concrete_print_read {version : Lexicon.Version} {input : Lexicon.Chars}
    {tokens : List Lexicon.Token} (h : Lexicon.Tokenization version input tokens) :
    Lexicon.printConcrete (Lexicon.readConcrete input tokens) = input :=
  Lexicon.printConcrete_readConcreteFrom h

/--
info: 'BSmtLib.SpecChecks.Lexicon.concrete_print_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.concrete_print_read

/-- The tokens of a concrete reading are the tokens it was read with. -/
theorem Lexicon.concrete_tokens (input : Lexicon.Chars) (tokens : List Lexicon.Token) :
    (Lexicon.readConcrete input tokens).tokens = tokens :=
  Lexicon.readConcreteFrom_tokens 0 input tokens

/--
info: 'BSmtLib.SpecChecks.Lexicon.concrete_tokens' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Lexicon.concrete_tokens

/--
The concrete printing of the concrete reading of an input has the tokens of the reading as its
tokenisation, and no other.
-/
theorem Lexicon.concrete_read {version : Lexicon.Version} {input : Lexicon.Chars}
    {tokens tokens' : List Lexicon.Token} (h : Lexicon.Tokenization version input tokens) :
    Lexicon.Tokenization version (Lexicon.printConcrete (Lexicon.readConcrete input tokens))
      tokens' ↔ tokens' = (Lexicon.readConcrete input tokens).tokens := by
  rw [Lexicon.concrete_print_read h, Lexicon.concrete_tokens]
  exact ⟨fun h' => Lexicon.unique _ _ _ _ h' h, fun e => e ▸ h⟩

/--
info: 'BSmtLib.SpecChecks.Lexicon.concrete_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.concrete_read

/--
The gaps of the concrete reading of a tokenisation are whitespace, and the last one is
whitespace at the end of the input.
-/
theorem Lexicon.concrete_gaps {version : Lexicon.Version} {input : Lexicon.Chars}
    {tokens : List Lexicon.Token} (h : Lexicon.Tokenization version input tokens) :
    (∀ piece ∈ (Lexicon.readConcrete input tokens).pieces, Lexicon.whitespace piece.1) ∧
      Lexicon.whitespaceAtEnd (Lexicon.readConcrete input tokens).final :=
  Lexicon.readConcreteFrom_gaps h

/--
info: 'BSmtLib.SpecChecks.Lexicon.concrete_gaps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.concrete_gaps

/--
Print-read for the canonical layout: the tokens of an input are the tokenisation of their
layout, with the same categories and characters, at the offsets at which the layout puts them.
-/
theorem Lexicon.layout_read {version : Lexicon.Version} {input : Lexicon.Chars}
    {tokens : List Lexicon.Token} (h : Lexicon.Tokenization version input tokens) :
    Lexicon.Tokenization version (Lexicon.layout tokens) (Lexicon.place tokens) :=
  Lexicon.layout_tokenization (Lexicon.tokenizationFrom_regex h)

/--
info: 'BSmtLib.SpecChecks.Lexicon.layout_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.layout_read

/-- The tokens as laid out keep their categories and characters: only their offsets change. -/
theorem Lexicon.place_keeps (tokens : List Lexicon.Token) :
    (Lexicon.place tokens).map Lexicon.form = tokens.map Lexicon.form :=
  Lexicon.place_form tokens

/--
info: 'BSmtLib.SpecChecks.Lexicon.place_keeps' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Lexicon.place_keeps

/--
Print-read for the canonical layout, completed by `Lexicon.unique`: the layout of the tokens of
an input has no other tokenisation.
-/
theorem Lexicon.layout_read_only {version : Lexicon.Version} {input : Lexicon.Chars}
    {tokens tokens' : List Lexicon.Token} (h : Lexicon.Tokenization version input tokens) :
    Lexicon.Tokenization version (Lexicon.layout tokens) tokens' ↔
      tokens' = Lexicon.place tokens :=
  ⟨fun h' => Lexicon.unique _ _ _ _ h' (Lexicon.layout_read h),
    fun e => e ▸ Lexicon.layout_read h⟩

/--
info: 'BSmtLib.SpecChecks.Lexicon.layout_read_only' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.layout_read_only

end BSmtLib.SpecChecks
