module

public import BSmtLibSpec.Facts.Lexicon.Examples
public import BSmtLibSpec.Facts.Proofs.Lexicon.Reserved
public import BSmtLibSpec.Facts.Proofs.Lexicon.Unique
public import BSmtLibSpec.Facts.Proofs.Lexicon.Compose
public import BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip

@[expose] public section

/-!
# Facts about the lexicon

The lexicon: every input has at most one tokenisation. Composition: reading can stop at the `)`
of a command and start again on the rest, possibly in another version. Round trips: the tokens of
an input can be printed back, exactly with the whitespace and comments between them and in a
canonical layout without them, and are read back from what is printed. Reserved words: the
reserved words that each version adds make up the standard's full lists, each word once.

Each theorem below proves a property of the specification, from the modules imported above.
Each is followed by the axioms its proof uses: only those of Lean's standard library, no
`sorry` and no axiom of its own. The build fails if that changes.
-/

namespace BSmtLibSpec.Facts

/-- Every input has at most one tokenisation. -/
theorem Lexicon.unique : Lexicon.Properties.Unique :=
  fun _ _ _ _ h₁ h₂ => Proofs.Lexicon.Unique.tokenizationFrom_unique h₁ h₂

/--
info: 'BSmtLibSpec.Facts.Lexicon.unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.unique

/-!
### Composition at a closing parenthesis

A command ends with a `)`, which needs no delimiter. Characters whose tokenisation ends with a
`)` at their end are a point where reading can stop and start again, possibly in another
version: a lexer fed them has handed over all their tokens and holds nothing back, the
tokenisations of the characters followed by more are their tokens followed by those of the more
read on their own, and the more read on their own from any offset are the same tokens, moved.
-/

/-- Characters whose tokenisation ends with a `)` at their end are handed over whole, and the
characters followed by more are tokenised as the two parts read on their own. -/
theorem Lexicon.composeAtClose : BSmtLibSpec.Lexer.ComposesAtClose := by
  intro version start tokens h hclose
  have hclose' : Lexicon.EndsWithClose tokens (0 + start.length) := by simpa using hclose
  refine ⟨Proofs.Lexicon.Compose.close_handoverMaximal h hclose, fun more tokens' => ?_⟩
  rw [Lexicon.Tokenization, Proofs.Lexicon.Compose.tokenizationFrom_close_iff h hclose' more
      tokens']
  constructor
  · rintro ⟨others, rfl, ho⟩
    rw [Nat.zero_add, ← Nat.zero_add start.length] at ho
    obtain ⟨others₀, rfl, h₀⟩ := Proofs.Lexicon.Compose.tokenizationFrom_moveBy_inv ho
    exact ⟨others₀, rfl, h₀⟩
  · rintro ⟨others, rfl, ho⟩
    exact ⟨_, rfl, by simpa using Proofs.Lexicon.Compose.tokenizationFrom_moveBy ho start.length⟩

/--
info: 'BSmtLibSpec.Facts.Lexicon.composeAtClose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.composeAtClose

/-- Characters read from any offset, in any version, are tokenised as they are on their own,
moved to that offset. -/
theorem Lexicon.readOnItsOwn : Lexicon.Properties.ReadsOnItsOwn := by
  intro version offset input tokens
  constructor
  · intro h
    rw [← Nat.zero_add offset] at h
    exact Proofs.Lexicon.Compose.tokenizationFrom_moveBy_inv h
  · rintro ⟨tokens₀, rfl, h₀⟩
    simpa using Proofs.Lexicon.Compose.tokenizationFrom_moveBy h₀ offset

/--
info: 'BSmtLibSpec.Facts.Lexicon.readOnItsOwn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.readOnItsOwn

/-!
### Round trips

`Lexicon.readConcrete input tokens` is the concrete reading of an input: its tokens with the
whitespace and comments between them, and `Lexicon.printConcrete` writes it back. The canonical
layout `Lexicon.layout` writes tokens with a single space between two of them, except after `(`
and before `)`, and a line feed after each top-level item: after the `)` that closes every open
parenthesis, and after a token outside parentheses; `Lexicon.place` gives the offsets at which
it puts them.
-/

/-- The concrete printer writes the input of a tokenisation back exactly. -/
theorem Lexicon.concrete_print_read {version : Lexicon.Version} {input : Regex.Chars}
    {tokens : List Lexicon.Token} (h : Lexicon.Tokenization version input tokens) :
    Proofs.Lexicon.RoundTrip.Tokens.printConcrete (Proofs.Lexicon.RoundTrip.Tokens.readConcrete
        input tokens) = input :=
  Proofs.Lexicon.RoundTrip.Tokens.printConcrete_readConcreteFrom h

/--
info: 'BSmtLibSpec.Facts.Lexicon.concrete_print_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.concrete_print_read

/-- The tokens of a concrete reading are the tokens it was read with. -/
theorem Lexicon.concrete_tokens (input : Regex.Chars) (tokens : List Lexicon.Token) :
    (Proofs.Lexicon.RoundTrip.Tokens.readConcrete input tokens).tokens = tokens :=
  Proofs.Lexicon.RoundTrip.Tokens.readConcreteFrom_tokens 0 input tokens

/--
info: 'BSmtLibSpec.Facts.Lexicon.concrete_tokens' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Lexicon.concrete_tokens

/--
The concrete printing of the concrete reading of an input has the tokens of the reading as its
tokenisation, and no other.
-/
theorem Lexicon.concrete_read {version : Lexicon.Version} {input : Regex.Chars}
    {tokens tokens' : List Lexicon.Token} (h : Lexicon.Tokenization version input tokens) :
    Lexicon.Tokenization version (Proofs.Lexicon.RoundTrip.Tokens.printConcrete
        (Proofs.Lexicon.RoundTrip.Tokens.readConcrete input tokens))
      tokens' ↔ tokens' = (Proofs.Lexicon.RoundTrip.Tokens.readConcrete input tokens).tokens := by
  rw [Lexicon.concrete_print_read h, Lexicon.concrete_tokens]
  exact ⟨fun h' => Lexicon.unique _ _ _ _ h' h, fun e => e ▸ h⟩

/--
info: 'BSmtLibSpec.Facts.Lexicon.concrete_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.concrete_read

/--
The gaps of the concrete reading of a tokenisation are whitespace, and the last one is
whitespace at the end of the input.
-/
theorem Lexicon.concrete_gaps {version : Lexicon.Version} {input : Regex.Chars}
    {tokens : List Lexicon.Token} (h : Lexicon.Tokenization version input tokens) :
    (∀ piece ∈ (Proofs.Lexicon.RoundTrip.Tokens.readConcrete input tokens).pieces,
    Lexicon.whitespace piece.1) ∧
      Lexicon.whitespaceAtEnd (Proofs.Lexicon.RoundTrip.Tokens.readConcrete input tokens).final :=
  Proofs.Lexicon.RoundTrip.Tokens.readConcreteFrom_gaps h

/--
info: 'BSmtLibSpec.Facts.Lexicon.concrete_gaps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.concrete_gaps

/--
Print-read for the canonical layout: the tokens of an input are the tokenisation of their
layout, with the same categories and characters, at the offsets at which the layout puts them.
-/
theorem Lexicon.layout_read {version : Lexicon.Version} {input : Regex.Chars}
    {tokens : List Lexicon.Token} (h : Lexicon.Tokenization version input tokens) :
    Lexicon.Tokenization version (Proofs.Lexicon.RoundTrip.Tokens.layout tokens)
        (Proofs.Lexicon.RoundTrip.Tokens.place tokens) :=
  Proofs.Lexicon.RoundTrip.Tokens.layout_tokenization
      (Proofs.Lexicon.RoundTrip.Tokens.tokenizationFrom_regex h)

/--
info: 'BSmtLibSpec.Facts.Lexicon.layout_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.layout_read

/-- The tokens as laid out keep their categories and characters: only their offsets change. -/
theorem Lexicon.place_keeps (tokens : List Lexicon.Token) :
    (Proofs.Lexicon.RoundTrip.Tokens.place tokens).map Proofs.Lexicon.RoundTrip.Tokens.form =
    tokens.map Proofs.Lexicon.RoundTrip.Tokens.form :=
  Proofs.Lexicon.RoundTrip.Tokens.place_form tokens

/--
info: 'BSmtLibSpec.Facts.Lexicon.place_keeps' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Lexicon.place_keeps

/--
Print-read for the canonical layout, completed by `Lexicon.unique`: the layout of the tokens of
an input has no other tokenisation.
-/
theorem Lexicon.layout_read_only {version : Lexicon.Version} {input : Regex.Chars}
    {tokens tokens' : List Lexicon.Token} (h : Lexicon.Tokenization version input tokens) :
    Lexicon.Tokenization version (Proofs.Lexicon.RoundTrip.Tokens.layout tokens) tokens' ↔
      tokens' = Proofs.Lexicon.RoundTrip.Tokens.place tokens :=
  ⟨fun h' => Lexicon.unique _ _ _ _ h' (Lexicon.layout_read h),
    fun e => e ▸ Lexicon.layout_read h⟩

/--
info: 'BSmtLibSpec.Facts.Lexicon.layout_read_only' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.layout_read_only

/-!
### Reserved words

`Lexicon.basicReservedWords` and `Lexicon.commandNames` build the reserved words of each version
from what each version adds. The standard lists them in full for each version, and
`Proofs.Lexicon.Reserved` transcribes those lists a second time: `listedBasicReservedWords` and
`listedCommandNames`, the latter with `define-funs-rec` added from 2.5 on (Reading L6).
-/

/-- The basic set of reserved words of each version is, up to order, the one the version lists. -/
theorem Lexicon.basicReservedWords_listed (version : Lexicon.Version) :
    (Lexicon.basicReservedWords version).Perm
      (Proofs.Lexicon.Reserved.listedBasicReservedWords version) :=
  Proofs.Lexicon.Reserved.basicReservedWords_listed version

/--
info: 'BSmtLibSpec.Facts.Lexicon.basicReservedWords_listed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.basicReservedWords_listed

/-- The command names of each version are, up to order, the ones the version lists, with
`define-funs-rec` added from 2.5 on. -/
theorem Lexicon.commandNames_listed (version : Lexicon.Version) :
    (Lexicon.commandNames version).Perm (Proofs.Lexicon.Reserved.listedCommandNames version) :=
  Proofs.Lexicon.Reserved.commandNames_listed version

/--
info: 'BSmtLibSpec.Facts.Lexicon.commandNames_listed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.commandNames_listed

/-- No word that a version reserves is listed twice: neither within the basic set or the command
names, nor in both. -/
theorem Lexicon.reservedWords_nodup (version : Lexicon.Version) :
    (Lexicon.basicReservedWords version ++ Lexicon.commandNames version).Nodup :=
  Proofs.Lexicon.Reserved.reservedWords_nodup version

/--
info: 'BSmtLibSpec.Facts.Lexicon.reservedWords_nodup' does not depend on any axioms
-/
#guard_msgs in
#print axioms Lexicon.reservedWords_nodup

end BSmtLibSpec.Facts
