import BSmtLib.SpecChecks.Lemmas
import BSmtLib.SpecChecks.Examples
import BSmtLib.SpecChecks.Reserved
import BSmtLib.SpecChecks.Grammar
import BSmtLib.SpecChecks.Unique
import BSmtLib.SpecChecks.Streaming
import BSmtLib.SpecChecks.StreamingFacts
import BSmtLib.SpecChecks.Grammar.Unique
import BSmtLib.SpecChecks.RoundTrip

/-!
# Checks of the specification

Proofs that the specification means what it says on the standard's own examples and lists,
and that every input has at most one tokenisation, with examples of what a lexer fed in slices
hands over; that what the properties of a lexer fed in slices ask for exists, and that a lexer
that has them hands over more as it is fed more; and that the grammar is unambiguous: every
sequence of tokens of a term or of a command has at most one syntax tree, and every script has
at most one parse; and that the tokens of an input can be printed back, exactly with the
whitespace and comments between them and in a canonical layout without them, and are read back
from what is printed; and that the syntax trees of terms and commands are printed as the tokens
they are read from, that the commands of a script are printed as characters that are read back
as them, and that these are the script's tokens in the canonical layout unless a 2.0 string
literal has a backslash that does not start `\\` or `\"`.
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
start of the input; both exist and are unique, so it is not vacuous. `Spec.Lexer.Sequential` is not a part of
`Spec.Lexer.Correct`, as it follows from `Spec.Lexer.StreamingInputCorrect`.
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

/-- The rules leave at most one syntax tree for every sequence of tokens of a term. -/
theorem Grammar.termsUnique : Grammar.TermsUnique :=
  fun _ _ _ _ h₁ h₂ => Grammar.Term.unique h₁ h₂ rfl

/--
info: 'BSmtLib.SpecChecks.Grammar.termsUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.termsUnique

/-- The rules leave at most one syntax tree for every sequence of tokens of a command. -/
theorem Grammar.commandsUnique : Grammar.CommandsUnique :=
  fun _ _ _ _ h₁ h₂ => Grammar.Command.unique h₁ h₂ rfl

/--
info: 'BSmtLib.SpecChecks.Grammar.commandsUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.commandsUnique

/-- Every script has at most one parse. -/
theorem Grammar.scriptsUnique : Grammar.ScriptsUnique :=
  fun _ _ _ _ h₁ h₂ => Grammar.scriptParseFrom_unique h₁ h₂

/--
info: 'BSmtLib.SpecChecks.Grammar.scriptsUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.scriptsUnique


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


/-!
### Round trips of syntax trees

`Grammar.printTerm` and `Grammar.printCommand` write a tree as syntax tokens, each symbol in the
form it records. `Grammar.printScript version` writes the commands of a script as characters:
each command's tokens in the version in force at it, laid out by `Lexicon.layout`, and followed
by a line feed. `Grammar.ScriptLexing` is the parse of a script together with the tokens of each
command and the version they are read in.
-/

/-- The grammar loses nothing: the tokens a term is read from are the tokens printed for it. -/
theorem Grammar.printTerm_eq {version : Lexicon.Version} {tokens : List Grammar.SyntaxToken}
    {term : Grammar.Tree.Term} (h : Grammar.Term version tokens term) :
    Grammar.printTerm term = tokens :=
  (Grammar.term_tokens h).symm

/--
info: 'BSmtLib.SpecChecks.Grammar.printTerm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.printTerm_eq

/-- The grammar loses nothing: the tokens a command is read from are the tokens printed for
it. -/
theorem Grammar.printCommand_eq {version : Lexicon.Version} {tokens : List Grammar.SyntaxToken}
    {command : Grammar.Tree.Command} (h : Grammar.Command version tokens command) :
    Grammar.printCommand command = tokens :=
  (Grammar.command_tokens h).symm

/--
info: 'BSmtLib.SpecChecks.Grammar.printCommand_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.printCommand_eq

/-- Print-read for terms: a term that some tokens are read as is read from its printed tokens,
and from them as nothing else. -/
theorem Grammar.term_print_read {version : Lexicon.Version} {tokens : List Grammar.SyntaxToken}
    {term term' : Grammar.Tree.Term} (h : Grammar.Term version tokens term) :
    Grammar.Term version (Grammar.printTerm term) term' ↔ term' = term := by
  rw [Grammar.printTerm_eq h]
  exact ⟨fun h' => Grammar.termsUnique _ _ _ _ h' h, fun e => e ▸ h⟩

/--
info: 'BSmtLib.SpecChecks.Grammar.term_print_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.term_print_read

/-- Idempotence for terms: printing the term read from printed tokens gives those tokens. -/
theorem Grammar.term_idempotent {version : Lexicon.Version} {term term' : Grammar.Tree.Term}
    (h : Grammar.Term version (Grammar.printTerm term) term') :
    Grammar.printTerm term' = Grammar.printTerm term :=
  Grammar.printTerm_eq h

/--
info: 'BSmtLib.SpecChecks.Grammar.term_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.term_idempotent

/-- Print-read for commands: a command that some tokens are read as is read from its printed
tokens, and from them as nothing else. -/
theorem Grammar.command_print_read {version : Lexicon.Version}
    {tokens : List Grammar.SyntaxToken} {command command' : Grammar.Tree.Command}
    (h : Grammar.Command version tokens command) :
    Grammar.Command version (Grammar.printCommand command) command' ↔ command' = command := by
  rw [Grammar.printCommand_eq h]
  exact ⟨fun h' => Grammar.commandsUnique _ _ _ _ h' h, fun e => e ▸ h⟩

/--
info: 'BSmtLib.SpecChecks.Grammar.command_print_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.command_print_read

/-- Idempotence for commands: printing the command read from printed tokens gives those
tokens. -/
theorem Grammar.command_idempotent {version : Lexicon.Version}
    {command command' : Grammar.Tree.Command}
    (h : Grammar.Command version (Grammar.printCommand command) command') :
    Grammar.printCommand command' = Grammar.printCommand command :=
  Grammar.printCommand_eq h

/--
info: 'BSmtLib.SpecChecks.Grammar.command_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.command_idempotent

/-- Idempotence for a command as characters: the characters printed for a command read from the
tokens of an input are read as a command whose characters are the same. -/
theorem Grammar.commandText_idempotent {version : Lexicon.Version} {input : Lexicon.Chars}
    {tokens tokens' : List Lexicon.Token} {command command' : Grammar.Tree.Command}
    (h : Lexicon.Tokenization version input tokens)
    (hc : Grammar.Command version (tokens.map (Grammar.SyntaxToken.ofToken version)) command)
    (h' : Lexicon.Tokenization version (Grammar.printCommandText version command) tokens')
    (hc' : Grammar.Command version (tokens'.map (Grammar.SyntaxToken.ofToken version)) command') :
    Grammar.printCommandText version command' = Grammar.printCommandText version command :=
  Grammar.printCommandText_idempotent h hc h' hc'

/--
info: 'BSmtLib.SpecChecks.Grammar.commandText_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.commandText_idempotent

/-- Print-read for scripts: the commands of a script are the parse of their printed characters,
and the only one. -/
theorem Grammar.script_print_read {version : Lexicon.Version} {input : Lexicon.Chars}
    {commands commands' : List Grammar.Tree.Command}
    (h : Grammar.ScriptParse version input commands) :
    Grammar.ScriptParse version (Grammar.printScript version commands) commands' ↔
      commands' = commands := by
  have hp : Grammar.ScriptParse version (Grammar.printScript version commands) commands := by
    simpa [Grammar.ScriptParse] using Grammar.printScript_read h 0 Lexicon.whitespace_nil
  exact ⟨fun h' => Grammar.scriptsUnique _ _ _ _ h' hp, fun e => e ▸ hp⟩

/--
info: 'BSmtLib.SpecChecks.Grammar.script_print_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.script_print_read

/-- Idempotence for scripts: printing a script that was read, reading the printed characters and
printing again gives the same characters. -/
theorem Grammar.script_idempotent {version : Lexicon.Version} {input : Lexicon.Chars}
    {commands commands' : List Grammar.Tree.Command}
    (h : Grammar.ScriptParse version input commands)
    (h' : Grammar.ScriptParse version (Grammar.printScript version commands) commands') :
    Grammar.printScript version commands' = Grammar.printScript version commands := by
  rw [(Grammar.script_print_read h).mp h']

/--
info: 'BSmtLib.SpecChecks.Grammar.script_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.script_idempotent

/-- A script parse records the tokens of its commands: it is the same as a parse. -/
theorem Grammar.scriptParse_iff_lexing {version : Lexicon.Version} {input : Lexicon.Chars}
    {commands : List Grammar.Tree.Command} :
    Grammar.ScriptParse version input commands ↔
      ∃ segments, Grammar.ScriptLexing version 0 input commands segments :=
  Grammar.scriptParseFrom_iff

/--
info: 'BSmtLib.SpecChecks.Grammar.scriptParse_iff_lexing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.scriptParse_iff_lexing

/--
Read-print for scripts: the characters printed for the commands of a script are the tokens of
its commands laid out canonically, each command followed by a line feed, unless a 2.0 string
literal among them has a backslash that does not start `\\` or `\"`.
-/
theorem Grammar.script_read_print {version : Lexicon.Version} {input : Lexicon.Chars}
    {commands : List Grammar.Tree.Command} {segments : List (Lexicon.Version × List Lexicon.Token)}
    (h : Grammar.ScriptLexing version 0 input commands segments)
    (hl : Grammar.NoLoneBackslashIn segments) :
    Grammar.printScript version commands = Grammar.layoutScript segments :=
  Grammar.printScript_layout h hl

/--
info: 'BSmtLib.SpecChecks.Grammar.script_read_print' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.script_read_print

end BSmtLib.SpecChecks
