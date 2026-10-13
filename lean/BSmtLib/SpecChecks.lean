import BSmtLib.SpecChecks.Lemmas
import BSmtLib.SpecChecks.Examples
import BSmtLib.SpecChecks.Reserved
import BSmtLib.SpecChecks.Unique
import BSmtLib.SpecChecks.Streaming
import BSmtLib.SpecChecks.StreamingFacts
import BSmtLib.SpecChecks.RoundTrip
import BSmtLib.SpecChecks.Grammar.OneToOne
import BSmtLib.SpecChecks.Grammar.Files
import BSmtLib.SpecChecks.RoundTrip.Files
import BSmtLib.SpecChecks.Compose
import BSmtLib.SpecChecks.Consumers
import BSmtLib.SpecChecks.Grammar.Examples
import BSmtLib.SpecChecks.Parser.Bridge

/-!
# Checks of the specification

Proofs that the specification means what it says. They are not part of the specification and
are not trusted.

- Examples: the standard's own examples and lists, of the lexicon and of the grammar, what a
  lexer fed in slices hands over, and the calls the traversal makes for a few scripts.
- The lexicon: every input has at most one tokenisation.
- A lexer fed in slices: what its properties ask for exists, and a lexer that is correct hands
  over more as it is fed more or the end of the input, and is correct on whole inputs.
- Composition: reading can stop at the `)` of a command and start again on the rest, possibly
  in another version.
- A lexer and its consumers: what a lexer does with a consumer is determined, and the input
  after a switch of the version is located as in the whole input.
- Round trips: the tokens of an input can be printed back, exactly with the whitespace and
  comments between them and in a canonical layout without them, and are read back from what is
  printed.
- The grammar: the tokens of a tree determine the tree, and every file has at most one reading,
  from which it is reproduced.
- The traversal: it makes the calls of a parser that goes by the items it receives, its calls
  rebuild the script, and they are placed by the items before them, for every handler.
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

`Spec.Lexer.HandsOverMaximal` asks for the tokens maximal to hand over on the longest viable
start of the input; both exist and are unique, so it is not vacuous. `Spec.Lexer.Sequential`
and `Spec.Lexer.WholeInputCorrect` are not a part of `Spec.Lexer.Correct`, as they follow from
it, for every lexer.
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

/-- A lexer that is `Correct` is `Sequential`: fed more slices, or the end of the input, it has
handed over what it had and possibly more, and once it has failed, it stays failed. -/
theorem Lexer.sequential {feed : Lexicon.Version → List Lexicon.Chars → Bool → Spec.Lexer.Fed}
    (h : Spec.Lexer.Correct feed) :
    ∀ version slices more, Spec.Lexer.Sequential feed version slices more :=
  Lexer.sequential_of_correct h

/--
info: 'BSmtLib.SpecChecks.Lexer.sequential' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.sequential

/-- A lexer that is `Correct` is `WholeInputCorrect`: fed slices and then the end of the input,
it has not failed and has handed over the tokens of the tokenisation of the input followed by
the end-of-file token exactly when the input has a tokenisation. -/
theorem Lexer.wholeInputCorrect
    {feed : Lexicon.Version → List Lexicon.Chars → Bool → Spec.Lexer.Fed}
    (h : Spec.Lexer.Correct feed) :
    ∀ version slices handed, Spec.Lexer.WholeInputCorrect feed version slices handed :=
  Lexer.wholeInputCorrect_of_correct h

/--
info: 'BSmtLib.SpecChecks.Lexer.wholeInputCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.wholeInputCorrect

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
theorem Lexicon.composeAtClose : Spec.Lexer.ComposesAtClose := by
  intro version start tokens h hclose
  have hclose' : Lexicon.EndsWithClose tokens (0 + start.length) := by simpa using hclose
  refine ⟨Lexicon.close_handoverMaximal h hclose, fun more tokens' => ?_⟩
  rw [Lexicon.Tokenization, Lexicon.tokenizationFrom_close_iff h hclose' more tokens']
  constructor
  · rintro ⟨others, rfl, ho⟩
    rw [Nat.zero_add, ← Nat.zero_add start.length] at ho
    obtain ⟨others₀, rfl, h₀⟩ := Lexicon.tokenizationFrom_moveBy_inv ho
    exact ⟨others₀, rfl, h₀⟩
  · rintro ⟨others, rfl, ho⟩
    exact ⟨_, rfl, by simpa using Lexicon.tokenizationFrom_moveBy ho start.length⟩

/--
info: 'BSmtLib.SpecChecks.Lexicon.composeAtClose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.composeAtClose

/-- Characters read from any offset, in any version, are tokenised as they are on their own,
moved to that offset. -/
theorem Lexicon.readOnItsOwn : Lexicon.ReadsOnItsOwn := by
  intro version offset input tokens
  constructor
  · intro h
    rw [← Nat.zero_add offset] at h
    exact Lexicon.tokenizationFrom_moveBy_inv h
  · rintro ⟨tokens₀, rfl, h₀⟩
    simpa using Lexicon.tokenizationFrom_moveBy h₀ offset

/--
info: 'BSmtLib.SpecChecks.Lexicon.readOnItsOwn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.readOnItsOwn

/-!
### A lexer and its consumers

`Spec.Lexer.Runs` states what a lexer does with a consumer relative to what it hands over to the
collector. What it does is determined by the input and the consumer, so the result it holds or
returns, where its discarding began and the version in force are too. The input after a switch
of the version is read on its own and located in the whole input; locating it so agrees with
locating its characters in the whole input, and from the start of the input, the tokens ready
are those the lexer hands over to the collector. The collector meets the obligation of every
consumer.
-/

/-- What a lexer does with a consumer, from any point on, is determined. -/
theorem Lexer.runsDetermined {feed : Lexicon.Version → List Lexicon.Chars → Bool → Spec.Lexer.Fed}
    {consumer : Spec.Lexer.Consumer} {start : Lexicon.Version} {input : Lexicon.Chars}
    {ended : Bool} {version : Lexicon.Version} {ready : List Spec.Lexer.Handed} {failed : Bool}
    {taken : List Spec.Lexer.Handed}
    {session session' : Spec.Lexer.Session consumer.Result consumer.Error}
    (h : Spec.Lexer.Runs feed consumer start input ended version ready failed taken session)
    (h' : Spec.Lexer.Runs feed consumer start input ended version ready failed taken session') :
    session = session' :=
  Lexer.runs_unique h h'

/--
info: 'BSmtLib.SpecChecks.Lexer.runsDetermined' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.runsDetermined

/-- Locating characters of an input read on its own after `before`, then moving the location
past `before`, is locating them in the whole input. -/
theorem Lexer.locateAfter (before input : Lexicon.Chars) (offset : Nat) :
    Spec.Lexer.locate (before ++ input) (before.length + offset) =
      (Spec.Lexer.locate input offset).after before :=
  Lexer.locate_after before input offset

/--
info: 'BSmtLib.SpecChecks.Lexer.locateAfter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.locateAfter

/-- From the start of the input, the tokens ready are those the lexer hands over to the
collector. -/
theorem Lexer.segmentAtStart (feed : Lexicon.Version → List Lexicon.Chars → Bool → Spec.Lexer.Fed)
    (version : Lexicon.Version) (input : Lexicon.Chars) (ended : Bool) :
    Spec.Lexer.segment feed version input ended 0 = feed version [input] ended :=
  Lexer.segment_zero feed version input ended

/--
info: 'BSmtLib.SpecChecks.Lexer.segmentAtStart' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.segmentAtStart

/-- The collector breaks at the end of the input. -/
theorem Lexer.collectorBreaksAtEnd : Spec.Lexer.collector.BreaksAtEnd :=
  Lexer.collector_breaksAtEnd

/--
info: 'BSmtLib.SpecChecks.Lexer.collectorBreaksAtEnd' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Lexer.collectorBreaksAtEnd


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
### The grammar

`Grammar.readTerm` and `Grammar.readCommand` read the tokens of a tree back as the tree, so two
trees with the same tokens are the same tree. A command is read back from its tokens whatever
follows them, and its characters end with its `)`, after which nothing changes the tokens before
it (`Lexicon.tokenizationFrom_close_prefix`); so the first command of a file is determined, and
with it the mode in which the rest is read.
-/

/-- Two terms of a version that are written with the same tokens are the same term. -/
theorem Grammar.termsOneToOne : Spec.Grammar.TermsOneToOne := by
  intro _ term term' _ _ h
  have h₁ := Grammar.readTerm_tokens term [] (n := sizeOf term + sizeOf term' + 1) (by omega)
  have h₂ := Grammar.readTerm_tokens term' [] (n := sizeOf term + sizeOf term' + 1) (by omega)
  rw [h, h₂] at h₁
  exact (Prod.mk.inj (Option.some.inj h₁)).1.symm

/--
info: 'BSmtLib.SpecChecks.Grammar.termsOneToOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.termsOneToOne

/-- Two commands of a version that are written with the same tokens are the same command. -/
theorem Grammar.commandsOneToOne : Spec.Grammar.CommandsOneToOne := by
  intro version command command' hv hv' h
  have h₁ := Grammar.readCommand_tokens version command [] hv
    (n := sizeOf command + sizeOf command' + 1) (by omega)
  have h₂ := Grammar.readCommand_tokens version command' [] hv'
    (n := sizeOf command + sizeOf command' + 1) (by omega)
  rw [h, h₂] at h₁
  exact (Prod.mk.inj (Option.some.inj h₁)).1.symm

/--
info: 'BSmtLib.SpecChecks.Grammar.commandsOneToOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.commandsOneToOne

/-- Every file has at most one reading. -/
theorem Grammar.filesUnique : Spec.Grammar.FilesUnique :=
  fun _ _ _ _ h h' => Grammar.fileFrom_unique h h'

/--
info: 'BSmtLib.SpecChecks.Grammar.filesUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.filesUnique

/-- A lexer fed the characters of a command has handed over all its tokens and holds nothing
back, so the next command can be read in the version the command switches to. -/
theorem Grammar.commandHandedOver : Spec.Grammar.CommandsHandedOverWhole :=
  fun _ _ _ _ h hc =>
    Lexicon.close_handoverMaximal h.1 (by simpa using Grammar.endsWithClose_of_command h hc)

/--
info: 'BSmtLib.SpecChecks.Grammar.commandHandedOver' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.commandHandedOver

/-!
### Reproducing a file

A file is reproduced from its reading, the concrete readings of its commands and what follows
the last of them, and its commands (`Grammar.reproduce`): each command is written as its
tokens, in the version in force, with the whitespace and comments of the input between them.
Only a 2.0 string literal can come out written differently: as one that stands for the same
content (`Lexicon.SameButStrings20`).
-/

/-- Every file is reproduced from its reading and its commands but for the spelling of 2.0
string literals that stand for the same content. -/
theorem Grammar.reproduceSimilar {version : Lexicon.Version} {input : Lexicon.Chars}
    {commands : List Grammar.Tree.Command} (h : Grammar.File version input commands) :
    ∃ segments final, Grammar.FileReadingFrom version 0 input commands segments final ∧
      Lexicon.SameButStrings20 (Grammar.reproduce version commands (segments.map Prod.snd) final)
        input := by
  obtain ⟨segments, final, hr⟩ := Grammar.exists_fileReading h
  exact ⟨segments, final, hr, Grammar.reproduce_similar hr⟩

/--
info: 'BSmtLib.SpecChecks.Grammar.reproduceSimilar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.reproduceSimilar

/-- A file has at most one reading. -/
theorem Grammar.readingUnique {version : Lexicon.Version} {input : Lexicon.Chars}
    {commands commands' : List Grammar.Tree.Command}
    {segments segments' : List (Lexicon.Version × Lexicon.Concrete)} {final final' : Lexicon.Chars}
    (h : Grammar.FileReadingFrom version 0 input commands segments final)
    (h' : Grammar.FileReadingFrom version 0 input commands' segments' final') :
    commands = commands' ∧ segments = segments' ∧ final = final' :=
  ⟨Grammar.fileFrom_unique h.file h'.file, Grammar.fileReadingFrom_unique h h'⟩

/--
info: 'BSmtLib.SpecChecks.Grammar.readingUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.readingUnique

/-- A file in which no 2.0 string literal has a lone backslash is reproduced exactly. -/
theorem Grammar.reproduceExact {version : Lexicon.Version} {input : Lexicon.Chars}
    {commands : List Grammar.Tree.Command}
    {segments : List (Lexicon.Version × Lexicon.Concrete)} {final : Lexicon.Chars}
    (h : Grammar.FileReadingFrom version 0 input commands segments final)
    (hl : ∀ segment ∈ segments, Lexicon.NoLoneBackslash segment.1 segment.2.tokens) :
    Grammar.reproduce version commands (segments.map Prod.snd) final = input :=
  Grammar.reproduce_eq h hl

/--
info: 'BSmtLib.SpecChecks.Grammar.reproduceExact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.reproduceExact

/-- A reproduced file is a file with the same commands, and it is reproduced exactly. -/
theorem Grammar.reproduceIdempotent {version : Lexicon.Version} {input : Lexicon.Chars}
    {commands : List Grammar.Tree.Command}
    {segments : List (Lexicon.Version × Lexicon.Concrete)} {final : Lexicon.Chars}
    (h : Grammar.FileReadingFrom version 0 input commands segments final) :
    Grammar.File version (Grammar.reproduce version commands (segments.map Prod.snd) final)
        commands ∧
      ∀ segments' final', Grammar.FileReadingFrom version 0
          (Grammar.reproduce version commands (segments.map Prod.snd) final) commands
          segments' final' →
        Grammar.reproduce version commands (segments'.map Prod.snd) final' =
          Grammar.reproduce version commands (segments.map Prod.snd) final := by
  obtain ⟨segments'', hr, he⟩ := Grammar.reproduce_reading h 0
  refine ⟨hr.file, fun segments' final' h' => ?_⟩
  obtain ⟨rfl, rfl⟩ := Grammar.fileReadingFrom_unique h' hr
  exact he

/--
info: 'BSmtLib.SpecChecks.Grammar.reproduceIdempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.reproduceIdempotent

/-!
### The traversal as a parser

`Parser.parseScript` is a program that makes the traversal's calls going by the items a parser
receives rather than by the syntax tree: it receives an item, and decides from it and from what
it received before what to do next. It makes the calls of the traversal of every script, for
every handler, so the traversal can be carried out by a parser that has only the items so far.
-/

/--
For every handler in a lawful monad, points, producer and policy, the traversal of a
script makes what `Parser.parseScript` makes run on what a parser receives for the script, given
fuel larger than ten times the size of the script; whatever follows is left untouched.
-/
theorem Parser.script_eq_parse {m : Type → Type} [Monad m] [LawfulMonad m] {ε : Type}
    {values : Spec.Parser.Traversal.Values} (points : Spec.Parser.Traversal.Points m)
    (handler : Spec.Parser.Traversal.Handler m ε values)
    (producer : Spec.Parser.Traversal.Producer m)
    (policy : Spec.Parser.VersionPolicy) {version : Lexicon.Version}
    {commands : List Grammar.Tree.Command} (h : Grammar.Script version commands)
    (rest : List Spec.Parser.Traversal.Received) {n : Nat} (hn : 10 * sizeOf commands < n) :
    Parser.Program.run points handler producer policy (Parser.parseScript n)
        (Spec.Parser.received commands ++ rest) =
      (Spec.Parser.Traversal.script points handler producer policy commands >>= fun _ =>
        pure ((), rest)) :=
  Parser.run_script version commands rest h hn

/--
info: 'BSmtLib.SpecChecks.Parser.script_eq_parse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.script_eq_parse

/-!
### What a recording shows

`Parser.Recovery.recover` rebuilds the commands of a script from the calls of its recording
alone: each call stands for the tree it reports, built from what the earlier calls it names
stand for.
-/

/-- The traversal of a script takes exactly what a parser receives for it, each item arriving
and then processed, in order. -/
theorem Parser.takesItsTokens : Spec.Parser.TakesItsTokens :=
  fun _ _ h => Parser.record_items h

/--
info: 'BSmtLib.SpecChecks.Parser.takesItsTokens' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.takesItsTokens

/-- The calls of the recording of a script rebuild the script. -/
theorem Parser.recoverRebuilds {version : Lexicon.Version} {commands : List Grammar.Tree.Command}
    (h : Grammar.Script version commands) :
    Parser.Recovery.recover version
      ((Spec.Parser.record commands).filter Spec.Parser.Event.isCall) = some commands :=
  Parser.recover_record h

/--
info: 'BSmtLib.SpecChecks.Parser.recoverRebuilds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.recoverRebuilds

/-- Two scripts from the same version whose traversals make the same calls are the same
script. -/
theorem Parser.callsDetermineScript : Spec.Parser.CallsDetermineScript := by
  intro version commands commands' h h' hcalls
  have := Parser.recover_record h
  rw [hcalls, Parser.recover_record h'] at this
  exact (Option.some.inj this).symm

/--
info: 'BSmtLib.SpecChecks.Parser.callsDetermineScript' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.callsDetermineScript

/-- What the traversal of a script has done before an item arrives, and before it is processed,
depends only on the items before it. -/
theorem Parser.placementDetermined : Spec.Parser.PlacementDetermined := by
  intro version commands commands' count h h' ht
  let n := 10 * (sizeOf commands + sizeOf commands') + 1
  rw [Parser.record_eq_trace h (n := n) (by omega), Parser.record_eq_trace h' (n := n) (by omega)]
  exact ⟨Parser.eventsBefore_trace _ _ _ _ _ ht,
    Parser.eventsBeforeProcessing_trace _ _ _ _ _ ht (Parser.received_length h h' ht)⟩

/--
info: 'BSmtLib.SpecChecks.Parser.placementDetermined' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.placementDetermined

/-!
### Every handler is placed as the recording

The properties of the traversal are stated on recordings. `Parser.cutRun` is the traversal of a
script with any handler, points, producer and policy, stopped at the arrival of the item
at a given position: what such a run has done before that item arrives. The two theorems below
carry `Spec.Parser.PlacementDetermined` over to every handler: the cut runs of two scripts are
equal when what a parser receives for them agrees before the cut, and when their recordings do.
They are checks of the specification, not properties stated in it.
-/

/--
For every handler in a lawful monad, points, producer and policy, what the traversals of
two valid scripts have done before the item at position `count` arrives is the same when what a
parser receives for them agrees before that item.
-/
theorem Parser.cutRunsAgree {m : Type → Type} [Monad m] [LawfulMonad m] {ε : Type}
    {values : Spec.Parser.Traversal.Values} (points : Spec.Parser.Traversal.Points m)
    (handler : Spec.Parser.Traversal.Handler m ε values)
    (producer : Spec.Parser.Traversal.Producer m)
    (policy : Spec.Parser.VersionPolicy) (count : Nat) {version version' : Lexicon.Version}
    {commands commands' : List Grammar.Tree.Command} (h : Grammar.Script version commands)
    (h' : Grammar.Script version' commands')
    (ht : (Spec.Parser.received commands).take count =
      (Spec.Parser.received commands').take count) :
    Parser.cutRun points handler producer policy count commands =
      Parser.cutRun points handler producer policy count commands' :=
  Parser.cutRun_eq points handler producer policy count h h' ht

/--
info: 'BSmtLib.SpecChecks.Parser.cutRunsAgree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.cutRunsAgree

/--
For every handler in a lawful monad, points, producer and policy, what the traversals of
two valid scripts have done before the item at position `count` arrives is the same when their
recordings agree before that item: a recording stands for the run with every handler.
-/
theorem Parser.cutRunsAgreeByRecord {m : Type → Type} [Monad m] [LawfulMonad m] {ε : Type}
    {values : Spec.Parser.Traversal.Values} (points : Spec.Parser.Traversal.Points m)
    (handler : Spec.Parser.Traversal.Handler m ε values)
    (producer : Spec.Parser.Traversal.Producer m)
    (policy : Spec.Parser.VersionPolicy) (count : Nat) {version version' : Lexicon.Version}
    {commands commands' : List Grammar.Tree.Command} (h : Grammar.Script version commands)
    (h' : Grammar.Script version' commands')
    (he : Spec.Parser.eventsBefore count (Spec.Parser.record commands) =
      Spec.Parser.eventsBefore count (Spec.Parser.record commands')) :
    Parser.cutRun points handler producer policy count commands =
      Parser.cutRun points handler producer policy count commands' :=
  Parser.cutRun_eq_of_record points handler producer policy count h h' he

/--
info: 'BSmtLib.SpecChecks.Parser.cutRunsAgreeByRecord' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.cutRunsAgreeByRecord

/--
For every handler in a lawful monad, points, producer and policy, what the traversals of
two valid scripts have done when the item at position `count` is rejected, before it is
processed and without its own arrival, is the same when their recordings agree before the
processing of that item.
-/
theorem Parser.processingCutRunsAgreeByRecord {m : Type → Type} [Monad m] [LawfulMonad m]
    {ε : Type} {values : Spec.Parser.Traversal.Values} (points : Spec.Parser.Traversal.Points m)
    (handler : Spec.Parser.Traversal.Handler m ε values)
    (producer : Spec.Parser.Traversal.Producer m)
    (policy : Spec.Parser.VersionPolicy) (count : Nat) {version version' : Lexicon.Version}
    {commands commands' : List Grammar.Tree.Command} (h : Grammar.Script version commands)
    (h' : Grammar.Script version' commands')
    (he : Spec.Parser.eventsBeforeProcessing count (Spec.Parser.record commands) =
      Spec.Parser.eventsBeforeProcessing count (Spec.Parser.record commands')) :
    Parser.processingCutRun points handler producer policy count commands =
      Parser.processingCutRun points handler producer policy count commands' :=
  Parser.processingCutRun_eq_of_record points handler producer policy count h h' he

/--
info: 'BSmtLib.SpecChecks.Parser.processingCutRunsAgreeByRecord' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.processingCutRunsAgreeByRecord

end BSmtLib.SpecChecks
