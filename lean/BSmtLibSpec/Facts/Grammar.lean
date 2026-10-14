import BSmtLibSpec.Facts.Grammar.Examples
import BSmtLibSpec.Facts.Proofs.Grammar.OneToOne
import BSmtLibSpec.Facts.Proofs.Grammar.Files
import BSmtLibSpec.Facts.Proofs.Grammar.RoundTrip

/-!
# Facts of the grammar

The grammar: the tokens of a tree determine the tree, and every file has at most one reading,
from which it is reproduced.

Each theorem below proves a property of the specification, from the modules imported above.
Each is followed by the axioms its proof uses: only those of Lean's standard library, no
`sorry` and no axiom of its own. The build fails if that changes.
-/

namespace BSmtLibSpec.Facts

/-!
### The grammar

`Grammar.readTerm` and `Grammar.readCommand` read the tokens of a tree back as the tree, so two
trees with the same tokens are the same tree. A command is read back from its tokens whatever
follows them, and its characters end with its `)`, after which nothing changes the tokens before
it (`Lexicon.tokenizationFrom_close_prefix`); so the first command of a file is determined, and
with it the mode in which the rest is read.
-/

/-- Two terms of a version that are written with the same tokens are the same term. -/
theorem Grammar.termsOneToOne : BSmtLibSpec.Grammar.Properties.TermsOneToOne := by
  intro _ term term' _ _ h
  have h₁ := Proofs.Grammar.OneToOne.readTerm_tokens term [] (n := sizeOf term + sizeOf term' + 1)
      (by omega)
  have h₂ := Proofs.Grammar.OneToOne.readTerm_tokens term' [] (n := sizeOf term + sizeOf term' + 1)
      (by omega)
  rw [h, h₂] at h₁
  exact (Prod.mk.inj (Option.some.inj h₁)).1.symm

/--
info: 'BSmtLibSpec.Facts.Grammar.termsOneToOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.termsOneToOne

/-- Two commands of a version that are written with the same tokens are the same command. -/
theorem Grammar.commandsOneToOne : BSmtLibSpec.Grammar.Properties.CommandsOneToOne := by
  intro version command command' hv hv' h
  have h₁ := Proofs.Grammar.OneToOne.readCommand_tokens version command [] hv
    (n := sizeOf command + sizeOf command' + 1) (by omega)
  have h₂ := Proofs.Grammar.OneToOne.readCommand_tokens version command' [] hv'
    (n := sizeOf command + sizeOf command' + 1) (by omega)
  rw [h, h₂] at h₁
  exact (Prod.mk.inj (Option.some.inj h₁)).1.symm

/--
info: 'BSmtLibSpec.Facts.Grammar.commandsOneToOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.commandsOneToOne

/-- Every file has at most one reading. -/
theorem Grammar.filesUnique : BSmtLibSpec.Grammar.Properties.FilesUnique :=
  fun _ _ _ _ h h' => Proofs.Grammar.Files.fileFrom_unique h h'

/--
info: 'BSmtLibSpec.Facts.Grammar.filesUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.filesUnique

/-- A lexer fed the characters of a command has handed over all its tokens and holds nothing
back, so the next command can be read in the version the command switches to. -/
theorem Grammar.commandHandedOver : BSmtLibSpec.Grammar.Properties.CommandsHandedOverWhole :=
  fun _ _ _ _ h hc =>
    Proofs.Lexicon.Compose.close_handoverMaximal h.1
        (by simpa using Proofs.Grammar.Files.endsWithClose_of_command h hc)

/--
info: 'BSmtLibSpec.Facts.Grammar.commandHandedOver' depends on axioms: [propext, Classical.choice, Quot.sound]
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
theorem Grammar.reproduceSimilar {version : Lexicon.Version} {input : Regex.Chars}
    {commands : List Grammar.Tree.Command} (h : Grammar.File version input commands) :
    ∃ segments final, Proofs.Grammar.RoundTrip.FileReadingFrom version 0 input commands segments
        final ∧
      Proofs.Lexicon.RoundTrip.Rewrite.SameButStrings20
          (Proofs.Grammar.RoundTrip.reproduce version commands (segments.map Prod.snd) final)
        input := by
  obtain ⟨segments, final, hr⟩ := Proofs.Grammar.RoundTrip.exists_fileReading h
  exact ⟨segments, final, hr, Proofs.Grammar.RoundTrip.reproduce_similar hr⟩

/--
info: 'BSmtLibSpec.Facts.Grammar.reproduceSimilar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.reproduceSimilar

/-- A file has at most one reading. -/
theorem Grammar.readingUnique {version : Lexicon.Version} {input : Regex.Chars}
    {commands commands' : List Grammar.Tree.Command}
    {segments segments' : List (Lexicon.Version × Proofs.Lexicon.RoundTrip.Tokens.Concrete)}
    {final final' : Regex.Chars}
    (h : Proofs.Grammar.RoundTrip.FileReadingFrom version 0 input commands segments final)
    (h' : Proofs.Grammar.RoundTrip.FileReadingFrom version 0 input commands' segments' final') :
    commands = commands' ∧ segments = segments' ∧ final = final' :=
  ⟨Proofs.Grammar.Files.fileFrom_unique h.file h'.file,
      Proofs.Grammar.RoundTrip.fileReadingFrom_unique h h'⟩

/--
info: 'BSmtLibSpec.Facts.Grammar.readingUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.readingUnique

/-- A file in which no 2.0 string literal has a lone backslash is reproduced exactly. -/
theorem Grammar.reproduceExact {version : Lexicon.Version} {input : Regex.Chars}
    {commands : List Grammar.Tree.Command}
    {segments : List (Lexicon.Version × Proofs.Lexicon.RoundTrip.Tokens.Concrete)}
    {final : Regex.Chars}
    (h : Proofs.Grammar.RoundTrip.FileReadingFrom version 0 input commands segments final)
    (hl : ∀ segment ∈ segments, Proofs.Lexicon.RoundTrip.Lexical.NoLoneBackslash segment.1
    segment.2.tokens) :
    Proofs.Grammar.RoundTrip.reproduce version commands (segments.map Prod.snd) final = input :=
  Proofs.Grammar.RoundTrip.reproduce_eq h hl

/--
info: 'BSmtLibSpec.Facts.Grammar.reproduceExact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.reproduceExact

/-- A reproduced file is a file with the same commands, and it is reproduced exactly. -/
theorem Grammar.reproduceIdempotent {version : Lexicon.Version} {input : Regex.Chars}
    {commands : List Grammar.Tree.Command}
    {segments : List (Lexicon.Version × Proofs.Lexicon.RoundTrip.Tokens.Concrete)}
    {final : Regex.Chars}
    (h : Proofs.Grammar.RoundTrip.FileReadingFrom version 0 input commands segments final) :
    Grammar.File version (Proofs.Grammar.RoundTrip.reproduce version commands
        (segments.map Prod.snd) final)
        commands ∧
      ∀ segments' final', Proofs.Grammar.RoundTrip.FileReadingFrom version 0
          (Proofs.Grammar.RoundTrip.reproduce version commands (segments.map Prod.snd) final)
              commands
          segments' final' →
        Proofs.Grammar.RoundTrip.reproduce version commands (segments'.map Prod.snd) final' =
          Proofs.Grammar.RoundTrip.reproduce version commands (segments.map Prod.snd) final := by
  obtain ⟨segments'', hr, he⟩ := Proofs.Grammar.RoundTrip.reproduce_reading h 0
  refine ⟨hr.file, fun segments' final' h' => ?_⟩
  obtain ⟨rfl, rfl⟩ := Proofs.Grammar.RoundTrip.fileReadingFrom_unique h' hr
  exact he

/--
info: 'BSmtLibSpec.Facts.Grammar.reproduceIdempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.reproduceIdempotent

end BSmtLibSpec.Facts
