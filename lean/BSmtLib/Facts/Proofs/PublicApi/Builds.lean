module

public import BSmtLib.Facts.Proofs.PublicApi.BuilderTraversal

@[expose] public section

/-!
# The builder builds the commands of every file

The witness of `builds_commands` in `Facts.PublicApi`: `Builder.builder`, whose state is the
version in force beside the commands. A state of the commands alone would not do: told the
version it starts in only by `setVersion`, such a handler is left in the same state by a file
whose first command does not depend on the version, and after that `check-sat-assuming` of a
symbol makes the same calls in 2.6 and in 2.7 while the file's commands differ.

The proof rests on three facts:
- the script reader with a handler whose calls never fail leaves it where the traversal of the
  file's commands, as the specification formalism (`BSmtLibSpec`) defines it, leaves it, for
  every handler of the formalism it agrees with
  (`Reader.Handler.Traversal.reader_follows_traversal`);
- the builder agrees with `specBuilder` (`Builder.agrees`);
- the traversal with `specBuilder` leaves the commands (`BuilderTraversal.script_builds`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.Builds

open BSmtLibSpec.Grammar
open BSmtLib.Facts.PublicApi.Adapters BSmtLib.Facts.PublicApi.Adapters.Content
open BSmtLib.Facts.PublicApi.Adapters.Builder

theorem libVersion_eq (version : BSmtLibSpec.Lexicon.Version) :
    libVersion version = BSmtLib.Facts.Lexer.Adapters.toVersion version := by
  cases version <;> rfl

/-- There is a handler told contents only, whose state is the version in force and a list of
commands of the formalism and whose sorts, s-expressions, attributes and terms are those of
the formalism, such that the script reader over it, with the initial version and no commands,
reads every file to the end and builds the file's commands. -/
theorem builds_commands :
    ∃ inst : ContentHandler (BSmtLibSpec.Lexicon.Version × List Tree.Command),
      inst.«Sort» = Tree.Sort ∧
      inst.SExpr = Tree.SExpr ∧
      inst.Attribute = Tree.Attribute ∧
      inst.Term = Tree.Term ∧
      ∀ version slices commands, File version slices.flatten commands →
        ∃ result before after,
          readThrough (Reader.script (version, []) allVersions (libVersion version)) slices =
            .ok (some result, before, after) ∧
          after.handler.2.reverse = commands := by
  refine ⟨Builder.builder, rfl, rfl, rfl, rfl, fun version slices commands hfile => ?_⟩
  obtain ⟨result, before, after, hread, htrav⟩ :=
    Reader.Handler.Traversal.reader_follows_traversal Builder.agrees version slices
      (version, []) hfile
  refine ⟨result, before, after, by rw [libVersion_eq]; exact hread, ?_⟩
  obtain ⟨v', hv'⟩ := BuilderTraversal.script_builds version version commands
    (Reader.Valid.script_of_file hfile)
  rw [hv'] at htrav
  have := (Prod.mk.inj htrav).2
  rw [← this]
  simp

end BSmtLib.Facts.Proofs.PublicApi.Builds
