import BSmtLib.Spec.Grammar.Rules

/-!
# Reading a script

How the characters of a script read as commands: each command is lexed and parsed in the
version in force where it starts.
-/

namespace BSmtLib.Spec.Grammar

open BSmtLib.Spec.Lexicon

/-- The input reads as the tokens and ends with the last of them: no whitespace follows. -/
def ReadsExactly (version : Version) (offset : Nat) (input : Chars) (tokens : List Token) :
    Prop :=
  ReadsFrom version offset input tokens ∧
    ∃ last, tokens.getLast? = some last ∧ last.offset + last.text.length = offset + input.length

/--
Reading P4: a version declaration is a `set-info` with the attribute `:smt-lib-version`.

The command is a version declaration: `set-info` with the attribute `:smt-lib-version`.
-/
def Tree.Command.DeclaresVersion (command : Tree.Command) : Prop :=
  ∃ value, command = .setInfo ⟨chars "smt-lib-version", value⟩

/--
Standard: 2.7 §3.11 Scripts: a script is a sequence of commands. Reading P4: a version
declaration starts its version at its first character. Reading P5: `exit` ends the script.

`ScriptReadsFrom version offset input commands`: starting in the version, the input, whose
first character is at `offset`, reads as the commands.

A version declaration starts the version it declares from its own first character: it is
read in that version, which accepts only a declaration of itself, and so is the input after
it. The library switches at the end of the declaration instead; a declaration reads the same
in every version, so the two agree.

A script is the commands of the input, which `exit` may end early: nothing after it is read.
-/
inductive ScriptReadsFrom : Version → Nat → Chars → List Tree.Command → Prop
  | done : ReadsFrom version offset input [] → ScriptReadsFrom version offset input []

  | command : ReadsExactly commandVersion offset segment tokens →
      Grammar.Command commandVersion (tokens.map (SyntaxToken.ofToken commandVersion)) command →
      (commandVersion = version ∨ command.DeclaresVersion) → command ≠ .exit →
      ScriptReadsFrom commandVersion (offset + segment.length) rest commands →
      ScriptReadsFrom version offset (segment ++ rest) (command :: commands)

  | exit : ReadsExactly version offset segment tokens →
      Grammar.Command version (tokens.map (SyntaxToken.ofToken version)) .exit →
      ScriptReadsFrom version offset (segment ++ rest) [.exit]

/--
Standard: 2.7 §3.11 Scripts. Readings P4 and P5, as `ScriptReadsFrom`.

`ScriptReads version input commands`: starting in the version, the input reads as the
commands.
-/
def ScriptReads (version : Version) (input : Chars) (commands : List Tree.Command) : Prop :=
  ScriptReadsFrom version 0 input commands

end BSmtLib.Spec.Grammar
