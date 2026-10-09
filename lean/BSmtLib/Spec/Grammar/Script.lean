import BSmtLib.Spec.Grammar.Rules

/-!
# Parsing a script

How the characters of a script parse as commands: each command is lexed and parsed in the
version in force where it starts.
-/

namespace BSmtLib.Spec.Grammar

open BSmtLib.Spec.Lexicon

/--
The tokens are a tokenisation of the input, which ends with the last of them: no whitespace
follows.
-/
def TokenizationExactly (version : Version) (offset : Nat) (input : Chars) (tokens : List Token) :
    Prop :=
  TokenizationFrom version offset input tokens ∧
    ∃ last, tokens.getLast? = some last ∧ last.offset + last.text.length = offset + input.length

/--
The command is a version declaration: `set-info` with the attribute `:smt-lib-version`.

Reading M1: a version declaration is a `set-info` with the attribute `:smt-lib-version`.
-/
def Tree.Command.DeclaresVersion (command : Tree.Command) : Prop :=
  ∃ value, command = .setInfo ⟨chars "smt-lib-version", value⟩

/--
`ScriptParseFrom version offset input commands`: starting in the version, the input, whose
first character is at `offset`, has the commands as a parse.

Standard: 2.7 §3.11 Scripts: a script is a sequence of commands. Reading M1: a version
declaration starts its version at its first character. Reading M2: `exit` ends the script.
Reading M3: `reset` keeps the version in force.

TODO: disagrees with M1 in `BSmtLib.Spec`, under which a declaration is parsed in the version
in force and its version applies after its closing parenthesis.

A version declaration starts the version it declares from its own first character: it is
parsed in that version, which accepts only a declaration of itself, and so is the input after
it. The library switches at the end of the declaration instead; a declaration parses the same
in every version, so the two agree.

A script is the commands of the input, which `exit` may end early: nothing after it is parsed.
-/
inductive ScriptParseFrom : Version → Nat → Chars → List Tree.Command → Prop
  | done : TokenizationFrom version offset input [] → ScriptParseFrom version offset input []

  | command : TokenizationExactly commandVersion offset segment tokens →
      Grammar.Command commandVersion (tokens.map (SyntaxToken.ofToken commandVersion)) command →
      (commandVersion = version ∨ command.DeclaresVersion) → command ≠ .exit →
      ScriptParseFrom commandVersion (offset + segment.length) rest commands →
      ScriptParseFrom version offset (segment ++ rest) (command :: commands)

  | exit : TokenizationExactly version offset segment tokens →
      Grammar.Command version (tokens.map (SyntaxToken.ofToken version)) .exit →
      ScriptParseFrom version offset (segment ++ rest) [.exit]

/--
`ScriptParse version input commands`: starting in the version, the input has the
commands as a parse.

Standard: 2.7 §3.11 Scripts. Readings M1 and M2, as `ScriptParseFrom`.
-/
def ScriptParse (version : Version) (input : Chars) (commands : List Tree.Command) : Prop :=
  ScriptParseFrom version 0 input commands

end BSmtLib.Spec.Grammar
