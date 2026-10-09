import BSmtLib.Spec.Grammar.Syntax

/-!
# Reading a file

How the characters of a file are read as commands, on three levels:

- **commands**: each command is a sequence of tokens of the version in force (`IsCommand`);
- **reading modes**: a run of commands is read in one version, until a command changes the
  mode in which the input after it is read (`Mode`, `Tree.Command.modeAfter`);
- **files**: a file is read from a starting version, mode after mode, up to the end of the
  input or up to `exit`, after which the rest of the file is not read (`File`).

A command that changes the mode does so after its closing parenthesis: it is read entirely in
the mode before it, and the mode after it starts with the character after its `)`. A lexer
hands over a parenthesis without reading past it, so no character is read in a mode it does not
belong to.

`Script` states the same on the level of tokens: which sequences of commands, each in its
version, make a script.
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
How the input after a command is read: in a version, or not at all.
-/
inductive Mode where
  /-- The input is read as commands of the version. -/
  | read (version : Version)
  /-- The input is not read: it need not be valid, nor even lexable. -/
  | unparsed

/--
The mode in which the input after the command is read, given the version the command is read
in, or `none` if the command cannot stand in a file: a version declaration of a version that is
not supported.

A version declaration is a `set-info` of `:smt-lib-version`; it is read in the version in force
like any other `set-info`, and the version it declares is read from its `)` on. `exit` stops the
reading. Every other command, `reset` among them, leaves the mode as it is.

Reading M1: a version declaration changes the mode after its `)`; the value of a declaration is
the number of a supported version. Reading M2: `exit` ends the reading; the input after it is
not read. Reading M3: `reset` does not return to the version the file started in.
-/
def Tree.Command.modeAfter (version : Version) : Tree.Command → Option Mode
  | .exit => some .unparsed
  | .setInfo ⟨keyword, value⟩ =>
    if keyword = chars "smt-lib-version" then
      match value with
      | some (.constant (.decimal decimal)) => (versionOfNumber decimal).map .read
      | _ => none
    else some (.read version)
  | _ => some (.read version)

/--
The version the command declares, if it is a version declaration of a supported version.
-/
def Tree.Command.declaredVersion (command : Tree.Command) : Option Version :=
  match command with
  | .setInfo ⟨keyword, some (.constant (.decimal decimal))⟩ =>
    if keyword = chars "smt-lib-version" then versionOfNumber decimal else none
  | _ => none

/--
`FileFrom version offset input commands`: read from the version, the input, whose first
character is at `offset`, has the commands.

Each command is the whitespace before it and its tokens, read in the version in force. After a
command that keeps the mode in a version, the rest is read in that version; after `exit`, the
rest is not read. A file that is not ended by `exit` ends with whitespace.

Standard: 2.7 §3.11 Scripts: a script is a sequence of commands. Readings M1, M2 and M3, as
`Tree.Command.modeAfter`.
-/
inductive FileFrom : Version → Nat → Chars → List Tree.Command → Prop
  /-- The end of the input, after whitespace. -/
  | done : TokenizationFrom version offset input [] → FileFrom version offset input []

  /-- A command after which the rest is read in a version. -/
  | command : TokenizationExactly version offset segment tokens →
      IsCommand version (tokens.map (SyntaxToken.ofToken version)) command →
      command.modeAfter version = some (.read next) →
      FileFrom next (offset + segment.length) rest commands →
      FileFrom version offset (segment ++ rest) (command :: commands)

  /-- A command after which the rest is not read: `exit`, and whatever follows it. -/
  | stop : TokenizationExactly version offset segment tokens →
      IsCommand version (tokens.map (SyntaxToken.ofToken version)) command →
      command.modeAfter version = some .unparsed →
      FileFrom version offset (segment ++ rest) [command]

/--
`File version input commands`: read from the version, the input has the commands.

Standard: 2.7 §3.11 Scripts, as `FileFrom`.
-/
def File (version : Version) (input : Chars) (commands : List Tree.Command) : Prop :=
  FileFrom version 0 input commands

/--
`Script version commands`: read from the version, the commands make a script: each is a command
of the version in force where it starts, and only the last one may stop the reading.

The commands of a file make a script (`File`); a script is what a parser of tokens is given.

Standard: 2.7 §3.11 Scripts. Readings M1, M2 and M3, as `Tree.Command.modeAfter`.
-/
inductive Script : Version → List Tree.Command → Prop
  /-- No more commands. -/
  | done : Script version []

  /-- A command after which the script goes on in a version. -/
  | command : command.Valid version → command.modeAfter version = some (.read next) →
      Script next commands → Script version (command :: commands)

  /-- A command after which nothing is read. -/
  | stop : command.Valid version → command.modeAfter version = some .unparsed →
      Script version [command]

end BSmtLib.Spec.Grammar
