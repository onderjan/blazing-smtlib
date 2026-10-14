module

public import BSmtLibSpec.Grammar.Syntax
public import BSmtLibSpec.Lexicon.Tokenization

@[expose] public section

/-!
# Reading a file

How the characters of a file are read as commands, on three levels:

- **commands**: each command is a sequence of tokens of the version in force (`Syntax.IsCommand`);
- **reading modes**: a run of commands is read in one version, until a command changes the
  mode in which the input after it is read (`File.Mode`, `Tree.Command.modeAfter`);
- **files**: a file is read from a starting version, mode after mode, up to the end of the
  input or up to `exit`, after which the rest of the file is not read (`File`).

A command that changes the mode does so after its closing parenthesis: it is read entirely in
the mode before it, and the mode after it starts with the character after its `)`. A lexer
hands over a parenthesis without reading past it, so no character is read in a mode it does not
belong to.
-/

namespace BSmtLibSpec.Grammar

open BSmtLibSpec.Lexicon
open Regex (Chars chars)

/--
How the input after a command is read: in a version, or not at all.
-/
inductive File.Mode where
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
def Tree.Command.modeAfter (version : Version) : Tree.Command → Option File.Mode
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
Whether the command is a version declaration that names no supported version: a `set-info` of
`:smt-lib-version` whose value is not the number of a supported version, a decimal of no
supported version, a symbol, a list, or no value at all. No script has such a command
(`Tree.Command.modeAfter` gives `none` for it); a parser rejects it after its `)`.

Reading M1: the value of a declaration is the number of a supported version.
-/
def Tree.Command.namesNoVersion : Tree.Command → Bool
  | .setInfo ⟨keyword, value⟩ =>
    decide (keyword = chars "smt-lib-version") &&
      match value with
      | some (.constant (.decimal decimal)) => (versionOfNumber decimal).isNone
      | _ => true
  | _ => false

/--
`File.From version offset input commands`: read from the version, the input, whose first
character is at `offset`, has the commands.

Each command is the whitespace before it and its tokens, read in the version in force. After a
command that keeps the mode in a version, the rest is read in that version; after `exit`, the
rest is not read. A file that is not ended by `exit` ends with whitespace.

Standard: 2.7 §3.11 Scripts: a script is a sequence of commands. Readings M1, M2 and M3, as
`Tree.Command.modeAfter`.
-/
inductive File.From : Version → Nat → Chars → List Tree.Command → Prop
  /-- The end of the input, after whitespace. -/
  | done : Tokenization.From version offset input [] → File.From version offset input []

  /-- A command after which the rest is read in a version. -/
  | command : Tokenization.Exactly version offset segment tokens →
      Syntax.IsCommand version (tokens.map (SyntaxToken.ofToken version)) command →
      command.modeAfter version = some (.read next) →
      File.From next (offset + segment.length) rest commands →
      File.From version offset (segment ++ rest) (command :: commands)

  /-- A command after which the rest is not read: `exit`, and whatever follows it. -/
  | stop : Tokenization.Exactly version offset segment tokens →
      Syntax.IsCommand version (tokens.map (SyntaxToken.ofToken version)) command →
      command.modeAfter version = some .unparsed →
      File.From version offset (segment ++ rest) [command]

/--
`File version input commands`: read from the version, the input has the commands.

Standard: 2.7 §3.11 Scripts, as `File.From`.
-/
def File (version : Version) (input : Chars) (commands : List Tree.Command) : Prop :=
  File.From version 0 input commands

end BSmtLibSpec.Grammar
