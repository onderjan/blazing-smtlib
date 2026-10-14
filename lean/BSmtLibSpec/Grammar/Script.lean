module

public import BSmtLibSpec.Grammar.File

@[expose] public section

/-!
# Scripts

`Script` states the same as `File` on the level of tokens: which sequences of commands, each in
its version, make a script.
-/

namespace BSmtLibSpec.Grammar

open BSmtLibSpec.Lexicon

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

end BSmtLibSpec.Grammar
