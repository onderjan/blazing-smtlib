module

public import BSmtLib.Token

public section

/-!
# How a command ended

The outcome of the command parser at the end of a command.
-/

namespace BSmtLib.Parser.Command

open BSmtLib (Version)

/--
Outcome of parsing a command with `CommandParser` (command, version switch, exit, or end of
file).
-/
inductive CommandOutcome where
  /-- A command other than `exit` and a version declaration was parsed, e.g. `(check-sat)`. -/
  | command
  /-- A version-switch command was parsed, e.g. `(set-info :smt-lib-version 2.6)`. -/
  | setVersion (version : Version)
  /-- The exit command `(exit)` was parsed. -/
  | exit
  /-- The end of the input was reached before a command. -/
  | endOfFile
  deriving BEq, Hashable, Repr

end BSmtLib.Parser.Command
