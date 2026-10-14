module

public import BSmtLib.Token

public section

/-!
# How a command ended

The outcome of the command parser at the end of a command (`SmtCommandOutcome`).
-/

namespace BSmtLib.Parser.Command

open BSmtLib.Token (Version)

/-- How a command ended (`SmtCommandOutcome`). -/
inductive CommandOutcome where
  /-- A command ended. -/
  | command
  /-- A version declaration ended, handled as `set-info`; a script switches to the version. -/
  | setVersion (version : Version)
  /-- `exit` ended. -/
  | exit
  /-- The input ended between commands. -/
  | endOfInput

end BSmtLib.Parser.Command
