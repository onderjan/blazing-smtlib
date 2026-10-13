import BSmtLibSpec.Lexicon.Properties

/-!
# The reserved words as the standard lists them

Each version of the standard lists its reserved words in full. These lists are transcribed
here and checked against the spec, which builds the reserved words of each version from what
the version adds. Not trusted: the lists are a second transcription, and the theorems show
that the two agree.
-/

namespace BSmtLib.SpecChecks.Lexicon

open BSmtLibSpec BSmtLibSpec.Lexicon
open BSmtLibSpec.Lexicon.Properties
open BSmtLibSpec.Regex (Chars chars)

/-- The basic set of reserved words, as each version lists it. -/
def listedBasicReservedWords : Version → List String
  | .v2_0 => ["par", "NUMERAL", "DECIMAL", "STRING", "_", "!", "as", "let", "forall", "exists"]
  | .v2_5 => ["BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING",
      "_", "!", "as", "let", "exists", "forall", "par"]
  | .v2_6 => ["BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING",
      "_", "!", "as", "let", "exists", "forall", "match", "par"]
  | .v2_7 => ["BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING",
      "_", "!", "as", "lambda", "let", "exists", "forall", "match", "par"]

/-- The command names, as each version lists them, with `define-funs-rec` added from 2.5 on. -/
def listedCommandNames : Version → List String
  | .v2_0 => ["set-logic", "set-option", "set-info", "declare-sort", "define-sort",
      "declare-fun", "define-fun", "push", "pop", "assert", "check-sat", "get-assertions",
      "get-proof", "get-unsat-core", "get-value", "get-assignment", "get-option", "get-info",
      "exit"]
  | .v2_5 => ["assert", "check-sat", "check-sat-assuming", "declare-const", "declare-fun",
      "declare-sort", "define-fun", "define-fun-rec", "define-funs-rec", "define-sort", "echo",
      "exit", "get-assertions", "get-assignment", "get-info", "get-model", "get-option",
      "get-proof", "get-unsat-assumptions", "get-unsat-core", "get-value", "pop", "push",
      "reset", "reset-assertions", "set-info", "set-logic", "set-option"]
  | .v2_6 => ["assert", "check-sat", "check-sat-assuming", "declare-const",
      "declare-datatype", "declare-datatypes", "declare-fun", "declare-sort", "define-fun",
      "define-fun-rec", "define-funs-rec", "define-sort", "echo", "exit", "get-assertions",
      "get-assignment", "get-info", "get-model", "get-option", "get-proof",
      "get-unsat-assumptions", "get-unsat-core", "get-value", "pop", "push", "reset",
      "reset-assertions", "set-info", "set-logic", "set-option"]
  | .v2_7 => ["assert", "check-sat", "check-sat-assuming", "declare-const",
      "declare-datatype", "declare-datatypes", "declare-fun", "declare-sort",
      "declare-sort-parameter", "define-const", "define-fun", "define-fun-rec",
      "define-funs-rec", "define-sort", "echo", "exit", "get-assertions", "get-assignment",
      "get-info", "get-model", "get-option", "get-proof", "get-unsat-assumptions",
      "get-unsat-core", "get-value", "pop", "push", "reset", "reset-assertions", "set-info",
      "set-logic", "set-option"]

theorem basicReservedWords_listed (version : Version) :
    (basicReservedWords version).Perm (listedBasicReservedWords version) := by
  cases version <;> decide

theorem commandNames_listed (version : Version) :
    (commandNames version).Perm (listedCommandNames version) := by
  cases version <;> decide

/-- No reserved word is listed twice. -/
theorem reservedWords_nodup (version : Version) :
    (basicReservedWords version ++ commandNames version).Nodup := by
  cases version <;> decide

end BSmtLib.SpecChecks.Lexicon
