import ParserSpec.Grammar

/-!
# Reading a script

How the characters of a script read as commands: each command is lexed and parsed in the
version in force where it starts.
-/

namespace ParserSpec

open LexerSpec

/-- The input reads as the tokens and ends with the last of them: no whitespace follows. -/
def ReadsExactly (version : Version) (offset : Nat) (input : Chars) (tokens : List Token) :
    Prop :=
  ReadsFrom version offset input tokens ∧
    ∃ last, tokens.getLast? = some last ∧ last.offset + last.text.length = offset + input.length

/-- The command is a version declaration: `set-info` with the attribute `:smt-lib-version`. -/
def Tree.Command.DeclaresVersion (command : Tree.Command) : Prop :=
  ∃ value, command = .setInfo ⟨chars "smt-lib-version", value⟩

/--
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
`ScriptReads version input commands`: starting in the version, the input reads as the
commands.
-/
def ScriptReads (version : Version) (input : Chars) (commands : List Tree.Command) : Prop :=
  ScriptReadsFrom version 0 input commands

/-! ## Version policies -/

/-- The version whose number the decimal is. -/
def versionOfNumber (decimal : Chars) : Option Version :=
  [Version.v2_0, .v2_5, .v2_6, .v2_7].find? (·.number = decimal)

/-- The version that the command declares, if it is a version declaration. -/
def Tree.Command.declaredVersion : Tree.Command → Option Version
  | .setInfo ⟨keyword, some (.constant (.decimal decimal))⟩ =>
    if keyword = chars "smt-lib-version" then versionOfNumber decimal else none
  | _ => none

/--
A policy on the versions that a script declares: which versions it may declare, and how many
declarations it may make, without a limit if there is none.
-/
structure VersionPolicy where
  allowed : List Version
  maxDeclarations : Option Nat

/-- The policy that restricts nothing: every version may be declared, any number of times. -/
def VersionPolicy.unrestricted : VersionPolicy :=
  { allowed := [.v2_0, .v2_5, .v2_6, .v2_7], maxDeclarations := none }

/--
`ScriptReadsUnder policy version input commands`: starting in the version, the input reads as
the commands, and its version declarations keep to the policy. A policy only restricts
`ScriptReads`, which is the reading under `VersionPolicy.unrestricted`.
-/
def ScriptReadsUnder (policy : VersionPolicy) (version : Version) (input : Chars)
    (commands : List Tree.Command) : Prop :=
  ScriptReads version input commands ∧
    (∀ declared ∈ commands.filterMap Tree.Command.declaredVersion, declared ∈ policy.allowed) ∧
    ∀ limit, policy.maxDeclarations = some limit →
      (commands.filterMap Tree.Command.declaredVersion).length ≤ limit

end ParserSpec
