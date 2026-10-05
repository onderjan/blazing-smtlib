import BSmtLib.Spec.Grammar

/-!
# Version policies

A policy restricts which versions a script may declare, and how often. The standard has no
such policies; they are this library's, and only restrict the reading of a script.
-/

namespace BSmtLib.Spec.Parser

open BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar

/-- The version whose number the decimal is. -/
def versionOfNumber (decimal : Chars) : Option Version :=
  [Version.v2_0, .v2_5, .v2_6, .v2_7].find? (·.number = decimal)

/-- The version that the command declares, if it is a version declaration. -/
def _root_.BSmtLib.Spec.Grammar.Tree.Command.declaredVersion : Tree.Command → Option Version
  | .setInfo ⟨keyword, some (.constant (.decimal decimal))⟩ =>
    if keyword = chars "smt-lib-version" then versionOfNumber decimal else none
  | _ => none

/--
Extension: version policies are this library's; the standard has none.

A policy on the versions that a script declares: which versions it may declare, and how many
declarations it may make, without a limit if there is none.
-/
structure VersionPolicy where
  allowed : List Version
  maxDeclarations : Option Nat

/--
Extension: as `VersionPolicy`.

The policy that restricts nothing: every version may be declared, any number of times.
-/
def VersionPolicy.unrestricted : VersionPolicy :=
  { allowed := [.v2_0, .v2_5, .v2_6, .v2_7], maxDeclarations := none }

/--
Extension: as `VersionPolicy`.

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

end BSmtLib.Spec.Parser
