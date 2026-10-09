import BSmtLib.Spec.Grammar

/-!
# Version policies

A policy restricts which versions a script may declare, and how often. The standard has no
such policies; they are this library's. A parser checks a version declaration against its
policy after the declaration's `set-info`, when the declaration is complete; a declaration that
breaks the policy stops the parse there.
-/

namespace BSmtLib.Spec.Parser

open BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar

/--
A policy on the versions that a script declares: which versions it may declare, and how many
declarations it may make, without a limit if there is none.
-/
structure VersionPolicy where
  allowed : List Version
  maxDeclarations : Option Nat

/--
The policy that restricts nothing: every version may be declared, any number of times.
-/
def VersionPolicy.unrestricted : VersionPolicy :=
  { allowed := [.v2_0, .v2_5, .v2_6, .v2_7], maxDeclarations := none }

/-- How a version declaration breaks a version policy. -/
inductive PolicyViolation where
  /-- The version is not among those the policy allows. -/
  | notAllowed (version : Version)
  /-- The script has already made as many declarations as the policy allows. -/
  | tooManyDeclarations (limit : Nat)

/--
The check of a declaration of the version against the policy, given the number of declarations
the script made before it.
-/
def VersionPolicy.check (policy : VersionPolicy) (declarations : Nat) (version : Version) :
    Except PolicyViolation Unit :=
  if version ∉ policy.allowed then .error (.notAllowed version)
  else match policy.maxDeclarations with
    | some limit => if limit ≤ declarations then .error (.tooManyDeclarations limit) else .ok ()
    | none => .ok ()

end BSmtLib.Spec.Parser
