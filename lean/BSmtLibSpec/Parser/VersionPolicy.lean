module

public import BSmtLibSpec.Grammar

@[expose] public section

/-!
# Version policies

A policy restricts which versions a script may declare, and how often. The standard has no
such policies; they are this library's. A parser checks a version declaration against its
policy after the declaration's `set-info`, when the declaration is complete; a declaration that
breaks the policy stops the parse there.
-/

namespace BSmtLibSpec.Parser

open BSmtLibSpec.Lexicon BSmtLibSpec.Grammar

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

/--
The syntax errors with which a parse rejects a version declaration.

A version that the policy does not allow and a version that the producer refuses to switch to
are the same error: what refused the version is not told.
-/
inductive VersionPolicy.Error where
  /-- The version is not among those the policy allows, or the producer refused it
  (`UnsupportedVersion`). -/
  | unsupportedVersion
  /-- The script has already made as many declarations as the policy allows
  (`TooManyVersionDeclarations`). -/
  | tooManyDeclarations (limit : Nat)

/--
The check of a declaration of the version against the policy, given the number of declarations
the script made before it: first the number of declarations, then the version.

A declaration that breaks both rules is rejected for the number of declarations.
-/
def VersionPolicy.check (policy : VersionPolicy) (declarations : Nat) (version : Version) :
    Except VersionPolicy.Error Unit :=
  match policy.maxDeclarations with
  | some limit =>
    if limit ≤ declarations then .error (.tooManyDeclarations limit)
    else if version ∉ policy.allowed then .error .unsupportedVersion else .ok ()
  | none => if version ∉ policy.allowed then .error .unsupportedVersion else .ok ()

end BSmtLibSpec.Parser
