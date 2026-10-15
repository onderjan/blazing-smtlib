module

public import BSmtLib.Facts.PublicApi.Adapters
public import BSmtLibSpec.Grammar.File

@[expose] public section

/-!
# Versions of the specification and of the library

The two releases' names in the specification and in the library, for the theorems that speak of
the specification.
-/

namespace BSmtLib.Facts.PublicApi.Adapters.Builder

/-- The library's version for a version of the specification: the same release. -/
def libVersion : BSmtLibSpec.Lexicon.Version → Token.Version
  | .v2_0 => .v2_0
  | .v2_5 => .v2_5
  | .v2_6 => .v2_6
  | .v2_7 => .v2_7

end BSmtLib.Facts.PublicApi.Adapters.Builder
