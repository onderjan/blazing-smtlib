module

public import BSmtLib.Parser

public section

/-!
# Patterns

The parser of the pattern of a case of `match`.
-/

namespace BSmtLib.Parser.Category.Pattern

open BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Token (Version)

/-- The state of the pattern parser. -/
inductive PatternState where
  | start
  /-- After the `(` of a constructor pattern. -/
  | opened
  /-- After the constructor, reading its arguments up to the `)`. -/
  | arguments (constructor : Symbol) (arguments : Array SymbolOrWildcard)

namespace PatternState

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- The wildcard `_` is a pattern from 2.7 on. -/
def wildcardAllowed (version : Version) : Bool :=
  version ≥ .v2_7

/-- The symbol or wildcard the token is, if it is one in the version. -/
def symbolOrWildcard? (version : Version) (token : Internal.Input) : Option SymbolOrWildcard :=
  match token with
  | .symbol symbol => some (.symbol symbol)
  | token => if wildcardAllowed version && token.isWord .underscore then some .wildcard else none

/--
A step of the pattern parser: ⟨symbol_⟩ | `(` ⟨symbol⟩ ⟨symbol_⟩+ `)`. Patterns are not handled.
-/
def step (version : Version) (self : PatternState) (token : Internal.Input) :
    PM H (Internal.Step PatternState Pattern) :=
  match self with
  | .start =>
    match token with
    | .parenOpen => pure (.more .opened)
    | token =>
      match symbolOrWildcard? version token with
      | some symbol => pure (.done (.single symbol))
      | none =>
        syntaxError (if wildcardAllowed version then .expectedSymbolUnderscoreOrParenOpen
          else .expectedSymbolOrParenOpen)
  | .opened =>
    match token with
    | .symbol constructor => pure (.more (.arguments constructor #[]))
    | _ => syntaxError .expectedSymbol
  | .arguments constructor found =>
    match token with
    | .parenClose =>
      if found.isEmpty then syntaxError .emptyPatternArguments
      else pure (.done (.constructor constructor found))
    | token =>
      match symbolOrWildcard? version token with
      | some argument => pure (.more (.arguments constructor (found.push argument)))
      | none =>
        syntaxError (if wildcardAllowed version then .expectedSymbolOrUnderscore
          else .expectedSymbol)

end PatternState

end BSmtLib.Parser.Category.Pattern
