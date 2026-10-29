module

public import BSmtLib.Parser

public section

/-!
# Patterns

The parser of the pattern of a case of `match`.
-/

namespace BSmtLib.Parser.Category.Pattern

open BSmtLib.Lexicon.Value (Symbol)
open BSmtLib.Grammar.Nodes BSmtLib.Handler
open BSmtLib (Version)
open BSmtLib.Parser.Internal (PM call syntaxError)

namespace Internal

/-- The state of the pattern parser. -/
inductive PatternState where
  | start
  /-- After the `(` of a constructor pattern. -/
  | opened
  /-- After the constructor, reading its arguments up to the `)`. -/
  | arguments (constructor : Symbol) (arguments : Array SimplePattern)

namespace PatternState

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- The wildcard `_` is a pattern from 2.7 on. -/
def wildcardAllowed (version : Version) : Bool :=
  version ≥ .v2_7

/-- The symbol or wildcard the token is, if it is one in the version. -/
def symbolOrWildcard? (version : Version) (token : Internal.Input) : Option SimplePattern :=
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
      | some symbol => pure (.done (.simple symbol))
      | none =>
        syntaxError (if wildcardAllowed version
          then (.expected #[.symbol, .reserved (.general .underscore), .token .parenOpen])
          else (.expected #[.symbol, .token .parenOpen]))
  | .opened =>
    match token with
    | .symbol constructor => pure (.more (.arguments constructor #[]))
    | _ => syntaxError (.expected #[.symbol])
  | .arguments constructor found =>
    match token with
    | .parenClose =>
      if hne : found.isEmpty then syntaxError (.empty .patternArguments)
      else pure (.done (.application
        ⟨constructor, found, PatternApplication.Internal.size_pos hne⟩))
    | token =>
      match symbolOrWildcard? version token with
      | some argument => pure (.more (.arguments constructor (found.push argument)))
      | none =>
        syntaxError (if wildcardAllowed version
          then (.expected #[.symbol, .reserved (.general .underscore)])
          else (.expected #[.symbol]))

end PatternState

end Internal

/-- Parses a simple match pattern. -/
structure SimplePatternParser where
  private mk ::

/-- Creates the parser. -/
def SimplePatternParser.new : SimplePatternParser := {}

instance : Inhabited SimplePatternParser := ⟨.new⟩

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/- LEAN: not an instance, as the parser does not name its handler, so that instance search could
not find the handler; the parser's `parse` puts it in place, as for the token parsers. -/
/-- The steps, with the handler `H`, of the simple pattern parser: it finishes at its first token,
which must be a simple pattern. -/
@[instance_reducible]
def Internal.simplePatternByToken (H : Type) {m : Type → Type} [Monad m] [Handler H m] :
    Internal.ParseByToken SimplePatternParser H m (Handler.Error H) SimplePatternBuf where
  arrive _ _ := pure ()
  step version _ token :=
    match Internal.PatternState.symbolOrWildcard? version token with
    | some pattern => pure (.done pattern.intoOwned)
    | none =>
      -- the underscore wildcard is not allowed in every version
      syntaxError (if Internal.PatternState.wildcardAllowed version
        then (.expected #[.symbol, .reserved (.general .underscore)])
        else (.expected #[.symbol]))
  reset self := self

instance : Parse SimplePatternParser H m (Handler.Error H) SimplePatternBuf where
  parse parser state cursor :=
    letI := Internal.simplePatternByToken H
    Internal.parseByToken parser state cursor

end

/- LEAN: as Rust's, the parser names its handler, whose types it does not use. -/
/-- Parses a match pattern. -/
structure PatternParser (H : Type) where
  private mk ::
  private state : Internal.PatternState

/-- Creates the parser. -/
def PatternParser.new {H : Type} : PatternParser H := ⟨.start⟩

instance {H : Type} : Inhabited (PatternParser H) := ⟨.new⟩

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

@[no_expose]
instance Internal.instParseByTokenPatternParser :
    Internal.ParseByToken (PatternParser H) H m (Handler.Error H) PatternBuf where
  arrive _ _ := pure ()
  step version parser token := do
    match ← parser.state.step version token with
    | .more state => return .more ⟨state⟩
    | .done result => return .done result.intoOwned
  reset _ := .new

instance : Parse (PatternParser H) H m (Handler.Error H) PatternBuf where
  parse := Internal.parseByToken

end

end BSmtLib.Parser.Category.Pattern
