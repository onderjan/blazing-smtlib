module

public import BSmtLib.Parser.Category.SortedVar
public import BSmtLib.Parser.Category.Combinator

public section

/-!
# Datatypes

The parsers of the parts of datatype declarations: a sort declaration `(` ⟨symbol⟩ ⟨numeral⟩ `)`,
a constructor, and a datatype declaration with or without `par`.
-/

namespace BSmtLib.Parser.Command.Internal.Datatype

open BSmtLib.Grammar.Nodes BSmtLib.Handler
open BSmtLib.Parser.Category.Combinator BSmtLib.Parser.Category.Sort
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Parser.Category.SortedVar BSmtLib.Parser.Category.Token
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.Token.Internal
open BSmtLib.Lexicon.Value (Numeral Symbol)
open BSmtLib.Grammar.Multiple (SortedVars)
open BSmtLib (Version)
open BSmtLib.Parser.Internal (PM call syntaxError)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- The state of the parser of a sort declaration `(` ⟨symbol⟩ ⟨numeral⟩ `)`. -/
inductive SortDecState where
  | start
  | opened
  | arity (symbol : Symbol)
  | close (symbol : Symbol) (arity : Numeral)

/-- A step of the parser of a sort declaration. -/
def SortDecState.step (self : SortDecState) (token : Internal.Input) :
    PM H (Internal.Step SortDecState (Symbol × Numeral)) := do
  match self with
  | .start =>
    expectOpen token
    return .more .opened
  | .opened => return .more (.arity (← expectSymbol token))
  | .arity symbol => return .more (.close symbol (← expectNumeral token))
  | .close symbol digits =>
    expectClose token
    return .done (symbol, digits)

end

/-- The state of the parser of a datatype constructor `(` ⟨symbol⟩ ⟨selector_dec⟩∗ `)`. -/
inductive ConstructorState (HandledSort : Type) where
  | start
  | opened
  | selectors (symbol : Symbol)
      (state : ListState (SortedVarState HandledSort) (Symbol × HandledSort))

/-- The state of the parser of a datatype declaration. -/
inductive DatatypeState (HandledSort : Type) where
  | start
  /-- After its `(`: `par` or the `(` of the first constructor follows. -/
  | kind
  /-- Reading the sort parameters of the form with `par`. -/
  | parameters (state : ListState Unit Symbol)
  /-- After the parameters, before the `(` of the constructors. -/
  | constructorsOpen
  /-- Reading the constructors; in the form without `par`, their `)` ends the declaration. -/
  | constructors (parametric : Bool)
      (state : ListState (ConstructorState HandledSort) (Symbol × SortedVars HandledSort))
  /-- After the constructors of the form with `par`, before the declaration's `)`. -/
  | close (constructors : Array (Symbol × SortedVars HandledSort))

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- A step of the constructor parser; a selector is parsed as a sorted variable. -/
def constructorStep (version : Version) (self : ConstructorState (Handler.«Sort» H))
    (token : Internal.Input) :
    PM H (Internal.Step (ConstructorState (Handler.«Sort» H))
      (Symbol × SortedVars (Handler.«Sort» H))) := do
  match self with
  | .start =>
    expectOpen token
    return .more .opened
  | .opened => return .more (.selectors (← expectSymbol token) (ListState.closed .start))
  | .selectors symbol state =>
    match ← state.step .start (sortedVarStep version) none token with
    | .more state => return .more (.selectors symbol state)
    | .done selectors => return .done (symbol, Grammar.Multiple.NamedValues.Internal.new selectors)

/--
A step of the parser of a datatype declaration, `(` ⟨constructor_dec⟩+ `)` |
`(` `par` `(` ⟨symbol⟩+ `)` `(` ⟨constructor_dec⟩+ `)` `)`, which finishes with its
constructors at its `)`. The start comes when the tokens determine the sort parameters: at the
`)` of the parameters, or at the `(` of the first constructor, which shows that the form has no
`par`.
-/
@[specialize start]
def datatypeStep (start : Array Symbol → PM H Unit) (version : Version)
    (self : DatatypeState (Handler.«Sort» H)) (token : Internal.Input) :
    PM H (Internal.Step (DatatypeState (Handler.«Sort» H))
      (Array (Symbol × SortedVars (Handler.«Sort» H)))) := do
  match self with
  | .start =>
    expectOpen token
    return .more .kind
  | .kind =>
    match token with
    | .parenOpen =>
      start #[]
      -- the `(` is the first constructor's
      return .more (.constructors false
        { opened := true, outside := false, inner := .opened, items := #[] })
    | token =>
      if token.isWord .par then return .more (.parameters (ListState.paren ()))
      else syntaxError (.expected #[.reserved (.general .par), .token .parenOpen])
  | .parameters state =>
    match ← state.step () symbolStep none token with
    | .more state => return .more (.parameters state)
    | .done parameters =>
      if parameters.isEmpty then syntaxError (.empty .datatypeParameters)
      start parameters
      return .more .constructorsOpen
  | .constructorsOpen =>
    expectOpen token
    return .more (.constructors true (ListState.closed .start))
  | .constructors parametric state =>
    match ← state.step .start (constructorStep version) none token with
    | .more state => return .more (.constructors parametric state)
    | .done constructors =>
      if constructors.isEmpty then syntaxError (.empty .datatypeConstructors)
      if parametric then return .more (.close constructors)
      else return .done constructors
  | .close constructors =>
    expectClose token
    return .done constructors

end

end BSmtLib.Parser.Command.Internal.Datatype
