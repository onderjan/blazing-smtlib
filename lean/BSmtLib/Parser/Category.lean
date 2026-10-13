import BSmtLib.Parser.Framework

/-!
# The category parsers

One parser for each syntactic category that terms are built from, each a state machine stepped
by single tokens (see `Parser.Framework`). A parser that a construct enters after the construct
has taken the first tokens of it is started in the state after those tokens.
-/

namespace BSmtLib.Parser

/-! ## Identifiers -/

/-- The state of the identifier parser. -/
inductive IdentState where
  /-- Before the identifier. -/
  | start
  /-- After its `(`, before the `_`. -/
  | opened
  /-- After `(` `_`, before its symbol. -/
  | afterUnderscore
  /-- After its symbol, reading its indices up to the `)`. -/
  | indices (symbol : Symbol) (indices : Array Index)

namespace IdentState

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A step of the identifier parser: a symbol is an identifier by itself; `(` `_` ⟨symbol⟩
⟨index⟩+ `)` an indexed one. A symbol is an index from 2.5 on.
-/
def step (version : Version) (self : IdentState) (token : Input) :
    PM H (Step IdentState Identifier) :=
  match self, token with
  | .start, .symbol symbol => pure (.done ⟨symbol, #[]⟩)
  | .start, .parenOpen => pure (.more .opened)
  | .start, _ => syntaxError .expectedIdent
  | .opened, token =>
    if token.isWord .underscore then pure (.more .afterUnderscore)
    else syntaxError .expectedUnderscore
  | .afterUnderscore, .symbol symbol => pure (.more (.indices symbol #[]))
  | .afterUnderscore, _ => syntaxError .expectedSymbol
  | .indices symbol found, .parenClose =>
    if found.isEmpty then syntaxError .emptyIdentIndices
    else pure (.done ⟨symbol, found⟩)
  | .indices symbol found, .constant (.numeral digits) =>
    pure (.more (.indices symbol (found.push (.numeral digits))))
  | .indices symbol found, .symbol index =>
    if version ≥ .v2_5 then pure (.more (.indices symbol (found.push (.symbol index))))
    else syntaxError .expectedIndexOrCloseParen
  | .indices _ _, _ => syntaxError .expectedIndexOrCloseParen

end IdentState

/-! ## Sorts -/

/-- What the sort parser is doing at its innermost open sort. -/
inductive SortMode where
  /-- Before a sort: the sort itself, or the next argument of the innermost application. -/
  | start
  /-- After the `(` of a sort, before its head. -/
  | opened
  /-- Reading a sort that is an indexed identifier. -/
  | identOnly (ident : IdentState)
  /-- Reading the indexed identifier at the head of an application. -/
  | startingIdent (ident : IdentState)

/-- An application of a sort, open: its head and the argument sorts handled so far. -/
structure SortLevel (HandledSort : Type) where
  head : Identifier
  arguments : Array HandledSort

/-- The state of the sort parser: its mode, and the open applications, innermost first. -/
structure SortState (HandledSort : Type) where
  mode : SortMode
  levels : List (SortLevel HandledSort)

/-- The sort parser before a sort. -/
def SortState.init {HandledSort : Type} : SortState HandledSort :=
  { mode := .start, levels := [] }

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- A sort is complete: it is handled, and is the result or the next argument. -/
def sortComplete (levels : List (SortLevel (Handler.«Sort» H))) (head : Identifier)
    (arguments : Array (Handler.«Sort» H)) :
    PM H (Step (SortState (Handler.«Sort» H)) (Handler.«Sort» H)) := do
  let sort ← call (Handler.handleSort head arguments)
  match levels with
  | [] => return .done sort
  | level :: outer =>
    return .more
      { mode := .start, levels := { level with arguments := level.arguments.push sort } :: outer }

/--
A step of the sort parser: ⟨identifier⟩ | `(` ⟨identifier⟩ ⟨sort⟩+ `)`. Each sort is handled
at its last token, its arguments before it.
-/
def sortStep (version : Version) (self : SortState (Handler.«Sort» H)) (token : Input) :
    PM H (Step (SortState (Handler.«Sort» H)) (Handler.«Sort» H)) :=
  match self.mode with
  | .start =>
    match token with
    | .symbol name => sortComplete self.levels ⟨name, #[]⟩ #[]
    | .parenOpen => pure (.more { self with mode := .opened })
    | .parenClose =>
      match self.levels with
      | [] => syntaxError .expectedSort
      | level :: outer =>
        if level.arguments.isEmpty then syntaxError .emptySortApplication
        else sortComplete outer level.head level.arguments
    | _ => syntaxError .expectedSort
  | .opened =>
    match token with
    | .symbol name =>
      pure (.more { mode := .start, levels := ⟨⟨name, #[]⟩, #[]⟩ :: self.levels })
    | .parenOpen => pure (.more { self with mode := .startingIdent .opened })
    | token =>
      if token.isWord .underscore then
        pure (.more { self with mode := .identOnly .afterUnderscore })
      else syntaxError .expectedSortInner
  | .identOnly ident => do
    match ← ident.step version token with
    | .more ident => return .more { self with mode := .identOnly ident }
    | .done head => sortComplete self.levels head #[]
  | .startingIdent ident => do
    match ← ident.step version token with
    | .more ident => return .more { self with mode := .startingIdent ident }
    | .done head => return .more { mode := .start, levels := ⟨head, #[]⟩ :: self.levels }

end

/-! ## S-expressions -/

/-- The state of the s-expression parser: the items of the open lists, innermost first. -/
abbrev SExprState (HandledSExpr : Type) := List (Array HandledSExpr)

/-- An s-expression is complete: it is the result, or the next item of the innermost list. -/
def sExprComplete {HandledSExpr : Type} (levels : SExprState HandledSExpr)
    (sExpr : HandledSExpr) : Step (SExprState HandledSExpr) HandledSExpr :=
  match levels with
  | [] => .done sExpr
  | items :: outer => .more (items.push sExpr :: outer)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A step of the s-expression parser: an atom is handled at its token, a list at its `)`, its items
before it. A reserved word is an s-expression from 2.6 on.
-/
def sExprStep (version : Version) (self : SExprState (Handler.SExpr H)) (token : Input) :
    PM H (Step (SExprState (Handler.SExpr H)) (Handler.SExpr H)) := do
  let atom ← match token with
    | .parenOpen => return .more (#[] :: self)
    | .parenClose =>
      match self with
      | [] => syntaxError .expectedSExpr
      | items :: outer => do
        let list ← call (Handler.handleSExpr (.list items))
        return sExprComplete outer list
    | .constant constant => pure (SExprNode.constant constant)
    | .symbol symbol => pure (.symbol symbol)
    | .keyword name => pure (.keyword name)
    | .reserved word =>
      if version ≥ .v2_6 then pure (.reserved word) else syntaxError .expectedSExpr
    | _ => syntaxError .expectedSExpr
  let handled ← call (Handler.handleSExpr atom)
  return sExprComplete self handled

end

/-! ## Attributes -/

/-- What the attribute parser is doing. -/
inductive AttributeMode (HandledSExpr : Type) where
  /-- Before an attribute's keyword, or the `)` after the attributes. -/
  | start
  /-- After an attribute's keyword: its value, the next keyword or the `)` follows. -/
  | afterName (keyword : KeywordView)
  /-- In the list value of an attribute: its items so far, and whether the parser is between
  them. -/
  | inside (keyword : KeywordView) (items : Array HandledSExpr) (sExpr : SExprState HandledSExpr)
      (outside : Bool)

/-- The state of the attribute parser: its mode, and the attributes handled so far. -/
structure AttributeState (HandledSExpr HandledAttribute : Type) where
  mode : AttributeMode HandledSExpr
  attributes : Array HandledAttribute

/-- The attribute parser before the attributes. -/
def AttributeState.init {HandledSExpr HandledAttribute : Type} :
    AttributeState HandledSExpr HandledAttribute :=
  { mode := .start, attributes := #[] }

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A step of the attribute parser, for attributes up to the `)` after them; with `single`, for
exactly one. An attribute is handled when the tokens determine it: an attribute with a value
at the value's last token; one without, at the token after its keyword, the next keyword or the
`)`. A list value is handed over as its items.
-/
def attributeStep (single : Bool) (version : Version)
    (self : AttributeState (Handler.SExpr H) (Handler.Attribute H)) (token : Input) :
    PM H (Step (AttributeState (Handler.SExpr H) (Handler.Attribute H))
      (Array (Handler.Attribute H))) := do
  let finish (attributes : Array (Handler.Attribute H)) :
      PM H (Step (AttributeState (Handler.SExpr H) (Handler.Attribute H))
        (Array (Handler.Attribute H))) :=
    if single && attributes.isEmpty then syntaxError .expectedAttribute
    else pure (.done attributes)
  match self.mode with
  | .start =>
    if single && !self.attributes.isEmpty then
      expectClose token
      return ← finish self.attributes
    match token with
    | .parenClose => finish self.attributes
    | .keyword name => return .more { self with mode := .afterName name }
    | _ => syntaxError .expectedAttribute
  | .afterName keyword =>
    let valued (value : AttributeValueNode (Handler.SExpr H)) := do
      let handled ← call (Handler.handleAttribute keyword (some value))
      return .more { mode := .start, attributes := self.attributes.push handled }
    match token with
    | .symbol symbol => valued (.symbol symbol)
    | .constant constant => valued (.constant constant)
    | .parenOpen => return .more { self with mode := .inside keyword #[] [] true }
    | .parenClose =>
      let handled ← call (Handler.handleAttribute keyword none)
      finish (self.attributes.push handled)
    | .keyword name =>
      -- a single attribute is followed by the `)`: reject the keyword before handing over
      if single then syntaxError (.expectedToken #[.parenClose])
      let handled ← call (Handler.handleAttribute keyword none)
      return .more { mode := .afterName name, attributes := self.attributes.push handled }
    | _ => syntaxError .expectedAttribute
  | .inside keyword items sExpr outside =>
    if outside then
      if let .parenClose := token then
        let handled ← call (Handler.handleAttribute keyword (some (.list items)))
        return .more { mode := .start, attributes := self.attributes.push handled }
    match ← sExprStep version sExpr token with
    | .more sExpr => return .more { self with mode := .inside keyword items sExpr false }
    | .done item => return .more { self with mode := .inside keyword (items.push item) [] true }

end

/-! ## Patterns -/

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
def symbolOrWildcard? (version : Version) (token : Input) : Option SymbolOrWildcard :=
  match token with
  | .symbol symbol => some (.symbol symbol)
  | token => if wildcardAllowed version && token.isWord .underscore then some .wildcard else none

/--
A step of the pattern parser: ⟨symbol_⟩ | `(` ⟨symbol⟩ ⟨symbol_⟩+ `)`. Patterns are not handled.
-/
def step (version : Version) (self : PatternState) (token : Input) :
    PM H (Step PatternState Pattern) :=
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

/-! ## Qualified identifiers -/

/-- The state of the qualified identifier parser. -/
inductive QualIdentState (HandledSort : Type) where
  | start
  /-- After its `(`: `_` or `as` follows. -/
  | opened
  /-- Reading an indexed identifier, unqualified. -/
  | indexed (ident : IdentState)
  /-- After `(` `as`, reading the identifier. -/
  | qualifiedIdent (ident : IdentState)
  /-- After the identifier of `(as`, reading its sort. -/
  | sort (identifier : Identifier) (sort : SortState HandledSort)
  /-- After the sort, before the `)`. -/
  | close (identifier : Identifier) (sort : HandledSort)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A step of the qualified identifier parser: ⟨identifier⟩ | `(` `as` ⟨identifier⟩ ⟨sort⟩ `)`. Its
sort is handled at the sort's last token; the identifier is not handled.
-/
def qualIdentStep (version : Version) (self : QualIdentState (Handler.«Sort» H)) (token : Input) :
    PM H (Step (QualIdentState (Handler.«Sort» H)) (Identifier × Option (Handler.«Sort» H))) := do
  match self with
  | .start =>
    match token with
    | .symbol symbol => return .done (⟨symbol, #[]⟩, none)
    | .parenOpen => return .more .opened
    | _ => syntaxError .expectedIdent
  | .opened =>
    if token.isWord .underscore then return .more (.indexed .afterUnderscore)
    else if token.isWord .as then return .more (.qualifiedIdent .start)
    else syntaxError .expectedUnderscoreOrAs
  | .indexed ident =>
    match ← ident.step version token with
    | .more ident => return .more (.indexed ident)
    | .done identifier => return .done (identifier, none)
  | .qualifiedIdent ident =>
    match ← ident.step version token with
    | .more ident => return .more (.qualifiedIdent ident)
    | .done identifier => return .more (.sort identifier .init)
  | .sort identifier sort =>
    match ← sortStep version sort token with
    | .more sort => return .more (.sort identifier sort)
    | .done sort => return .more (.close identifier sort)
  | .close identifier sort =>
    expectClose token
    return .done (identifier, some sort)

end

/-! ## Sorted variables -/

/-- The state of the sorted variable parser. -/
inductive SortedVarState (HandledSort : Type) where
  | start
  /-- After its `(`, before its symbol. -/
  | opened
  /-- Reading its sort. -/
  | sort (symbol : Symbol) (sort : SortState HandledSort)
  /-- After its sort, before the `)`. -/
  | close (symbol : Symbol) (sort : HandledSort)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- A step of the sorted variable parser: `(` ⟨symbol⟩ ⟨sort⟩ `)`. -/
def sortedVarStep (version : Version) (self : SortedVarState (Handler.«Sort» H)) (token : Input) :
    PM H (Step (SortedVarState (Handler.«Sort» H)) (Symbol × Handler.«Sort» H)) := do
  match self with
  | .start =>
    expectOpen token
    return .more .opened
  | .opened => return .more (.sort (← expectSymbol token) .init)
  | .sort symbol sort =>
    match ← sortStep version sort token with
    | .more sort => return .more (.sort symbol sort)
    | .done sort => return .more (.close symbol sort)
  | .close symbol sort =>
    expectClose token
    return .done (symbol, sort)

end

end BSmtLib.Parser
