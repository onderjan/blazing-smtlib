module

public import BSmtLib.Parser.Internal.Fused.Basic

public section

/-!
# The category parsers of the fused reader

The steps of the port's category parsers that the fused reader fuses (identifiers, sorts, lists
of sorts, sorted variables, signatures, and qualified identifiers in parentheses without `as`),
on the token's category, reading its content only where they need it. Each returns what it did
through a value that its caller, into which it is inlined, takes apart at once, so that the value
is never built.
-/

namespace BSmtLib.Parser.Internal.Fused.Category

open BSmtLib.Multiple (FunctionSignature)
open BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Parser.Internal.Fused.Basic
open BSmtLib.Parser.Category.Combinator.Internal (ListState)
open BSmtLib.Parser.Category.Ident.Internal (IdentState)
open BSmtLib.Parser.Category.QualifiedIdent.Internal (QualIdentState)
open BSmtLib.Parser.Category.Sort.Internal (SortState SortLevel)
open BSmtLib.Parser.Category.SortedVar.Internal (SortedVarState)
open BSmtLib.Parser.Command.Internal.Function (SignatureState)
open BSmtLib.Plain (Symbol Numeral)
open BSmtLib.Token (BatchTag BatchCursor TokenCategory Version)
open BSmtLib.Token.Reserved (GeneralReserved)

/-- A step of a category parser that calls no handler: on with the state, done with the
result, or a syntax error. -/
inductive PureOutcome (σ ρ : Type) where
  | more (state : σ)
  | done (result : ρ)
  | error (kind : SyntaxErrorKind)

/-- A step of a category parser that calls the handler, with the handler after it. -/
inductive HandledOutcome (H σ ρ ε : Type) where
  | more (h : H) (state : σ)
  | done (h : H) (result : ρ)
  | error (h : H) (cause : ε)

/-! ## Tokens by category -/

section

variable {batch : BatchTag}

/-- The symbol the token is in the version: an unquoted symbol that is not reserved in it, or a
quoted symbol. -/
@[inline]
def symbolOf? (version : Version) (category : TokenCategory) (next : BatchCursor batch)
    (token : Token batch) : Option Symbol :=
  match category with
  | .unquotedSymbol =>
    let content := contentOf next token
    match reservedAt? version next token with
    | none => some (Symbol.Internal.newUnchecked false content)
    | some _ => none
  | .quotedSymbol => some (Symbol.Internal.newUnchecked true (contentOf next token))
  | _ => none

/-- Whether the token is the general reserved word in the version. -/
@[inline]
def isWord (version : Version) (category : TokenCategory) (next : BatchCursor batch)
    (token : Token batch) (word : GeneralReserved) : Bool :=
  match category with
  | .unquotedSymbol =>
    match reservedAt? version next token with
    | some (.general w) => w == word
    | _ => false
  | _ => false

end

/-! ## Identifiers -/

/-- `IdentState.step` on the token's category. -/
@[inline]
def identStep {batch : BatchTag} (version : Version) (self : IdentState)
    (category : TokenCategory) (next : BatchCursor batch) (token : Token batch) :
    PureOutcome IdentState Ident :=
  match self with
  | .start =>
    match category with
    | .parenOpen => .more .opened
    | _ =>
      match symbolOf? version category next token with
      | some symbol => .done ⟨symbol, #[]⟩
      | none => .error (.expected #[.ident])
  | .opened =>
    if isWord version category next token .underscore then .more .afterUnderscore
    else .error (.expected #[.reserved (.general .underscore)])
  | .afterUnderscore =>
    match symbolOf? version category next token with
    | some symbol => .more (.indices symbol #[])
    | none => .error (.expected #[.symbol])
  | .indices symbol found =>
    match category with
    | .parenClose =>
      if found.isEmpty then .error (.empty .identIndices) else .done ⟨symbol, found⟩
    | .numeral =>
      .more (.indices symbol
        (found.push (.numeral (Numeral.Internal.newUnchecked (contentOf next token)))))
    | _ =>
      match symbolOf? version category next token with
      | some index =>
        if version ≥ .v2_5 then .more (.indices symbol (found.push (.symbol index)))
        else .error (.expected #[.index, .token .parenClose])
      | none => .error (.expected #[.index, .token .parenClose])

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-! ## Sorts -/

/-- The sort state of the handler. -/
abbrev SortStateOf (H : Type) {m : Type → Type} [Handler H m] := SortState (Handler.«Sort» H)

/-- The outcome of a sort step. -/
abbrev SortOutcome (H : Type) {m : Type → Type} [Handler H m] :=
  HandledOutcome H (SortStateOf H) (Handler.«Sort» H) (Cause H)

/-- `sortComplete`: the sort is handled, and is the result or the next argument. -/
@[inline]
def sortComplete (h : H) (levels : List (SortLevel (Handler.«Sort» H))) (head : Ident)
    (arguments : Array (Handler.«Sort» H)) : m (SortOutcome H) := do
  match ← runHandler (Handler.handleSort head (.new arguments)) h with
  | (.error e, h) => return .error h (.handler e)
  | (.ok sort, h) =>
    match levels with
    | [] => return .done h sort
    | level :: outer =>
      return .more h
        { mode := .start, levels := { level with arguments := level.arguments.push sort } :: outer }

/-- `sortStep` on the token's category. -/
@[inline]
def sortStep {batch : BatchTag} (version : Version) (h : H) (self : SortStateOf H)
    (category : TokenCategory) (next : BatchCursor batch) (token : Token batch) :
    m (SortOutcome H) :=
  let { mode, levels } := self
  match mode with
  | .start =>
    match category with
    | .parenOpen => return .more h { mode := .opened, levels }
    | .parenClose =>
      match levels with
      | [] => return .error h (.syntax (.expected #[.sort]))
      | level :: outer =>
        if level.arguments.isEmpty then return .error h (.syntax (.empty .sortApplication))
        else sortComplete h outer level.head level.arguments
    | _ =>
      match symbolOf? version category next token with
      | some name => sortComplete h levels ⟨name, #[]⟩ #[]
      | none => return .error h (.syntax (.expected #[.sort]))
  | .opened =>
    match category with
    | .parenOpen => return .more h { mode := .startingIdent .opened, levels }
    | _ =>
      match symbolOf? version category next token with
      | some name => return .more h { mode := .start, levels := ⟨⟨name, #[]⟩, #[]⟩ :: levels }
      | none =>
        if isWord version category next token .underscore then
          return .more h { mode := .identOnly .afterUnderscore, levels }
        else
          return .error h
            (.syntax (.expected #[.reserved (.general .underscore), .symbol, .token .parenOpen]))
  | .identOnly ident =>
    match identStep version ident category next token with
    | .more ident => return .more h { mode := .identOnly ident, levels }
    | .done head => sortComplete h levels head #[]
    | .error kind => return .error h (.syntax kind)
  | .startingIdent ident =>
    match identStep version ident category next token with
    | .more ident => return .more h { mode := .startingIdent ident, levels }
    | .done head => return .more h { mode := .start, levels := ⟨head, #[]⟩ :: levels }
    | .error kind => return .error h (.syntax kind)

/-- `ListState.step` without a maximum, of sorts, on the token's category. -/
@[inline]
def sortsStep {batch : BatchTag} (version : Version) (h : H)
    (self : ListState (SortStateOf H) (Handler.«Sort» H)) (category : TokenCategory)
    (next : BatchCursor batch) (token : Token batch) :
    m (HandledOutcome H (ListState (SortStateOf H) (Handler.«Sort» H))
      (Array (Handler.«Sort» H)) (Cause H)) := do
  let { opened, outside, inner, items } := self
  if !opened then
    match category with
    | .parenOpen => return .more h { opened := true, outside, inner, items }
    | _ => return .error h (.syntax (.expected #[.token .parenOpen]))
  else if outside && category == .parenClose then
    return .done h items
  else
    match ← sortStep version h inner category next token with
    | .more h state => return .more h { opened, outside := false, inner := state, items }
    | .done h item =>
      return .more h { opened, outside := true, inner := .init, items := items.push item }
    | .error h cause => return .error h cause

/-! ## Sorted variables -/

/-- The sorted variable state of the handler. -/
abbrev SortedVarOf (H : Type) {m : Type → Type} [Handler H m] :=
  SortedVarState (Handler.«Sort» H)

/-- The list of sorted variables of the handler. -/
abbrev SortedVarsOf (H : Type) {m : Type → Type} [Handler H m] :=
  ListState (SortedVarOf H) (Symbol × Handler.«Sort» H)

/-- `sortedVarStep` on the token's category. -/
@[inline]
def sortedVarStep {batch : BatchTag} (version : Version) (h : H) (self : SortedVarOf H)
    (category : TokenCategory) (next : BatchCursor batch) (token : Token batch) :
    m (HandledOutcome H (SortedVarOf H) (Symbol × Handler.«Sort» H) (Cause H)) := do
  match self with
  | .start =>
    match category with
    | .parenOpen => return .more h .opened
    | _ => return .error h (.syntax (.expected #[.token .parenOpen]))
  | .opened =>
    match symbolOf? version category next token with
    | some symbol => return .more h (.sort symbol .init)
    | none => return .error h (.syntax (.expected #[.symbol]))
  | .sort symbol sort =>
    match ← sortStep version h sort category next token with
    | .more h sort => return .more h (.sort symbol sort)
    | .done h sort => return .more h (.close symbol sort)
    | .error h cause => return .error h cause
  | .close symbol sort =>
    match category with
    | .parenClose => return .done h (symbol, sort)
    | _ => return .error h (.syntax (.expected #[.token .parenClose]))

/-- `ListState.step` without a maximum, of sorted variables, on the token's category. -/
@[inline]
def sortedVarsStep {batch : BatchTag} (version : Version) (h : H) (self : SortedVarsOf H)
    (category : TokenCategory) (next : BatchCursor batch) (token : Token batch) :
    m (HandledOutcome H (SortedVarsOf H) (Array (Symbol × Handler.«Sort» H)) (Cause H)) := do
  let { opened, outside, inner, items } := self
  if !opened then
    match category with
    | .parenOpen => return .more h { opened := true, outside, inner, items }
    | _ => return .error h (.syntax (.expected #[.token .parenOpen]))
  else if outside && category == .parenClose then
    return .done h items
  else
    match ← sortedVarStep version h inner category next token with
    | .more h state => return .more h { opened, outside := false, inner := state, items }
    | .done h item =>
      return .more h { opened, outside := true, inner := .start, items := items.push item }
    | .error h cause => return .error h cause

/-! ## Signatures and qualified identifiers -/

/-- `signatureStep` on the token's category. -/
@[inline]
def signatureStep {batch : BatchTag} (version : Version) (h : H)
    (self : SignatureState (Handler.«Sort» H)) (category : TokenCategory)
    (next : BatchCursor batch) (token : Token batch) :
    m (HandledOutcome H (SignatureState (Handler.«Sort» H)) (FunctionSignature (Handler.«Sort» H))
      (Cause H)) := do
  match self with
  | .start =>
    match symbolOf? version category next token with
    | some symbol => return .more h (.parameters symbol (ListState.paren .start))
    | none => return .error h (.syntax (.expected #[.symbol]))
  | .parameters symbol state =>
    match ← sortedVarsStep version h state category next token with
    | .more h state => return .more h (.parameters symbol state)
    | .done h parameters => return .more h (.result symbol parameters .init)
    | .error h cause => return .error h cause
  | .result symbol parameters state =>
    match ← sortStep version h state category next token with
    | .more h state => return .more h (.result symbol parameters state)
    | .done h result => return .done h (FunctionSignature.Internal.new symbol parameters result)
    | .error h cause => return .error h cause

/-- A qualified identifier in parentheses, as `qualIdentStep` from its `(`, without `as`: none
for the states of `as`. -/
@[inline]
def qualIdentStep {batch : BatchTag} (version : Version)
    (self : QualIdentState (Handler.«Sort» H)) (category : TokenCategory)
    (next : BatchCursor batch) (token : Token batch) :
    Option (PureOutcome (QualIdentState (Handler.«Sort» H)) Ident) :=
  match self with
  | .opened =>
    if isWord version category next token .underscore then some (.more (.indexed .afterUnderscore))
    else if isWord version category next token .as then some (.more (.qualifiedIdent .start))
    else some (.error (.expected #[.reserved (.general .underscore), .reserved (.general .as)]))
  | .indexed ident =>
    match identStep version ident category next token with
    | .more ident => some (.more (.indexed ident))
    | .done identifier => some (.done identifier)
    | .error kind => some (.error kind)
  | _ => none

end

/-! ## The category parsers as functions of their own

The parsers above, as functions of their own, specialised to the handler but not inlined: a
caller that is itself inlined into the loop calls them, so that the loop holds one call instead
of a copy of each, at the cost of the value of the result built at each call. -/

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- `sortStep`, not inlined. -/
@[noinline, specialize]
def sortStepOutlined {batch : BatchTag} (version : Version) (h : H) (self : SortStateOf H)
    (category : TokenCategory) (next : BatchCursor batch) (token : Token batch) :
    m (SortOutcome H) :=
  sortStep version h self category next token

/-- `sortsStep`, not inlined. -/
@[noinline, specialize]
def sortsStepOutlined {batch : BatchTag} (version : Version) (h : H)
    (self : ListState (SortStateOf H) (Handler.«Sort» H)) (category : TokenCategory)
    (next : BatchCursor batch) (token : Token batch) :
    m (HandledOutcome H (ListState (SortStateOf H) (Handler.«Sort» H))
      (Array (Handler.«Sort» H)) (Cause H)) :=
  sortsStep version h self category next token

/-- `sortedVarsStep`, not inlined. -/
@[noinline, specialize]
def sortedVarsStepOutlined {batch : BatchTag} (version : Version) (h : H)
    (self : SortedVarsOf H) (category : TokenCategory) (next : BatchCursor batch)
    (token : Token batch) :
    m (HandledOutcome H (SortedVarsOf H) (Array (Symbol × Handler.«Sort» H)) (Cause H)) :=
  sortedVarsStep version h self category next token

/-- `signatureStep`, not inlined. -/
@[noinline, specialize]
def signatureStepOutlined {batch : BatchTag} (version : Version) (h : H)
    (self : SignatureState (Handler.«Sort» H)) (category : TokenCategory)
    (next : BatchCursor batch) (token : Token batch) :
    m (HandledOutcome H (SignatureState (Handler.«Sort» H)) (FunctionSignature (Handler.«Sort» H))
      (Cause H)) :=
  signatureStep version h self category next token

end

end BSmtLib.Parser.Internal.Fused.Category
