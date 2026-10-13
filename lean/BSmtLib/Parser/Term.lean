import BSmtLib.Parser.Category

/-!
# The term parser

A state machine stepped by single tokens, with a stack of levels: one for each construct whose
inner term is being read, innermost first. A level keeps what its construct needs when the inner
term is complete: the arguments of an application so far, the scope value of a binder or a
match case, the scrutinee of a match. Between inner terms, the mode keeps the construct's data.

Every construct's last call comes at its `)`: the end of a binder, of a match case, the match
itself and an annotation are called after their `)` is consumed.
-/

/- LEAN: Rust's `TermSlot`, without the speculative fast paths of its `parse` (the fused term
loop). Rust keeps a pending term beside its state; here the modes that wait for a `)` hold it. -/

namespace BSmtLib.Parser

/-- A binder of sorted variables. -/
inductive SortedBinder where
  | quantifier (quantifier : Quantifier)
  | lambda

/-- What a binder is. -/
inductive BinderKind where
  | «let»
  | sorted (binder : SortedBinder)

/-- A construct whose inner term is being read. -/
inductive TermLevel (HandledSort HandledTerm Scope : Type) where
  /-- An application, reading its arguments. -/
  | application (function : Identifier) (sort : Option HandledSort)
      (arguments : Array HandledTerm)
  /-- A `let`, reading the term of the binding of the symbol. -/
  | letBinding (bindings : Array (Symbol × HandledTerm)) (symbol : Symbol)
  /-- A binder, reading its body. -/
  | binder (kind : BinderKind) (scope : Scope)
  /-- An annotation, reading the annotated term. -/
  | annotation
  /-- A match, reading its scrutinee. -/
  | matchScrutinee
  /-- A case of a match, reading its body. -/
  | matchCase (scrutinee : HandledTerm) (cases : Array (Pattern × HandledTerm))
      (pattern : Pattern) (scope : Scope)

/-- What the term parser is doing. -/
inductive TermMode (HandledSExpr HandledAttribute HandledSort HandledTerm Scope : Type) where
  /-- Before a term, or the `)` of the innermost application. -/
  | start
  /-- After the `(` of a term. -/
  | opened
  /-- Reading a term that is a qualified identifier in parentheses. -/
  | qualIdent (state : QualIdentState HandledSort)
  /-- Reading the qualified identifier in parentheses at the head of an application. -/
  | applicationHead (state : QualIdentState HandledSort)
  /-- After `(` `let`, before the `(` of the bindings. -/
  | letBindingsOpen
  /-- Between the bindings: `(` opens the next, `)` ends them. -/
  | letBindingOpen (bindings : Array (Symbol × HandledTerm))
  /-- After the `(` of a binding, before its symbol. -/
  | letBindingSymbol (bindings : Array (Symbol × HandledTerm))
  /-- After the term of a binding, before its `)`. -/
  | letBindingClose (bindings : Array (Symbol × HandledTerm))
  /-- Reading the sorted variables of a binder. -/
  | sortedVars (binder : SortedBinder)
      (state : ListState (SortedVarState HandledSort) (Symbol × HandledSort))
  /-- After the body of a binder, before its `)`. -/
  | binderClose (kind : BinderKind) (scope : Scope) (body : HandledTerm)
  /-- After the scrutinee, before the `(` of the cases. -/
  | matchCasesOpen (scrutinee : HandledTerm)
  /-- Between the cases: `(` opens the next, `)` ends them. -/
  | matchCaseOpen (scrutinee : HandledTerm) (cases : Array (Pattern × HandledTerm))
  /-- Reading the pattern of a case. -/
  | matchPattern (scrutinee : HandledTerm) (cases : Array (Pattern × HandledTerm))
      (state : PatternState)
  /-- After the body of a case, before its `)`. -/
  | matchCaseClose (scrutinee : HandledTerm) (cases : Array (Pattern × HandledTerm))
      (pattern : Pattern) (scope : Scope) (body : HandledTerm)
  /-- After the cases, before the match's `)`. -/
  | matchClose (scrutinee : HandledTerm) (cases : Array (Pattern × HandledTerm))
  /-- Reading the attributes of an annotation, up to its `)`. -/
  | annotating (term : HandledTerm) (state : AttributeState HandledSExpr HandledAttribute)

/-- The state of the term parser. -/
structure TermState (HandledSExpr HandledAttribute HandledSort HandledTerm Scope : Type) where
  mode : TermMode HandledSExpr HandledAttribute HandledSort HandledTerm Scope
  levels : List (TermLevel HandledSort HandledTerm Scope)

/-- The term parser before a term. -/
def TermState.init {HandledSExpr HandledAttribute HandledSort HandledTerm Scope : Type} :
    TermState HandledSExpr HandledAttribute HandledSort HandledTerm Scope :=
  { mode := .start, levels := [] }

/-- The state of the term parser of the handler. -/
abbrev TermStateOf (H : Type) {m : Type → Type} [Handler H m] :=
  TermState (Handler.SExpr H) (Handler.Attribute H) (Handler.«Sort» H) (Handler.Term H)
    (Handler.Scope H)

/-- The level of the term parser of the handler. -/
abbrev TermLevelOf (H : Type) {m : Type → Type} [Handler H m] :=
  TermLevel (Handler.«Sort» H) (Handler.Term H) (Handler.Scope H)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A term is complete: it is the result, or it goes to the innermost level's construct. A match
starts when its scrutinee is complete, at the scrutinee's last token.
-/
@[inline]
def termComplete (levels : List (TermLevelOf H)) (term : Handler.Term H) :
    PM H (Step (TermStateOf H) (Handler.Term H)) := do
  match levels with
  | [] => return .done term
  | .application function sort arguments :: outer =>
    return .more
      { mode := .start, levels := .application function sort (arguments.push term) :: outer }
  | .letBinding bindings symbol :: outer =>
    return .more { mode := .letBindingClose (bindings.push (symbol, term)), levels := outer }
  | .binder kind scope :: outer =>
    return .more { mode := .binderClose kind scope term, levels := outer }
  | .annotation :: outer =>
    return .more { mode := .annotating term .init, levels := outer }
  | .matchScrutinee :: outer =>
    call (Handler.startMatch term)
    return .more { mode := .matchCasesOpen term, levels := outer }
  | .matchCase scrutinee cases pattern scope :: outer =>
    return .more { mode := .matchCaseClose scrutinee cases pattern scope term, levels := outer }

/-- The start of a binder of sorted variables, with all its variables. -/
def startBinder (binder : SortedBinder) (variables : Array (Symbol × Handler.«Sort» H)) :
    PM H (Handler.Scope H) :=
  match binder with
  | .quantifier quantifier => call (Handler.startQuantifier quantifier variables)
  | .lambda => call (Handler.startLambda variables)

/-- The end of a binder, with its scope value and its body. -/
def endBinder (kind : BinderKind) (scope : Handler.Scope H) (body : Handler.Term H) :
    PM H (Handler.Term H) :=
  match kind with
  | .let => call (Handler.endLet scope body)
  | .sorted (.quantifier quantifier) => call (Handler.endQuantifier quantifier scope body)
  | .sorted .lambda => call (Handler.endLambda scope body)

/-- The operator after the `(` of a term. -/
def termOpened (self : TermStateOf H) (token : Input) :
    PM H (Step (TermStateOf H) (Handler.Term H)) :=
  let into mode := pure (Step.more { self with mode })
  let enter level := pure (Step.more { mode := .start, levels := level :: self.levels })
  match token with
  | .symbol function => enter (.application ⟨function, #[]⟩ none #[])
  | .parenOpen => into (.applicationHead .opened)
  | .reserved (.general word) =>
    match word with
    | .let => into .letBindingsOpen
    | .lambda => into (.sortedVars .lambda (ListState.paren .start))
    | .forall => into (.sortedVars (.quantifier .forall) (ListState.paren .start))
    | .exists => into (.sortedVars (.quantifier .exists) (ListState.paren .start))
    | .match => enter .matchScrutinee
    | .exclamationMark => enter .annotation
    | .underscore => into (.qualIdent (.indexed .afterUnderscore))
    | .as => into (.qualIdent (.qualifiedIdent .start))
    | _ => syntaxError .expectedOperator
  | _ => syntaxError .expectedOperator

/--
A step of the term parser.

⟨spec_constant⟩ and ⟨qual_identifier⟩ are handled at their last token; an application at its
`)`, after its arguments. A binder starts with all its bindings or variables at their `)`, and
ends at its own `)`. A match starts at its scrutinee's last token; each case starts at its
pattern's last token and ends at its `)`; the match is handled at its `)`. An annotation is
handled at its `)`, after its attributes.
-/
def termStep (version : Version) (self : TermStateOf H) (token : Input) :
    PM H (Step (TermStateOf H) (Handler.Term H)) := do
  let into mode := pure (Step.more { self with mode })
  match self.mode with
  | .start =>
    match token with
    | .parenOpen => into .opened
    | .parenClose =>
      match self.levels with
      | .application function sort arguments :: outer =>
        if arguments.isEmpty then syntaxError .emptyTermApplication
        let term ← call (Handler.handleTerm (.application function sort arguments))
        termComplete outer term
      | _ => syntaxError .expectedTerm
    | .symbol symbol =>
      let term ← call (Handler.handleTerm (.identifier ⟨symbol, #[]⟩ none))
      termComplete self.levels term
    | .constant constant =>
      let term ← call (Handler.handleTerm (.constant constant))
      termComplete self.levels term
    | _ => syntaxError .expectedTerm
  | .opened => termOpened self token
  | .qualIdent state =>
    match ← qualIdentStep version state token with
    | .more state => into (.qualIdent state)
    | .done (identifier, sort) =>
      let term ← call (Handler.handleTerm (.identifier identifier sort))
      termComplete self.levels term
  | .applicationHead state =>
    match ← qualIdentStep version state token with
    | .more state => into (.applicationHead state)
    | .done (function, sort) =>
      return .more { mode := .start, levels := .application function sort #[] :: self.levels }
  | .letBindingsOpen =>
    expectOpen token
    into (.letBindingOpen #[])
  | .letBindingOpen bindings =>
    match token with
    | .parenOpen => into (.letBindingSymbol bindings)
    | .parenClose =>
      if bindings.isEmpty then syntaxError .emptyLetBindings
      let scope ← call (Handler.startLet bindings)
      return .more { mode := .start, levels := .binder .let scope :: self.levels }
    | _ => syntaxError (.expectedToken #[.parenOpen, .parenClose])
  | .letBindingSymbol bindings =>
    let symbol ← expectSymbol token
    return .more { mode := .start, levels := .letBinding bindings symbol :: self.levels }
  | .letBindingClose bindings =>
    expectClose token
    into (.letBindingOpen bindings)
  | .sortedVars binder state =>
    match ← state.step .start (sortedVarStep version) none token with
    | .more state => into (.sortedVars binder state)
    | .done variables =>
      if variables.isEmpty then
        syntaxError (match binder with
          | .lambda => .emptyLambdaBindings
          | _ => .emptyQuantifierBindings)
      let scope ← startBinder binder variables
      return .more { mode := .start, levels := .binder (.sorted binder) scope :: self.levels }
  | .binderClose kind scope body =>
    expectClose token
    let term ← endBinder kind scope body
    termComplete self.levels term
  | .matchCasesOpen scrutinee =>
    expectOpen token
    into (.matchCaseOpen scrutinee #[])
  | .matchCaseOpen scrutinee cases =>
    match token with
    | .parenOpen => into (.matchPattern scrutinee cases .start)
    | .parenClose =>
      if cases.isEmpty then syntaxError .emptyMatchCases
      into (.matchClose scrutinee cases)
    | _ => syntaxError (.expectedToken #[.parenOpen, .parenClose])
  | .matchPattern scrutinee cases state =>
    match ← state.step version token with
    | .more state => into (.matchPattern scrutinee cases state)
    | .done pattern =>
      let scope ← call (Handler.startMatchCase scrutinee pattern)
      let level := TermLevel.matchCase scrutinee cases pattern scope
      return .more { mode := .start, levels := level :: self.levels }
  | .matchCaseClose scrutinee cases pattern scope body =>
    expectClose token
    let handled ← call (Handler.endMatchCase scope scrutinee body)
    into (.matchCaseOpen scrutinee (cases.push (pattern, handled)))
  | .matchClose scrutinee cases =>
    expectClose token
    let term ← call (Handler.endMatch scrutinee cases)
    termComplete self.levels term
  | .annotating term state =>
    match ← attributeStep false version state token with
    | .more state => into (.annotating term state)
    | .done attributes =>
      if attributes.isEmpty then syntaxError .emptyAnnotation
      let annotated ← call (Handler.annotateTerm term attributes)
      termComplete self.levels annotated

end

end BSmtLib.Parser
