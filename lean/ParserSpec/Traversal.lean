import ParserSpec.Script

/-!
# The traversal

The handler contract: which handler calls the parser makes for each syntax tree, with which
arguments, in which order. A handler call receives the parts of its construct that are
already handled, as the values the handler returned for them.

A draft, written after what the Rust parser does.
-/

namespace ParserSpec

open LexerSpec

namespace Traversal

/-- A term as the handler receives it, its parts already handled. -/
inductive TermNode (HandledSort HandledTerm : Type) where
  | constant (constant : Tree.SpecConstant)
  /-- A qualified identifier, with its sort if it is qualified by `as`. -/
  | identifier (identifier : Tree.Identifier) (sort : Option HandledSort)
  /-- An application of a qualified identifier to at least one argument. -/
  | application (function : Tree.Identifier) (sort : Option HandledSort)
      (arguments : List HandledTerm)

/-- An s-expression as the handler receives it, its items already handled. -/
inductive SExprNode (HandledSExpr : Type) where
  | constant (constant : Tree.SpecConstant)
  | symbol (name : Chars)
  | reserved (word : Chars)
  | keyword (name : Chars)
  | list (items : List HandledSExpr)

/-- An attribute value as the handler receives it, its s-expressions already handled. -/
inductive AttributeValueNode (HandledSExpr : Type) where
  | constant (constant : Tree.SpecConstant)
  | symbol (name : Chars)
  | list (items : List HandledSExpr)

/-- The handler of the categories that terms are built from (`SmtHandler`). -/
structure TermHandler (m : Type → Type)
    (HandledSExpr HandledAttribute HandledSort HandledTerm : Type) where
  handleSort : Tree.Identifier → List HandledSort → m HandledSort
  handleTerm : TermNode HandledSort HandledTerm → m HandledTerm
  handleSExpr : SExprNode HandledSExpr → m HandledSExpr
  handleAttribute : Chars → Option (AttributeValueNode HandledSExpr) → m HandledAttribute
  annotateTerm : HandledTerm → List HandledAttribute → m HandledTerm
  startLet : List (Chars × HandledTerm) → m Unit
  endLet : HandledTerm → m HandledTerm
  startQuantifier : Tree.Quantifier → Chars → HandledSort → m Unit
  endQuantifier : HandledTerm → m HandledTerm
  startLambda : Chars → HandledSort → m Unit
  endLambda : HandledTerm → m HandledTerm
  startMatch : HandledTerm → m Unit
  startMatchCase : Tree.Pattern → m Unit
  endMatchCase : HandledTerm → m Unit
  endMatch : m HandledTerm

/-- The signature of a defined function, its sorts already handled. -/
structure Signature (HandledSort : Type) where
  symbol : Chars
  parameters : List (Chars × HandledSort)
  result : HandledSort

/-- A datatype constructor, the sorts of its selectors already handled. -/
structure Constructor (HandledSort : Type) where
  symbol : Chars
  selectors : List (Chars × HandledSort)

/-- The handler of commands (`CommandHandler`). -/
structure CommandHandler (m : Type → Type)
    (HandledSExpr HandledAttribute HandledSort HandledTerm : Type)
    extends TermHandler m HandledSExpr HandledAttribute HandledSort HandledTerm where
  echo : Chars → m Unit
  getOption : Chars → m Unit
  setOption : HandledAttribute → m Unit
  getInfo : Chars → m Unit
  setInfo : HandledAttribute → m Unit
  setLogic : Chars → m Unit
  getValue : List HandledTerm → m Unit
  getAssertions : m Unit
  getAssignment : m Unit
  getModel : m Unit
  getProof : m Unit
  getUnsatAssumptions : m Unit
  getUnsatCore : m Unit
  declareSort : Chars → Chars → m Unit
  declareSortParameter : Chars → m Unit
  declareFun : Chars → List HandledSort → HandledSort → m Unit
  assert : HandledTerm → m Unit
  checkSat : List HandledTerm → m Unit
  reset : m Unit
  resetAssertions : m Unit
  exit : m Unit
  push : Chars → m Unit
  pop : Chars → m Unit
  startDefineSort : Chars → List Chars → m Unit
  endDefineSort : HandledSort → m Unit
  startDefineFun : Signature HandledSort → m Unit
  endDefineFun : HandledTerm → m Unit
  startDefineFunsRec : List (Signature HandledSort) → m Unit
  startRecursiveBody : m Unit
  endRecursiveBody : HandledTerm → m Unit
  endDefineFunsRec : m Unit
  startDeclareDatatypes : List (Chars × Chars) → m Unit
  startDatatypeDeclaration : List Chars → m Unit
  endDatatypeDeclaration : List (Constructor HandledSort) → m Unit
  endDeclareDatatypes : m Unit

section

variable {m : Type → Type} [Monad m] {HandledSExpr HandledAttribute HandledSort HandledTerm : Type}
variable (handler : TermHandler m HandledSExpr HandledAttribute HandledSort HandledTerm)

mutual

/-- A sort: its argument sorts, then the sort. -/
def sort : Tree.Sort → m HandledSort
  | .mk identifier arguments => do
    let handled ← sorts arguments
    handler.handleSort identifier handled

/-- Sorts, one after another. -/
def sorts : List Tree.Sort → m (List HandledSort)
  | [] => pure []
  | first :: rest => do
    let handled ← sort first
    let others ← sorts rest
    pure (handled :: others)

end

mutual

/-- An s-expression: a list's items, then the list. -/
def sExpr : Tree.SExpr → m HandledSExpr
  | .constant constant => handler.handleSExpr (.constant constant)
  | .symbol name => handler.handleSExpr (.symbol name)
  | .reserved word => handler.handleSExpr (.reserved word)
  | .keyword name => handler.handleSExpr (.keyword name)
  | .list items => do
    let handled ← sExprs items
    handler.handleSExpr (.list handled)

/-- S-expressions, one after another. -/
def sExprs : List Tree.SExpr → m (List HandledSExpr)
  | [] => pure []
  | first :: rest => do
    let handled ← sExpr first
    let others ← sExprs rest
    pure (handled :: others)

end

/--
An attribute: the s-expressions of its value, then the attribute. A list value is handed
over as its items; the list itself is not handled as an s-expression.
-/
def «attribute» : Tree.Attribute → m HandledAttribute
  | ⟨name, none⟩ => handler.handleAttribute name none
  | ⟨name, some (.constant constant)⟩ => handler.handleAttribute name (some (.constant constant))
  | ⟨name, some (.symbol symbol)⟩ => handler.handleAttribute name (some (.symbol symbol))
  | ⟨name, some (.list items)⟩ => do
    let handled ← sExprs handler items
    handler.handleAttribute name (some (.list handled))

/-- Attributes, one after another. -/
def attributes : List Tree.Attribute → m (List HandledAttribute)
  | [] => pure []
  | first :: rest => do
    let handled ← Traversal.attribute handler first
    let others ← attributes rest
    pure (handled :: others)

/-- A qualified identifier: its sort, if it has one. -/
def qualIdentifier : Tree.QualIdentifier → m (Tree.Identifier × Option HandledSort)
  | .plain identifier => pure (identifier, none)
  | .as identifier qualification => do
    let handled ← sort handler qualification
    pure (identifier, some handled)

/--
The variables of a binder, one after another: the sort of a variable, then the start of the
binder for it. A binder of several variables is started once for each of them.
-/
def openVariables (start : Chars → HandledSort → m Unit) : List Tree.SortedVar → m Unit
  | [] => pure ()
  | ⟨name, variableSort⟩ :: rest => do
    let handled ← sort handler variableSort
    start name handled
    openVariables start rest

/-- Ends a binder as many times as it was started. -/
def closeTimes (close : HandledTerm → m HandledTerm) : Nat → HandledTerm → m HandledTerm
  | 0, term => pure term
  | count + 1, term => do
    let closed ← close term
    closeTimes close count closed

mutual

/-- A term. -/
def term : Tree.Term → m HandledTerm
  /- ⟨spec_constant⟩ -/
  | .constant constant => handler.handleTerm (.constant constant)

  /- ⟨qual_identifier⟩: its sort, then the term -/
  | .identifier identifier => do
    let (identifier, qualification) ← qualIdentifier handler identifier
    handler.handleTerm (.identifier identifier qualification)

  /- an application: the sort of the function, its arguments, then the term -/
  | .application function arguments => do
    let (function, qualification) ← qualIdentifier handler function
    let handled ← terms arguments
    handler.handleTerm (.application function qualification handled)

  /- `let`: the terms of the bindings, the start, the body, then the end -/
  | .«let» bindingList body => do
    let handled ← bindings bindingList
    handler.startLet handled
    let result ← term body
    handler.endLet result

  /- `lambda`: the variables, the body, then an end for each variable -/
  | .lambda variables body => do
    openVariables handler handler.startLambda variables
    let result ← term body
    closeTimes handler.endLambda variables.length result

  /- `forall`, `exists`: the variables, the body, then an end for each variable -/
  | .quantified quantifier variables body => do
    openVariables handler (handler.startQuantifier quantifier) variables
    let result ← term body
    closeTimes handler.endQuantifier variables.length result

  /- `match`: the scrutinee, the start, the cases, then the end -/
  | .«match» scrutinee caseList => do
    let handled ← term scrutinee
    handler.startMatch handled
    cases caseList
    handler.endMatch

  /- an annotation: the term, its attributes, then the annotation -/
  | .annotated annotated attributeList => do
    let handled ← term annotated
    let handledAttributes ← attributes handler attributeList
    handler.annotateTerm handled handledAttributes

/-- Terms, one after another. -/
def terms : List Tree.Term → m (List HandledTerm)
  | [] => pure []
  | first :: rest => do
    let handled ← term first
    let others ← terms rest
    pure (handled :: others)

/-- The bindings of a `let`, one after another: the term of each. -/
def bindings : List (Chars × Tree.Term) → m (List (Chars × HandledTerm))
  | [] => pure []
  | (name, bound) :: rest => do
    let handled ← term bound
    let others ← bindings rest
    pure ((name, handled) :: others)

/-- The cases of a `match`, one after another: the start of each, its body, then its end. -/
def cases : List (Tree.Pattern × Tree.Term) → m Unit
  | [] => pure ()
  | (pattern, body) :: rest => do
    handler.startMatchCase pattern
    let result ← term body
    handler.endMatchCase result
    cases rest

end

end

/-- A propositional literal as the term it is: the symbol, or `not` applied to it. -/
def Tree.PropLiteral.asTerm : Tree.PropLiteral → Tree.Term
  | .positive symbol => .identifier (.plain ⟨symbol, []⟩)
  | .negative symbol =>
    .application (.plain ⟨chars "not", []⟩) [.identifier (.plain ⟨symbol, []⟩)]

section

variable {m : Type → Type} [Monad m] {HandledSExpr HandledAttribute HandledSort HandledTerm : Type}
variable (handler : CommandHandler m HandledSExpr HandledAttribute HandledSort HandledTerm)

/-- The signature of a function: the sorts of its parameters, then its result sort. -/
def signature (symbol : Chars) (parameters : List Tree.SortedVar) (result : Tree.Sort) :
    m (Signature HandledSort) := do
  let handledParameters ← parameters.mapM fun ⟨name, parameterSort⟩ => do
    pure (name, ← sort handler.toTermHandler parameterSort)
  let handledResult ← sort handler.toTermHandler result
  pure ⟨symbol, handledParameters, handledResult⟩

/--
A datatype declaration: the start with its sort parameters, the sorts of the selectors of its
constructors, then the end with the constructors.
-/
def datatype (declaration : Tree.DatatypeDec) : m Unit := do
  handler.startDatatypeDeclaration declaration.parameters
  let constructors ← declaration.constructors.mapM fun constructor => do
    let selectors ← constructor.selectors.mapM fun selector => do
      pure (selector.symbol, ← sort handler.toTermHandler selector.sort)
    pure (⟨constructor.symbol, selectors⟩ : Constructor HandledSort)
  handler.endDatatypeDeclaration constructors

/-- The body of a recursive function: the start, the body, then the end. -/
def recursiveBody (body : Tree.Term) : m Unit := do
  handler.startRecursiveBody
  let result ← term handler.toTermHandler body
  handler.endRecursiveBody result

/-- A command. -/
def command : Tree.Command → m Unit
  | .assert asserted => do handler.assert (← term handler.toTermHandler asserted)
  /- `check-sat` is `check-sat-assuming` without assumptions -/
  | .checkSat => handler.checkSat []
  | .checkSatAssuming assumptions => do
    handler.checkSat (← terms handler.toTermHandler assumptions)
  /- the literals of 2.5 and 2.6 are handled as the terms they are -/
  | .checkSatAssumingLiterals literals => do
    handler.checkSat (← terms handler.toTermHandler (literals.map Tree.PropLiteral.asTerm))
  /- `declare-const` is `declare-fun` without parameters -/
  | .declareConst symbol declaredSort => do
    handler.declareFun symbol [] (← sort handler.toTermHandler declaredSort)
  /- `declare-datatype` is `declare-datatypes` of one datatype, whose arity is the number of
  its sort parameters -/
  | .declareDatatype symbol declaration => do
    handler.startDeclareDatatypes [(symbol, chars (toString declaration.parameters.length))]
    datatype handler declaration
    handler.endDeclareDatatypes
  | .declareDatatypes sortDecs declarations => do
    handler.startDeclareDatatypes (sortDecs.map fun sortDec => (sortDec.symbol, sortDec.arity))
    declarations.forM (datatype handler)
    handler.endDeclareDatatypes
  | .declareFun symbol parameters result => do
    let handledParameters ← sorts handler.toTermHandler parameters
    let handledResult ← sort handler.toTermHandler result
    handler.declareFun symbol handledParameters handledResult
  | .declareSort symbol arity => handler.declareSort symbol arity
  | .declareSortParameter symbol => handler.declareSortParameter symbol
  /- `define-const` is `define-fun` without parameters -/
  | .defineConst symbol definedSort body => do
    handler.startDefineFun ⟨symbol, [], ← sort handler.toTermHandler definedSort⟩
    handler.endDefineFun (← term handler.toTermHandler body)
  | .defineFun ⟨symbol, parameters, result, body⟩ => do
    handler.startDefineFun (← signature handler symbol parameters result)
    handler.endDefineFun (← term handler.toTermHandler body)
  /- `define-fun-rec` is `define-funs-rec` of one function -/
  | .defineFunRec ⟨symbol, parameters, result, body⟩ => do
    handler.startDefineFunsRec [← signature handler symbol parameters result]
    recursiveBody handler body
    handler.endDefineFunsRec
  | .defineFunsRec declarations bodies => do
    let signatures ← declarations.mapM fun declaration =>
      signature handler declaration.symbol declaration.parameters declaration.result
    handler.startDefineFunsRec signatures
    bodies.forM (recursiveBody handler)
    handler.endDefineFunsRec
  | .defineSort symbol parameters definedSort => do
    handler.startDefineSort symbol parameters
    handler.endDefineSort (← sort handler.toTermHandler definedSort)
  | .echo content => handler.echo content
  | .exit => handler.exit
  | .getAssertions => handler.getAssertions
  | .getAssignment => handler.getAssignment
  | .getInfo flag => handler.getInfo flag
  | .getModel => handler.getModel
  | .getOption keyword => handler.getOption keyword
  | .getProof => handler.getProof
  | .getUnsatAssumptions => handler.getUnsatAssumptions
  | .getUnsatCore => handler.getUnsatCore
  | .getValue values => do handler.getValue (← terms handler.toTermHandler values)
  | .pop count => handler.pop count
  | .push count => handler.push count
  | .reset => handler.reset
  | .resetAssertions => handler.resetAssertions
  | .setInfo info => do handler.setInfo (← Traversal.attribute handler.toTermHandler info)
  | .setLogic symbol => handler.setLogic symbol
  | .setOption option => do handler.setOption (← Traversal.attribute handler.toTermHandler option)

/-- A script: its commands, one after another. -/
def script (commands : List Tree.Command) : m Unit :=
  commands.forM (command handler)

end

end Traversal

end ParserSpec
