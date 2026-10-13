import BSmtLib.Spec.Grammar
import BSmtLib.Spec.Parser.Policy

/-!
# The traversal

The handler contract: which handler calls a parser makes for each syntax tree, with which
arguments, in which order, and at which token. The standard has no parser; this is the
library's.

## Calls

A handler is told about a tree bottom-up: each call receives the parts of its construct that
are already handled, as the values the handler returned for them, and the names and constants
as they were written. A call that brings names into scope returns a scope value, which the call
that ends the scope receives back. The calls are the constructors of `Call`; a handler answers
each of them (`Handler`).

No two constructs are reported with the same calls, so the calls determine the tree; and the
calls come in an order in which a handler never has to keep anything back: it can build what it
builds with a stack.

## Tokens

The traversal also marks two points of each token, through `Points`: its arrival, when the
parser takes it from its producer, and its processing. Every call is placed between two such
points:

- A call comes after the processing of the token that determines it, never earlier. So two
  inputs that agree on their first tokens agree on the calls up to the next token's arrival.
- The last call of a construct with parentheses comes after its `)`, even where its parts are
  complete earlier.
- A call that opens a scope comes right after the token that completes its arguments, before the
  first token of what it scopes arrives.
- Only `startScript` comes at an arrival: when the script's first token arrives, before it is
  processed.

The tokens the traversal takes are exactly the tokens the tree is written as (`Tree.Command.tokens`
and the others), followed by the end of the input. After `exit`, the producer discards the rest
of the input, so the parser receives the end of the input right after the `)` of `exit`.

## The producer

Besides the handler, the traversal tells the producer of the tokens two things (`Producer`): to
switch the version after a version declaration, which it may refuse, and to discard the rest of
the input after `exit`. Each comes after the handler's call for the same `)`.

## Failures

A handler call can fail with the handler's error, and a version declaration can be rejected: if
it breaks the version policy, or if the producer refuses to switch to it. A failure stops the
traversal: no call and no token point follows it.

A version declaration that names no supported version cannot stand in a script (Reading M1), but
a parser only knows it at the declaration's `)`. The traversal takes such a declaration as
`set-info`, like any other, and then rejects it as a version that is not supported, as it
rejects a version the policy does not allow: the commands it is the last of are what a parser
takes before it fails.
-/

namespace BSmtLib.Spec.Parser

open BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar

/--
A propositional literal as the term it is written as: the symbol, or `not` applied to it.
-/
def _root_.BSmtLib.Spec.Grammar.Tree.PropLiteral.asTerm : Tree.PropLiteral → Tree.Term
  | .positive symbol => .identifier (.plain ⟨symbol, []⟩)
  | .negative negation symbol =>
    .application (.plain ⟨negation, []⟩) [.identifier (.plain ⟨symbol, []⟩)]

namespace Traversal

/-! ## Calls -/

/--
The types of the values a handler returns for what it is told about: handled s-expressions,
attributes, sorts and terms, and scope values.
-/
structure Values where
  sExpr : Type
  «attribute» : Type
  sort : Type
  term : Type
  scope : Type

/-- What a call returns. -/
inductive Returns where
  | sExpr
  | attribute
  | sort
  | term
  | scope
  | nothing

/-- The type of what a call returns, in the handler's values. -/
def Values.of (values : Values) : Returns → Type
  | .sExpr => values.sExpr
  | .attribute => values.«attribute»
  | .sort => values.sort
  | .term => values.term
  | .scope => values.scope
  | .nothing => Unit

/-- A term as the handler receives it, its parts already handled. -/
inductive TermNode (values : Values) where
  | constant (constant : Tree.SpecConstant)
  /-- A qualified identifier, with its sort if it is qualified by `as`. -/
  | identifier (identifier : Tree.Identifier) (sort : Option values.sort)
  /-- An application of a qualified identifier to its arguments. -/
  | application (function : Tree.Identifier) (sort : Option values.sort)
      (arguments : List values.term)

/-- An s-expression as the handler receives it, its items already handled. -/
inductive SExprNode (values : Values) where
  | constant (constant : Tree.SpecConstant)
  | symbol (symbol : Tree.Symbol)
  | reserved (word : Chars)
  | keyword (name : Chars)
  | list (items : List values.sExpr)

/--
The value of an attribute as the handler receives it, the s-expressions of a list value already
handled. A list value is handed over as its items; the list itself is not an s-expression.
-/
inductive AttributeValueNode (values : Values) where
  | constant (constant : Tree.SpecConstant)
  | symbol (symbol : Tree.Symbol)
  | list (items : List values.sExpr)

/-- The signature of a defined function, its sorts already handled. -/
structure Signature (values : Values) where
  symbol : Tree.Symbol
  parameters : List (Tree.Symbol × values.sort)
  result : values.sort

/-- A datatype constructor, the sorts of its selectors already handled. -/
structure Constructor (values : Values) where
  symbol : Tree.Symbol
  selectors : List (Tree.Symbol × values.sort)

/--
The calls a handler is told, each with what it returns: one constructor for each method of the
library's handler traits.
-/
inductive Call (values : Values) : Returns → Type where
  -- Sorts, s-expressions, attributes and terms (`SmtHandler`)
  | handleSort (identifier : Tree.Identifier) (arguments : List values.sort) : Call values .sort
  | handleSExpr (sExpr : SExprNode values) : Call values .sExpr
  | handleAttribute (keyword : Chars) (value : Option (AttributeValueNode values)) :
      Call values .attribute
  | handleTerm (term : TermNode values) : Call values .term
  | annotateTerm (term : values.term) (attributes : List values.«attribute») : Call values .term
  | startLet (bindings : List (Tree.Symbol × values.term)) : Call values .scope
  | endLet (scope : values.scope) (body : values.term) : Call values .term
  | startQuantifier (quantifier : Tree.Quantifier) (variables : List (Tree.Symbol × values.sort)) :
      Call values .scope
  | endQuantifier (quantifier : Tree.Quantifier) (scope : values.scope) (body : values.term) :
      Call values .term
  | startLambda (variables : List (Tree.Symbol × values.sort)) : Call values .scope
  | endLambda (scope : values.scope) (body : values.term) : Call values .term
  /-- An early check of the scrutinee, before the first case. -/
  | startMatch (scrutinee : values.term) : Call values .nothing
  | startMatchCase (scrutinee : values.term) (pattern : Tree.Pattern) : Call values .scope
  | endMatchCase (scope : values.scope) (body : values.term) : Call values .term
  | handleMatch (scrutinee : values.term) (cases : List (Tree.Pattern × values.term)) :
      Call values .term
  -- Commands (`SmtCommandHandler`)
  | commandAssert (term : values.term) : Call values .nothing
  | commandCheckSat : Call values .nothing
  | commandCheckSatAssuming (assumptions : List values.term) : Call values .nothing
  | commandDeclareConst (symbol : Tree.Symbol) (sort : values.sort) : Call values .nothing
  | startDeclareDatatype (symbol : Tree.Symbol) (parameters : List Tree.Symbol) :
      Call values .nothing
  | endDeclareDatatype (constructors : List (Constructor values)) : Call values .nothing
  | startDeclareDatatypes (sorts : List (Tree.Symbol × Chars)) : Call values .nothing
  | startDatatypeDeclaration (parameters : List Tree.Symbol) : Call values .nothing
  | endDatatypeDeclaration (constructors : List (Constructor values)) : Call values .nothing
  | endDeclareDatatypes : Call values .nothing
  | commandDeclareFun (symbol : Tree.Symbol) (parameters : List values.sort)
      (result : values.sort) : Call values .nothing
  | commandDeclareSort (symbol : Tree.Symbol) (arity : Chars) : Call values .nothing
  | commandDeclareSortParameter (symbol : Tree.Symbol) : Call values .nothing
  | commandDefineConst (symbol : Tree.Symbol) (sort : values.sort) (body : values.term) :
      Call values .nothing
  | startDefineFun (signature : Signature values) : Call values .nothing
  | endDefineFun (body : values.term) : Call values .nothing
  | startDefineFunRec (signature : Signature values) : Call values .nothing
  | endDefineFunRec (body : values.term) : Call values .nothing
  | startDefineFunsRec (signatures : List (Signature values)) : Call values .nothing
  | startRecursiveBody : Call values .nothing
  | endRecursiveBody (body : values.term) : Call values .nothing
  | endDefineFunsRec : Call values .nothing
  | startDefineSort (symbol : Tree.Symbol) (parameters : List Tree.Symbol) : Call values .nothing
  | endDefineSort (sort : values.sort) : Call values .nothing
  | commandEcho (content : Chars) : Call values .nothing
  | commandExit : Call values .nothing
  | commandGetAssertions : Call values .nothing
  | commandGetAssignment : Call values .nothing
  | commandGetInfo (flag : Chars) : Call values .nothing
  | commandGetModel : Call values .nothing
  | commandGetOption (keyword : Chars) : Call values .nothing
  | commandGetProof : Call values .nothing
  | commandGetUnsatAssumptions : Call values .nothing
  | commandGetUnsatCore : Call values .nothing
  | commandGetValue (terms : List values.term) : Call values .nothing
  | commandPop (count : Chars) : Call values .nothing
  | commandPush (count : Chars) : Call values .nothing
  | commandReset : Call values .nothing
  | commandResetAssertions : Call values .nothing
  | commandSetInfo (info : values.«attribute») : Call values .nothing
  | commandSetLogic (symbol : Tree.Symbol) : Call values .nothing
  | commandSetOption (option : values.«attribute») : Call values .nothing
  /-- The handler's switch to the version a script declares, after the producer's. -/
  | setVersion (version : Version) : Call values .nothing

/--
A handler in a monad `m`, with errors of type `ε`: its answer to each call, and the start and the
end of a script, which cannot fail.
-/
structure Handler (m : Type → Type) (ε : Type) (values : Values) where
  call : {returns : Returns} → Call values returns → ExceptT ε m (values.of returns)
  startScript : m Unit
  endScript : m Unit

/-! ## Tokens and failures -/

/-- What a parser takes from its producer: a token, or the end of the input. -/
inductive Received where
  | token (token : SyntaxToken)
  | endOfInput

/--
The two points of each token in a parse: the token arrives at the parser, which takes it from
its producer; then the parser processes it. Between them come only the calls due at the token's
arrival, which do not depend on the token.
-/
structure Points (m : Type → Type) where
  arrive : Received → m Unit
  process : Received → m Unit

/-- A producer's refusal to switch the version (`SmtVersionRefused`). -/
structure VersionRefused where

/--
The producer of the tokens in a monad `m`, as far as the traversal tells it anything: its switch
of the version, which it may refuse, and its discarding of the rest of the input, which cannot
fail.
-/
structure Producer (m : Type → Type) where
  setVersion : Version → ExceptT VersionRefused m Unit
  discardRest : m Unit

/-- The party that failed: the parse, with a syntax error, or the handler. -/
inductive Cause (ε : Type) where
  | syntax (error : VersionError)
  | handler (error : ε)

/-- What the traversal does: it runs in `m`, and stops with the party that failed. -/
abbrev Run (m : Type → Type) (ε α : Type) := ExceptT (Cause ε) m α

/-! ## The traversal of each category -/

section

variable {m : Type → Type} [Monad m] {ε : Type} {values : Values}
variable (points : Points m) (handler : Handler m ε values)

/-- The handler's answer to the call; its failure is the handler's. -/
def call {returns : Returns} (request : Call values returns) : Run m ε (values.of returns) :=
  ExceptT.adapt Cause.handler (handler.call request)

/--
The parser takes what it receives: it arrives, the calls due at its arrival are made, then the
parser processes it.
-/
def receive (received : Received) (atArrival : Run m ε Unit := pure ()) : Run m ε Unit := do
  ExceptT.lift (points.arrive received)
  atArrival
  ExceptT.lift (points.process received)

/-- The parser takes the token. -/
def take (token : SyntaxToken) : Run m ε Unit :=
  receive points (.token token)

/-- The parser takes the tokens, one after another, with no call between them. -/
def takeAll (tokens : List SyntaxToken) : Run m ε Unit :=
  tokens.forM (take points)

mutual

/-- A sort: its argument sorts, then the sort, after its last token. -/
def sort : Tree.Sort → Run m ε values.sort
  /- ⟨identifier⟩ -/
  | .mk identifier [] => do
    takeAll points identifier.tokens
    call handler (.handleSort identifier [])
  /- `(` ⟨identifier⟩ ⟨sort⟩+ `)` -/
  | .mk identifier arguments => do
    take points .parenOpen
    takeAll points identifier.tokens
    let handled ← sorts arguments
    take points .parenClose
    call handler (.handleSort identifier handled)

/-- Sorts, one after another. -/
def sorts : List Tree.Sort → Run m ε (List values.sort)
  | [] => pure []
  | first :: rest => do
    let handled ← sort first
    let others ← sorts rest
    pure (handled :: others)

end

mutual

/-- An s-expression: a list's items, then the list, after its `)`. -/
def sExpr : Tree.SExpr → Run m ε values.sExpr
  | .constant value => do
    take points value.token
    call handler (.handleSExpr (.constant value))
  | .symbol name => do
    take points (.symbol name)
    call handler (.handleSExpr (.symbol name))
  | .reserved w => do
    take points (.reserved w)
    call handler (.handleSExpr (.reserved w))
  | .keyword name => do
    take points (.keyword name)
    call handler (.handleSExpr (.keyword name))
  | .list items => do
    take points .parenOpen
    let handled ← sExprs items
    take points .parenClose
    call handler (.handleSExpr (.list handled))

/-- S-expressions, one after another. -/
def sExprs : List Tree.SExpr → Run m ε (List values.sExpr)
  | [] => pure []
  | first :: rest => do
    let handled ← sExpr first
    let others ← sExprs rest
    pure (handled :: others)

end

/-- The value of an attribute: its tokens, and the s-expressions of a list value. -/
def attributeValue : Tree.AttributeValue → Run m ε (AttributeValueNode values)
  | .constant value => do
    take points value.token
    pure (.constant value)
  | .symbol name => do
    take points (.symbol name)
    pure (.symbol name)
  | .list items => do
    take points .parenOpen
    let handled ← sExprs points handler items
    take points .parenClose
    pure (.list handled)

/--
An attribute whose keyword is already taken, then the token after it, `following`: the keyword
of the next attribute, or the `)` after the attributes.

An attribute with a value is handled after the value's last token, before `following`. An
attribute without a value is handled only after `following`, the token that shows it has no
value.
-/
def attributeThen (keyword : Chars) (following : SyntaxToken) :
    Option Tree.AttributeValue → Run m ε values.«attribute»
  | some value => do
    let node ← attributeValue points handler value
    let handled ← call handler (.handleAttribute keyword (some node))
    take points following
    pure handled
  | none => do
    take points following
    call handler (.handleAttribute keyword none)

/--
Attributes from the one whose keyword is already taken on, up to the `)` after them, each as in
`attributeThen`.
-/
def attributesThen (keyword : Chars) (value : Option Tree.AttributeValue) :
    List Tree.Attribute → Run m ε (List values.«attribute»)
  | [] => do
    let handled ← attributeThen points handler keyword .parenClose value
    pure [handled]
  | ⟨nextKeyword, nextValue⟩ :: rest => do
    let handled ← attributeThen points handler keyword (.keyword nextKeyword) value
    let others ← attributesThen nextKeyword nextValue rest
    pure (handled :: others)

/-- A qualified identifier: its tokens and its sort, if it is qualified by `as`. -/
def qualIdentifier : Tree.QualIdentifier → Run m ε (Tree.Identifier × Option values.sort)
  /- ⟨identifier⟩ -/
  | .plain identifier => do
    takeAll points identifier.tokens
    pure (identifier, none)
  /- `(` `as` ⟨identifier⟩ ⟨sort⟩ `)` -/
  | .as identifier qualification => do
    takeAll points [.parenOpen, word "as"]
    takeAll points identifier.tokens
    let handled ← sort points handler qualification
    take points .parenClose
    pure (identifier, some handled)

/-- Sorted variables, one after another, each `(` ⟨symbol⟩ ⟨sort⟩ `)`: the sort of each. -/
def sortedVars : List Tree.SortedVar → Run m ε (List (Tree.Symbol × values.sort))
  | [] => pure []
  | ⟨symbol, variableSort⟩ :: rest => do
    takeAll points [.parenOpen, .symbol symbol]
    let handled ← sort points handler variableSort
    take points .parenClose
    let others ← sortedVars rest
    pure ((symbol, handled) :: others)

mutual

/-- A term. -/
def term : Tree.Term → Run m ε values.term
  /- ⟨spec_constant⟩ -/
  | .constant value => do
    take points value.token
    call handler (.handleTerm (.constant value))

  /- ⟨qual_identifier⟩: its sort, then the term -/
  | .identifier qualified => do
    let (name, qualification) ← qualIdentifier points handler qualified
    call handler (.handleTerm (.identifier name qualification))

  /- `(` ⟨qual_identifier⟩ ⟨term⟩+ `)`: the sort of the function, its arguments, then the term
  after the `)` -/
  | .application function arguments => do
    take points .parenOpen
    let (name, qualification) ← qualIdentifier points handler function
    let handled ← terms arguments
    take points .parenClose
    call handler (.handleTerm (.application name qualification handled))

  /- `(` `let` `(` ⟨var_binding⟩+ `)` ⟨term⟩ `)`: the bound terms, the start after the `)` of
  the bindings, the body, then the end after the `)` -/
  | .«let» bindingList body => do
    takeAll points [.parenOpen, word "let", .parenOpen]
    let handled ← bindings bindingList
    take points .parenClose
    let scope ← call handler (.startLet handled)
    let result ← term body
    take points .parenClose
    call handler (.endLet scope result)

  /- `(` `lambda` `(` ⟨sorted_var⟩+ `)` ⟨term⟩ `)`: the sorts of the variables, the start with
  all of them after the `)` of the variables, the body, then the end after the `)` -/
  | .lambda variables body => do
    takeAll points [.parenOpen, word "lambda", .parenOpen]
    let handled ← sortedVars points handler variables
    take points .parenClose
    let scope ← call handler (.startLambda handled)
    let result ← term body
    take points .parenClose
    call handler (.endLambda scope result)

  /- `(` `forall` or `exists` `(` ⟨sorted_var⟩+ `)` ⟨term⟩ `)`: as `lambda`, with the quantifier
  passed to the start and to the end -/
  | .quantified quantifier variables body => do
    takeAll points [.parenOpen, quantifier.word, .parenOpen]
    let handled ← sortedVars points handler variables
    take points .parenClose
    let scope ← call handler (.startQuantifier quantifier handled)
    let result ← term body
    take points .parenClose
    call handler (.endQuantifier quantifier scope result)

  /- `(` `match` ⟨term⟩ `(` ⟨match_case⟩+ `)` `)`: the scrutinee, the start after its last
  token, the cases, then the match with the scrutinee and the cases after the `)` -/
  | .«match» scrutinee caseList => do
    takeAll points [.parenOpen, word "match"]
    let handled ← term scrutinee
    call handler (.startMatch handled)
    take points .parenOpen
    let handledCases ← cases handled caseList
    takeAll points [.parenClose, .parenClose]
    call handler (.handleMatch handled handledCases)

  /- `(` `!` ⟨term⟩ ⟨attribute⟩+ `)`: the term, its attributes, then the annotation after the
  `)` -/
  | .annotated annotated attributeList => do
    takeAll points [.parenOpen, word "!"]
    let handled ← term annotated
    let handledAttributes ← match attributeList with
      | [] => do
        take points .parenClose
        pure []
      | ⟨keyword, value⟩ :: rest => do
        take points (.keyword keyword)
        attributesThen points handler keyword value rest
    call handler (.annotateTerm handled handledAttributes)

/-- Terms, one after another. -/
def terms : List Tree.Term → Run m ε (List values.term)
  | [] => pure []
  | first :: rest => do
    let handled ← term first
    let others ← terms rest
    pure (handled :: others)

/-- The bindings of a `let`, one after another, each `(` ⟨symbol⟩ ⟨term⟩ `)`: the term of each. -/
def bindings : List (Tree.Symbol × Tree.Term) → Run m ε (List (Tree.Symbol × values.term))
  | [] => pure []
  | (symbol, bound) :: rest => do
    takeAll points [.parenOpen, .symbol symbol]
    let handled ← term bound
    take points .parenClose
    let others ← bindings rest
    pure ((symbol, handled) :: others)

/--
The cases of a `match`, one after another, each `(` ⟨pattern⟩ ⟨term⟩ `)`: the start with the
scrutinee and the pattern after the pattern's last token, the body, then the end after the `)`.
-/
def cases (scrutinee : values.term) :
    List (Tree.Pattern × Tree.Term) → Run m ε (List (Tree.Pattern × values.term))
  | [] => pure []
  | (pattern, body) :: rest => do
    take points .parenOpen
    takeAll points pattern.tokens
    let scope ← call handler (.startMatchCase scrutinee pattern)
    let result ← term body
    take points .parenClose
    let handled ← call handler (.endMatchCase scope result)
    let others ← cases scrutinee rest
    pure ((pattern, handled) :: others)

end

/-! ## The traversal of commands -/

/--
The signature of a function, ⟨symbol⟩ `(` ⟨sorted_var⟩∗ `)` ⟨sort⟩: the sorts of its parameters,
then its result sort.
-/
def signature (symbol : Tree.Symbol) (parameters : List Tree.SortedVar) (result : Tree.Sort) :
    Run m ε (Signature values) := do
  takeAll points [.symbol symbol, .parenOpen]
  let handledParameters ← sortedVars points handler parameters
  take points .parenClose
  let handledResult ← sort points handler result
  pure ⟨symbol, handledParameters, handledResult⟩

/-- Selectors, one after another, each `(` ⟨symbol⟩ ⟨sort⟩ `)`: the sort of each. -/
def selectors : List Tree.SelectorDec → Run m ε (List (Tree.Symbol × values.sort))
  | [] => pure []
  | ⟨symbol, selectorSort⟩ :: rest => do
    takeAll points [.parenOpen, .symbol symbol]
    let handledSort ← sort points handler selectorSort
    take points .parenClose
    let others ← selectors rest
    pure ((symbol, handledSort) :: others)

/--
A constructor, `(` ⟨symbol⟩ ⟨selector_dec⟩∗ `)`, whose `(` is already taken: the sorts of its
selectors.
-/
def constructorAfterOpen (constructor : Tree.ConstructorDec) : Run m ε (Constructor values) := do
  take points (.symbol constructor.symbol)
  let handledSelectors ← selectors points handler constructor.selectors
  take points .parenClose
  pure ⟨constructor.symbol, handledSelectors⟩

/-- Constructors, one after another, each `(` ⟨symbol⟩ ⟨selector_dec⟩∗ `)`. -/
def constructors (list : List Tree.ConstructorDec) : Run m ε (List (Constructor values)) :=
  list.mapM fun constructor => do
    take points .parenOpen
    constructorAfterOpen points handler constructor

/--
A datatype declaration, given the start to make: the start with its sort parameters, then the
sorts of the selectors of its constructors, up to the declaration's `)`. It returns the handled
constructors, for the end that follows.

The start comes when the tokens determine the sort parameters: in the form with `par`, after
the `)` of the parameters; in the form without, after the `(` of the first constructor, the
token after the declaration's `(`, which shows that the form has no `par`.
-/
def datatype (start : List Tree.Symbol → Run m ε Unit) (declaration : Tree.DatatypeDec) :
    Run m ε (List (Constructor values)) :=
  match declaration.parameters, declaration.constructors with
  /- `(` ⟨constructor_dec⟩+ `)` -/
  | [], first :: rest => do
    takeAll points [.parenOpen, .parenOpen]
    start []
    let handledFirst ← constructorAfterOpen points handler first
    let others ← constructors points handler rest
    take points .parenClose
    pure (handledFirst :: others)
  /- `(` `)`: no datatype declaration of any version, written as the form without `par` -/
  | [], [] => do
    takeAll points [.parenOpen, .parenClose]
    start []
    pure []
  /- `(` `par` `(` ⟨symbol⟩+ `)` `(` ⟨constructor_dec⟩+ `)` `)` -/
  | parameters, list => do
    takeAll points [.parenOpen, word "par", .parenOpen]
    takeAll points (parameters.map .symbol)
    take points .parenClose
    start parameters
    take points .parenOpen
    let handled ← constructors points handler list
    takeAll points [.parenClose, .parenClose]
    pure handled

/--
The bodies of recursive functions, one after another, each between its start and its end. A
body has no parentheses of its own: its start comes right after the token before it, and its
end after its last token.
-/
def recursiveBodies : List Tree.Term → Run m ε Unit
  | [] => pure ()
  | body :: rest => do
    call handler .startRecursiveBody
    let handled ← term points handler body
    call handler (.endRecursiveBody handled)
    recursiveBodies rest

/--
The first two tokens of a command, `(` and its name, given the calls due when its `(` arrives.
-/
def opening (atArrival : Run m ε Unit) (name : String) : Run m ε Unit := do
  receive points (.token .parenOpen) atArrival
  take points (word name)

/--
A command, given the calls due when its first token arrives. Every command's last call comes
after its `)`.

A version declaration is a `set-info` like any other: the command switches nothing. The switch
belongs to the script the command is in (`commands`).
-/
def command (atArrival : Run m ε Unit) : Tree.Command → Run m ε Unit
  | .assert asserted => do
    opening points atArrival "assert"
    let handled ← term points handler asserted
    take points .parenClose
    call handler (.commandAssert handled)
  | .checkSat => do
    opening points atArrival "check-sat"
    take points .parenClose
    call handler .commandCheckSat
  | .checkSatAssuming assumptions => do
    opening points atArrival "check-sat-assuming"
    take points .parenOpen
    let handled ← terms points handler assumptions
    takeAll points [.parenClose, .parenClose]
    call handler (.commandCheckSatAssuming handled)
  /- the literals of 2.5 and 2.6 are handled as the terms they are written as -/
  | .checkSatAssumingLiterals literals => do
    opening points atArrival "check-sat-assuming"
    take points .parenOpen
    let handled ← terms points handler (literals.map Tree.PropLiteral.asTerm)
    takeAll points [.parenClose, .parenClose]
    call handler (.commandCheckSatAssuming handled)
  | .declareConst symbol declaredSort => do
    opening points atArrival "declare-const"
    take points (.symbol symbol)
    let handled ← sort points handler declaredSort
    take points .parenClose
    call handler (.commandDeclareConst symbol handled)
  /- the start after the parameters, determined as in `datatype`, the end after the `)` -/
  | .declareDatatype symbol declaration => do
    opening points atArrival "declare-datatype"
    take points (.symbol symbol)
    let handled ← datatype points handler
      (fun parameters => call handler (.startDeclareDatatype symbol parameters)) declaration
    take points .parenClose
    call handler (.endDeclareDatatype handled)
  /- the start after the `)` of the sort declarations; each datatype; the end after the `)` -/
  | .declareDatatypes sortDecs declarations => do
    opening points atArrival "declare-datatypes"
    take points .parenOpen
    takeAll points (sortDecs.flatMap Tree.SortDec.tokens)
    take points .parenClose
    call handler
      (.startDeclareDatatypes (sortDecs.map fun sortDec => (sortDec.symbol, sortDec.arity)))
    take points .parenOpen
    declarations.forM fun declaration => do
      let handled ← datatype points handler
        (fun parameters => call handler (.startDatatypeDeclaration parameters)) declaration
      call handler (.endDatatypeDeclaration handled)
    takeAll points [.parenClose, .parenClose]
    call handler .endDeclareDatatypes
  | .declareFun symbol parameters result => do
    opening points atArrival "declare-fun"
    takeAll points [.symbol symbol, .parenOpen]
    let handledParameters ← sorts points handler parameters
    take points .parenClose
    let handledResult ← sort points handler result
    take points .parenClose
    call handler (.commandDeclareFun symbol handledParameters handledResult)
  | .declareSort symbol arity => do
    opening points atArrival "declare-sort"
    takeAll points [.symbol symbol, .numeral arity, .parenClose]
    call handler (.commandDeclareSort symbol arity)
  | .declareSortParameter symbol => do
    opening points atArrival "declare-sort-parameter"
    takeAll points [.symbol symbol, .parenClose]
    call handler (.commandDeclareSortParameter symbol)
  /- the sort, the body, then the definition after the `)` -/
  | .defineConst symbol definedSort body => do
    opening points atArrival "define-const"
    take points (.symbol symbol)
    let handledSort ← sort points handler definedSort
    let handledBody ← term points handler body
    take points .parenClose
    call handler (.commandDefineConst symbol handledSort handledBody)
  /- the start after the result sort's last token, the body, the end after the `)` -/
  | .defineFun ⟨symbol, parameters, result, body⟩ => do
    opening points atArrival "define-fun"
    let handledSignature ← signature points handler symbol parameters result
    call handler (.startDefineFun handledSignature)
    let handledBody ← term points handler body
    take points .parenClose
    call handler (.endDefineFun handledBody)
  /- as `define-fun` -/
  | .defineFunRec ⟨symbol, parameters, result, body⟩ => do
    opening points atArrival "define-fun-rec"
    let handledSignature ← signature points handler symbol parameters result
    call handler (.startDefineFunRec handledSignature)
    let handledBody ← term points handler body
    take points .parenClose
    call handler (.endDefineFunRec handledBody)
  /- the start after the `)` of the declarations; the bodies, the first one's start after the
  `(` before it; the end after the `)` -/
  | .defineFunsRec declarations bodies => do
    opening points atArrival "define-funs-rec"
    take points .parenOpen
    let signatures ← declarations.mapM fun declaration => do
      take points .parenOpen
      let handled ← signature points handler declaration.symbol declaration.parameters
        declaration.result
      take points .parenClose
      pure handled
    take points .parenClose
    call handler (.startDefineFunsRec signatures)
    take points .parenOpen
    recursiveBodies points handler bodies
    takeAll points [.parenClose, .parenClose]
    call handler .endDefineFunsRec
  /- the start after the `)` of the parameters, the sort, the end after the `)` -/
  | .defineSort symbol parameters definedSort => do
    opening points atArrival "define-sort"
    takeAll points [.symbol symbol, .parenOpen]
    takeAll points (parameters.map .symbol)
    take points .parenClose
    call handler (.startDefineSort symbol parameters)
    let handled ← sort points handler definedSort
    take points .parenClose
    call handler (.endDefineSort handled)
  | .echo content => do
    opening points atArrival "echo"
    takeAll points [.string content, .parenClose]
    call handler (.commandEcho content)
  | .exit => do
    opening points atArrival "exit"
    take points .parenClose
    call handler .commandExit
  | .getAssertions => do
    opening points atArrival "get-assertions"
    take points .parenClose
    call handler .commandGetAssertions
  | .getAssignment => do
    opening points atArrival "get-assignment"
    take points .parenClose
    call handler .commandGetAssignment
  | .getInfo flag => do
    opening points atArrival "get-info"
    takeAll points [.keyword flag, .parenClose]
    call handler (.commandGetInfo flag)
  | .getModel => do
    opening points atArrival "get-model"
    take points .parenClose
    call handler .commandGetModel
  | .getOption keyword => do
    opening points atArrival "get-option"
    takeAll points [.keyword keyword, .parenClose]
    call handler (.commandGetOption keyword)
  | .getProof => do
    opening points atArrival "get-proof"
    take points .parenClose
    call handler .commandGetProof
  | .getUnsatAssumptions => do
    opening points atArrival "get-unsat-assumptions"
    take points .parenClose
    call handler .commandGetUnsatAssumptions
  | .getUnsatCore => do
    opening points atArrival "get-unsat-core"
    take points .parenClose
    call handler .commandGetUnsatCore
  | .getValue valueTerms => do
    opening points atArrival "get-value"
    take points .parenOpen
    let handled ← terms points handler valueTerms
    takeAll points [.parenClose, .parenClose]
    call handler (.commandGetValue handled)
  | .pop count => do
    opening points atArrival "pop"
    takeAll points [.numeral count, .parenClose]
    call handler (.commandPop count)
  | .push count => do
    opening points atArrival "push"
    takeAll points [.numeral count, .parenClose]
    call handler (.commandPush count)
  | .reset => do
    opening points atArrival "reset"
    take points .parenClose
    call handler .commandReset
  | .resetAssertions => do
    opening points atArrival "reset-assertions"
    take points .parenClose
    call handler .commandResetAssertions
  | .setInfo ⟨keyword, value⟩ => do
    opening points atArrival "set-info"
    take points (.keyword keyword)
    let handled ← attributeThen points handler keyword .parenClose value
    call handler (.commandSetInfo handled)
  | .setLogic symbol => do
    opening points atArrival "set-logic"
    takeAll points [.symbol symbol, .parenClose]
    call handler (.commandSetLogic symbol)
  | .setOption ⟨keyword, value⟩ => do
    opening points atArrival "set-option"
    take points (.keyword keyword)
    let handled ← attributeThen points handler keyword .parenClose value
    call handler (.commandSetOption handled)

/-! ## The traversal of a script -/

/--
Whether the command is a version declaration that names no supported version: a `set-info` of
`:smt-lib-version` whose value is not the number of a supported version, a decimal of no
supported version, a symbol, a list, or no value at all. No script has such a command
(`Tree.Command.modeAfter` gives `none` for it); a parser rejects it after its `)`.

Reading M1: the value of a declaration is the number of a supported version.
-/
def _root_.BSmtLib.Spec.Grammar.Tree.Command.namesNoVersion : Tree.Command → Bool
  | .setInfo ⟨keyword, value⟩ =>
    decide (keyword = chars "smt-lib-version") &&
      match value with
      | some (.constant (.decimal decimal)) => (versionOfNumber decimal).isNone
      | _ => true
  | _ => false

/--
The switch of a script to the version a declaration names, right after the declaration's
`set-info`, given the producer and the number of declarations the script made before it: the
check against the policy, the producer's switch, which it may refuse, then the handler's switch.
A refusal is rejected as a version the policy does not allow. The new version holds from the
next command.
-/
def switchVersion (producer : Producer m) (policy : VersionPolicy) (declarations : Nat)
    (version : Version) : Run m ε Unit := do
  match policy.check declarations version with
  | .error error => throw (.syntax error)
  | .ok () => pure ()
  ExceptT.adapt (fun _ => Cause.syntax .unsupportedVersion) (producer.setVersion version)
  call handler (.setVersion version)

/--
The commands of a script, given the producer, the calls due when the next token arrives and the
number of version declarations made before them, up to the end of the input, which the parser
receives as well. After a version declaration, the script switches the version. After `exit`,
the producer discards the rest of the input and the script ends; the parser then receives the
end of the input alone. A version declaration that names no supported version is rejected
after its `set-info`, as a version that is not supported.
-/
def commands (producer : Producer m) (policy : VersionPolicy) :
    Run m ε Unit → Nat → List Tree.Command → Run m ε Unit
  | atArrival, _, [] => do
    receive points .endOfInput atArrival
    ExceptT.lift handler.endScript
  | atArrival, _, .exit :: _ => do
    command points handler atArrival .exit
    ExceptT.lift producer.discardRest
    ExceptT.lift handler.endScript
    receive points .endOfInput
  | atArrival, declarations, first :: rest => do
    command points handler atArrival first
    match first.declaredVersion with
    | none =>
      if first.namesNoVersion then throw (.syntax .unsupportedVersion)
      else commands producer policy (pure ()) declarations rest
    | some version => do
      switchVersion handler producer policy declarations version
      commands producer policy (pure ()) (declarations + 1) rest

/--
A script under a version policy, given the producer: the start, when its first token arrives,
before the parser processes it; its commands, each version declaration followed by its check
against the policy and the switches; then the end, at the end of the input or, after `exit`,
after the producer's discarding and before the end of the input.
-/
def script (producer : Producer m) (policy : VersionPolicy) (commandList : List Tree.Command) :
    Run m ε Unit :=
  commands points handler producer policy (ExceptT.lift handler.startScript) 0 commandList

end

end Traversal

end BSmtLib.Spec.Parser
