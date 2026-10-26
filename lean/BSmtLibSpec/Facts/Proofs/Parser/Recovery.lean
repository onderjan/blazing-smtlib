module

public import BSmtLibSpec.Parser
public import BSmtLibSpec.Grammar.Properties

@[expose] public section

/-!
# Rebuilding a script from its calls

`recover` rebuilds the commands of a script from the calls of its recording run alone. It goes
through the calls in order and keeps, for each call, what it stands for (`Fragment`): a call
that returns a handled value stands for the tree it reports, built from what the earlier calls
it names stand for. A recorded call names an earlier call by its number, which is the position
of that call's fragment. A command made of several calls waits in `Pending` until its last call.
The handler's version switch changes the version in force, which tells the literals of
2.5 and 2.6 from terms in `check-sat-assuming`.

Not trusted: this is a check of the specification.
-/

namespace BSmtLibSpec.Facts.Proofs.Parser.Recovery

open BSmtLibSpec.Lexicon BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal

/-- What a call stands for. -/
inductive Fragment where
  /-- A call that returns nothing. -/
  | none
  | sort (sort : Tree.«Sort»)
  | sExpr (sExpr : Tree.SExpr)
  | «attribute» (annotation : Tree.Attribute)
  | term (term : Tree.Term)
  /-- The start of a `let`: its bindings. -/
  | bindings (bindings : List (Tree.Symbol × Tree.Term))
  /-- The start of a quantifier or a `lambda`: its variables. -/
  | variables (variables : List Tree.SortedVar)
  /-- The start of a case of a `match`: its pattern. -/
  | pattern (pattern : Tree.Pattern)

/-- What the calls so far stand for, each at its number. -/
abbrev Env := List Fragment

namespace Env

variable (env : Env)

def sort (i : Nat) : Option Tree.«Sort» :=
  match env[i]? with
  | some (.sort sort) => some sort
  | _ => Option.none

def sExpr (i : Nat) : Option Tree.SExpr :=
  match env[i]? with
  | some (.sExpr sExpr) => some sExpr
  | _ => Option.none

def «attribute» (i : Nat) : Option Tree.Attribute :=
  match env[i]? with
  | some (.«attribute» annotation) => some annotation
  | _ => Option.none

def term (i : Nat) : Option Tree.Term :=
  match env[i]? with
  | some (.term term) => some term
  | _ => Option.none

def bindings (i : Nat) : Option (List (Tree.Symbol × Tree.Term)) :=
  match env[i]? with
  | some (.bindings bindings) => some bindings
  | _ => Option.none

def variables (i : Nat) : Option (List Tree.SortedVar) :=
  match env[i]? with
  | some (.variables variables) => some variables
  | _ => Option.none

/-- Sorted variables, from symbols and the numbers of their sorts. -/
def sortedVars (list : List (Tree.Symbol × Nat)) : Option (List Tree.SortedVar) :=
  list.mapM fun (symbol, i) => (env.sort i).map fun sort => ⟨symbol, sort⟩

/-- A qualified identifier, from its identifier and the number of its sort, if it has one. -/
def qualIdentifier (identifier : Tree.Identifier) : Option Nat → Option Tree.QualIdentifier
  | Option.none => some (.plain identifier)
  | some i => (env.sort i).map (.as identifier)

/-- The s-expression a node stands for. -/
def sExprNode : SExprNode Recorded → Option Tree.SExpr
  | .constant constant => some (.constant constant)
  | .symbol symbol => some (.symbol symbol)
  | .reserved w => some (.reserved w)
  | .keyword name => some (.keyword name)
  | .list items => (items.mapM env.sExpr).map .list

/-- The attribute value a node stands for. -/
def valueNode : AttributeValueNode Recorded → Option Tree.AttributeValue
  | .constant constant => some (.constant constant)
  | .symbol symbol => some (.symbol symbol)
  | .list items => (items.mapM env.sExpr).map .list

/-- The term a node stands for. -/
def termNode : TermNode Recorded → Option Tree.Term
  | .constant constant => some (.constant constant)
  | .identifier identifier sort => (env.qualIdentifier identifier sort).map .identifier
  | .application identifier sort arguments => do
    let function ← env.qualIdentifier identifier sort
    let arguments ← arguments.mapM env.term
    pure (.application function arguments)

/-- The function declaration a signature stands for. -/
def signature (signature : Signature Recorded) : Option Tree.FunctionDec := do
  let parameters ← env.sortedVars signature.parameters
  let result ← env.sort signature.result
  pure ⟨signature.symbol, parameters, result⟩

/-- The constructor declaration a handled constructor stands for. -/
def constructor (constructor : Constructor Recorded) : Option Tree.ConstructorDec :=
  (constructor.selectors.mapM fun (symbol, i) =>
    (env.sort i).map fun sort => (⟨symbol, sort⟩ : Tree.SelectorDec)).map
      (⟨constructor.symbol, ·⟩)

/-- What a call that returns a value stands for; `none` for one that returns nothing. -/
def fragment : {returns : Returns} → Call Recorded returns → Option Fragment
  | _, .handleSort identifier arguments =>
    (arguments.mapM env.sort).map fun arguments => .sort (.mk identifier arguments)
  | _, .handleSExpr node => (env.sExprNode node).map .sExpr
  | _, .handleAttribute keyword Option.none => some (.«attribute» ⟨keyword, Option.none⟩)
  | _, .handleAttribute keyword (some node) =>
    (env.valueNode node).map fun value => .«attribute» ⟨keyword, some value⟩
  | _, .handleTerm node => (env.termNode node).map .term
  | _, .annotateTerm term attributes => do
    let term ← env.term term
    let attributes ← attributes.mapM env.«attribute»
    pure (.term (.annotated term attributes))
  | _, .startLet bindings =>
    (bindings.mapM fun ((symbol, i) : Tree.Symbol × Nat) =>
      (env.term i).map (symbol, ·)).map .bindings
  | _, .endLet scope body => do
    let bindings ← env.bindings scope
    let body ← env.term body
    pure (.term (.«let» bindings body))
  | _, .startQuantifier _ variables => (env.sortedVars variables).map .variables
  | _, .endQuantifier quantifier scope body => do
    let variables ← env.variables scope
    let body ← env.term body
    pure (.term (.quantified quantifier variables body))
  | _, .startLambda variables => (env.sortedVars variables).map .variables
  | _, .endLambda scope body => do
    let variables ← env.variables scope
    let body ← env.term body
    pure (.term (.lambda variables body))
  | _, .startMatchCase _ pattern => some (.pattern pattern)
  | _, .endMatchCase _ _ body => (env.term body).map .term
  | _, .endMatch scrutinee cases => do
    let scrutinee ← env.term scrutinee
    let cases ← cases.mapM fun ((pattern, i) : Tree.Pattern × Nat) =>
      (env.term i).map (pattern, ·)
    pure (.term (.«match» scrutinee cases))
  | _, _ => some .none

end Env

/-- A command made of several calls, before its last call. -/
inductive Pending where
  | none
  | declareDatatype (symbol : Tree.Symbol) (parameters : List Tree.Symbol)
  /-- `declare-datatypes`: its sorts, the datatypes declared so far, and the parameters of the
  datatype being declared. -/
  | declareDatatypes (sorts : List Tree.SortDec) (done : List Tree.DatatypeDec)
      (parameters : List Tree.Symbol)
  | defineFun (declaration : Tree.FunctionDec)
  | defineFunRec (declaration : Tree.FunctionDec)
  /-- `define-funs-rec`: its declarations and the bodies so far. -/
  | defineFunsRec (declarations : List Tree.FunctionDec) (bodies : List Tree.Term)
  | defineSort (symbol : Tree.Symbol) (parameters : List Tree.Symbol)

/-- Where the rebuilding is. -/
structure State where
  version : Version
  env : Env
  pending : Pending
  commands : List Tree.Command

/-- The literal a term of `check-sat-assuming` is written as, in 2.5 and 2.6. -/
def literalOf : Tree.Term → Option Tree.PropLiteral
  | .identifier (.plain ⟨symbol, []⟩) => some (.positive symbol)
  | .application (.plain ⟨negation, []⟩) [.identifier (.plain ⟨symbol, []⟩)] =>
    some (.negative negation symbol)
  | _ => Option.none

namespace State

variable (state : State)

/-- The state with the command added. -/
def add (command : Tree.Command) : State := { state with commands := state.commands ++ [command] }

/-- What a call that returns nothing does to the commands. -/
def command : Call Recorded .nothing → Option State
  | .commandAssert term => (state.env.term term).map fun term => state.add (.assert term)
  | .commandCheckSat => some (state.add .checkSat)
  | .commandCheckSatAssuming terms => do
    let terms ← terms.mapM state.env.term
    if Version.v2_7 ∈ state.version.upTo then pure (state.add (.checkSatAssuming terms))
    else do
      let literals ← terms.mapM literalOf
      pure (state.add (.checkSatAssumingLiterals literals))
  | .commandDeclareConst symbol sort =>
    (state.env.sort sort).map fun sort => state.add (.declareConst symbol sort)
  | .startDeclareDatatype symbol parameters =>
    some { state with pending := .declareDatatype symbol parameters }
  | .endDeclareDatatype constructors =>
    match state.pending with
    | .declareDatatype symbol parameters => do
      let constructors ← constructors.mapM state.env.constructor
      pure { state.add (.declareDatatype symbol ⟨parameters, constructors⟩) with pending := .none }
    | _ => Option.none
  | .startDeclareDatatypes sorts =>
    some { state with
      pending := .declareDatatypes (sorts.map fun (symbol, arity) => ⟨symbol, arity⟩) [] [] }
  | .startDatatypeDeclaration parameters =>
    match state.pending with
    | .declareDatatypes sorts done _ =>
      some { state with pending := .declareDatatypes sorts done parameters }
    | _ => Option.none
  | .endDatatypeDeclaration constructors =>
    match state.pending with
    | .declareDatatypes sorts done parameters => do
      let constructors ← constructors.mapM state.env.constructor
      pure { state with
        pending := .declareDatatypes sorts (done ++ [⟨parameters, constructors⟩]) [] }
    | _ => Option.none
  | .endDeclareDatatypes =>
    match state.pending with
    | .declareDatatypes sorts done _ =>
      some { state.add (.declareDatatypes sorts done) with pending := .none }
    | _ => Option.none
  | .commandDeclareFun symbol parameters result => do
    let parameters ← parameters.mapM state.env.sort
    let result ← state.env.sort result
    pure (state.add (.declareFun symbol parameters result))
  | .commandDeclareSort symbol arity => some (state.add (.declareSort symbol arity))
  | .commandDeclareSortParameter symbol => some (state.add (.declareSortParameter symbol))
  | .commandDefineConst symbol sort body => do
    let sort ← state.env.sort sort
    let body ← state.env.term body
    pure (state.add (.defineConst symbol sort body))
  | .startDefineFun signature =>
    (state.env.signature signature).map fun declaration =>
      { state with pending := .defineFun declaration }
  | .endDefineFun body =>
    match state.pending with
    | .defineFun ⟨symbol, parameters, result⟩ => do
      let body ← state.env.term body
      pure { state.add (.defineFun ⟨symbol, parameters, result, body⟩) with pending := .none }
    | _ => Option.none
  | .startDefineFunRec signature =>
    (state.env.signature signature).map fun declaration =>
      { state with pending := .defineFunRec declaration }
  | .endDefineFunRec body =>
    match state.pending with
    | .defineFunRec ⟨symbol, parameters, result⟩ => do
      let body ← state.env.term body
      pure { state.add (.defineFunRec ⟨symbol, parameters, result, body⟩) with
        pending := .none }
    | _ => Option.none
  | .startDefineFunsRec signatures =>
    (signatures.mapM state.env.signature).map fun declarations =>
      { state with pending := .defineFunsRec declarations [] }
  | .startRecursiveBody _ => some state
  | .endRecursiveBody body =>
    match state.pending with
    | .defineFunsRec declarations bodies =>
      (state.env.term body).map fun body =>
        { state with pending := .defineFunsRec declarations (bodies ++ [body]) }
    | _ => Option.none
  | .endDefineFunsRec =>
    match state.pending with
    | .defineFunsRec declarations bodies =>
      some { state.add (.defineFunsRec declarations bodies) with pending := .none }
    | _ => Option.none
  | .startDefineSort symbol parameters =>
    some { state with pending := .defineSort symbol parameters }
  | .endDefineSort sort =>
    match state.pending with
    | .defineSort symbol parameters =>
      (state.env.sort sort).map fun sort =>
        { state.add (.defineSort symbol parameters sort) with pending := .none }
    | _ => Option.none
  | .commandEcho content => some (state.add (.echo content))
  | .commandExit => some (state.add .exit)
  | .commandGetAssertions => some (state.add .getAssertions)
  | .commandGetAssignment => some (state.add .getAssignment)
  | .commandGetInfo flag => some (state.add (.getInfo flag))
  | .commandGetModel => some (state.add .getModel)
  | .commandGetOption keyword => some (state.add (.getOption keyword))
  | .commandGetProof => some (state.add .getProof)
  | .commandGetUnsatAssumptions => some (state.add .getUnsatAssumptions)
  | .commandGetUnsatCore => some (state.add .getUnsatCore)
  | .commandGetValue terms =>
    (terms.mapM state.env.term).map fun terms => state.add (.getValue terms)
  | .commandPop count => some (state.add (.pop count))
  | .commandPush count => some (state.add (.push count))
  | .commandReset => some (state.add .reset)
  | .commandResetAssertions => some (state.add .resetAssertions)
  | .commandSetInfo info => (state.env.«attribute» info).map fun info => state.add (.setInfo info)
  | .commandSetLogic symbol => some (state.add (.setLogic symbol))
  | .commandSetOption option =>
    (state.env.«attribute» option).map fun option => state.add (.setOption option)
  | .startMatch _ => some state

/-- The state with the fragment of a call added at the call's number. -/
def push (fragment : Fragment) : State := { state with env := state.env ++ [fragment] }

/-- What a call does: its fragment goes at its number, and a call that returns nothing acts on
the commands. -/
def call : {returns : Returns} → Call Recorded returns → Option State
  | .nothing, request => (state.push .none).command request
  | _, request => (state.env.fragment request).map state.push

end State

/-- What an event does: a call acts, the handler's version switch stands for nothing and
changes the version in force, and every other event is not a call. -/
def step (state : State) : Event → Option State
  | .call _ request => state.call request
  | .handlerSwitch version => some { state.push .none with version }
  | _ => some state

/-- The state where the rebuilding of a script with the initial version starts. -/
def initial (version : Version) : State := ⟨version, [], .none, []⟩

/-- The commands that the calls rebuild, with the initial version, if they rebuild any. -/
def recover (version : Version) (calls : List Event) : Option (List Tree.Command) :=
  (calls.foldlM step (initial version)).map State.commands

end BSmtLibSpec.Facts.Proofs.Parser.Recovery
