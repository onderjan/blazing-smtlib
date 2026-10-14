module

public import BSmtLibSpec.Facts.Proofs.Parser.Program

@[expose] public section

/-!
# Equations of the traversal

Equations of the functions of `BSmtLibSpec.Parser.Traversal` for each form of their argument, which
hold by definition. Lean does not derive all of them itself: it cannot for functions that
match a list against `[]` in one case and against any list in the next.

Not trusted: everything here is proved.
-/

namespace BSmtLibSpec.Facts.Proofs.Parser.Equations

open BSmtLibSpec.Lexicon BSmtLibSpec.Grammar BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal

variable {m : Type → Type} [Monad m] {ε : Type} {values : Values}
variable {points : Points m} {handler : Handler m ε values}


theorem sort_nil (identifier : Tree.Identifier) :
    sort points handler (.mk identifier []) =
      (do takeAll points identifier.tokens
          Program.callSort handler (.handleSort identifier [])) := rfl

theorem sort_cons (identifier : Tree.Identifier) (first : Tree.«Sort») (others : List Tree.«Sort») :
    sort points handler (.mk identifier (first :: others)) =
      (do take points .parenOpen; takeAll points identifier.tokens
          let handled ← sorts points handler (first :: others); take points .parenClose
          Program.callSort handler (.handleSort identifier handled)) := rfl

theorem sExpr_constant (value) :
    sExpr points handler (.constant value) = (do
      take points value.token
      Program.callSExpr handler (.handleSExpr (.constant value))) := rfl

theorem sExpr_symbol (name) :
    sExpr points handler (.symbol name) = (do
      take points (.symbol name)
      Program.callSExpr handler (.handleSExpr (.symbol name))) := rfl

theorem sExpr_reserved (w) :
    sExpr points handler (.reserved w) = (do
      take points (.reserved w)
      Program.callSExpr handler (.handleSExpr (.reserved w))) := rfl

theorem sExpr_keyword (name) :
    sExpr points handler (.keyword name) = (do
      take points (.keyword name)
      Program.callSExpr handler (.handleSExpr (.keyword name))) := rfl

theorem sExpr_list (items) :
    sExpr points handler (.list items) = (do
      take points .parenOpen
      let handled ← sExprs points handler items
      take points .parenClose
      Program.callSExpr handler (.handleSExpr (.list handled))) := rfl

theorem attributeThen_some (keyword) (following) (value) :
    attributeThen points handler keyword following (some value) = (do
      let node ← attributeValue points handler value
      let handled ← Program.callAttribute handler (.handleAttribute keyword (some node))
      take points following
      pure handled) := rfl

theorem attributeThen_none (keyword) (following) :
    attributeThen points handler keyword following (none) = (do
      take points following
      Program.callAttribute handler (.handleAttribute keyword none)) := rfl

theorem term_constant (value) (atArrival : Run m ε Unit) :
    term points handler (.constant value) atArrival = (do
      receive points (.token value.token) atArrival
      Program.callTerm handler (.handleTerm (.constant value))) := rfl

theorem term_identifier (qualified) (atArrival : Run m ε Unit) :
    term points handler (.identifier qualified) atArrival = (do
      let (name, qualification) ← qualIdentifier points handler qualified atArrival
      Program.callTerm handler (.handleTerm (.identifier name qualification))) := rfl

theorem term_application (function) (arguments) (atArrival : Run m ε Unit) :
    term points handler (.application function arguments) atArrival = (do
      receive points (.token .parenOpen) atArrival
      let (name, qualification) ← qualIdentifier points handler function
      let handled ← terms points handler arguments
      take points .parenClose
      Program.callTerm handler (.handleTerm (.application name qualification handled))) := rfl

theorem term_let (bindingList) (body) (atArrival : Run m ε Unit) :
    term points handler (.«let» bindingList body) atArrival = (do
      takeAllArriving points atArrival [.parenOpen, word "let", .parenOpen]
      let handled ← bindings points handler bindingList
      take points .parenClose
      let scope ← Program.callScope handler (.startLet handled)
      let result ← term points handler body
      take points .parenClose
      Program.callTerm handler (.endLet scope result)) := rfl

theorem term_lambda (variables) (body) (atArrival : Run m ε Unit) :
    term points handler (.lambda variables body) atArrival = (do
      takeAllArriving points atArrival [.parenOpen, word "lambda", .parenOpen]
      let handled ← sortedVars points handler variables
      take points .parenClose
      let scope ← Program.callScope handler (.startLambda handled)
      let result ← term points handler body
      take points .parenClose
      Program.callTerm handler (.endLambda scope result)) := rfl

theorem term_quantified (quantifier) (variables) (body) (atArrival : Run m ε Unit) :
    term points handler (.quantified quantifier variables body) atArrival = (do
      takeAllArriving points atArrival [.parenOpen, quantifier.word, .parenOpen]
      let handled ← sortedVars points handler variables
      take points .parenClose
      let scope ← Program.callScope handler (.startQuantifier quantifier handled)
      let result ← term points handler body
      take points .parenClose
      Program.callTerm handler (.endQuantifier quantifier scope result)) := rfl

theorem term_match (scrutinee) (caseList) (atArrival : Run m ε Unit) :
    term points handler (.«match» scrutinee caseList) atArrival = (do
      takeAllArriving points atArrival [.parenOpen, word "match"]
      let handled ← term points handler scrutinee
      Program.callUnit handler (.startMatch handled)
      take points .parenOpen
      let handledCases ← cases points handler handled caseList
      takeAll points [.parenClose, .parenClose]
      Program.callTerm handler (.endMatch handled handledCases)) := rfl

theorem term_annotated (annotated) (attributeList) (atArrival : Run m ε Unit) :
    term points handler (.annotated annotated attributeList) atArrival = (do
      takeAllArriving points atArrival [.parenOpen, word "!"]
      let handled ← term points handler annotated
      let handledAttributes ← match attributeList with
        | [] => do
          take points .parenClose
          pure []
        | ⟨keyword, value⟩ :: rest => do
          take points (.keyword keyword)
          attributesThen points handler keyword value rest
      Program.callTerm handler (.annotateTerm handled handledAttributes)) := rfl

theorem cases_cons (scrutinee : values.term) (pattern : Tree.Pattern) (body : Tree.Term)
    (rest : List (Tree.Pattern × Tree.Term)) :
    cases points handler scrutinee ((pattern, body) :: rest) = (do
      take points .parenOpen
      takeAll points pattern.tokens
      let scope ← Program.callScope handler (.startMatchCase scrutinee pattern)
      let result ← term points handler body
      take points .parenClose
      let handled ← Program.callTerm handler (.endMatchCase scope scrutinee result)
      let others ← cases points handler scrutinee rest
      pure ((pattern, handled) :: others)) := rfl

theorem recursiveBodies_cons (signature : Signature values) (body : Tree.Term)
    (rest : List (Signature values × Tree.Term)) :
    recursiveBodies points handler ((signature, body) :: rest) = (do
      let handled ← term points handler body
        (Program.callUnit handler (.startRecursiveBody signature))
      Program.callUnit handler (.endRecursiveBody handled)
      recursiveBodies points handler rest) := rfl

theorem switchVersion_eq (producer : Producer m)
    (policy : VersionPolicy) (declarations : Nat) (version : Version) :
    switchVersion handler producer policy declarations version = (do
      match policy.check declarations version with
      | .error error => throw (.syntax error)
      | .ok () => pure ()
      ExceptT.adapt (fun _ => Cause.«syntax» .unsupportedVersion) (producer.setVersion version)
      ExceptT.lift (handler.setVersion version)) := rfl

theorem command_assert (asserted) :
    command points handler (.assert asserted) = (do
      opening points "assert"
      let handled ← term points handler asserted
      take points .parenClose
      Program.callUnit handler (.commandAssert handled)) := rfl

theorem command_checkSat :
    command points handler (.checkSat) = (do
      opening points "check-sat"
      take points .parenClose
      Program.callUnit handler .commandCheckSat) := rfl

theorem command_checkSatAssuming (assumptions) :
    command points handler (.checkSatAssuming assumptions) = (do
      opening points "check-sat-assuming"
      take points .parenOpen
      let handled ← terms points handler assumptions
      takeAll points [.parenClose, .parenClose]
      Program.callUnit handler (.commandCheckSatAssuming handled)) := rfl

theorem command_checkSatAssumingLiterals (literals) :
    command points handler (.checkSatAssumingLiterals literals) = (do
      opening points "check-sat-assuming"
      take points .parenOpen
      let handled ← terms points handler (literals.map Tree.PropLiteral.asTerm)
      takeAll points [.parenClose, .parenClose]
      Program.callUnit handler (.commandCheckSatAssuming handled)) := rfl

theorem command_declareConst (symbol) (declaredSort) :
    command points handler (.declareConst symbol declaredSort) = (do
      opening points "declare-const"
      take points (.symbol symbol)
      let handled ← sort points handler declaredSort
      take points .parenClose
      Program.callUnit handler (.commandDeclareConst symbol handled)) := rfl

theorem command_declareDatatype (symbol) (declaration) :
    command points handler (.declareDatatype symbol declaration) = (do
      opening points "declare-datatype"
      take points (.symbol symbol)
      let handled ← datatype points handler
        (fun parameters => Program.callUnit handler (.startDeclareDatatype symbol parameters))
        declaration
      take points .parenClose
      Program.callUnit handler (.endDeclareDatatype handled)) := rfl

theorem command_declareDatatypes (sortDecs) (declarations) :
    command points handler (.declareDatatypes sortDecs declarations) = (do
      opening points "declare-datatypes"
      take points .parenOpen
      takeAll points (sortDecs.flatMap Tree.SortDec.tokens)
      take points .parenClose
      Program.callUnit handler
        (.startDeclareDatatypes (sortDecs.map fun sortDec => (sortDec.symbol, sortDec.arity)))
      take points .parenOpen
      declarations.forM fun declaration => do
        let handled ← datatype points handler
          (fun parameters => Program.callUnit handler (.startDatatypeDeclaration parameters))
          declaration
        Program.callUnit handler (.endDatatypeDeclaration handled)
      takeAll points [.parenClose, .parenClose]
      Program.callUnit handler .endDeclareDatatypes) := rfl

theorem command_declareFun (symbol) (parameters) (result) :
    command points handler (.declareFun symbol parameters result) = (do
      opening points "declare-fun"
      takeAll points [.symbol symbol, .parenOpen]
      let handledParameters ← sorts points handler parameters
      take points .parenClose
      let handledResult ← sort points handler result
      take points .parenClose
      Program.callUnit handler (.commandDeclareFun symbol handledParameters handledResult)) := rfl

theorem command_declareSort (symbol) (arity) :
    command points handler (.declareSort symbol arity) = (do
      opening points "declare-sort"
      takeAll points [.symbol symbol, .numeral arity, .parenClose]
      Program.callUnit handler (.commandDeclareSort symbol arity)) := rfl

theorem command_declareSortParameter (symbol) :
    command points handler (.declareSortParameter symbol) = (do
      opening points "declare-sort-parameter"
      takeAll points [.symbol symbol, .parenClose]
      Program.callUnit handler (.commandDeclareSortParameter symbol)) := rfl

theorem command_defineConst (symbol) (definedSort) (body) :
    command points handler (.defineConst symbol definedSort body) = (do
      opening points "define-const"
      take points (.symbol symbol)
      let handledSort ← sort points handler definedSort
      let handledBody ← term points handler body
      take points .parenClose
      Program.callUnit handler (.commandDefineConst symbol handledSort handledBody)) := rfl

theorem command_defineFun (symbol) (parameters) (result) (body) :
    command points handler (.defineFun ⟨symbol, parameters, result, body⟩) = (do
      opening points "define-fun"
      let handledSignature ← signature points handler symbol parameters result
      Program.callUnit handler (.startDefineFun handledSignature)
      let handledBody ← term points handler body
      take points .parenClose
      Program.callUnit handler (.endDefineFun handledBody)) := rfl

theorem command_defineFunRec (symbol) (parameters) (result) (body) :
    command points handler (.defineFunRec ⟨symbol, parameters, result, body⟩) = (do
      opening points "define-fun-rec"
      let handledSignature ← signature points handler symbol parameters result
      Program.callUnit handler (.startDefineFunRec handledSignature)
      let handledBody ← term points handler body
      take points .parenClose
      Program.callUnit handler (.endDefineFunRec handledBody)) := rfl

theorem command_defineFunsRec (declarations) (bodies) :
    command points handler (.defineFunsRec declarations bodies) = (do
      opening points "define-funs-rec"
      take points .parenOpen
      let signatures ← declarations.mapM fun declaration => do
        take points .parenOpen
        let handled ← signature points handler declaration.symbol declaration.parameters
          declaration.result
        take points .parenClose
        pure handled
      take points .parenClose
      Program.callUnit handler (.startDefineFunsRec signatures)
      take points .parenOpen
      recursiveBodies points handler (signatures.zip bodies)
      takeAll points [.parenClose, .parenClose]
      Program.callUnit handler .endDefineFunsRec) := rfl

theorem command_defineSort (symbol) (parameters) (definedSort) :
    command points handler (.defineSort symbol parameters definedSort) = (do
      opening points "define-sort"
      takeAll points [.symbol symbol, .parenOpen]
      takeAll points (parameters.map .symbol)
      take points .parenClose
      Program.callUnit handler (.startDefineSort symbol parameters)
      let handled ← sort points handler definedSort
      take points .parenClose
      Program.callUnit handler (.endDefineSort handled)) := rfl

theorem command_echo (content) :
    command points handler (.echo content) = (do
      opening points "echo"
      takeAll points [.string content, .parenClose]
      Program.callUnit handler (.commandEcho content)) := rfl

theorem command_exit :
    command points handler (.exit) = (do
      opening points "exit"
      take points .parenClose
      Program.callUnit handler .commandExit) := rfl

theorem command_getAssertions :
    command points handler (.getAssertions) = (do
      opening points "get-assertions"
      take points .parenClose
      Program.callUnit handler .commandGetAssertions) := rfl

theorem command_getAssignment :
    command points handler (.getAssignment) = (do
      opening points "get-assignment"
      take points .parenClose
      Program.callUnit handler .commandGetAssignment) := rfl

theorem command_getInfo (flag) :
    command points handler (.getInfo flag) = (do
      opening points "get-info"
      takeAll points [.keyword flag, .parenClose]
      Program.callUnit handler (.commandGetInfo flag)) := rfl

theorem command_getModel :
    command points handler (.getModel) = (do
      opening points "get-model"
      take points .parenClose
      Program.callUnit handler .commandGetModel) := rfl

theorem command_getOption (keyword) :
    command points handler (.getOption keyword) = (do
      opening points "get-option"
      takeAll points [.keyword keyword, .parenClose]
      Program.callUnit handler (.commandGetOption keyword)) := rfl

theorem command_getProof :
    command points handler (.getProof) = (do
      opening points "get-proof"
      take points .parenClose
      Program.callUnit handler .commandGetProof) := rfl

theorem command_getUnsatAssumptions :
    command points handler (.getUnsatAssumptions) = (do
      opening points "get-unsat-assumptions"
      take points .parenClose
      Program.callUnit handler .commandGetUnsatAssumptions) := rfl

theorem command_getUnsatCore :
    command points handler (.getUnsatCore) = (do
      opening points "get-unsat-core"
      take points .parenClose
      Program.callUnit handler .commandGetUnsatCore) := rfl

theorem command_getValue (valueTerms) :
    command points handler (.getValue valueTerms) = (do
      opening points "get-value"
      take points .parenOpen
      let handled ← terms points handler valueTerms
      takeAll points [.parenClose, .parenClose]
      Program.callUnit handler (.commandGetValue handled)) := rfl

theorem command_pop (count) :
    command points handler (.pop count) = (do
      opening points "pop"
      takeAll points [.numeral count, .parenClose]
      Program.callUnit handler (.commandPop count)) := rfl

theorem command_push (count) :
    command points handler (.push count) = (do
      opening points "push"
      takeAll points [.numeral count, .parenClose]
      Program.callUnit handler (.commandPush count)) := rfl

theorem command_reset :
    command points handler (.reset) = (do
      opening points "reset"
      take points .parenClose
      Program.callUnit handler .commandReset) := rfl

theorem command_resetAssertions :
    command points handler (.resetAssertions) = (do
      opening points "reset-assertions"
      take points .parenClose
      Program.callUnit handler .commandResetAssertions) := rfl

theorem command_setInfo (keyword) (value) :
    command points handler (.setInfo ⟨keyword, value⟩) = (do
      opening points "set-info"
      take points (.keyword keyword)
      let handled ← attributeThen points handler keyword .parenClose value
      Program.callUnit handler (.commandSetInfo handled)) := rfl

theorem command_setLogic (symbol) :
    command points handler (.setLogic symbol) = (do
      opening points "set-logic"
      takeAll points [.symbol symbol, .parenClose]
      Program.callUnit handler (.commandSetLogic symbol)) := rfl

theorem command_setOption (keyword) (value) :
    command points handler (.setOption ⟨keyword, value⟩) = (do
      opening points "set-option"
      take points (.keyword keyword)
      let handled ← attributeThen points handler keyword .parenClose value
      Program.callUnit handler (.commandSetOption handled)) := rfl

theorem datatype_plain (start : List Tree.Symbol → Run m ε Unit) (first : Tree.ConstructorDec)
    (rest : List Tree.ConstructorDec) :
    datatype points handler start ⟨[], first :: rest⟩ = (do
      takeAll points [.parenOpen, .parenOpen]
      start []
      let handledFirst ← constructorAfterOpen points handler first
      let others ← constructors points handler rest
      take points .parenClose
      pure (handledFirst :: others)) := rfl

theorem datatype_empty (start : List Tree.Symbol → Run m ε Unit) :
    datatype points handler start ⟨[], []⟩ = (do
      takeAll points [.parenOpen, .parenClose]
      start []
      pure []) := rfl

theorem datatype_par (start : List Tree.Symbol → Run m ε Unit) (parameter : Tree.Symbol)
    (parameters : List Tree.Symbol) (list : List Tree.ConstructorDec) :
    datatype points handler start ⟨parameter :: parameters, list⟩ = (do
      takeAll points [.parenOpen, word "par", .parenOpen]
      takeAll points ((parameter :: parameters).map .symbol)
      take points .parenClose
      start (parameter :: parameters)
      take points .parenOpen
      let handled ← constructors points handler list
      takeAll points [.parenClose, .parenClose]
      pure handled) := rfl

end BSmtLibSpec.Facts.Proofs.Parser.Equations
