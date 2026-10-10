import BSmtLib.SpecChecks.Parser.Program

/-!
# Equations of the traversal

Equations of the functions of `Spec.Parser.Traversal` for each form of their argument, which
hold by definition. Lean does not derive all of them itself: it cannot for functions that
match a list against `[]` in one case and against any list in the next.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Parser

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal

variable {m : Type → Type} [Monad m] {ε : Type} {values : Values}
variable {points : Points m} {handler : Handler m ε values}


theorem sort_nil (identifier : Tree.Identifier) :
    sort points handler (.mk identifier []) =
      (do takeAll points identifier.tokens
          Program.callSort handler (.handleSort identifier [])) := rfl

theorem sort_cons (identifier : Tree.Identifier) (first : Tree.Sort) (others : List Tree.Sort) :
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

theorem term_constant (value) :
    term points handler (.constant value) = (do
      take points value.token
      Program.callTerm handler (.handleTerm (.constant value))) := rfl

theorem term_identifier (qualified) :
    term points handler (.identifier qualified) = (do
      let (name, qualification) ← qualIdentifier points handler qualified
      Program.callTerm handler (.handleTerm (.identifier name qualification))) := rfl

theorem term_application (function) (arguments) :
    term points handler (.application function arguments) = (do
      take points .parenOpen
      let (name, qualification) ← qualIdentifier points handler function
      let handled ← terms points handler arguments
      take points .parenClose
      Program.callTerm handler (.handleTerm (.application name qualification handled))) := rfl

theorem term_let (bindingList) (body) :
    term points handler (.«let» bindingList body) = (do
      takeAll points [.parenOpen, word "let", .parenOpen]
      let handled ← bindings points handler bindingList
      take points .parenClose
      let scope ← Program.callScope handler (.startLet handled)
      let result ← term points handler body
      take points .parenClose
      Program.callTerm handler (.endLet scope result)) := rfl

theorem term_lambda (variables) (body) :
    term points handler (.lambda variables body) = (do
      takeAll points [.parenOpen, word "lambda", .parenOpen]
      let handled ← sortedVars points handler variables
      take points .parenClose
      let scope ← Program.callScope handler (.startLambda handled)
      let result ← term points handler body
      take points .parenClose
      Program.callTerm handler (.endLambda scope result)) := rfl

theorem term_quantified (quantifier) (variables) (body) :
    term points handler (.quantified quantifier variables body) = (do
      takeAll points [.parenOpen, quantifier.word, .parenOpen]
      let handled ← sortedVars points handler variables
      take points .parenClose
      let scope ← Program.callScope handler (.startQuantifier quantifier handled)
      let result ← term points handler body
      take points .parenClose
      Program.callTerm handler (.endQuantifier quantifier scope result)) := rfl

theorem term_match (scrutinee) (caseList) :
    term points handler (.«match» scrutinee caseList) = (do
      takeAll points [.parenOpen, word "match"]
      let handled ← term points handler scrutinee
      Program.callUnit handler (.startMatch handled)
      take points .parenOpen
      let handledCases ← cases points handler handled caseList
      takeAll points [.parenClose, .parenClose]
      Program.callTerm handler (.handleMatch handled handledCases)) := rfl

theorem term_annotated (annotated) (attributeList) :
    term points handler (.annotated annotated attributeList) = (do
      takeAll points [.parenOpen, word "!"]
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
      let handled ← Program.callTerm handler (.endMatchCase scope result)
      let others ← cases points handler scrutinee rest
      pure ((pattern, handled) :: others)) := rfl

theorem recursiveBodies_cons (body : Tree.Term) (rest : List Tree.Term) :
    recursiveBodies points handler (body :: rest) = (do
      Program.callUnit handler .startRecursiveBody
      let handled ← term points handler body
      Program.callUnit handler (.endRecursiveBody handled)
      recursiveBodies points handler rest) := rfl

theorem switchVersion_eq (producerSwitch : Version → ExceptT VersionRefused m Unit)
    (policy : VersionPolicy) (declarations : Nat) (version : Version) :
    switchVersion handler producerSwitch policy declarations version = (do
      match policy.check declarations version with
      | .error violation => throw (.policy violation)
      | .ok () => pure ()
      ExceptT.adapt Cause.producer (producerSwitch version)
      Program.callUnit handler (.setVersion version)) := rfl

theorem command_assert (atArrival : Run m ε Unit) (asserted) :
    command points handler atArrival (.assert asserted) = (do
      opening points atArrival "assert"
      let handled ← term points handler asserted
      take points .parenClose
      Program.callUnit handler (.commandAssert handled)) := rfl

theorem command_checkSat (atArrival : Run m ε Unit) :
    command points handler atArrival (.checkSat) = (do
      opening points atArrival "check-sat"
      take points .parenClose
      Program.callUnit handler .commandCheckSat) := rfl

theorem command_checkSatAssuming (atArrival : Run m ε Unit) (assumptions) :
    command points handler atArrival (.checkSatAssuming assumptions) = (do
      opening points atArrival "check-sat-assuming"
      take points .parenOpen
      let handled ← terms points handler assumptions
      takeAll points [.parenClose, .parenClose]
      Program.callUnit handler (.commandCheckSatAssuming handled)) := rfl

theorem command_checkSatAssumingLiterals (atArrival : Run m ε Unit) (literals) :
    command points handler atArrival (.checkSatAssumingLiterals literals) = (do
      opening points atArrival "check-sat-assuming"
      take points .parenOpen
      let handled ← terms points handler (literals.map Tree.PropLiteral.asTerm)
      takeAll points [.parenClose, .parenClose]
      Program.callUnit handler (.commandCheckSatAssuming handled)) := rfl

theorem command_declareConst (atArrival : Run m ε Unit) (symbol) (declaredSort) :
    command points handler atArrival (.declareConst symbol declaredSort) = (do
      opening points atArrival "declare-const"
      take points (.symbol symbol)
      let handled ← sort points handler declaredSort
      take points .parenClose
      Program.callUnit handler (.commandDeclareConst symbol handled)) := rfl

theorem command_declareDatatype (atArrival : Run m ε Unit) (symbol) (declaration) :
    command points handler atArrival (.declareDatatype symbol declaration) = (do
      opening points atArrival "declare-datatype"
      take points (.symbol symbol)
      let handled ← datatype points handler
        (fun parameters => Program.callUnit handler (.startDeclareDatatype symbol parameters))
        declaration
      take points .parenClose
      Program.callUnit handler (.endDeclareDatatype handled)) := rfl

theorem command_declareDatatypes (atArrival : Run m ε Unit) (sortDecs) (declarations) :
    command points handler atArrival (.declareDatatypes sortDecs declarations) = (do
      opening points atArrival "declare-datatypes"
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

theorem command_declareFun (atArrival : Run m ε Unit) (symbol) (parameters) (result) :
    command points handler atArrival (.declareFun symbol parameters result) = (do
      opening points atArrival "declare-fun"
      takeAll points [.symbol symbol, .parenOpen]
      let handledParameters ← sorts points handler parameters
      take points .parenClose
      let handledResult ← sort points handler result
      take points .parenClose
      Program.callUnit handler (.commandDeclareFun symbol handledParameters handledResult)) := rfl

theorem command_declareSort (atArrival : Run m ε Unit) (symbol) (arity) :
    command points handler atArrival (.declareSort symbol arity) = (do
      opening points atArrival "declare-sort"
      takeAll points [.symbol symbol, .numeral arity, .parenClose]
      Program.callUnit handler (.commandDeclareSort symbol arity)) := rfl

theorem command_declareSortParameter (atArrival : Run m ε Unit) (symbol) :
    command points handler atArrival (.declareSortParameter symbol) = (do
      opening points atArrival "declare-sort-parameter"
      takeAll points [.symbol symbol, .parenClose]
      Program.callUnit handler (.commandDeclareSortParameter symbol)) := rfl

theorem command_defineConst (atArrival : Run m ε Unit) (symbol) (definedSort) (body) :
    command points handler atArrival (.defineConst symbol definedSort body) = (do
      opening points atArrival "define-const"
      take points (.symbol symbol)
      let handledSort ← sort points handler definedSort
      let handledBody ← term points handler body
      take points .parenClose
      Program.callUnit handler (.commandDefineConst symbol handledSort handledBody)) := rfl

theorem command_defineFun (atArrival : Run m ε Unit) (symbol) (parameters) (result) (body) :
    command points handler atArrival (.defineFun ⟨symbol, parameters, result, body⟩) = (do
      opening points atArrival "define-fun"
      let handledSignature ← signature points handler symbol parameters result
      Program.callUnit handler (.startDefineFun handledSignature)
      let handledBody ← term points handler body
      take points .parenClose
      Program.callUnit handler (.endDefineFun handledBody)) := rfl

theorem command_defineFunRec (atArrival : Run m ε Unit) (symbol) (parameters) (result) (body) :
    command points handler atArrival (.defineFunRec ⟨symbol, parameters, result, body⟩) = (do
      opening points atArrival "define-fun-rec"
      let handledSignature ← signature points handler symbol parameters result
      Program.callUnit handler (.startDefineFunRec handledSignature)
      let handledBody ← term points handler body
      take points .parenClose
      Program.callUnit handler (.endDefineFunRec handledBody)) := rfl

theorem command_defineFunsRec (atArrival : Run m ε Unit) (declarations) (bodies) :
    command points handler atArrival (.defineFunsRec declarations bodies) = (do
      opening points atArrival "define-funs-rec"
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
      recursiveBodies points handler bodies
      takeAll points [.parenClose, .parenClose]
      Program.callUnit handler .endDefineFunsRec) := rfl

theorem command_defineSort (atArrival : Run m ε Unit) (symbol) (parameters) (definedSort) :
    command points handler atArrival (.defineSort symbol parameters definedSort) = (do
      opening points atArrival "define-sort"
      takeAll points [.symbol symbol, .parenOpen]
      takeAll points (parameters.map .symbol)
      take points .parenClose
      Program.callUnit handler (.startDefineSort symbol parameters)
      let handled ← sort points handler definedSort
      take points .parenClose
      Program.callUnit handler (.endDefineSort handled)) := rfl

theorem command_echo (atArrival : Run m ε Unit) (content) :
    command points handler atArrival (.echo content) = (do
      opening points atArrival "echo"
      takeAll points [.string content, .parenClose]
      Program.callUnit handler (.commandEcho content)) := rfl

theorem command_exit (atArrival : Run m ε Unit) :
    command points handler atArrival (.exit) = (do
      opening points atArrival "exit"
      take points .parenClose
      Program.callUnit handler .commandExit) := rfl

theorem command_getAssertions (atArrival : Run m ε Unit) :
    command points handler atArrival (.getAssertions) = (do
      opening points atArrival "get-assertions"
      take points .parenClose
      Program.callUnit handler .commandGetAssertions) := rfl

theorem command_getAssignment (atArrival : Run m ε Unit) :
    command points handler atArrival (.getAssignment) = (do
      opening points atArrival "get-assignment"
      take points .parenClose
      Program.callUnit handler .commandGetAssignment) := rfl

theorem command_getInfo (atArrival : Run m ε Unit) (flag) :
    command points handler atArrival (.getInfo flag) = (do
      opening points atArrival "get-info"
      takeAll points [.keyword flag, .parenClose]
      Program.callUnit handler (.commandGetInfo flag)) := rfl

theorem command_getModel (atArrival : Run m ε Unit) :
    command points handler atArrival (.getModel) = (do
      opening points atArrival "get-model"
      take points .parenClose
      Program.callUnit handler .commandGetModel) := rfl

theorem command_getOption (atArrival : Run m ε Unit) (keyword) :
    command points handler atArrival (.getOption keyword) = (do
      opening points atArrival "get-option"
      takeAll points [.keyword keyword, .parenClose]
      Program.callUnit handler (.commandGetOption keyword)) := rfl

theorem command_getProof (atArrival : Run m ε Unit) :
    command points handler atArrival (.getProof) = (do
      opening points atArrival "get-proof"
      take points .parenClose
      Program.callUnit handler .commandGetProof) := rfl

theorem command_getUnsatAssumptions (atArrival : Run m ε Unit) :
    command points handler atArrival (.getUnsatAssumptions) = (do
      opening points atArrival "get-unsat-assumptions"
      take points .parenClose
      Program.callUnit handler .commandGetUnsatAssumptions) := rfl

theorem command_getUnsatCore (atArrival : Run m ε Unit) :
    command points handler atArrival (.getUnsatCore) = (do
      opening points atArrival "get-unsat-core"
      take points .parenClose
      Program.callUnit handler .commandGetUnsatCore) := rfl

theorem command_getValue (atArrival : Run m ε Unit) (valueTerms) :
    command points handler atArrival (.getValue valueTerms) = (do
      opening points atArrival "get-value"
      take points .parenOpen
      let handled ← terms points handler valueTerms
      takeAll points [.parenClose, .parenClose]
      Program.callUnit handler (.commandGetValue handled)) := rfl

theorem command_pop (atArrival : Run m ε Unit) (count) :
    command points handler atArrival (.pop count) = (do
      opening points atArrival "pop"
      takeAll points [.numeral count, .parenClose]
      Program.callUnit handler (.commandPop count)) := rfl

theorem command_push (atArrival : Run m ε Unit) (count) :
    command points handler atArrival (.push count) = (do
      opening points atArrival "push"
      takeAll points [.numeral count, .parenClose]
      Program.callUnit handler (.commandPush count)) := rfl

theorem command_reset (atArrival : Run m ε Unit) :
    command points handler atArrival (.reset) = (do
      opening points atArrival "reset"
      take points .parenClose
      Program.callUnit handler .commandReset) := rfl

theorem command_resetAssertions (atArrival : Run m ε Unit) :
    command points handler atArrival (.resetAssertions) = (do
      opening points atArrival "reset-assertions"
      take points .parenClose
      Program.callUnit handler .commandResetAssertions) := rfl

theorem command_setInfo (atArrival : Run m ε Unit) (keyword) (value) :
    command points handler atArrival (.setInfo ⟨keyword, value⟩) = (do
      opening points atArrival "set-info"
      take points (.keyword keyword)
      let handled ← attributeThen points handler keyword .parenClose value
      Program.callUnit handler (.commandSetInfo handled)) := rfl

theorem command_setLogic (atArrival : Run m ε Unit) (symbol) :
    command points handler atArrival (.setLogic symbol) = (do
      opening points atArrival "set-logic"
      takeAll points [.symbol symbol, .parenClose]
      Program.callUnit handler (.commandSetLogic symbol)) := rfl

theorem command_setOption (atArrival : Run m ε Unit) (keyword) (value) :
    command points handler atArrival (.setOption ⟨keyword, value⟩) = (do
      opening points atArrival "set-option"
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

end BSmtLib.SpecChecks.Parser
