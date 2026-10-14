import BSmtLib.Parser.Command.CommandOutcome
import BSmtLib.Parser.Command.Datatype
import BSmtLib.Parser.Command.Definition
import BSmtLib.Parser.Command.Function

/-!
# The standard commands

The payload parser of the standard commands: what follows a command's name, up to its `)`, and
the last call that each command makes at its `)`.
-/

namespace BSmtLib.Parser.Command.Standard

open BSmtLib.Nodes BSmtLib.Traits BSmtLib.Parser.Category.Attribute
    BSmtLib.Parser.Category.Combinator
open BSmtLib.Parser.Category.Sort BSmtLib.Parser.Category.Term BSmtLib.Parser.Category.Token
open BSmtLib.Parser.Command.Datatype BSmtLib.Parser.Command.Definition
    BSmtLib.Parser.Command.Function
open BSmtLib.Plain (NumeralView KeywordView StringContentView)
open BSmtLib.Token (Version)
open BSmtLib.Token.Reserved (CommandNameReserved)

/-- The shape of a propositional literal read so far, ⟨symbol⟩ | `(` `not` ⟨symbol⟩ `)`. -/
inductive LiteralShape where
  | start
  | negation
  | negated
  | close

/-- The state of the parser of a propositional literal: its shape, and the term it is. -/
structure LiteralState (HandledSExpr HandledAttribute HandledSort HandledTerm Scope : Type) where
  shape : LiteralShape
  term : TermState HandledSExpr HandledAttribute HandledSort HandledTerm Scope

/-- The literal parser before a literal. -/
def LiteralState.init {HandledSExpr HandledAttribute HandledSort HandledTerm Scope : Type} :
    LiteralState HandledSExpr HandledAttribute HandledSort HandledTerm Scope :=
  { shape := .start, term := .init }

/-- The state of the literal parser of the handler. -/
abbrev LiteralStateOf (H : Type) {m : Type → Type} [Handler H m] :=
  LiteralState (Handler.SExpr H) (Handler.Attribute H) (Handler.«Sort» H) (Handler.Term H)
    (Handler.Scope H)

/-- Whether the symbol is `not`, quoted or not. -/
def Symbol.isNot (symbol : Symbol) : Bool :=
  symbol.content.asSlice.toByteArray == "not".toUTF8

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/--
A step of the literal parser: each token that fits the shape of a literal goes to the term
parser, which hands the literal over as the term it is.
-/
def literalStep (version : Version) (self : LiteralStateOf H) (token : Input) :
    PM H (Step (LiteralStateOf H) (Handler.Term H)) := do
  let shape ← match self.shape, token with
    | .start, .symbol _ => pure LiteralShape.start
    | .start, .parenOpen => pure .negation
    | .negation, .symbol symbol =>
      if Symbol.isNot symbol then pure .negated
      else syntaxError .expectedPropositionalLiteral
    | .negated, .symbol _ => pure .close
    | .close, .parenClose => pure .start
    | _, _ => syntaxError .expectedPropositionalLiteral
  match ← termStep version self.term token with
  | .more term => return .more { shape, term }
  | .done term => return .done term

end

/-- The last call of a command, made at its `)`. -/
inductive FinalCall (HandledAttribute HandledSort HandledTerm : Type) where
  | assert (term : HandledTerm)
  | checkSat
  | checkSatAssuming (terms : Array HandledTerm)
  | declareConst (symbol : Symbol) (sort : HandledSort)
  | declareFun (symbol : Symbol) (parameters : Array HandledSort) (result : HandledSort)
  | declareSort (symbol : Symbol) (arity : NumeralView)
  | declareSortParameter (symbol : Symbol)
  | endDeclareDatatype (constructors : Array (Constructor HandledSort))
  | endDeclareDatatypes
  | defineConst (symbol : Symbol) (sort : HandledSort) (body : HandledTerm)
  | endDefineFun (body : HandledTerm)
  | endDefineFunRec (body : HandledTerm)
  | endDefineFunsRec
  | endDefineSort (sort : HandledSort)
  | echo (content : StringContentView)
  | exit
  | getAssertions
  | getAssignment
  | getInfo (flag : KeywordView)
  | getModel
  | getOption (keyword : KeywordView)
  | getProof
  | getUnsatAssumptions
  | getUnsatCore
  | getValue (terms : Array HandledTerm)
  | pop (count : NumeralView)
  | push (count : NumeralView)
  | reset
  | resetAssertions
  | setLogic (symbol : Symbol)

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/-- Makes the last call of a command. -/
def finalCall : FinalCall (Handler.Attribute H) (Handler.«Sort» H) (Handler.Term H) → PM H Unit
  | .assert term => call (CommandHandler.commandAssert term)
  | .checkSat => call (CommandHandler.commandCheckSat (H := H))
  | .checkSatAssuming terms => call (CommandHandler.commandCheckSatAssuming terms)
  | .declareConst symbol sort => call (CommandHandler.commandDeclareConst symbol sort)
  | .declareFun symbol parameters result =>
    call (CommandHandler.commandDeclareFun symbol parameters result)
  | .declareSort symbol arity => call (CommandHandler.commandDeclareSort (H := H) symbol arity)
  | .declareSortParameter symbol =>
    call (CommandHandler.commandDeclareSortParameter (H := H) symbol)
  | .endDeclareDatatype constructors => call (CommandHandler.endDeclareDatatype constructors)
  | .endDeclareDatatypes => call (CommandHandler.endDeclareDatatypes (H := H))
  | .defineConst symbol sort body => call (CommandHandler.commandDefineConst symbol sort body)
  | .endDefineFun body => call (CommandHandler.endDefineFun body)
  | .endDefineFunRec body => call (CommandHandler.endDefineFunRec body)
  | .endDefineFunsRec => call (CommandHandler.endDefineFunsRec (H := H))
  | .endDefineSort sort => call (CommandHandler.endDefineSort sort)
  | .echo content => call (CommandHandler.commandEcho (H := H) content)
  | .exit => call (CommandHandler.commandExit (H := H))
  | .getAssertions => call (CommandHandler.commandGetAssertions (H := H))
  | .getAssignment => call (CommandHandler.commandGetAssignment (H := H))
  | .getInfo flag => call (CommandHandler.commandGetInfo (H := H) flag)
  | .getModel => call (CommandHandler.commandGetModel (H := H))
  | .getOption keyword => call (CommandHandler.commandGetOption (H := H) keyword)
  | .getProof => call (CommandHandler.commandGetProof (H := H))
  | .getUnsatAssumptions => call (CommandHandler.commandGetUnsatAssumptions (H := H))
  | .getUnsatCore => call (CommandHandler.commandGetUnsatCore (H := H))
  | .getValue terms => call (CommandHandler.commandGetValue terms)
  | .pop count => call (CommandHandler.commandPop (H := H) count)
  | .push count => call (CommandHandler.commandPush (H := H) count)
  | .reset => call (CommandHandler.commandReset (H := H))
  | .resetAssertions => call (CommandHandler.commandResetAssertions (H := H))
  | .setLogic symbol => call (CommandHandler.commandSetLogic (H := H) symbol)

end

/-- The commands whose payload starts with a symbol. -/
inductive NamedCommand where
  | declareConst
  | declareDatatype
  | declareFun
  | declareSort
  | declareSortParameter
  | defineConst
  | defineSort
  | setLogic

/-- Whether the keyword is `smt-lib-version`, which a version declaration has. -/
def isVersionKeyword (name : KeywordView) : Bool :=
  name.asSlice.toByteArray == "smt-lib-version".toUTF8

/-- What the tokens of a `set-info` so far tell of a version declaration. -/
inductive Declaration where
  /-- Before the keyword. -/
  | start
  /-- The keyword is not `smt-lib-version`: no declaration. -/
  | other
  /-- After the keyword `smt-lib-version`, before its value. -/
  | keyword
  /-- After the value of a declaration: the version it names, if it names one. -/
  | value (version : Option Version)

/-- What the tokens of a `set-info` tell of a version declaration after the token. -/
def Declaration.next (self : Declaration) (token : Input) : Declaration :=
  match self, token with
  | .start, .keyword name => if isVersionKeyword name then .keyword else .other
  | .start, _ => .other
  | .keyword, .constant (.decimal text) => .value (Version.fromDecimal? text.asSlice)
  | .keyword, _ => .value none
  | declaration, _ => declaration

/-- The state of the parser of a command's payload, after its name. -/
inductive Payload (HandledSExpr HandledAttribute HandledSort HandledTerm Scope : Type) where
  /-- Before the command's `)`, which the last call follows. -/
  | closing (final : FinalCall HandledAttribute HandledSort HandledTerm)
  /-- Before the symbol of a command that starts with one. -/
  | named (command : NamedCommand)
  | assert (state : TermState HandledSExpr HandledAttribute HandledSort HandledTerm Scope)
  | checkSatAssuming
      (state : ListState (TermState HandledSExpr HandledAttribute HandledSort HandledTerm Scope)
        HandledTerm)
  | checkSatAssumingLiterals
      (state : ListState
        (LiteralState HandledSExpr HandledAttribute HandledSort HandledTerm Scope) HandledTerm)
  | declareConst (symbol : Symbol) (state : SortState HandledSort)
  | declareFunParameters (symbol : Symbol) (state : ListState (SortState HandledSort) HandledSort)
  | declareFunResult (symbol : Symbol) (parameters : Array HandledSort)
      (state : SortState HandledSort)
  | declareSort (symbol : Symbol)
  | declareDatatype (symbol : Symbol) (state : DatatypeState HandledSort)
  | declareDatatypesSorts (state : ListState SortDecState (Symbol × NumeralView))
  | declareDatatypesDatatypes (count : Nat)
      (state : ListState (DatatypeState HandledSort) Unit)
  | defineSortParameters (symbol : Symbol) (state : ListState Unit Symbol)
  | defineSortBody (state : SortState HandledSort)
  | defineConstSort (symbol : Symbol) (state : SortState HandledSort)
  | defineSignature (definition : DefinitionEnd HandledSort) (state : SignatureState HandledSort)
  | defineBody (definition : DefinitionEnd HandledSort)
      (state : TermState HandledSExpr HandledAttribute HandledSort HandledTerm Scope)
  | defineFunsRecDeclarations
      (state : ListState (FunctionDecState HandledSort) (Signature HandledSort))
  /-- The bodies of `define-funs-rec`, with the signatures of the functions, one per body. -/
  | defineFunsRecBodies (signatures : Array (Signature HandledSort))
      (state : ListState (TermState HandledSExpr HandledAttribute HandledSort HandledTerm Scope)
        Unit)
  | echo
  | getInfo
  | getOption
  | getValue
      (state : ListState (TermState HandledSExpr HandledAttribute HandledSort HandledTerm Scope)
        HandledTerm)
  | pop
  | push
  /-- `set-info`: what its tokens so far tell of a version declaration, and its attribute. -/
  | setInfo (declaration : Declaration) (state : AttributeState HandledSExpr HandledAttribute)
  | setOption (state : AttributeState HandledSExpr HandledAttribute)

/-- The payload state of the handler. -/
abbrev PayloadOf (H : Type) {m : Type → Type} [Handler H m] :=
  Payload (Handler.SExpr H) (Handler.Attribute H) (Handler.«Sort» H) (Handler.Term H)
    (Handler.Scope H)

/-- The payload of the standard command, in the version. -/
def Payload.init {HandledSExpr HandledAttribute HandledSort HandledTerm Scope : Type}
    (name : CommandNameReserved) (version : Version) :
    Payload HandledSExpr HandledAttribute HandledSort HandledTerm Scope :=
  match name with
  | .assert => .assert .init
  | .checkSat => .closing .checkSat
  | .checkSatAssuming =>
    if version ≥ .v2_7 then .checkSatAssuming (ListState.paren .init)
    else .checkSatAssumingLiterals (ListState.paren .init)
  | .declareConst => .named .declareConst
  | .declareDatatype => .named .declareDatatype
  | .declareDatatypes => .declareDatatypesSorts (ListState.paren .start)
  | .declareFun => .named .declareFun
  | .declareSort => .named .declareSort
  | .declareSortParameter => .named .declareSortParameter
  | .defineConst => .named .defineConst
  | .defineFun => .defineSignature .defineFun .start
  | .defineFunRec => .defineSignature .defineFunRec .start
  | .defineFunsRec => .defineFunsRecDeclarations (ListState.paren .start)
  | .defineSort => .named .defineSort
  | .echo => .echo
  | .exit => .closing .exit
  | .getAssertions => .closing .getAssertions
  | .getAssignment => .closing .getAssignment
  | .getInfo => .getInfo
  | .getModel => .closing .getModel
  | .getOption => .getOption
  | .getProof => .closing .getProof
  | .getUnsatAssumptions => .closing .getUnsatAssumptions
  | .getUnsatCore => .closing .getUnsatCore
  | .getValue => .getValue (ListState.paren .init)
  | .pop => .pop
  | .push => .push
  | .reset => .closing .reset
  | .resetAssertions => .closing .resetAssertions
  | .setInfo => .setInfo .start .init
  | .setLogic => .named .setLogic
  | .setOption => .setOption .init

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/--
A step of the payload parser.

A version declaration, at its `)`, is handled as `set-info` and reported in the outcome; the
check against a posture and the switches are the script's. A declaration that names no version
is handled as `set-info` and then rejected at its `)`.
-/
def payloadStep (version : Version) (self : PayloadOf H) (token : Input) :
    PM H (Step (PayloadOf H) CommandOutcome) := do
  let close (final : FinalCall (Handler.Attribute H) (Handler.«Sort» H) (Handler.Term H)) :
      PM H (Step (PayloadOf H) CommandOutcome) :=
    pure (.more (.closing final))
  match self with
  | .closing final =>
    expectClose token
    finalCall final
    return .done (match final with
      | .exit => .exit
      | _ => .command)
  | .named command =>
    let symbol ← expectSymbol token
    match command with
    | .declareConst => return .more (.declareConst symbol .init)
    | .declareDatatype => return .more (.declareDatatype symbol .start)
    | .declareFun => return .more (.declareFunParameters symbol (ListState.paren .init))
    | .declareSort => return .more (.declareSort symbol)
    | .declareSortParameter => close (.declareSortParameter symbol)
    | .defineConst => return .more (.defineConstSort symbol .init)
    | .defineSort => return .more (.defineSortParameters symbol (ListState.paren ()))
    | .setLogic => close (.setLogic symbol)
  | .assert state =>
    match ← termStep version state token with
    | .more state => return .more (.assert state)
    | .done term => close (.assert term)
  | .checkSatAssuming state =>
    match ← state.step .init (termStep version) none token with
    | .more state => return .more (.checkSatAssuming state)
    | .done assumptions => close (.checkSatAssuming assumptions)
  | .checkSatAssumingLiterals state =>
    match ← state.step .init (literalStep version) none token with
    | .more state => return .more (.checkSatAssumingLiterals state)
    | .done assumptions => close (.checkSatAssuming assumptions)
  | .declareConst symbol state =>
    match ← sortStep version state token with
    | .more state => return .more (.declareConst symbol state)
    | .done sort => close (.declareConst symbol sort)
  | .declareFunParameters symbol state =>
    match ← state.step .init (sortStep version) none token with
    | .more state => return .more (.declareFunParameters symbol state)
    | .done parameters => return .more (.declareFunResult symbol parameters .init)
  | .declareFunResult symbol parameters state =>
    match ← sortStep version state token with
    | .more state => return .more (.declareFunResult symbol parameters state)
    | .done result => close (.declareFun symbol parameters result)
  | .declareSort symbol => close (.declareSort symbol (← expectNumeral token))
  | .declareDatatype symbol state =>
    let start parameters := call (CommandHandler.startDeclareDatatype symbol parameters)
    match ← datatypeStep start version state token with
    | .more state => return .more (.declareDatatype symbol state)
    | .done constructors => close (.endDeclareDatatype constructors)
  | .declareDatatypesSorts state =>
    match ← state.step .start SortDecState.step none token with
    | .more state => return .more (.declareDatatypesSorts state)
    | .done sorts =>
      if sorts.isEmpty then syntaxError .emptyDatatypeIntroductions
      call (CommandHandler.startDeclareDatatypes (H := H) sorts)
      return .more (.declareDatatypesDatatypes sorts.size (ListState.paren .start))
  | .declareDatatypesDatatypes count state =>
    let start parameters := call (CommandHandler.startDatatypeDeclaration (H := H) parameters)
    let datatype (state : DatatypeState (Handler.«Sort» H)) (token : Input) := do
      match ← datatypeStep start version state token with
      | .more state => return Step.more state
      | .done constructors =>
        call (CommandHandler.endDatatypeDeclaration constructors)
        return .done ()
    match ← state.step .start datatype (some count) token with
    | .more state => return .more (.declareDatatypesDatatypes count state)
    | .done datatypes =>
      if datatypes.size != count then syntaxError .expectedDatatype
      close .endDeclareDatatypes
  | .defineSortParameters symbol state =>
    match ← state.step () symbolStep none token with
    | .more state => return .more (.defineSortParameters symbol state)
    | .done parameters =>
      call (CommandHandler.startDefineSort (H := H) symbol parameters)
      return .more (.defineSortBody .init)
  | .defineSortBody state =>
    match ← sortStep version state token with
    | .more state => return .more (.defineSortBody state)
    | .done sort => close (.endDefineSort sort)
  | .defineConstSort symbol state =>
    match ← sortStep version state token with
    | .more state => return .more (.defineConstSort symbol state)
    | .done sort =>
      return .more (.defineBody (.defineConst symbol sort) .init)
  | .defineSignature definition state =>
    match ← signatureStep version state token with
    | .more state => return .more (.defineSignature definition state)
    | .done signature =>
      match definition with
      | .defineFunRec => call (CommandHandler.startDefineFunRec signature)
      | _ => call (CommandHandler.startDefineFun signature)
      return .more (.defineBody definition .init)
  | .defineBody definition state =>
    match ← termStep version state token with
    | .more state => return .more (.defineBody definition state)
    | .done body =>
      close (match definition with
        | .defineConst symbol sort => .defineConst symbol sort body
        | .defineFun => .endDefineFun body
        | .defineFunRec => .endDefineFunRec body)
  | .defineFunsRecDeclarations state =>
    match ← state.step .start (functionDecStep version) none token with
    | .more state => return .more (.defineFunsRecDeclarations state)
    | .done signatures =>
      if signatures.isEmpty then syntaxError .emptyFunctionSignatures
      call (CommandHandler.startDefineFunsRec signatures)
      return .more (.defineFunsRecBodies signatures (ListState.paren .init))
  | .defineFunsRecBodies signatures state =>
    match ← bodiesStep signatures.size version state token with
    | .more state => return .more (.defineFunsRecBodies signatures state)
    | .done bodies =>
      if bodies.size != signatures.size then syntaxError .expectedFunctionBody
      close .endDefineFunsRec
  | .echo => close (.echo (← expectString token))
  | .getInfo => close (.getInfo (← expectKeyword token))
  | .getOption => close (.getOption (← expectKeyword token))
  | .getValue state =>
    match ← state.step .init (termStep version) none token with
    | .more state => return .more (.getValue state)
    | .done values =>
      if values.isEmpty then syntaxError .emptyGetValueTerms
      close (.getValue values)
  | .pop => close (.pop (← expectNumeral token))
  | .push => close (.push (← expectNumeral token))
  | .setInfo declaration state =>
    -- the keyword of the attribute, then the token after it, tell whether it declares a version
    let declaration := declaration.next token
    match ← attributeStep true version state token with
    | .more state => return .more (.setInfo declaration state)
    | .done attributes =>
      let some info := attributes[0]? | syntaxError .expectedAttribute
      call (CommandHandler.commandSetInfo info)
      match declaration with
      | .value (some declared) => return .done (.setVersion declared)
      | .keyword | .value none => syntaxError .unsupportedVersion
      | .start | .other => return .done .command
  | .setOption state =>
    match ← attributeStep true version state token with
    | .more state => return .more (.setOption state)
    | .done attributes =>
      let some option := attributes[0]? | syntaxError .expectedAttribute
      call (CommandHandler.commandSetOption option)
      return .done .command

/--
The calls due when a token arrives at the payload parser, before it takes the token: the start
of a recursive body of `define-funs-rec`, when the token begins a body that is due.
-/
def payloadArrive (self : PayloadOf H) (token : Input) : PM H Unit :=
  match self with
  | .defineFunsRecBodies signatures state => bodiesArrive signatures state token
  | _ => pure ()

end

end BSmtLib.Parser.Command.Standard
