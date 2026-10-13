import BSmtLib.Parser.Term

/-!
# The command parser

A state machine stepped by single tokens over one command: its `(`, its name, then the payload
parser of the command, which finishes at the command's `)`. A command's parts are parsed into
values the parser holds, and handed over at the handler call; every command's last call comes
at its `)`.
-/

namespace BSmtLib.Parser

/-! ## Parts of commands -/

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- The parser of a single symbol, as an element of a list. -/
def symbolStep (_ : Unit) (token : Input) : PM H (Step Unit Symbol) := do
  return .done (← expectSymbol token)

/-- The state of the parser of a sort declaration `(` ⟨symbol⟩ ⟨numeral⟩ `)`. -/
inductive SortDecState where
  | start
  | opened
  | arity (symbol : Symbol)
  | close (symbol : Symbol) (arity : NumeralView)

/-- A step of the parser of a sort declaration. -/
def SortDecState.step (self : SortDecState) (token : Input) :
    PM H (Step SortDecState (Symbol × NumeralView)) := do
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
      if symbol.isNot then pure .negated
      else syntaxError .expectedPropositionalLiteral
    | .negated, .symbol _ => pure .close
    | .close, .parenClose => pure .start
    | _, _ => syntaxError .expectedPropositionalLiteral
  match ← termStep version self.term token with
  | .more term => return .more { shape, term }
  | .done term => return .done term

end

/-- The state of the parser of a function signature `⟨symbol⟩ (⟨sorted_var⟩∗) ⟨sort⟩`. -/
inductive SignatureState (HandledSort : Type) where
  | start
  | parameters (symbol : Symbol)
      (state : ListState (SortedVarState HandledSort) (Symbol × HandledSort))
  | result (symbol : Symbol) (parameters : Array (Symbol × HandledSort))
      (state : SortState HandledSort)

/-- The state of the parser of a function declaration `(` signature `)`. -/
inductive FunctionDecState (HandledSort : Type) where
  | start
  | signature (state : SignatureState HandledSort)
  | close (signature : Signature HandledSort)

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
      (state : ListState (ConstructorState HandledSort) (Constructor HandledSort))
  /-- After the constructors of the form with `par`, before the declaration's `)`. -/
  | close (constructors : Array (Constructor HandledSort))

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- A step of the signature parser; the sorts are handled at their last tokens. -/
def signatureStep (version : Version) (self : SignatureState (Handler.«Sort» H)) (token : Input) :
    PM H (Step (SignatureState (Handler.«Sort» H)) (Signature (Handler.«Sort» H))) := do
  match self with
  | .start => return .more (.parameters (← expectSymbol token) (ListState.paren .start))
  | .parameters symbol state =>
    match ← state.step .start (sortedVarStep version) none token with
    | .more state => return .more (.parameters symbol state)
    | .done parameters => return .more (.result symbol parameters .init)
  | .result symbol parameters state =>
    match ← sortStep version state token with
    | .more state => return .more (.result symbol parameters state)
    | .done result => return .done ⟨symbol, parameters, result⟩

/-- A step of the parser of a function declaration. -/
def functionDecStep (version : Version) (self : FunctionDecState (Handler.«Sort» H))
    (token : Input) :
    PM H (Step (FunctionDecState (Handler.«Sort» H)) (Signature (Handler.«Sort» H))) := do
  match self with
  | .start =>
    expectOpen token
    return .more (.signature .start)
  | .signature state =>
    match ← signatureStep version state token with
    | .more state => return .more (.signature state)
    | .done signature => return .more (.close signature)
  | .close signature =>
    expectClose token
    return .done signature

/-- A step of the constructor parser; a selector is parsed as a sorted variable. -/
def constructorStep (version : Version) (self : ConstructorState (Handler.«Sort» H))
    (token : Input) :
    PM H (Step (ConstructorState (Handler.«Sort» H)) (Constructor (Handler.«Sort» H))) := do
  match self with
  | .start =>
    expectOpen token
    return .more .opened
  | .opened => return .more (.selectors (← expectSymbol token) (ListState.closed .start))
  | .selectors symbol state =>
    match ← state.step .start (sortedVarStep version) none token with
    | .more state => return .more (.selectors symbol state)
    | .done selectors => return .done ⟨symbol, selectors⟩

/--
A step of the parser of a datatype declaration, `(` ⟨constructor_dec⟩+ `)` |
`(` `par` `(` ⟨symbol⟩+ `)` `(` ⟨constructor_dec⟩+ `)` `)`, which finishes with its
constructors at its `)`. The start comes when the tokens determine the sort parameters: at the
`)` of the parameters, or at the `(` of the first constructor, which shows that the form has no
`par`.
-/
@[specialize start]
def datatypeStep (start : Array Symbol → PM H Unit) (version : Version)
    (self : DatatypeState (Handler.«Sort» H)) (token : Input) :
    PM H (Step (DatatypeState (Handler.«Sort» H)) (Array (Constructor (Handler.«Sort» H)))) := do
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
      else syntaxError .expectedDatatypeKind
  | .parameters state =>
    match ← state.step () symbolStep none token with
    | .more state => return .more (.parameters state)
    | .done parameters =>
      if parameters.isEmpty then syntaxError .emptyDatatypeParameters
      start parameters
      return .more .constructorsOpen
  | .constructorsOpen =>
    expectOpen token
    return .more (.constructors true (ListState.closed .start))
  | .constructors parametric state =>
    match ← state.step .start (constructorStep version) none token with
    | .more state => return .more (.constructors parametric state)
    | .done constructors =>
      if constructors.isEmpty then syntaxError .emptyDatatypeConstructors
      if parametric then return .more (.close constructors)
      else return .done constructors
  | .close constructors =>
    expectClose token
    return .done constructors

end

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/--
A step of the parser of a recursive body: the body between `start_recursive_body` and
`end_recursive_body`, which comes at the body's last token, as a body has no `)` of its own.
-/
def bodyStep (version : Version) (self : TermStateOf H) (token : Input) :
    PM H (Step (TermStateOf H) Unit) := do
  match ← termStep version self token with
  | .more term => return .more term
  | .done body =>
    call (CommandHandler.endRecursiveBody body)
    return .done ()

/--
A step of the list of recursive bodies, as many as the functions. A body's start is not made
here but when its first token arrives (`bodiesArrive`).
-/
def bodiesStep (count : Nat) (version : Version) (self : ListState (TermStateOf H) Unit)
    (token : Input) : PM H (Step (ListState (TermStateOf H) Unit) (Array Unit)) :=
  self.step .init (bodyStep version) (some count) token

/--
The calls due when a token arrives at the list of recursive bodies: between bodies, a token that
can begin a body, any but `)`, while a body is still due, starts it, with the signature of its
function, before the list takes the token.
-/
def bodiesArrive (signatures : Array (Signature (Handler.«Sort» H)))
    (self : ListState (TermStateOf H) Unit) (token : Input) : PM H Unit :=
  if self.opened && self.outside then
    match token, signatures[self.items.size]? with
    | .parenClose, _ => pure ()
    | _, some signature => call (CommandHandler.startRecursiveBody signature)
    | _, none => pure ()
  else pure ()

end

/-! ## Commands -/

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

/-- The definitions whose body is a term, by the call that ends them: `define-const` with its
name and its handled sort. -/
inductive DefinitionEnd (HandledSort : Type) where
  | defineConst (symbol : Symbol) (sort : HandledSort)
  | defineFun
  | defineFunRec

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

/-- How a command ended (`SmtCommandOutcome`). -/
inductive CommandOutcome where
  /-- A command ended. -/
  | command
  /-- A version declaration ended, handled as `set-info`; a script switches to the version. -/
  | setVersion (version : Version)
  /-- `exit` ended. -/
  | exit
  /-- The input ended between commands. -/
  | endOfInput

/-- The state of the command parser. -/
inductive CommandState (HandledSExpr HandledAttribute HandledSort HandledTerm Scope : Type) where
  /-- Before a command, or the end of the input. -/
  | awaiting
  /-- After the `(` of a command, before its name. -/
  | opened
  | payload (state : Payload HandledSExpr HandledAttribute HandledSort HandledTerm Scope)

/-- The command parser state of the handler. -/
abbrev CommandStateOf (H : Type) {m : Type → Type} [Handler H m] :=
  CommandState (Handler.SExpr H) (Handler.Attribute H) (Handler.«Sort» H) (Handler.Term H)
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
A step of the command parser: `(`, the command's name, its payload up to its `)`; or the end of
the input between commands. A symbol as the name, even one spelled as a standard command's
name, names a non-standard command.
-/
def commandStep (version : Version) (self : CommandStateOf H) (token : Input) :
    PM H (Step (CommandStateOf H) CommandOutcome) := do
  match self with
  | .awaiting =>
    match token with
    | .parenOpen => return .more .opened
    | .endOfInput => return .done .endOfInput
    | _ => syntaxError .expectedCommand
  | .opened =>
    match token with
    | .reserved (.commandName name) => return .more (.payload (Payload.init name version))
    | .symbol name => throw (.handler (CommandHandler.nonstandardCommand (H := H) name))
    | _ => syntaxError .expectedCommandName
  | .payload payload =>
    match ← payloadStep version payload token with
    | .more payload => return .more (.payload payload)
    | .done outcome => return .done outcome

/--
The calls due when a token arrives at the payload parser, before it takes the token: the start
of a recursive body of `define-funs-rec`, when the token begins a body that is due.
-/
def payloadArrive (self : PayloadOf H) (token : Input) : PM H Unit :=
  match self with
  | .defineFunsRecBodies signatures state => bodiesArrive signatures state token
  | _ => pure ()

/-- The calls due when a token arrives at the command parser: those of its payload parser. -/
def commandArrive (self : CommandStateOf H) (token : Input) : PM H Unit :=
  match self with
  | .payload payload => payloadArrive payload token
  | _ => pure ()

end

end BSmtLib.Parser
