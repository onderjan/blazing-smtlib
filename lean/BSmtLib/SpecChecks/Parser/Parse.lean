import BSmtLib.SpecChecks.Parser.Program

/-!
# The traversal as a parser

The traversal of `Spec.Parser.Traversal` goes by the syntax tree. `parseScript` makes the same
handler calls among the same items, but goes by the items: it is a `Program`, which decides
what to do next from what it has received. `Parser.Simulation` proves that it makes the calls of
the traversal of every script on the items of the script.

It reads the categories as the traversal goes through them. A reader of a list reads up to the
`)` after the list and receives that `)` too (`untilClose`); where the traversal decides by an
item that it has not yet taken, the reader receives that item first and goes on with a reader
that starts with it (`...At`). Readers of categories that nest take fuel, as the readers of
`Grammar.Read` do; each is one step (`...Step`) given the reader with less fuel.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Parser

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal Program

variable {values : Values}

/-- Receive a `)`, or get stuck. -/
def expectClose : Program values Unit := do
  match ← next with
  | .token .parenClose => pure ()
  | _ => .stuck

/-- Receive a `(`, or get stuck. -/
def expectOpen : Program values Unit := do
  match ← next with
  | .token .parenOpen => pure ()
  | _ => .stuck

/-- Receive a symbol and go on with it, or get stuck. -/
def expectSymbol {α : Type} (continuation : Tree.Symbol → Program values α) :
    Program values α := do
  match ← next with
  | .token (.symbol name) => continuation name
  | _ => .stuck

/-- The list read by `element` from each item, up to a `)`, given the rest of the list. -/
def listStep {α : Type} (element : Received → Program values α)
    (others : Program values (List α)) : Program values (List α) := do
  match ← next with
  | .token .parenClose => pure []
  | item => do
    let first ← element item
    let rest ← others
    pure (first :: rest)

/-- The list read by `element` from each item, up to the `)` after it, of fewer than `k`
elements. -/
def untilClose {α : Type} (element : Received → Program values α) : Nat → Program values (List α)
  | 0 => .stuck
  | k + 1 => listStep element (untilClose element k)

/-- An index from its item. -/
def indexAt : Received → Program values Tree.Index
  | .token (.numeral digits) => pure (.numeral digits)
  | .token (.symbol name) => pure (.symbol name)
  | _ => .stuck

/-- A symbol from its item. -/
def symbolAt : Received → Program values Tree.Symbol
  | .token (.symbol name) => pure name
  | _ => .stuck

/-- An indexed identifier after its `_`: its symbol and its indices up to the `)`. -/
def indexedAfterWord (n : Nat) : Program values Tree.Identifier :=
  expectSymbol fun name => do
    let list ← untilClose indexAt n
    pure ⟨name, list⟩

/-- An identifier whose first item is received. -/
def identifierAt (n : Nat) : Received → Program values Tree.Identifier
  | .token (.symbol name) => pure ⟨name, []⟩
  | .token .parenOpen => do
    match ← next with
    | .token (.reserved w) => if w = chars "_" then indexedAfterWord n else .stuck
    | _ => .stuck
  | _ => .stuck

/-! ## Sorts -/

/-- A sort whose first item is received, given the reader of the sorts in it. -/
def sortStep (sortAt : Received → Program values values.sort) (n : Nat) :
    Received → Program values values.sort
  | .token (.symbol name) => emitSort (.handleSort ⟨name, []⟩ [])
  | .token .parenOpen => do
    match ← next with
    | .token (.reserved w) =>
      if w = chars "_" then do
        let identifier ← indexedAfterWord n
        emitSort (.handleSort identifier [])
      else .stuck
    | item => do
      let identifier ← identifierAt n item
      let arguments ← untilClose sortAt n
      emitSort (.handleSort identifier arguments)
  | _ => .stuck

/-- A sort whose first item is received. -/
def sortAt : Nat → Received → Program values values.sort
  | 0, _ => .stuck
  | n + 1, item => sortStep (sortAt n) n item

/-- A sort. -/
def parseSort (n : Nat) : Program values values.sort := parseWith (sortAt n)

/-! ## S-expressions and attributes -/

/-- The constant an item is, if it is one. -/
def constantOf : Received → Option Tree.SpecConstant
  | .token (.numeral digits) => some (.numeral digits)
  | .token (.decimal text) => some (.decimal text)
  | .token (.hexadecimal digits) => some (.hexadecimal digits)
  | .token (.binary digits) => some (.binary digits)
  | .token (.string content) => some (.string content)
  | _ => none

/-- An s-expression whose first item is received, given the reader of the s-expressions in
it. -/
def sExprStep (sExprAt : Received → Program values values.sExpr) (n : Nat) :
    Received → Program values values.sExpr
  | .token .parenOpen => do
    let items ← untilClose sExprAt n
    emitSExpr (.handleSExpr (.list items))
  | .token (.symbol name) => emitSExpr (.handleSExpr (.symbol name))
  | .token (.reserved w) => emitSExpr (.handleSExpr (.reserved w))
  | .token (.keyword name) => emitSExpr (.handleSExpr (.keyword name))
  | item =>
    match constantOf item with
    | some constant => emitSExpr (.handleSExpr (.constant constant))
    | none => .stuck

/-- An s-expression whose first item is received. -/
def sExprAt : Nat → Received → Program values values.sExpr
  | 0, _ => .stuck
  | n + 1, item => sExprStep (sExprAt n) n item

/-- An attribute value whose first item is received, if the item starts a value. -/
def valueAt (n : Nat) : Received → Option (Program values (AttributeValueNode values))
  | .token .parenOpen => some do
    let items ← untilClose (sExprAt n) n
    pure (.list items)
  | .token (.symbol name) => some (pure (.symbol name))
  | item => (constantOf item).map fun constant => pure (.constant constant)

/--
An attribute whose keyword is received, then the item after it: the handled attribute, the
value as the handler received it, and the item after the attribute.
-/
def attributeAfter (n : Nat) (keyword : Chars) :
    Program values (values.«attribute» × Option (AttributeValueNode values) × Received) := do
  let item ← next
  match valueAt n item with
  | some value => do
    let node ← value
    let handled ← emitAttribute (.handleAttribute keyword (some node))
    let following ← next
    pure (handled, some node, following)
  | none => do
    let handled ← emitAttribute (.handleAttribute keyword none)
    pure (handled, none, item)

/-- Attributes from the one whose keyword is received on, up to the `)` after them, given the
reader of the attributes after the first. -/
def attributesStep (attributesFrom : Chars → Program values (List values.«attribute»))
    (n : Nat) (keyword : Chars) : Program values (List values.«attribute») := do
  let (handled, _, following) ← attributeAfter n keyword
  match following with
  | .token .parenClose => pure [handled]
  | .token (.keyword next) => do
    let others ← attributesFrom next
    pure (handled :: others)
  | _ => .stuck

/-- Attributes from the one whose keyword is received on, up to the `)` after them. -/
def attributesFrom : Nat → Chars → Program values (List values.«attribute»)
  | 0, _ => .stuck
  | n + 1, keyword => attributesStep (attributesFrom n) n keyword

/-! ## Terms -/

/-- A sorted variable whose `(` is received. -/
def sortedVarAt (n : Nat) : Received → Program values (Tree.Symbol × values.sort)
  | .token .parenOpen => expectSymbol fun name => do
    let handled ← parseSort n
    expectClose
    pure (name, handled)
  | _ => .stuck

/-- A symbol or the wildcard, from an item. -/
def symbolOrWildcardOf : Received → Option Tree.SymbolOrWildcard
  | .token (.symbol name) => some (.symbol name)
  | .token (.reserved w) => if w = chars "_" then some .wildcard else none
  | _ => none

/-- A symbol or the wildcard from its item. -/
def symbolOrWildcardAt (item : Received) : Program values Tree.SymbolOrWildcard :=
  match symbolOrWildcardOf item with
  | some symbol => pure symbol
  | none => .stuck

/-- A pattern whose first item is received. -/
def patternAt (n : Nat) : Received → Program values Tree.Pattern
  | .token .parenOpen => expectSymbol fun name => do
    let arguments ← untilClose symbolOrWildcardAt n
    pure (.constructor name arguments)
  | item => do
    let symbol ← symbolOrWildcardAt item
    pure (.single symbol)

/-- The quantifier a reserved word names, if it names one. -/
def quantifierOf (w : Chars) : Option Tree.Quantifier :=
  if w = chars "forall" then some .«forall»
  else if w = chars "exists" then some .«exists»
  else none

/-- A binding of a `let` whose `(` is received, given the reader of terms. -/
def bindingAt (termAt : Received → Program values values.term) :
    Received → Program values (Tree.Symbol × values.term)
  | .token .parenOpen => expectSymbol fun name => do
    let handled ← parseWith termAt
    expectClose
    pure (name, handled)
  | _ => .stuck

/-- A case of a `match` whose `(` is received, given the reader of terms and the scrutinee. -/
def caseAt (termAt : Received → Program values values.term) (n : Nat)
    (scrutinee : values.term) : Received → Program values (Tree.Pattern × values.term)
  | .token .parenOpen => do
    let pattern ← parseWith (patternAt n)
    let scope ← emitScope (.startMatchCase scrutinee pattern)
    let body ← parseWith termAt
    expectClose
    let handled ← emitTerm (.endMatchCase scope scrutinee body)
    pure (pattern, handled)
  | _ => .stuck

/-- A term after its `(` and a reserved word, given the reader of the terms in it. -/
def termAfterWord (termAt : Received → Program values values.term) (n : Nat) (w : Chars) :
    Program values values.term :=
  if w = chars "_" then do
    let identifier ← indexedAfterWord n
    emitTerm (.handleTerm (.identifier identifier none))
  else if w = chars "as" then do
    let identifier ← parseWith (identifierAt n)
    let sort ← parseSort n
    expectClose
    emitTerm (.handleTerm (.identifier identifier (some sort)))
  else if w = chars "let" then do
    expectOpen
    let handled ← untilClose (bindingAt termAt) n
    let scope ← emitScope (.startLet handled)
    let body ← parseWith termAt
    expectClose
    emitTerm (.endLet scope body)
  else if w = chars "lambda" then do
    expectOpen
    let handled ← untilClose (sortedVarAt n) n
    let scope ← emitScope (.startLambda handled)
    let body ← parseWith termAt
    expectClose
    emitTerm (.endLambda scope body)
  else if let some quantifier := quantifierOf w then do
    expectOpen
    let handled ← untilClose (sortedVarAt n) n
    let scope ← emitScope (.startQuantifier quantifier handled)
    let body ← parseWith termAt
    expectClose
    emitTerm (.endQuantifier quantifier scope body)
  else if w = chars "match" then do
    let scrutinee ← parseWith termAt
    emitUnit (.startMatch scrutinee)
    expectOpen
    let handled ← untilClose (caseAt termAt n scrutinee) n
    expectClose
    emitTerm (.endMatch scrutinee handled)
  else if w = chars "!" then do
    let term ← parseWith termAt
    let attributes ← do
      match ← next with
      | .token .parenClose => pure []
      | .token (.keyword keyword) => attributesFrom n keyword
      | _ => .stuck
    emitTerm (.annotateTerm term attributes)
  else .stuck

/-- The function of an application whose `(` is received, then its arguments, given the
reader of terms. -/
def applicationAt (termAt : Received → Program values values.term) (n : Nat) :
    Received → Program values values.term
  | .token .parenOpen => do
    match ← next with
    | .token (.reserved w) =>
      if w = chars "as" then do
        let identifier ← parseWith (identifierAt n)
        let sort ← parseSort n
        expectClose
        let arguments ← untilClose termAt n
        emitTerm (.handleTerm (.application identifier (some sort) arguments))
      else if w = chars "_" then do
        let identifier ← indexedAfterWord n
        let arguments ← untilClose termAt n
        emitTerm (.handleTerm (.application identifier none arguments))
      else .stuck
    | _ => .stuck
  | .token (.symbol name) => do
    let arguments ← untilClose termAt n
    emitTerm (.handleTerm (.application ⟨name, []⟩ none arguments))
  | _ => .stuck

/-- A term whose first item is received, given the reader of the terms in it. -/
def termStep (termAt : Received → Program values values.term) (n : Nat) :
    Received → Program values values.term
  | .token (.symbol name) => emitTerm (.handleTerm (.identifier ⟨name, []⟩ none))
  | .token .parenOpen => do
    match ← next with
    | .token (.reserved w) => termAfterWord termAt n w
    | item => applicationAt termAt n item
  | item =>
    match constantOf item with
    | some constant => emitTerm (.handleTerm (.constant constant))
    | none => .stuck

/-- A term whose first item is received. -/
def termAt : Nat → Received → Program values values.term
  | 0, _ => .stuck
  | n + 1, item => termStep (termAt n) n item

/-- A term. -/
def parseTerm (n : Nat) : Program values values.term := parseWith (termAt n)

/-! ## The parts of commands -/

/-- The signature of a function after its symbol: its parameters, then its result sort. -/
def signatureAfter (n : Nat) (symbol : Tree.Symbol) : Program values (Signature values) := do
  expectOpen
  let parameters ← untilClose (sortedVarAt n) n
  let result ← parseSort n
  pure ⟨symbol, parameters, result⟩

/-- A constructor after its `(`. -/
def constructorAfterOpen (n : Nat) : Program values (Constructor values) :=
  expectSymbol fun name => do
    let handled ← untilClose (sortedVarAt n) n
    pure ⟨name, handled⟩

/-- A constructor whose `(` is received. -/
def constructorAt (n : Nat) : Received → Program values (Constructor values)
  | .token .parenOpen => constructorAfterOpen n
  | _ => .stuck

/-- A datatype declaration whose `(` is received, given the start to make once its parameters
are known. -/
def datatypeAt (n : Nat) (start : List Tree.Symbol → Program values Unit) :
    Received → Program values (List (Constructor values))
  | .token .parenOpen => do
    match ← next with
    | .token .parenOpen => do
      start []
      let first ← constructorAfterOpen n
      let others ← untilClose (constructorAt n) n
      pure (first :: others)
    | .token .parenClose => do
      start []
      pure []
    | .token (.reserved w) =>
      if w = chars "par" then do
        expectOpen
        let parameters ← untilClose symbolAt n
        start parameters
        expectOpen
        let handled ← untilClose (constructorAt n) n
        expectClose
        pure handled
      else .stuck
    | _ => .stuck
  | _ => .stuck

/-- A datatype declaration of `declare-datatypes` whose `(` is received, and its end. -/
def declarationAt (n : Nat) (item : Received) : Program values Unit := do
  let handled ← datatypeAt n
    (fun parameters => emitUnit (.startDatatypeDeclaration parameters)) item
  emitUnit (.endDatatypeDeclaration handled)

/-- A sort declaration whose `(` is received. -/
def sortDecAt : Received → Program values (Tree.Symbol × Chars)
  | .token .parenOpen => expectSymbol fun name => do
    match ← next with
    | .token (.numeral arity) => do
      expectClose
      pure (name, arity)
    | _ => .stuck
  | _ => .stuck

/-- A function declaration whose `(` is received. -/
def functionDecAt (n : Nat) : Received → Program values (Signature values)
  | .token .parenOpen => expectSymbol fun name => do
    let handled ← signatureAfter n name
    expectClose
    pure handled
  | _ => .stuck

/-- The recursive bodies, one for each of the signatures, each between its start with its
signature, at the arrival of its first item, and its end. -/
def recursiveBodies (n : Nat) : List (Signature values) → Program values Unit
  | [] => pure ()
  | signature :: signatures => do
    let handled ← Program.receive (some (.startRecursiveBody signature)) (termAt n)
    emitUnit (.endRecursiveBody handled)
    recursiveBodies n signatures

/-! ## Commands -/

/-- How the reading goes on after a command: it stops after `exit`, and otherwise goes on, in
the version the command declares if it declares one. -/
inductive After where
  | exit
  | continue (declared : Option Version)

/-- The version a `set-info` declares, given its keyword and its value as the handler got it. -/
def declaredBy (keyword : Chars) : Option (AttributeValueNode values) → Option Version
  | some (.constant (.decimal decimal)) =>
    if keyword = chars "smt-lib-version" then versionOfNumber decimal else none
  | _ => none

/-- The end of a command: its `)`, then its call. -/
def bare (request : Call values .nothing) : Program values After := do
  expectClose
  emitUnit request
  pure (.continue none)

/-- A command after its name. -/
def commandAfter (n : Nat) (w : Chars) : Program values After :=
  if w = chars "assert" then do
    let handled ← parseTerm n
    bare (.commandAssert handled)
  else if w = chars "check-sat" then bare .commandCheckSat
  else if w = chars "check-sat-assuming" then do
    expectOpen
    let handled ← untilClose (termAt n) n
    bare (.commandCheckSatAssuming handled)
  else if w = chars "declare-const" then expectSymbol fun name => do
    let handled ← parseSort n
    bare (.commandDeclareConst name handled)
  else if w = chars "declare-datatype" then expectSymbol fun name => do
    let handled ← parseWith (datatypeAt n fun parameters =>
      emitUnit (.startDeclareDatatype name parameters))
    bare (.endDeclareDatatype handled)
  else if w = chars "declare-datatypes" then do
    expectOpen
    let sorts ← untilClose sortDecAt n
    emitUnit (.startDeclareDatatypes sorts)
    expectOpen
    let _ ← untilClose (declarationAt n) n
    bare .endDeclareDatatypes
  else if w = chars "declare-fun" then expectSymbol fun name => do
    expectOpen
    let parameters ← untilClose (sortAt n) n
    let result ← parseSort n
    bare (.commandDeclareFun name parameters result)
  else if w = chars "declare-sort" then expectSymbol fun name => do
    match ← next with
    | .token (.numeral arity) => bare (.commandDeclareSort name arity)
    | _ => .stuck
  else if w = chars "declare-sort-parameter" then expectSymbol fun name =>
    bare (.commandDeclareSortParameter name)
  else if w = chars "define-const" then expectSymbol fun name => do
    let sort ← parseSort n
    let body ← parseTerm n
    bare (.commandDefineConst name sort body)
  else if w = chars "define-fun" then expectSymbol fun name => do
    let signature ← signatureAfter n name
    emitUnit (.startDefineFun signature)
    let body ← parseTerm n
    bare (.endDefineFun body)
  else if w = chars "define-fun-rec" then expectSymbol fun name => do
    let signature ← signatureAfter n name
    emitUnit (.startDefineFunRec signature)
    let body ← parseTerm n
    bare (.endDefineFunRec body)
  else if w = chars "define-funs-rec" then do
    expectOpen
    let signatures ← untilClose (functionDecAt n) n
    emitUnit (.startDefineFunsRec signatures)
    expectOpen
    recursiveBodies n signatures
    expectClose
    bare .endDefineFunsRec
  else if w = chars "define-sort" then expectSymbol fun name => do
    expectOpen
    let parameters ← untilClose symbolAt n
    emitUnit (.startDefineSort name parameters)
    let sort ← parseSort n
    bare (.endDefineSort sort)
  else if w = chars "echo" then do
    match ← next with
    | .token (.string content) => bare (.commandEcho content)
    | _ => .stuck
  else if w = chars "exit" then do
    expectClose
    emitUnit .commandExit
    pure .exit
  else if w = chars "get-assertions" then bare .commandGetAssertions
  else if w = chars "get-assignment" then bare .commandGetAssignment
  else if w = chars "get-info" then do
    match ← next with
    | .token (.keyword flag) => bare (.commandGetInfo flag)
    | _ => .stuck
  else if w = chars "get-model" then bare .commandGetModel
  else if w = chars "get-option" then do
    match ← next with
    | .token (.keyword keyword) => bare (.commandGetOption keyword)
    | _ => .stuck
  else if w = chars "get-proof" then bare .commandGetProof
  else if w = chars "get-unsat-assumptions" then bare .commandGetUnsatAssumptions
  else if w = chars "get-unsat-core" then bare .commandGetUnsatCore
  else if w = chars "get-value" then do
    expectOpen
    let handled ← untilClose (termAt n) n
    bare (.commandGetValue handled)
  else if w = chars "pop" then do
    match ← next with
    | .token (.numeral count) => bare (.commandPop count)
    | _ => .stuck
  else if w = chars "push" then do
    match ← next with
    | .token (.numeral count) => bare (.commandPush count)
    | _ => .stuck
  else if w = chars "reset" then bare .commandReset
  else if w = chars "reset-assertions" then bare .commandResetAssertions
  else if w = chars "set-info" then do
    match ← next with
    | .token (.keyword keyword) => do
      let (handled, node, following) ← attributeAfter n keyword
      match following with
      | .token .parenClose => do
        emitUnit (.commandSetInfo handled)
        pure (.continue (declaredBy keyword node))
      | _ => .stuck
    | _ => .stuck
  else if w = chars "set-logic" then expectSymbol fun name => bare (.commandSetLogic name)
  else if w = chars "set-option" then do
    match ← next with
    | .token (.keyword keyword) => do
      let (handled, _, following) ← attributeAfter n keyword
      match following with
      | .token .parenClose => do
        emitUnit (.commandSetOption handled)
        pure (.continue none)
      | _ => .stuck
    | _ => .stuck
  else .stuck

/-- A command after its `(`. -/
def commandAfterOpen (n : Nat) : Program values After := do
  match ← next with
  | .token (.reserved w) => commandAfter n w
  | _ => .stuck

/-- After `exit`: the end of the input, and nothing else. -/
def endAfterExit : Program values Unit := do
  match ← Program.receive none .done with
  | .endOfInput => pure ()
  | _ => .stuck

/-- The commands of a script from the next item on, given the number of version declarations
before it, and the reader of the commands after the next one. -/
def commandsStep (commandsFrom : Nat → Program values Unit) (n : Nat) (declarations : Nat) :
    Program values Unit := do
  match ← Program.receive none .done with
  | .endOfInput => pure ()
  | .token .parenOpen => do
    match ← commandAfterOpen n with
    | .exit => .discard endAfterExit
    | .continue none => commandsFrom declarations
    | .continue (some version) =>
      .switch declarations version (commandsFrom (declarations + 1))
  | _ => .stuck

/-- The commands of a script from the next item on, given the number of version declarations
before it. -/
def commandsFrom : Nat → Nat → Program values Unit
  | 0, _ => .stuck
  | n + 1, declarations => commandsStep (commandsFrom n) n declarations

/-- A script read from the version, with fuel `n`: the handler is told the version, then the
commands. -/
def parseScript (n : Nat) (version : Version) : Program values Unit :=
  .setVersion version (commandsFrom n 0)

end BSmtLib.SpecChecks.Parser
