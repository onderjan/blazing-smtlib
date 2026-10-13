import BSmtLib.ParserProofs.Adapters.Bridge

/-!
# Library handlers for spec handlers

`Bridged h₀ nonstandard` is a library handler with no state of its own: each of its calls turns
the parser's values into the spec's, through the bridge, and asks the spec's handler `h₀`, in
the monad `h₀` runs in, lifted into the parser's `StateT`. A non-standard command fails with
`nonstandard`. `liftHandler h₀` is `h₀` lifted into the same monad.

`recordingLibrary` is the library handler whose state is the log of a recording run
(`List Event`): each call writes down what the spec's recording handler writes down for it.

These definitions are adapters: the root theorems of `BSmtLib.ParserProofs` and
`BSmtLib.EndToEnd` are stated with them, so they are trusted, and are to be read with the spec.
-/

namespace BSmtLib.ParserProofs

open BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal

/-- The library handler that asks the spec's handler `h₀`; it holds nothing. -/
structure Bridged {m : Type → Type} {ε : Type} {values : Values}
    (h₀ : Traversal.Handler m ε values) (nonstandard : ε) : Type where

section

variable {m : Type → Type} [Monad m] {ε : Type} {values : Values}
variable {h₀ : Traversal.Handler m ε values} {nonstandard : ε}

/-- A run of `m` that may fail, in the parser's monad of the bridged handler. -/
def liftCall {σ α : Type} (action : ExceptT ε m α) : ExceptT ε (StateT σ m) α :=
  ExceptT.mk (StateT.lift action.run)

variable (h₀ nonstandard) in
/-- The answer of `h₀` to the call, lifted. -/
abbrev bridgedCall {returns : Returns} (request : Call values returns) :
    ExceptT ε (StateT (Bridged h₀ nonstandard) m) (values.of returns) :=
  liftCall (h₀.call request)

/-! The bridge's turning of nodes into the spec's, for the types of `values`: the handler
instance needs them before it exists, so they cannot be the bridge's functions themselves. -/

/-- The spec's term node for a term node of the parser, with the values of `values`. -/
def termNodeOf : Parser.TermNode values.sort values.term → TermNode values
  | .constant c => .constant (Bridge.constant c)
  | .identifier i s => .identifier (Bridge.identifier i) s
  | .application i s args => .application (Bridge.identifier i) s args.toList

/-- The spec's S-expression node for one of the parser, with the values of `values`. -/
def sExprNodeOf : Parser.SExprNode values.sExpr → SExprNode values
  | .constant c => .constant (Bridge.constant c)
  | .symbol s => .symbol (Bridge.symbol s)
  | .reserved w => .reserved (Bridge.reserved w)
  | .keyword k => .keyword (Bridge.keyword k)
  | .list items => .list items.toList

/-- The spec's attribute value node for one of the parser, with the values of `values`. -/
def attributeValueOf : Parser.AttributeValueNode values.sExpr → AttributeValueNode values
  | .constant c => .constant (Bridge.constant c)
  | .symbol s => .symbol (Bridge.symbol s)
  | .list items => .list items.toList

/-- The bridged handler's values are those of `h₀`; it answers each call of terms, and the
version, by turning the values into the spec's and asking `h₀`. -/
instance : Parser.Handler (Bridged h₀ nonstandard) m where
  Error := ε
  SExpr := values.sExpr
  Attribute := values.«attribute»
  «Sort» := values.sort
  Term := values.term
  Scope := values.scope
  setVersion v := StateT.lift (h₀.setVersion (Bridge.version v))
  handleSort i args := bridgedCall h₀ nonstandard (.handleSort (Bridge.identifier i) args.toList)
  handleTerm node := bridgedCall h₀ nonstandard (.handleTerm (termNodeOf node))
  handleSExpr node := bridgedCall h₀ nonstandard (.handleSExpr (sExprNodeOf node))
  handleAttribute k v := bridgedCall h₀ nonstandard
    (.handleAttribute (Bridge.keyword k) (v.map attributeValueOf))
  annotateTerm t attrs := bridgedCall h₀ nonstandard (.annotateTerm t attrs.toList)
  startLet bs := bridgedCall h₀ nonstandard (.startLet (Bridge.pairs bs))
  endLet s t := bridgedCall h₀ nonstandard (.endLet s t)
  startQuantifier q vs := bridgedCall h₀ nonstandard
    (.startQuantifier (Bridge.quantifier q) (Bridge.pairs vs))
  endQuantifier q s t := bridgedCall h₀ nonstandard (.endQuantifier (Bridge.quantifier q) s t)
  startLambda vs := bridgedCall h₀ nonstandard (.startLambda (Bridge.pairs vs))
  endLambda s t := bridgedCall h₀ nonstandard (.endLambda s t)
  startMatch t := bridgedCall h₀ nonstandard (.startMatch t)
  startMatchCase t p := bridgedCall h₀ nonstandard (.startMatchCase t (Bridge.pattern p))
  endMatchCase s t b := bridgedCall h₀ nonstandard (.endMatchCase s t b)
  endMatch t cs := bridgedCall h₀ nonstandard
    (.endMatch t (cs.toList.map fun (p, b) => (Bridge.pattern p, b)))

/-- The bridged handler answers each command by turning the values into the spec's and asking
`h₀`; a non-standard command fails with `nonstandard`. -/
instance : Parser.CommandHandler (Bridged h₀ nonstandard) m where
  nonstandardCommand _ := nonstandard
  commandAssert t := bridgedCall h₀ nonstandard (.commandAssert t)
  commandCheckSat := bridgedCall h₀ nonstandard .commandCheckSat
  commandCheckSatAssuming ts := bridgedCall h₀ nonstandard (.commandCheckSatAssuming ts.toList)
  commandDeclareConst s t := bridgedCall h₀ nonstandard (.commandDeclareConst (Bridge.symbol s) t)
  startDeclareDatatype s ps := bridgedCall h₀ nonstandard
    (.startDeclareDatatype (Bridge.symbol s) (ps.toList.map Bridge.symbol))
  endDeclareDatatype cs := bridgedCall h₀ nonstandard
    (.endDeclareDatatype (cs.toList.map (Bridge.constructor (H := Bridged h₀ nonstandard))))
  startDeclareDatatypes ss := bridgedCall h₀ nonstandard
    (.startDeclareDatatypes (ss.toList.map fun (s, n) => (Bridge.symbol s, Bridge.chars n.asSlice)))
  startDatatypeDeclaration ps := bridgedCall h₀ nonstandard
    (.startDatatypeDeclaration (ps.toList.map Bridge.symbol))
  endDatatypeDeclaration cs := bridgedCall h₀ nonstandard
    (.endDatatypeDeclaration (cs.toList.map (Bridge.constructor (H := Bridged h₀ nonstandard))))
  endDeclareDatatypes := bridgedCall h₀ nonstandard .endDeclareDatatypes
  commandDeclareFun s ps r := bridgedCall h₀ nonstandard
    (.commandDeclareFun (Bridge.symbol s) ps.toList r)
  commandDeclareSort s n := bridgedCall h₀ nonstandard
    (.commandDeclareSort (Bridge.symbol s) (Bridge.chars n.asSlice))
  commandDeclareSortParameter s := bridgedCall h₀ nonstandard
    (.commandDeclareSortParameter (Bridge.symbol s))
  commandDefineConst s t b := bridgedCall h₀ nonstandard
    (.commandDefineConst (Bridge.symbol s) t b)
  startDefineFun sig := bridgedCall h₀ nonstandard
    (.startDefineFun (Bridge.signature (H := Bridged h₀ nonstandard) sig))
  endDefineFun b := bridgedCall h₀ nonstandard (.endDefineFun b)
  startDefineFunRec sig := bridgedCall h₀ nonstandard
    (.startDefineFunRec (Bridge.signature (H := Bridged h₀ nonstandard) sig))
  endDefineFunRec b := bridgedCall h₀ nonstandard (.endDefineFunRec b)
  startDefineFunsRec sigs := bridgedCall h₀ nonstandard
    (.startDefineFunsRec (sigs.toList.map (Bridge.signature (H := Bridged h₀ nonstandard))))
  startRecursiveBody sig := bridgedCall h₀ nonstandard
    (.startRecursiveBody (Bridge.signature (H := Bridged h₀ nonstandard) sig))
  endRecursiveBody b := bridgedCall h₀ nonstandard (.endRecursiveBody b)
  endDefineFunsRec := bridgedCall h₀ nonstandard .endDefineFunsRec
  startDefineSort s ps := bridgedCall h₀ nonstandard
    (.startDefineSort (Bridge.symbol s) (ps.toList.map Bridge.symbol))
  endDefineSort t := bridgedCall h₀ nonstandard (.endDefineSort t)
  commandEcho c := bridgedCall h₀ nonstandard (.commandEcho (Bridge.chars c.asSlice))
  commandExit := bridgedCall h₀ nonstandard .commandExit
  commandGetAssertions := bridgedCall h₀ nonstandard .commandGetAssertions
  commandGetAssignment := bridgedCall h₀ nonstandard .commandGetAssignment
  commandGetInfo k := bridgedCall h₀ nonstandard (.commandGetInfo (Bridge.keyword k))
  commandGetModel := bridgedCall h₀ nonstandard .commandGetModel
  commandGetOption k := bridgedCall h₀ nonstandard (.commandGetOption (Bridge.keyword k))
  commandGetProof := bridgedCall h₀ nonstandard .commandGetProof
  commandGetUnsatAssumptions := bridgedCall h₀ nonstandard .commandGetUnsatAssumptions
  commandGetUnsatCore := bridgedCall h₀ nonstandard .commandGetUnsatCore
  commandGetValue ts := bridgedCall h₀ nonstandard (.commandGetValue ts.toList)
  commandPop n := bridgedCall h₀ nonstandard (.commandPop (Bridge.chars n.asSlice))
  commandPush n := bridgedCall h₀ nonstandard (.commandPush (Bridge.chars n.asSlice))
  commandReset := bridgedCall h₀ nonstandard .commandReset
  commandResetAssertions := bridgedCall h₀ nonstandard .commandResetAssertions
  commandSetInfo a := bridgedCall h₀ nonstandard (.commandSetInfo a)
  commandSetLogic s := bridgedCall h₀ nonstandard (.commandSetLogic (Bridge.symbol s))
  commandSetOption a := bridgedCall h₀ nonstandard (.commandSetOption a)

variable (h₀ nonstandard) in
/-- The spec's handler `h₀`, lifted into the parser's monad of the bridged handler. -/
def liftHandler :
    Traversal.Handler (StateT (Bridged h₀ nonstandard) m) ε (valuesOf (Bridged h₀ nonstandard))
    where
  call {returns} request := bridgedCall (returns := returns) h₀ nonstandard request
  setVersion v := StateT.lift (h₀.setVersion v)

end

/-- The recording handler's answer, with its errors (of which it has none) in `Unit`. -/
abbrev recordingCall {returns : Returns} (request : Call Recorded returns) :
    ExceptT Unit Recording (Recorded.of returns) :=
  ExceptT.adapt (fun error => nomatch error) (recordingHandler.call request)

/-- The library handler of terms whose state is the log of a recording run: each call writes
down what the spec's recording handler writes down for it and returns what it returns, the number
of calls before it. It fails on nothing. -/
instance recordingLibraryTerms : Parser.Handler (List Event) Id where
  Error := Unit
  SExpr := Nat
  Attribute := Nat
  «Sort» := Nat
  Term := Nat
  Scope := Nat
  setVersion v := recordingHandler.setVersion (Bridge.version v)
  handleSort i args := recordingCall (.handleSort (Bridge.identifier i) args.toList)
  handleTerm node := recordingCall (.handleTerm (termNodeOf node))
  handleSExpr node := recordingCall (.handleSExpr (sExprNodeOf node))
  handleAttribute k v := recordingCall
    (.handleAttribute (Bridge.keyword k) (v.map attributeValueOf))
  annotateTerm t attrs := recordingCall (.annotateTerm t attrs.toList)
  startLet bs := recordingCall (.startLet (Bridge.pairs bs))
  endLet s t := recordingCall (.endLet s t)
  startQuantifier q vs := recordingCall
    (.startQuantifier (Bridge.quantifier q) (Bridge.pairs vs))
  endQuantifier q s t := recordingCall (.endQuantifier (Bridge.quantifier q) s t)
  startLambda vs := recordingCall (.startLambda (Bridge.pairs vs))
  endLambda s t := recordingCall (.endLambda s t)
  startMatch t := recordingCall (.startMatch t)
  startMatchCase t p := recordingCall (.startMatchCase t (Bridge.pattern p))
  endMatchCase s t b := recordingCall (.endMatchCase s t b)
  endMatch t cs := recordingCall
    (.endMatch t (cs.toList.map fun (p, b) => (Bridge.pattern p, b)))

/-- The library handler of commands whose state is the log of a recording run: each call writes
down what the spec's recording handler writes down for it. A non-standard command fails with
`()`. -/
instance recordingLibrary : Parser.CommandHandler (List Event) Id where
  nonstandardCommand _ := ()
  commandAssert t := recordingCall (.commandAssert t)
  commandCheckSat := recordingCall .commandCheckSat
  commandCheckSatAssuming ts := recordingCall (.commandCheckSatAssuming ts.toList)
  commandDeclareConst s t := recordingCall (.commandDeclareConst (Bridge.symbol s) t)
  startDeclareDatatype s ps := recordingCall
    (.startDeclareDatatype (Bridge.symbol s) (ps.toList.map Bridge.symbol))
  endDeclareDatatype cs := recordingCall
    (.endDeclareDatatype (cs.toList.map (Bridge.constructor (H := List Event))))
  startDeclareDatatypes ss := recordingCall
    (.startDeclareDatatypes (ss.toList.map fun (s, n) => (Bridge.symbol s, Bridge.chars n.asSlice)))
  startDatatypeDeclaration ps := recordingCall
    (.startDatatypeDeclaration (ps.toList.map Bridge.symbol))
  endDatatypeDeclaration cs := recordingCall
    (.endDatatypeDeclaration (cs.toList.map (Bridge.constructor (H := List Event))))
  endDeclareDatatypes := recordingCall .endDeclareDatatypes
  commandDeclareFun s ps r := recordingCall
    (.commandDeclareFun (Bridge.symbol s) ps.toList r)
  commandDeclareSort s n := recordingCall
    (.commandDeclareSort (Bridge.symbol s) (Bridge.chars n.asSlice))
  commandDeclareSortParameter s := recordingCall
    (.commandDeclareSortParameter (Bridge.symbol s))
  commandDefineConst s t b := recordingCall
    (.commandDefineConst (Bridge.symbol s) t b)
  startDefineFun sig := recordingCall
    (.startDefineFun (Bridge.signature (H := List Event) sig))
  endDefineFun b := recordingCall (.endDefineFun b)
  startDefineFunRec sig := recordingCall
    (.startDefineFunRec (Bridge.signature (H := List Event) sig))
  endDefineFunRec b := recordingCall (.endDefineFunRec b)
  startDefineFunsRec sigs := recordingCall
    (.startDefineFunsRec (sigs.toList.map (Bridge.signature (H := List Event))))
  startRecursiveBody sig := recordingCall
    (.startRecursiveBody (Bridge.signature (H := List Event) sig))
  endRecursiveBody b := recordingCall (.endRecursiveBody b)
  endDefineFunsRec := recordingCall .endDefineFunsRec
  startDefineSort s ps := recordingCall
    (.startDefineSort (Bridge.symbol s) (ps.toList.map Bridge.symbol))
  endDefineSort t := recordingCall (.endDefineSort t)
  commandEcho c := recordingCall (.commandEcho (Bridge.chars c.asSlice))
  commandExit := recordingCall .commandExit
  commandGetAssertions := recordingCall .commandGetAssertions
  commandGetAssignment := recordingCall .commandGetAssignment
  commandGetInfo k := recordingCall (.commandGetInfo (Bridge.keyword k))
  commandGetModel := recordingCall .commandGetModel
  commandGetOption k := recordingCall (.commandGetOption (Bridge.keyword k))
  commandGetProof := recordingCall .commandGetProof
  commandGetUnsatAssumptions := recordingCall .commandGetUnsatAssumptions
  commandGetUnsatCore := recordingCall .commandGetUnsatCore
  commandGetValue ts := recordingCall (.commandGetValue ts.toList)
  commandPop n := recordingCall (.commandPop (Bridge.chars n.asSlice))
  commandPush n := recordingCall (.commandPush (Bridge.chars n.asSlice))
  commandReset := recordingCall .commandReset
  commandResetAssertions := recordingCall .commandResetAssertions
  commandSetInfo a := recordingCall (.commandSetInfo a)
  commandSetLogic s := recordingCall (.commandSetLogic (Bridge.symbol s))
  commandSetOption a := recordingCall (.commandSetOption a)

end BSmtLib.ParserProofs
