module

public import BSmtLib.Facts.Proofs.Reader.Handler.Traversal
public import BSmtLib.Facts.PublicApi.Adapters.Content
public import BSmtLib.Facts.PublicApi.Adapters.Builder
import all BSmtLib.Facts.PublicApi.Adapters.Content
import all BSmtLib.Facts.Parser.Adapters.Bridge

@[expose] public section

/-!
# A handler that builds the commands

`builder` is a handler told contents only whose values are the specification's trees and whose
state is the version in force and the commands built so far, newest first. Each call builds the
tree it is told of from the trees of its parts; a command's last call adds the command, and a
command whose parts come in several calls (a definition, a datatype declaration) is kept at the
head of the list and completed by its later calls. `answer` is what it does with a call of the
specification, `specBuilder` the specification's handler that does it, and the library handler
agrees with it (`agrees`). None of its calls fails (`noFails`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.Builder

open BSmtLibSpec BSmtLibSpec.Grammar
open BSmtLibSpec.Parser

/-! ## The values and the state -/

/-- What the builder returns for a scope: the bindings of a `let`, the variables of a binder,
or nothing for a case of a `match`. -/
inductive Scope where
  | bindings (bindings : List (Tree.Symbol × Tree.Term))
  | variables (variables : List Tree.SortedVar)
  | none

/-- The builder's values: the specification's trees. -/
abbrev treeValues : Traversal.Values := ⟨Tree.SExpr, Tree.Attribute, Tree.Sort, Tree.Term, Scope⟩

/-- The builder's state: the version in force, and the commands built so far, newest first. -/
abbrev State := Lexicon.Version × List Tree.Command

/-! ## Building a tree from its parts -/

/-- The qualified identifier, with its sort if it has one. -/
def qualified (identifier : Tree.Identifier) : Option Tree.Sort → Tree.QualIdentifier
  | none => .plain identifier
  | some sort => .as identifier sort

/-- The term the handler is told of. -/
def termOf : Traversal.TermNode treeValues → Tree.Term
  | .constant c => .constant c
  | .identifier i s => .identifier (qualified i s)
  | .application i s args => .application (qualified i s) args

/-- The s-expression the handler is told of. -/
def sExprOf : Traversal.SExprNode treeValues → Tree.SExpr
  | .constant c => .constant c
  | .symbol s => .symbol s
  | .reserved w => .reserved w
  | .keyword k => .keyword k
  | .list items => .list items

/-- The value of an attribute the handler is told of. -/
def valueOf : Traversal.AttributeValueNode treeValues → Tree.AttributeValue
  | .constant c => .constant c
  | .symbol s => .symbol s
  | .list items => .list items

/-- The sorted variables. -/
def sortedVarsOf (variables : List (Tree.Symbol × Tree.Sort)) : List Tree.SortedVar :=
  variables.map fun (symbol, sort) => ⟨symbol, sort⟩

/-- The function declaration of a signature. -/
def declarationOf (signature : Traversal.Signature treeValues) : Tree.FunctionDec :=
  ⟨signature.symbol, sortedVarsOf signature.parameters, signature.result⟩

/-- The constructor declaration. -/
def constructorOf (constructor : Traversal.Constructor treeValues) : Tree.ConstructorDec :=
  ⟨constructor.symbol, constructor.selectors.map fun (symbol, sort) => ⟨symbol, sort⟩⟩

/-- The literal a term of `check-sat-assuming` is written as, in 2.5 and 2.6. -/
def literalOf : Tree.Term → Option Tree.PropLiteral
  | .identifier (.plain ⟨symbol, []⟩) => some (.positive symbol)
  | .application (.plain ⟨negation, []⟩) [.identifier (.plain ⟨symbol, []⟩)] =>
    some (.negative negation symbol)
  | _ => none

/-- A sort to hold the place of the sort of a definition in progress. -/
def placeSort : Tree.Sort := .mk ⟨⟨[], false⟩, []⟩ []

/-- A term to hold the place of the body of a definition in progress. -/
def placeTerm : Tree.Term := .constant (.numeral [])

/-- The last datatype declaration with its constructors. -/
def withConstructors (constructors : List Tree.ConstructorDec) :
    List Tree.DatatypeDec → List Tree.DatatypeDec
  | [] => []
  | [last] => [⟨last.parameters, constructors⟩]
  | first :: rest => first :: withConstructors constructors rest

/-- What a call that returns nothing does to the commands built so far, newest first. -/
def command (version : Lexicon.Version) (built : List Tree.Command) :
    Traversal.Call treeValues .nothing → List Tree.Command
  | .startMatch _ => built
  | .commandAssert t => .assert t :: built
  | .commandCheckSat => .checkSat :: built
  | .commandCheckSatAssuming ts =>
    (match version with
      | .v2_7 => .checkSatAssuming ts
      | _ => .checkSatAssumingLiterals (ts.filterMap literalOf)) :: built
  | .commandDeclareConst s t => .declareConst s t :: built
  | .startDeclareDatatype s ps => .declareDatatype s ⟨ps, []⟩ :: built
  | .endDeclareDatatype cs =>
    match built with
    | .declareDatatype s ⟨ps, _⟩ :: rest => .declareDatatype s ⟨ps, cs.map constructorOf⟩ :: rest
    | _ => built
  | .startDeclareDatatypes sorts =>
    .declareDatatypes (sorts.map fun (symbol, arity) => ⟨symbol, arity⟩) [] :: built
  | .startDatatypeDeclaration ps =>
    match built with
    | .declareDatatypes sorts done :: rest => .declareDatatypes sorts (done ++ [⟨ps, []⟩]) :: rest
    | _ => built
  | .endDatatypeDeclaration cs =>
    match built with
    | .declareDatatypes sorts done :: rest =>
      .declareDatatypes sorts (withConstructors (cs.map constructorOf) done) :: rest
    | _ => built
  | .endDeclareDatatypes => built
  | .commandDeclareFun s ps r => .declareFun s ps r :: built
  | .commandDeclareSort s n => .declareSort s n :: built
  | .commandDeclareSortParameter s => .declareSortParameter s :: built
  | .commandDefineConst s t b => .defineConst s t b :: built
  | .startDefineFun sig =>
    .defineFun ⟨sig.symbol, sortedVarsOf sig.parameters, sig.result, placeTerm⟩ :: built
  | .endDefineFun b =>
    match built with
    | .defineFun ⟨s, ps, r, _⟩ :: rest => .defineFun ⟨s, ps, r, b⟩ :: rest
    | _ => built
  | .startDefineFunRec sig =>
    .defineFunRec ⟨sig.symbol, sortedVarsOf sig.parameters, sig.result, placeTerm⟩ :: built
  | .endDefineFunRec b =>
    match built with
    | .defineFunRec ⟨s, ps, r, _⟩ :: rest => .defineFunRec ⟨s, ps, r, b⟩ :: rest
    | _ => built
  | .startDefineFunsRec sigs => .defineFunsRec (sigs.map declarationOf) [] :: built
  | .startRecursiveBody _ => built
  | .endRecursiveBody b =>
    match built with
    | .defineFunsRec ds bs :: rest => .defineFunsRec ds (bs ++ [b]) :: rest
    | _ => built
  | .endDefineFunsRec => built
  | .startDefineSort s ps => .defineSort s ps placeSort :: built
  | .endDefineSort t =>
    match built with
    | .defineSort s ps _ :: rest => .defineSort s ps t :: rest
    | _ => built
  | .commandEcho c => .echo c :: built
  | .commandExit => .exit :: built
  | .commandGetAssertions => .getAssertions :: built
  | .commandGetAssignment => .getAssignment :: built
  | .commandGetInfo k => .getInfo k :: built
  | .commandGetModel => .getModel :: built
  | .commandGetOption k => .getOption k :: built
  | .commandGetProof => .getProof :: built
  | .commandGetUnsatAssumptions => .getUnsatAssumptions :: built
  | .commandGetUnsatCore => .getUnsatCore :: built
  | .commandGetValue ts => .getValue ts :: built
  | .commandPop n => .pop n :: built
  | .commandPush n => .push n :: built
  | .commandReset => .reset :: built
  | .commandResetAssertions => .resetAssertions :: built
  | .commandSetInfo a => .setInfo a :: built
  | .commandSetLogic s => .setLogic s :: built
  | .commandSetOption a => .setOption a :: built

/-- What the builder does with a call: the tree it is told of, and for a call that returns
nothing, the commands built so far changed as `command` says. -/
def answer : {returns : Traversal.Returns} → Traversal.Call treeValues returns →
    StateM State (treeValues.of returns)
  | .sort, .handleSort i args => pure (.mk i args)
  | .sExpr, .handleSExpr node => pure (sExprOf node)
  | .attribute, .handleAttribute k v => pure ⟨k, v.map valueOf⟩
  | .term, .handleTerm node => pure (termOf node)
  | .term, .annotateTerm t attrs => pure (.annotated t attrs)
  | .scope, .startLet bs => pure (.bindings bs)
  | .term, .endLet (.bindings bs) body => pure (.let bs body)
  | .term, .endLet _ body => pure body
  | .scope, .startQuantifier _ vs => pure (.variables (sortedVarsOf vs))
  | .term, .endQuantifier q (.variables vs) body => pure (.quantified q vs body)
  | .term, .endQuantifier _ _ body => pure body
  | .scope, .startLambda vs => pure (.variables (sortedVarsOf vs))
  | .term, .endLambda (.variables vs) body => pure (.lambda vs body)
  | .term, .endLambda _ body => pure body
  | .scope, .startMatchCase _ _ => pure .none
  | .term, .endMatchCase _ _ body => pure body
  | .term, .endMatch t cs => pure (.match t cs)
  | .nothing, request => modify fun (version, built) => (version, command version built request)

/-- The builder as a handler of the specification. -/
def specBuilder : BSmtLibSpec.Parser.Traversal.Handler (StateT State Id) Unit treeValues where
  call request := ExceptT.lift (answer request)
  setVersion version := modify fun (_, built) => (version, built)

/-! ## The builder told contents -/

section

open BSmtLib.Facts.PublicApi.Adapters (Content.Symbol Content.Index Content.Identifier
  Content.Constant Content.SymbolOrWildcard Content.Pattern Content.TermNode Content.SExprNode
  Content.AttributeValueNode Content.Signature Content.Constructor Content.ContentHandler)

/-- The tree of a symbol told by its content. -/
def symbolT (s : Content.Symbol) : Tree.Symbol := ⟨s.name, s.quoted⟩

/-- The tree of an index. -/
def indexT : Content.Index → Tree.Index
  | .numeral digits => .numeral digits
  | .symbol s => .symbol (symbolT s)

/-- The tree of an identifier. -/
def identifierT (i : Content.Identifier) : Tree.Identifier :=
  ⟨symbolT i.symbol, i.indices.map indexT⟩

/-- The tree of a constant. -/
def constantT : Content.Constant → Tree.SpecConstant
  | .numeral d => .numeral d
  | .decimal d => .decimal d
  | .hexadecimal d => .hexadecimal d
  | .binary d => .binary d
  | .string c => .string c

/-- The tree of a symbol or wildcard. -/
def symbolOrWildcardT : Content.SymbolOrWildcard → Tree.SymbolOrWildcard
  | .symbol s => .symbol (symbolT s)
  | .wildcard => .wildcard

/-- The tree of a pattern. -/
def patternT : Content.Pattern → Tree.Pattern
  | .single s => .single (symbolOrWildcardT s)
  | .constructor c args => .constructor (symbolT c) (args.map symbolOrWildcardT)

/-- The pairs with the trees of their symbols. -/
def pairsT {α : Type} (items : List (Content.Symbol × α)) : List (Tree.Symbol × α) :=
  items.map fun (s, a) => (symbolT s, a)

/-- The specification's node of a term node told by its contents. -/
def termNodeT : Content.TermNode Tree.Sort Tree.Term → Traversal.TermNode treeValues
  | .constant c => .constant (constantT c)
  | .identifier i s => .identifier (identifierT i) s
  | .application i s args => .application (identifierT i) s args

/-- The specification's node of an s-expression node. -/
def sExprNodeT : Content.SExprNode Tree.SExpr → Traversal.SExprNode treeValues
  | .constant c => .constant (constantT c)
  | .symbol s => .symbol (symbolT s)
  | .reserved w => .reserved (BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.reserved w)
  | .keyword k => .keyword k
  | .list items => .list items

/-- The specification's node of an attribute value node. -/
def attributeValueNodeT : Content.AttributeValueNode Tree.SExpr →
    Traversal.AttributeValueNode treeValues
  | .constant c => .constant (constantT c)
  | .symbol s => .symbol (symbolT s)
  | .list items => .list items

/-- The specification's signature. -/
def signatureT (sig : Content.Signature Tree.Sort) : Traversal.Signature treeValues :=
  ⟨symbolT sig.symbol, pairsT sig.parameters, sig.result⟩

/-- The specification's constructor. -/
def constructorT (c : Content.Constructor Tree.Sort) : Traversal.Constructor treeValues :=
  ⟨symbolT c.symbol, pairsT c.selectors⟩

/-- A call of the builder, as the specification's. -/
abbrev ask {returns : Traversal.Returns} (request : Traversal.Call treeValues returns) :
    ExceptT Unit (StateM State) (treeValues.of returns) :=
  ExceptT.lift (answer request)

open BSmtLib.Facts.Parser.Adapters.Bridge in
/-- The builder told contents only: each call is `answer` on the specification's call for it. -/
instance builder : Content.ContentHandler State where
  Error := Unit
  SExpr := Tree.SExpr
  Attribute := Tree.Attribute
  «Sort» := Tree.Sort
  Term := Tree.Term
  Scope := Scope
  setVersion v := modify fun (_, built) => (Bridge.version v, built)
  handleSort i args := ask (.handleSort (identifierT i) args)
  handleTerm node := ask (.handleTerm (termNodeT node))
  handleSExpr node := ask (.handleSExpr (sExprNodeT node))
  handleAttribute k v := ask (.handleAttribute k (v.map attributeValueNodeT))
  annotateTerm t attrs := ask (.annotateTerm t attrs)
  startLet bs := ask (.startLet (pairsT bs))
  endLet s t := ask (.endLet s t)
  startQuantifier q vs := ask (.startQuantifier (Bridge.quantifier q) (pairsT vs))
  endQuantifier q s t := ask (.endQuantifier (Bridge.quantifier q) s t)
  startLambda vs := ask (.startLambda (pairsT vs))
  endLambda s t := ask (.endLambda s t)
  startMatch t := ask (.startMatch t)
  startMatchCase t p := ask (.startMatchCase t (patternT p))
  endMatchCase s t b := ask (.endMatchCase s t b)
  endMatch t cs := ask (.endMatch t (cs.map fun (p, b) => (patternT p, b)))
  nonstandardCommand _ := ()
  commandAssert t := ask (.commandAssert t)
  commandCheckSat := ask .commandCheckSat
  commandCheckSatAssuming ts := ask (.commandCheckSatAssuming ts)
  commandDeclareConst s t := ask (.commandDeclareConst (symbolT s) t)
  startDeclareDatatype s ps := ask (.startDeclareDatatype (symbolT s) (ps.map symbolT))
  endDeclareDatatype cs := ask (.endDeclareDatatype (cs.map constructorT))
  startDeclareDatatypes ss := ask (.startDeclareDatatypes (pairsT ss))
  startDatatypeDeclaration ps := ask (.startDatatypeDeclaration (ps.map symbolT))
  endDatatypeDeclaration cs := ask (.endDatatypeDeclaration (cs.map constructorT))
  endDeclareDatatypes := ask .endDeclareDatatypes
  commandDeclareFun s ps r := ask (.commandDeclareFun (symbolT s) ps r)
  commandDeclareSort s n := ask (.commandDeclareSort (symbolT s) n)
  commandDeclareSortParameter s := ask (.commandDeclareSortParameter (symbolT s))
  commandDefineConst s t b := ask (.commandDefineConst (symbolT s) t b)
  startDefineFun sig := ask (.startDefineFun (signatureT sig))
  endDefineFun b := ask (.endDefineFun b)
  startDefineFunRec sig := ask (.startDefineFunRec (signatureT sig))
  endDefineFunRec b := ask (.endDefineFunRec b)
  startDefineFunsRec sigs := ask (.startDefineFunsRec (sigs.map signatureT))
  startRecursiveBody sig := ask (.startRecursiveBody (signatureT sig))
  endRecursiveBody b := ask (.endRecursiveBody b)
  endDefineFunsRec := ask .endDefineFunsRec
  startDefineSort s ps := ask (.startDefineSort (symbolT s) (ps.map symbolT))
  endDefineSort t := ask (.endDefineSort t)
  commandEcho c := ask (.commandEcho c)
  commandExit := ask .commandExit
  commandGetAssertions := ask .commandGetAssertions
  commandGetAssignment := ask .commandGetAssignment
  commandGetInfo k := ask (.commandGetInfo k)
  commandGetModel := ask .commandGetModel
  commandGetOption k := ask (.commandGetOption k)
  commandGetProof := ask .commandGetProof
  commandGetUnsatAssumptions := ask .commandGetUnsatAssumptions
  commandGetUnsatCore := ask .commandGetUnsatCore
  commandGetValue ts := ask (.commandGetValue ts)
  commandPop n := ask (.commandPop n)
  commandPush n := ask (.commandPush n)
  commandReset := ask .commandReset
  commandResetAssertions := ask .commandResetAssertions
  commandSetInfo a := ask (.commandSetInfo a)
  commandSetLogic s := ask (.commandSetLogic (symbolT s))
  commandSetOption a := ask (.commandSetOption a)

end

/-! ## The builder agrees with the specification's -/

section

open BSmtLib.Facts.PublicApi.Adapters.Content
open BSmtLib.Facts.Parser.Adapters.Bridge (Agrees)
open BSmtLib.Facts.Parser.Adapters.Bridge.Bridge

theorem map_map_eq {α β γ : Type} {f : α → β} {g : β → γ} {k : α → γ} (h : ∀ x, g (f x) = k x)
    (l : List α) : (l.map f).map g = l.map k := by
  rw [List.map_map]; exact List.map_congr_left fun x _ => h x

theorem symbolT_ofSymbol (s : BSmtLib.Plain.Symbol) : symbolT (ofSymbol s) = symbol s := rfl

theorem indexT_ofIndex (i : BSmtLib.Nodes.Index) : indexT (ofIndex i) = index i := by
  cases i <;> rfl

theorem identifierT_ofIdentifier (i : BSmtLib.Nodes.Ident) :
    identifierT (ofIdentifier i) = identifier i := by
  obtain ⟨s, is⟩ := i
  show (⟨symbolT (ofSymbol s), (is.toList.map ofIndex).map indexT⟩ : Tree.Identifier) = ⟨_, _⟩
  rw [map_map_eq indexT_ofIndex]; (try rfl)

theorem constantT_ofConstant (c : BSmtLib.Nodes.SpecialConstant) :
    constantT (ofConstant c) = constant c := by
  cases c <;> rfl

theorem symbolOrWildcardT_of (s : BSmtLib.Nodes.SimplePattern) :
    symbolOrWildcardT (ofSymbolOrWildcard s) = symbolOrWildcard s := by
  cases s <;> rfl

theorem patternT_ofPattern (p : BSmtLib.Nodes.Pattern) : patternT (ofPattern p) = pattern p := by
  cases p with
  | simple s => exact congrArg Tree.Pattern.single (symbolOrWildcardT_of s)
  | application a =>
    show Tree.Pattern.constructor _ _ = Tree.Pattern.constructor _ _
    rw [map_map_eq symbolOrWildcardT_of]; (try rfl)

theorem pairsT_ofPairs {α : Type} (items : Array (BSmtLib.Plain.Symbol × α)) :
    pairsT (ofPairs items) = pairs items :=
  map_map_eq (fun _ => rfl) _


theorem termNodeT_of (n : BSmtLib.Nodes.Term Tree.Sort Tree.Term) :
    termNodeT (ofTermNode n) = termNode (H := State) n := by
  cases n with
  | specialConstant c => exact congrArg Traversal.TermNode.constant (constantT_ofConstant c)
  | qualifiedIdent i s =>
    exact congrArg (fun x => Traversal.TermNode.identifier (values := treeValues) x s)
      (identifierT_ofIdentifier i)
  | application i s args _ =>
    exact congrArg
      (fun x => Traversal.TermNode.application (values := treeValues) x s args.asSlice.toList)
      (identifierT_ofIdentifier i)

theorem sExprNodeT_of (n : BSmtLib.Nodes.SExpr Tree.SExpr) :
    sExprNodeT (ofSExprNode n) = sExprNode (H := State) n := by
  cases n <;> first
    | rfl
    | (show Traversal.SExprNode.constant (constantT (ofConstant _)) = _
       rw [constantT_ofConstant]; rfl)

theorem attributeValueNodeT_of (n : BSmtLib.Nodes.AttributeValue Tree.SExpr) :
    attributeValueNodeT (ofAttributeValueNode n) = attributeValue (H := State) n := by
  cases n <;> first
    | rfl
    | (show Traversal.AttributeValueNode.constant (constantT (ofConstant _)) = _
       rw [constantT_ofConstant]; rfl)

theorem signatureT_of (sig : BSmtLib.Multiple.FunctionSignature Tree.Sort) :
    signatureT (ofSignature sig) = signature (H := State) sig := by
  obtain ⟨s, ps, r⟩ := sig
  show (⟨symbolT (ofSymbol s), pairsT (ofPairs ps), r⟩ : Traversal.Signature treeValues) = ⟨_, _, _⟩
  rw [pairsT_ofPairs]; (try rfl)

theorem constructorT_of (c : BSmtLib.Plain.Symbol × BSmtLib.Multiple.SortedVars Tree.Sort) :
    constructorT (ofConstructor c) = constructor (H := State) c := by
  obtain ⟨s, sel⟩ := c
  show (⟨symbolT (ofSymbol s), pairsT (ofPairs sel.toArray)⟩ : Traversal.Constructor treeValues) =
    ⟨_, _⟩
  rw [pairsT_ofPairs]; (try rfl)

/-- The library's handler of the builder answers every call as `specBuilder` does. -/
theorem agrees : Agrees (H := State) (m := Id) specBuilder where
  handleSort i args := by
    show ask _ = ask _; rw [identifierT_ofIdentifier]; (try rfl)
  handleTerm node := by show ask _ = ask _; rw [termNodeT_of]
  handleSExpr node := by show ask _ = ask _; rw [sExprNodeT_of]
  handleAttribute k v := by
    show ask _ = ask _
    rw [show Option.map attributeValueNodeT (Option.map ofAttributeValueNode v) =
        Option.map (attributeValue (H := State)) v by
      cases v <;> simp [attributeValueNodeT_of]]
    rfl
  annotateTerm t attrs := rfl
  startLet bs := by show ask _ = ask _; rw [pairsT_ofPairs]; (try rfl)
  endLet s t := rfl
  startQuantifier q vs := by show ask _ = ask _; rw [pairsT_ofPairs]; (try rfl)
  endQuantifier q s t := rfl
  startLambda vs := by show ask _ = ask _; rw [pairsT_ofPairs]; (try rfl)
  endLambda s t := rfl
  startMatch t := rfl
  startMatchCase t p := by show ask _ = ask _; rw [patternT_ofPattern]; (try rfl)
  endMatchCase s t b := rfl
  endMatch t cs := by
    show ask _ = ask _
    rw [map_map_eq (k := fun (pb : BSmtLib.Nodes.Pattern × Tree.Term) => (pattern pb.1, pb.2))
      (fun pb => by
        obtain ⟨p, b⟩ := pb; show (patternT (ofPattern p), b) = _; rw [patternT_ofPattern])]
    rfl
  setVersion v := rfl
  commandAssert t := rfl
  commandCheckSat := rfl
  commandCheckSatAssuming ts := rfl
  commandDeclareConst s t := rfl
  startDeclareDatatype s ps := by
    show ask _ = ask _; rw [map_map_eq symbolT_ofSymbol]; (try rfl)
  endDeclareDatatype cs := by
    show ask _ = ask _; rw [map_map_eq constructorT_of]; (try rfl)
  startDeclareDatatypes ss := by
    show ask _ = ask _
    unfold pairsT
    rw [map_map_eq (k := fun (sn : BSmtLib.Plain.Symbol × BSmtLib.Plain.Numeral) =>
      (symbol sn.1, chars sn.2.asSlice)) (fun sn => by obtain ⟨s, n⟩ := sn; rfl)]
  startDatatypeDeclaration ps := by
    show ask _ = ask _; rw [map_map_eq symbolT_ofSymbol]; (try rfl)
  endDatatypeDeclaration cs := by
    show ask _ = ask _; rw [map_map_eq constructorT_of]; (try rfl)
  endDeclareDatatypes := rfl
  commandDeclareFun s ps r := rfl
  commandDeclareSort s n := rfl
  commandDeclareSortParameter s := rfl
  commandDefineConst s t b := rfl
  startDefineFun sig := by show ask _ = ask _; rw [signatureT_of]; (try rfl)
  endDefineFun b := rfl
  startDefineFunRec sig := by show ask _ = ask _; rw [signatureT_of]; (try rfl)
  endDefineFunRec b := rfl
  startDefineFunsRec sigs := by
    show ask _ = ask _; rw [map_map_eq signatureT_of]; (try rfl)
  startRecursiveBody sig := by show ask _ = ask _; rw [signatureT_of]; (try rfl)
  endRecursiveBody b := rfl
  endDefineFunsRec := rfl
  startDefineSort s ps := by
    show ask _ = ask _; rw [map_map_eq symbolT_ofSymbol]; (try rfl)
  endDefineSort t := rfl
  commandEcho c := rfl
  commandExit := rfl
  commandGetAssertions := rfl
  commandGetAssignment := rfl
  commandGetInfo k := rfl
  commandGetModel := rfl
  commandGetOption k := rfl
  commandGetProof := rfl
  commandGetUnsatAssumptions := rfl
  commandGetUnsatCore := rfl
  commandGetValue ts := rfl
  commandPop n := rfl
  commandPush n := rfl
  commandReset := rfl
  commandResetAssertions := rfl
  commandSetInfo a := rfl
  commandSetLogic s := rfl
  commandSetOption a := rfl

end

/-- No call of the builder fails. -/
instance noFails : Parser.Blank.Basic.NoFails State where
  noNonstandard parser := Empty.elim parser
  handleSort := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  handleTerm := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  handleSExpr := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  handleAttribute := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  annotateTerm := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startLet := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endLet := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startQuantifier := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endQuantifier := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startLambda := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endLambda := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startMatch := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startMatchCase := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endMatchCase := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endMatch := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandAssert := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandCheckSat := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandCheckSatAssuming := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandDeclareConst := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDeclareDatatype := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDeclareDatatype := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDeclareDatatypes := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDatatypeDeclaration := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDatatypeDeclaration := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDeclareDatatypes := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandDeclareFun := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandDeclareSort := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandDeclareSortParameter := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandDefineConst := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDefineFun := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDefineFun := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDefineFunRec := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDefineFunRec := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDefineFunsRec := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startRecursiveBody := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endRecursiveBody := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDefineFunsRec := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  startDefineSort := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  endDefineSort := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandEcho := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandExit := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetAssertions := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetAssignment := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetInfo := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetModel := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetOption := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetProof := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetUnsatAssumptions := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetUnsatCore := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandGetValue := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandPop := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandPush := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandReset := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandResetAssertions := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandSetInfo := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandSetLogic := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩
  commandSetOption := by intros; exact ⟨fun _ => ⟨_, _, rfl⟩⟩

end BSmtLib.Facts.Proofs.PublicApi.Builder
