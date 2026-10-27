module

public import BSmtLib.Facts.PublicApi.Adapters

@[expose] public section

/-!
# Handlers that see contents only

A library handler is handed views of the bytes names and constants were written with, and a view
keeps the storage it points into: the slice the reader was fed, or the lexer's buffer. A handler
could read the whole input from that storage. The theorems about the public API (`BSmtLib.Facts`,
`BSmtLib.Facts.PublicApi`) therefore speak of handlers that are told what the parser's handler is
told with each view replaced by its content, as a list of bytes (`ContentHandler`);
`instCommandHandler` makes such a handler a library handler, which converts each view before every
call.
-/

namespace BSmtLib.Facts.PublicApi.Adapters.Content


/-- The content of a view: its bytes as a list. -/
def contentOf (slice : ByteSlice) : ByteList := slice.toByteArray.toList

/-! ## What the parser hands over, as contents -/

/-- A symbol: its content, without the bars of a quoted symbol, and whether it was quoted. -/
structure Symbol where
  name : ByteList
  quoted : Bool

/-- An index of an indexed identifier. -/
inductive Index where
  | numeral (digits : ByteList)
  | symbol (symbol : Symbol)

/-- An identifier: a symbol, with its indices if it is indexed. -/
structure Identifier where
  symbol : Symbol
  indices : List Index

/-- A constant: its kind and its content. -/
inductive Constant where
  | numeral (digits : ByteList)
  | decimal (text : ByteList)
  | hexadecimal (digits : ByteList)
  | binary (digits : ByteList)
  | string (content : ByteList)

/-- A symbol, or the wildcard `_`, in a pattern. -/
inductive SymbolOrWildcard where
  | symbol (symbol : Symbol)
  | wildcard

/-- The pattern of a case of `match`. -/
inductive Pattern where
  | single (symbol : SymbolOrWildcard)
  | constructor (constructor : Symbol) (arguments : List SymbolOrWildcard)

/-- A term that binds nothing, its parts already handled. -/
inductive TermNode (S T : Type) where
  | constant (constant : Constant)
  | identifier (identifier : Identifier) (sort : Option S)
  | application (function : Identifier) (sort : Option S) (arguments : List T)

/-- An s-expression, its items already handled. -/
inductive SExprNode (X : Type) where
  | constant (constant : Constant)
  | symbol (symbol : Symbol)
  | reserved (word : Lexicon.Reserved)
  | keyword (name : ByteList)
  | list (items : List X)

/-- The value of an attribute, the items of a list value already handled. -/
inductive AttributeValueNode (X : Type) where
  | constant (constant : Constant)
  | symbol (symbol : Symbol)
  | list (items : List X)

/-- The signature of a defined function, its sorts already handled. -/
structure Signature (S : Type) where
  symbol : Symbol
  parameters : List (Symbol × S)
  result : S

/-- A datatype constructor, the sorts of its selectors already handled. -/
structure Constructor (S : Type) where
  symbol : Symbol
  selectors : List (Symbol × S)

/-! ## Views replaced by contents -/

/-- The symbol's content. -/
def ofSymbol (s : Lexicon.Value.Symbol) : Symbol := ⟨contentOf s.asSlice, s.isQuoted⟩

/-- The index's content. -/
def ofIndex : Grammar.Nodes.Index → Index
  | .numeral digits => .numeral (contentOf digits.asSlice)
  | .symbol s => .symbol (ofSymbol s)

/-- The identifier's content. -/
def ofIdentifier (i : Grammar.Nodes.Ident) : Identifier :=
  ⟨ofSymbol i.name, i.indices.toList.map ofIndex⟩

/-- The constant's content. -/
def ofConstant : Grammar.Nodes.SpecialConstant → Constant
  | .numeral d => .numeral (contentOf d.asSlice)
  | .decimal d => .decimal (contentOf d.asSlice)
  | .hexadecimal d => .hexadecimal (contentOf d.asSlice)
  | .binary d => .binary (contentOf d.asSlice)
  | .string c => .string (contentOf c.asSlice)

/-- The symbol or wildcard's content. -/
def ofSymbolOrWildcard : Grammar.Nodes.SimplePattern → SymbolOrWildcard
  | .symbol s => .symbol (ofSymbol s)
  | .wildcard => .wildcard

/-- The pattern's content. -/
def ofPattern : Grammar.Nodes.Pattern → Pattern
  | .simple s => .single (ofSymbolOrWildcard s)
  | .application ⟨c, args, _⟩ => .constructor (ofSymbol c) (args.toList.map ofSymbolOrWildcard)

/-- The term node's content. -/
def ofTermNode {S T : Type} : Grammar.Nodes.Term S T → TermNode S T
  | .specialConstant c => .constant (ofConstant c)
  | .qualifiedIdent i s => .identifier (ofIdentifier i) s
  | .application i s args _ => .application (ofIdentifier i) s args.asSlice.toList

/-- The s-expression node's content. -/
def ofSExprNode {X : Type} : Grammar.Nodes.SExpr X → SExprNode X
  | .specialConstant c => .constant (ofConstant c)
  | .symbol s => .symbol (ofSymbol s)
  | .reserved w => .reserved w
  | .keyword k => .keyword (contentOf k.asSlice)
  | .sExprs items => .list items.asSlice.toList

/-- The attribute value node's content. -/
def ofAttributeValueNode {X : Type} : Grammar.Nodes.AttributeValue X → AttributeValueNode X
  | .specialConstant c => .constant (ofConstant c)
  | .symbol s => .symbol (ofSymbol s)
  | .sExprs items => .list items.asSlice.toList

/-- The pairs with their symbols' contents. -/
def ofPairs {α : Type} (items : Array (Lexicon.Value.Symbol × α)) : List (Symbol × α) :=
  items.toList.map fun (s, a) => (ofSymbol s, a)

/-- The signature's content. -/
def ofSignature {S : Type} (sig : Grammar.Multiple.FunctionSignature S) : Signature S :=
  ⟨ofSymbol sig.name, ofPairs sig.params, sig.resultSort⟩

/-- The constructor's content. -/
def ofConstructor {S : Type} (c : Lexicon.Value.Symbol × Grammar.Multiple.SortedVars S) : Constructor S :=
  ⟨ofSymbol c.1, ofPairs c.2.toArray⟩

open Content

/--
A handler of commands that is told contents only: the calls of `Handler` and
`CommandHandler`, in `Id`, with every view replaced by its content and every array by a
list.
-/
class ContentHandler (C : Type) where
  Error : Type
  SExpr : Type
  Attribute : Type
  «Sort» : Type
  Term : Type
  Scope : Type
  setVersion : Version → StateM C Unit
  handleSort : Content.Identifier → List «Sort» → ExceptT Error (StateM C) «Sort»
  handleTerm : Content.TermNode «Sort» Term → ExceptT Error (StateM C) Term
  handleSExpr : Content.SExprNode SExpr → ExceptT Error (StateM C) SExpr
  handleAttribute : ByteList → Option (Content.AttributeValueNode SExpr) →
    ExceptT Error (StateM C) Attribute
  annotateTerm : Term → List Attribute → ExceptT Error (StateM C) Term
  startLet : List (Content.Symbol × Term) → ExceptT Error (StateM C) Scope
  endLet : Scope → Term → ExceptT Error (StateM C) Term
  startQuantifier : Grammar.Nodes.QuantifierKind → List (Content.Symbol × «Sort») →
    ExceptT Error (StateM C) Scope
  endQuantifier : Grammar.Nodes.QuantifierKind → Scope → Term → ExceptT Error (StateM C) Term
  startLambda : List (Content.Symbol × «Sort») → ExceptT Error (StateM C) Scope
  endLambda : Scope → Term → ExceptT Error (StateM C) Term
  startMatch : Term → ExceptT Error (StateM C) Unit
  startMatchCase : Term → Content.Pattern → ExceptT Error (StateM C) Scope
  endMatchCase : Scope → Term → Term → ExceptT Error (StateM C) Term
  endMatch : Term → List (Content.Pattern × Term) → ExceptT Error (StateM C) Term
  nonstandardCommand : Content.Symbol → Error
  commandAssert : Term → ExceptT Error (StateM C) Unit
  commandCheckSat : ExceptT Error (StateM C) Unit
  commandCheckSatAssuming : List Term → ExceptT Error (StateM C) Unit
  commandDeclareConst : Content.Symbol → «Sort» → ExceptT Error (StateM C) Unit
  startDeclareDatatype : Content.Symbol → List Content.Symbol → ExceptT Error (StateM C) Unit
  endDeclareDatatype : List (Content.Constructor «Sort») → ExceptT Error (StateM C) Unit
  startDeclareDatatypes : List (Content.Symbol × ByteList) → ExceptT Error (StateM C) Unit
  startDatatypeDeclaration : List Content.Symbol → ExceptT Error (StateM C) Unit
  endDatatypeDeclaration : List (Content.Constructor «Sort») → ExceptT Error (StateM C) Unit
  endDeclareDatatypes : ExceptT Error (StateM C) Unit
  commandDeclareFun : Content.Symbol → List «Sort» → «Sort» → ExceptT Error (StateM C) Unit
  commandDeclareSort : Content.Symbol → ByteList → ExceptT Error (StateM C) Unit
  commandDeclareSortParameter : Content.Symbol → ExceptT Error (StateM C) Unit
  commandDefineConst : Content.Symbol → «Sort» → Term → ExceptT Error (StateM C) Unit
  startDefineFun : Content.Signature «Sort» → ExceptT Error (StateM C) Unit
  endDefineFun : Term → ExceptT Error (StateM C) Unit
  startDefineFunRec : Content.Signature «Sort» → ExceptT Error (StateM C) Unit
  endDefineFunRec : Term → ExceptT Error (StateM C) Unit
  startDefineFunsRec : List (Content.Signature «Sort») → ExceptT Error (StateM C) Unit
  startRecursiveBody : Content.Signature «Sort» → ExceptT Error (StateM C) Unit
  endRecursiveBody : Term → ExceptT Error (StateM C) Unit
  endDefineFunsRec : ExceptT Error (StateM C) Unit
  startDefineSort : Content.Symbol → List Content.Symbol → ExceptT Error (StateM C) Unit
  endDefineSort : «Sort» → ExceptT Error (StateM C) Unit
  commandEcho : ByteList → ExceptT Error (StateM C) Unit
  commandExit : ExceptT Error (StateM C) Unit
  commandGetAssertions : ExceptT Error (StateM C) Unit
  commandGetAssignment : ExceptT Error (StateM C) Unit
  commandGetInfo : ByteList → ExceptT Error (StateM C) Unit
  commandGetModel : ExceptT Error (StateM C) Unit
  commandGetOption : ByteList → ExceptT Error (StateM C) Unit
  commandGetProof : ExceptT Error (StateM C) Unit
  commandGetUnsatAssumptions : ExceptT Error (StateM C) Unit
  commandGetUnsatCore : ExceptT Error (StateM C) Unit
  commandGetValue : List Term → ExceptT Error (StateM C) Unit
  commandPop : ByteList → ExceptT Error (StateM C) Unit
  commandPush : ByteList → ExceptT Error (StateM C) Unit
  commandReset : ExceptT Error (StateM C) Unit
  commandResetAssertions : ExceptT Error (StateM C) Unit
  commandSetInfo : Attribute → ExceptT Error (StateM C) Unit
  commandSetLogic : Content.Symbol → ExceptT Error (StateM C) Unit
  commandSetOption : Attribute → ExceptT Error (StateM C) Unit

namespace ContentHandler

variable {C : Type} [ContentHandler C]

/-- A content handler as a library handler of terms: each call is the content handler's, told
the contents of the views. -/
instance instHandler : Handler C Id where
  Error := Error C
  SExpr := SExpr C
  Attribute := Attribute C
  «Sort» := «Sort» C
  Term := Term C
  Scope := Scope C
  setVersion v := setVersion v
  handleSort i args := handleSort (ofIdentifier i) args.asSlice.toList
  handleTerm node := handleTerm (ofTermNode node)
  handleSExpr node := handleSExpr (ofSExprNode node)
  handleAttribute k v := handleAttribute (contentOf k.asSlice) (v.map ofAttributeValueNode)
  annotateTerm t attrs := annotateTerm t attrs.asSlice.toList
  startLet bs := startLet (ofPairs bs.toArray)
  endLet s t := endLet s t
  startQuantifier q vs := startQuantifier q (ofPairs vs.toArray)
  endQuantifier q s t := endQuantifier q s t
  startLambda vs := startLambda (ofPairs vs.toArray)
  endLambda s t := endLambda s t
  startMatch t := startMatch t
  startMatchCase t p := startMatchCase t (ofPattern p)
  endMatchCase s t b := endMatchCase s t b
  endMatch t cs := endMatch t (cs.toArray.toList.map fun (p, b) => (ofPattern p, b))

/-- A content handler as a library handler of commands: each call is the content handler's,
told the contents of the views. -/
instance instCommandHandler : Handler.CommandHandler C Id where
  NonstandardParser := Empty
  nonstandardCommand s := throw (nonstandardCommand (ofSymbol s))
  commandAssert t := commandAssert t
  commandCheckSat := commandCheckSat
  commandCheckSatAssuming ts := commandCheckSatAssuming ts.asSlice.toList
  commandDeclareConst s t := commandDeclareConst (ofSymbol s) t
  startDeclareDatatype s ps := startDeclareDatatype (ofSymbol s) (ps.toArray.toList.map ofSymbol)
  endDeclareDatatype cs := endDeclareDatatype (cs.toArray.toList.map ofConstructor)
  startDeclareDatatypes ss :=
    startDeclareDatatypes (ss.toArray.toList.map fun (s, n) => (ofSymbol s, contentOf n.asSlice))
  startDatatypeDeclaration ps := startDatatypeDeclaration (ps.toArray.toList.map ofSymbol)
  endDatatypeDeclaration cs := endDatatypeDeclaration (cs.toArray.toList.map ofConstructor)
  endDeclareDatatypes := endDeclareDatatypes
  commandDeclareFun s ps r := commandDeclareFun (ofSymbol s) ps.asSlice.toList r
  commandDeclareSort s n := commandDeclareSort (ofSymbol s) (contentOf n.asSlice)
  commandDeclareSortParameter s := commandDeclareSortParameter (ofSymbol s)
  commandDefineConst s t b := commandDefineConst (ofSymbol s) t b
  startDefineFun sig := startDefineFun (ofSignature sig)
  endDefineFun b := endDefineFun b
  startDefineFunRec sig := startDefineFunRec (ofSignature sig)
  endDefineFunRec b := endDefineFunRec b
  startDefineFunsRec sigs := startDefineFunsRec (sigs.toArray.toList.map ofSignature)
  startRecursiveBody sig := startRecursiveBody (ofSignature sig)
  endRecursiveBody b := endRecursiveBody b
  endDefineFunsRec := endDefineFunsRec
  startDefineSort s ps := startDefineSort (ofSymbol s) (ps.toArray.toList.map ofSymbol)
  endDefineSort t := endDefineSort t
  commandEcho c := commandEcho (contentOf c.asSlice)
  commandExit := commandExit
  commandGetAssertions := commandGetAssertions
  commandGetAssignment := commandGetAssignment
  commandGetInfo k := commandGetInfo (contentOf k.asSlice)
  commandGetModel := commandGetModel
  commandGetOption k := commandGetOption (contentOf k.asSlice)
  commandGetProof := commandGetProof
  commandGetUnsatAssumptions := commandGetUnsatAssumptions
  commandGetUnsatCore := commandGetUnsatCore
  commandGetValue ts := commandGetValue ts.asSlice.toList
  commandPop n := commandPop (contentOf n.asSlice)
  commandPush n := commandPush (contentOf n.asSlice)
  commandReset := commandReset
  commandResetAssertions := commandResetAssertions
  commandSetInfo a := commandSetInfo a
  commandSetLogic s := commandSetLogic (ofSymbol s)
  commandSetOption a := commandSetOption a

end ContentHandler

end BSmtLib.Facts.PublicApi.Adapters.Content
