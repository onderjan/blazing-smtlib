module

public import BSmtLib.Facts.PublicApi.Adapters.Content
public import BSmtLib.Facts.Parser.Adapters

@[expose] public section

/-!
# The recording handler, told contents only

The recording handler of the parser proofs (`Parser.Adapters.Handler.recordingLibrary`) uses of the
views it is handed only their contents. `recorderContent` is the same handler as a `ContentHandler`:
each call writes down what the specification's recording handler writes down for it, built from the
contents. As a library handler it is the recording handler itself (`instCommandHandler_eq`), so
everything proved of the one holds of the other.
-/

open BSmtLib.Facts.PublicApi.Adapters BSmtLib.Facts.PublicApi.Adapters.Content

namespace BSmtLib.Facts.Proofs.PublicApi.Recorder

open BSmtLibSpec BSmtLibSpec.Grammar BSmtLibSpec.Parser BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Facts.Parser.Adapters.Handler (recordingCall)

namespace ToSpec

/-- The specification's symbol for a symbol's content. -/
def symbol (s : Content.Symbol) : Tree.Symbol := ⟨s.name, s.quoted⟩

/-- The specification's index for an index's content. -/
def index : Content.Index → Tree.Index
  | .numeral digits => .numeral digits
  | .symbol s => .symbol (symbol s)

/-- The specification's identifier for an identifier's content. -/
def identifier (i : Content.Identifier) : Tree.Identifier := ⟨symbol i.symbol, i.indices.map index⟩

/-- The specification's constant for a constant's content. -/
def constant : Content.Constant → Tree.SpecConstant
  | .numeral d => .numeral d
  | .decimal d => .decimal d
  | .hexadecimal d => .hexadecimal d
  | .binary d => .binary d
  | .string c => .string c

/-- The specification's symbol or wildcard. -/
def symbolOrWildcard : Content.SymbolOrWildcard → Tree.SymbolOrWildcard
  | .symbol s => .symbol (symbol s)
  | .wildcard => .wildcard

/-- The specification's pattern. -/
def pattern : Content.Pattern → Tree.Pattern
  | .single s => .single (symbolOrWildcard s)
  | .constructor c args => .constructor (symbol c) (args.map symbolOrWildcard)

/-- The specification's quantifier. -/
def quantifier : Grammar.Nodes.QuantifierKind → Tree.Quantifier
  | .forall => .forall
  | .exists => .exists

/-- The pairs with their symbols the specification's. -/
def pairs {α : Type} (items : List (Content.Symbol × α)) : List (Tree.Symbol × α) :=
  items.map fun (s, a) => (symbol s, a)

/-- The specification's term node. -/
def termNode : Content.TermNode Nat Nat → Traversal.TermNode Recorded
  | .constant c => .constant (constant c)
  | .identifier i s => .identifier (identifier i) s
  | .application i s args => .application (identifier i) s args

/-- The specification's s-expression node. -/
def sExprNode : Content.SExprNode Nat → Traversal.SExprNode Recorded
  | .constant c => .constant (constant c)
  | .symbol s => .symbol (symbol s)
  | .reserved w => .reserved (Parser.Adapters.Bridge.Bridge.reserved w)
  | .keyword k => .keyword k
  | .list items => .list items

/-- The specification's attribute value node. -/
def attributeValue : Content.AttributeValueNode Nat → Traversal.AttributeValueNode Recorded
  | .constant c => .constant (constant c)
  | .symbol s => .symbol (symbol s)
  | .list items => .list items

/-- The specification's signature. -/
def signature (sig : Content.Signature Nat) : Traversal.Signature Recorded :=
  ⟨symbol sig.symbol, pairs sig.parameters, sig.result⟩

/-- The specification's constructor. -/
def constructor (c : Content.Constructor Nat) : Traversal.Constructor Recorded :=
  ⟨symbol c.symbol, pairs c.selectors⟩

end ToSpec

/-- The recording handler, told contents only. -/
@[instance_reducible]
def recorderContent : ContentHandler (List Event) where
  Error := Unit
  SExpr := Nat
  Attribute := Nat
  «Sort» := Nat
  Term := Nat
  Scope := Nat
  setVersion v := recordingHandler.setVersion (Parser.Adapters.Bridge.Bridge.version v)
  handleSort i args := recordingCall (.handleSort (ToSpec.identifier i) args)
  handleTerm node := recordingCall (.handleTerm (ToSpec.termNode node))
  handleSExpr node := recordingCall (.handleSExpr (ToSpec.sExprNode node))
  handleAttribute k v := recordingCall (.handleAttribute k (v.map ToSpec.attributeValue))
  annotateTerm t attrs := recordingCall (.annotateTerm t attrs)
  startLet bs := recordingCall (.startLet (ToSpec.pairs bs))
  endLet s t := recordingCall (.endLet s t)
  startQuantifier q vs := recordingCall (.startQuantifier (ToSpec.quantifier q) (ToSpec.pairs vs))
  endQuantifier q s t := recordingCall (.endQuantifier (ToSpec.quantifier q) s t)
  startLambda vs := recordingCall (.startLambda (ToSpec.pairs vs))
  endLambda s t := recordingCall (.endLambda s t)
  startMatch t := recordingCall (.startMatch t)
  startMatchCase t p := recordingCall (.startMatchCase t (ToSpec.pattern p))
  endMatchCase s t b := recordingCall (.endMatchCase s t b)
  endMatch t cs := recordingCall (.endMatch t (cs.map fun (p, b) => (ToSpec.pattern p, b)))
  nonstandardCommand _ := ()
  commandAssert t := recordingCall (.commandAssert t)
  commandCheckSat := recordingCall .commandCheckSat
  commandCheckSatAssuming ts := recordingCall (.commandCheckSatAssuming ts)
  commandDeclareConst s t := recordingCall (.commandDeclareConst (ToSpec.symbol s) t)
  startDeclareDatatype s ps :=
    recordingCall (.startDeclareDatatype (ToSpec.symbol s) (ps.map ToSpec.symbol))
  endDeclareDatatype cs := recordingCall (.endDeclareDatatype (cs.map ToSpec.constructor))
  startDeclareDatatypes ss :=
    recordingCall (.startDeclareDatatypes (ss.map fun (s, n) => (ToSpec.symbol s, n)))
  startDatatypeDeclaration ps := recordingCall (.startDatatypeDeclaration (ps.map ToSpec.symbol))
  endDatatypeDeclaration cs := recordingCall (.endDatatypeDeclaration (cs.map ToSpec.constructor))
  endDeclareDatatypes := recordingCall .endDeclareDatatypes
  commandDeclareFun s ps r := recordingCall (.commandDeclareFun (ToSpec.symbol s) ps r)
  commandDeclareSort s n := recordingCall (.commandDeclareSort (ToSpec.symbol s) n)
  commandDeclareSortParameter s := recordingCall (.commandDeclareSortParameter (ToSpec.symbol s))
  commandDefineConst s t b := recordingCall (.commandDefineConst (ToSpec.symbol s) t b)
  startDefineFun sig := recordingCall (.startDefineFun (ToSpec.signature sig))
  endDefineFun b := recordingCall (.endDefineFun b)
  startDefineFunRec sig := recordingCall (.startDefineFunRec (ToSpec.signature sig))
  endDefineFunRec b := recordingCall (.endDefineFunRec b)
  startDefineFunsRec sigs := recordingCall (.startDefineFunsRec (sigs.map ToSpec.signature))
  startRecursiveBody sig := recordingCall (.startRecursiveBody (ToSpec.signature sig))
  endRecursiveBody b := recordingCall (.endRecursiveBody b)
  endDefineFunsRec := recordingCall .endDefineFunsRec
  startDefineSort s ps := recordingCall (.startDefineSort (ToSpec.symbol s) (ps.map ToSpec.symbol))
  endDefineSort t := recordingCall (.endDefineSort t)
  commandEcho c := recordingCall (.commandEcho c)
  commandExit := recordingCall .commandExit
  commandGetAssertions := recordingCall .commandGetAssertions
  commandGetAssignment := recordingCall .commandGetAssignment
  commandGetInfo k := recordingCall (.commandGetInfo k)
  commandGetModel := recordingCall .commandGetModel
  commandGetOption k := recordingCall (.commandGetOption k)
  commandGetProof := recordingCall .commandGetProof
  commandGetUnsatAssumptions := recordingCall .commandGetUnsatAssumptions
  commandGetUnsatCore := recordingCall .commandGetUnsatCore
  commandGetValue ts := recordingCall (.commandGetValue ts)
  commandPop n := recordingCall (.commandPop n)
  commandPush n := recordingCall (.commandPush n)
  commandReset := recordingCall .commandReset
  commandResetAssertions := recordingCall .commandResetAssertions
  commandSetInfo a := recordingCall (.commandSetInfo a)
  commandSetLogic s := recordingCall (.commandSetLogic (ToSpec.symbol s))
  commandSetOption a := recordingCall (.commandSetOption a)

/-! ## The contents turned into the specification's are the views turned into it -/

open BSmtLib.Facts.Parser.Adapters.Bridge (Bridge.symbol Bridge.index Bridge.identifier
    Bridge.constant Bridge.symbolOrWildcard Bridge.pattern Bridge.pairs)

theorem symbol_of (s : Lexicon.Value.Symbol) : ToSpec.symbol (Content.ofSymbol s) = Bridge.symbol s :=
  rfl

theorem index_of (i : Grammar.Nodes.Index) : ToSpec.index (Content.ofIndex i) = Bridge.index i := by
  cases i <;> rfl

theorem identifier_of (i : Grammar.Nodes.Ident) :
    ToSpec.identifier (Content.ofIdentifier i) = Bridge.identifier i := by
  simp [ToSpec.identifier, Content.ofIdentifier, Bridge.identifier, List.map_map,
    Function.comp_def, index_of, symbol_of]

theorem constant_of (c : Grammar.Nodes.SpecialConstant) :
    ToSpec.constant (Content.ofConstant c) = Bridge.constant c := by
  cases c <;> rfl

theorem symbolOrWildcard_of (s : Grammar.Nodes.SimplePattern) :
    ToSpec.symbolOrWildcard (Content.ofSymbolOrWildcard s) = Bridge.symbolOrWildcard s := by
  cases s <;> rfl

theorem pattern_of (p : Grammar.Nodes.Pattern) :
    ToSpec.pattern (Content.ofPattern p) = Bridge.pattern p := by
  cases p <;> simp [ToSpec.pattern, Content.ofPattern, Bridge.pattern, List.map_map,
    Function.comp_def, symbolOrWildcard_of, symbol_of]

theorem pairs_of {α : Type} (items : Array (Lexicon.Value.Symbol × α)) :
    ToSpec.pairs (Content.ofPairs items) = Bridge.pairs items := by
  simp [ToSpec.pairs, Content.ofPairs, Bridge.pairs, List.map_map, Function.comp_def, symbol_of]

theorem termNode_of (n : Grammar.Nodes.Term Nat Nat) :
    ToSpec.termNode (Content.ofTermNode n) = Parser.Adapters.Handler.termNodeOf
        (values := Recorded) n := by
  cases n <;> simp [ToSpec.termNode, Content.ofTermNode, Parser.Adapters.Handler.termNodeOf,
      identifier_of,
    constant_of]
  all_goals rfl

theorem sExprNode_of (n : Grammar.Nodes.SExpr Nat) :
    ToSpec.sExprNode (Content.ofSExprNode n) = Parser.Adapters.Handler.sExprNodeOf
        (values := Recorded) n := by
  cases n <;> simp [ToSpec.sExprNode, Content.ofSExprNode, Parser.Adapters.Handler.sExprNodeOf,
      constant_of]
  all_goals rfl

theorem attributeValue_of (n : Grammar.Nodes.AttributeValue Nat) :
    ToSpec.attributeValue (Content.ofAttributeValueNode n) =
      Parser.Adapters.Handler.attributeValueOf (values := Recorded) n := by
  cases n <;> simp [ToSpec.attributeValue, Content.ofAttributeValueNode,
    Parser.Adapters.Handler.attributeValueOf,
    constant_of]
  all_goals rfl

/-- As a library handler of terms, the content recorder is the recording handler. -/
theorem instHandler_eq :
    @ContentHandler.instHandler (List Event) recorderContent =
      Parser.Adapters.Handler.recordingLibraryTerms := by
  unfold ContentHandler.instHandler Parser.Adapters.Handler.recordingLibraryTerms recorderContent
  dsimp only
  congr 1 <;> funext
  all_goals try rfl
  all_goals try simp only [List.map_map, Function.comp_def, identifier_of, termNode_of,
    sExprNode_of, attributeValue_of, pattern_of, Option.map_map]
  all_goals try erw [pairs_of]
  all_goals try rfl
  all_goals (rename_i q _ _; cases q <;> rfl)


theorem signature_of (sig : Grammar.Multiple.FunctionSignature Nat) :
    ToSpec.signature (Content.ofSignature sig) =
      Parser.Adapters.Bridge.Bridge.signature (H := List Event) sig := by
  simp only [ToSpec.signature, Content.ofSignature, Parser.Adapters.Bridge.Bridge.signature]
  erw [pairs_of]
  rfl

theorem constructor_of (c : Lexicon.Value.Symbol × Grammar.Multiple.SortedVars Nat) :
    ToSpec.constructor (Content.ofConstructor c) =
      Parser.Adapters.Bridge.Bridge.constructor (H := List Event) c := by
  simp only [ToSpec.constructor, Content.ofConstructor, Parser.Adapters.Bridge.Bridge.constructor]
  erw [pairs_of]
  rfl

/-- As a library handler of commands, the content recorder is the recording handler. -/
theorem instCommandHandler_eq :
    @ContentHandler.instCommandHandler (List Event) recorderContent =
      Parser.Adapters.Handler.recordingLibrary := by
  unfold ContentHandler.instCommandHandler Parser.Adapters.Handler.recordingLibrary
  congr 1
  · exact instHandler_eq
  all_goals funext
  all_goals unfold recorderContent
  all_goals dsimp only
  all_goals try rfl
  all_goals try simp only [List.map_map, Function.comp_def, signature_of, constructor_of]
  all_goals try rfl
  all_goals erw [signature_of]

end BSmtLib.Facts.Proofs.PublicApi.Recorder
