module

public import BSmtLib.Parser.Adapter
public import BSmtLib.Parser.Script
public import BSmtLibSpec.Parser
public import BSmtLibSpec.Grammar.Properties

@[expose] public section

/-!
# From the parser's values to the spec's

The parser hands over views of bytes and arrays; the spec's traversal hands over characters and
lists. The functions here turn the one into the other, and `Agrees` says that a handler of the
library (an instance of `Parser.CommandHandler`) answers each call as a handler of the spec
answers the same call with the values turned into the spec's: the link between the library's
handler class and the spec's handler structure. The theorems about the parser are stated for
such a pair, so they hold for every library handler that sees in a view only its bytes.

`Bridge.received` is what a token as the parser takes it stands for in the spec.

These definitions are adapters: the root theorems of `BSmtLib.Facts.Parser` and
`BSmtLib.Facts.Reader` are stated with them, so they are trusted, and are to be read with the spec.
-/

open BSmtLib.Lexicon.Value

namespace BSmtLib.Facts.Parser.Adapters.Bridge

open BSmtLibSpec.Regex (Chars)
open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal

namespace Bridge

/-- The characters of the bytes. -/
def chars (bytes : ByteSlice) : Chars := bytes.toByteArray.toList

/-- The spec's symbol for a symbol of the parser: its characters, quoted or not. -/
def symbol (s : Symbol) : Tree.Symbol := ⟨chars s.asSlice, s.isQuoted⟩

/-- The spec's index for an index of the parser. -/
def index : Grammar.Nodes.Index → Tree.Index
  | .numeral digits => .numeral (chars digits.asSlice)
  | .symbol s => .symbol (symbol s)

/-- The spec's identifier for an identifier of the parser: its symbol and its indices. -/
def identifier (i : Grammar.Nodes.Ident) : Tree.Identifier :=
  ⟨symbol i.name, i.indices.toList.map index⟩

/-- The spec's constant for a constant of the parser, of the same kind and characters. -/
def constant : Grammar.Nodes.SpecialConstant → Tree.SpecConstant
  | .numeral d => .numeral (chars d.asSlice)
  | .decimal d => .decimal (chars d.asSlice)
  | .hexadecimal d => .hexadecimal (chars d.asSlice)
  | .binary d => .binary (chars d.asSlice)
  | .string c => .string (chars c.asSlice)

/-- The characters of a keyword. -/
def keyword (k : Keyword) : Chars := chars k.asSlice

/-- The characters the spec spells a reserved word with. -/
def reserved (w : Token.Reserved) : Chars := BSmtLibSpec.Regex.chars w.asStr

/-- The spec's symbol or wildcard for the parser's. -/
def symbolOrWildcard : Grammar.Nodes.SimplePattern → Tree.SymbolOrWildcard
  | .symbol s => .symbol (symbol s)
  | .wildcard => .wildcard

/-- The spec's pattern for a pattern of the parser. -/
def pattern : Grammar.Nodes.Pattern → Tree.Pattern
  | .simple s => .single (symbolOrWildcard s)
  | .application ⟨c, args, _⟩ => .constructor (symbol c) (args.toList.map symbolOrWildcard)

/-- The spec's quantifier for a quantifier of the parser. -/
def quantifier : Grammar.Nodes.QuantifierKind → Tree.Quantifier
  | .forall => .forall
  | .exists => .exists

/-- The spec's version for a version of the library. -/
def version : Version → BSmtLibSpec.Lexicon.Version
  | .v2_0 => .v2_0
  | .v2_5 => .v2_5
  | .v2_6 => .v2_6
  | .v2_7 => .v2_7

/-- The pairs with their symbols turned into the spec's, as a list. -/
def pairs {α : Type} (items : Array (Symbol × α)) : List (Tree.Symbol × α) :=
  items.toList.map fun (s, a) => (symbol s, a)

/-- What a token as the parser takes it stands for in the spec: none for whitespace and
comments, which the spec has no place for. -/
def received : Parser.Internal.Input → Option Received
  | .parenOpen => some (.token .parenOpen)
  | .parenClose => some (.token .parenClose)
  | .constant c => some (.token (constant c).token)
  | .symbol s => some (.token (.symbol (symbol s)))
  | .keyword k => some (.token (.keyword (keyword k)))
  | .reserved w => some (.token (.reserved (reserved w)))
  | .endOfInput => some .endOfInput
  | .layout => none

end Bridge

/-- The parser's tokens stand for the spec's tokens, one by one. -/
def Stands (inputs : List Parser.Internal.Input)
    (tokens : List BSmtLibSpec.Grammar.SyntaxToken) : Prop :=
  inputs.map Bridge.received = tokens.map fun token => some (.token token)

section

variable {H : Type} {m : Type → Type} [Handler H m]

/-- The values of the spec's traversal that a library handler's types make. -/
abbrev valuesOf (H : Type) {m : Type → Type} [Handler H m] : Values :=
  ⟨Handler.SExpr H, Handler.Attribute H, Handler.«Sort» H,
    Handler.Term H, Handler.Scope H⟩

namespace Bridge

/-- The spec's term node for a term node of the parser, with the handler's values. -/
def termNode : Grammar.Nodes.Term (Handler.«Sort» H) (Handler.Term H) →
    TermNode (valuesOf H)
  | .specialConstant c => .constant (constant c)
  | .qualifiedIdent i s => .identifier (identifier i) s
  | .application i s args _ => .application (identifier i) s args.asSlice.toList

/-- The spec's S-expression node for one of the parser, with the handler's values. -/
def sExprNode : Grammar.Nodes.SExpr (Handler.SExpr H) → SExprNode (valuesOf H)
  | .specialConstant c => .constant (constant c)
  | .symbol s => .symbol (symbol s)
  | .reserved w => .reserved (reserved w)
  | .keyword k => .keyword (keyword k)
  | .sExprs items => .list items.asSlice.toList

/-- The spec's attribute value node for one of the parser, with the handler's values. -/
def attributeValue : Grammar.Nodes.AttributeValue (Handler.SExpr H) →
    AttributeValueNode (valuesOf H)
  | .specialConstant c => .constant (constant c)
  | .symbol s => .symbol (symbol s)
  | .sExprs items => .list items.asSlice.toList

/-- The spec's signature for a signature of the parser, with the handler's sorts. -/
def signature (sig : Grammar.Multiple.FunctionSignature (Handler.«Sort» H)) :
    Signature (valuesOf H) :=
  ⟨symbol sig.name, pairs sig.params, sig.resultSort⟩

/-- The spec's constructor for a constructor of the parser, with the handler's sorts. -/
def constructor (c : Lexicon.Value.Symbol × Grammar.Multiple.SortedVars (Handler.«Sort» H)) :
    Constructor (valuesOf H) :=
  ⟨symbol c.1, pairs c.2.toArray⟩


/-! The spec handler's answers, with the types of the library handler's values. -/

/-- The answer of the spec's handler `h` to a call that returns a sort. -/
def callSort (h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H))
    (request : Call (valuesOf H) .sort) :
    ExceptT (Handler.Error H) (StateT H m) (Handler.«Sort» H) :=
  h.call request

/-- The answer of the spec's handler `h` to a call that returns an S-expression. -/
def callSExpr (h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H))
    (request : Call (valuesOf H) .sExpr) :
    ExceptT (Handler.Error H) (StateT H m) (Handler.SExpr H) :=
  h.call request

/-- The answer of the spec's handler `h` to a call that returns an attribute. -/
def callAttribute (h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H))
    (request : Call (valuesOf H) .attribute) :
    ExceptT (Handler.Error H) (StateT H m) (Handler.Attribute H) :=
  h.call request

/-- The answer of the spec's handler `h` to a call that returns a term. -/
def callTerm (h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H))
    (request : Call (valuesOf H) .term) :
    ExceptT (Handler.Error H) (StateT H m) (Handler.Term H) :=
  h.call request

/-- The answer of the spec's handler `h` to a call that returns a scope. -/
def callScope (h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H))
    (request : Call (valuesOf H) .scope) :
    ExceptT (Handler.Error H) (StateT H m) (Handler.Scope H) :=
  h.call request

/-- The answer of the spec's handler `h` to a call that returns nothing. -/
def callUnit (h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H))
    (request : Call (valuesOf H) .nothing) :
    ExceptT (Handler.Error H) (StateT H m) Unit :=
  h.call request

end Bridge

/--
The library handler answers each call of terms as the spec's handler `h` answers the call with
the values turned into the spec's.
-/
structure TermAgrees (h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H)) :
    Prop where
  handleSort : ∀ i args, Handler.handleSort (H := H) i args =
    Bridge.callSort h (.handleSort (Bridge.identifier i) args.asSlice.toList)
  handleTerm : ∀ node, Handler.handleTerm (H := H) node =
    Bridge.callTerm h (.handleTerm (Bridge.termNode node))
  handleSExpr : ∀ node, Handler.handleSExpr (H := H) node =
    Bridge.callSExpr h (.handleSExpr (Bridge.sExprNode node))
  handleAttribute : ∀ k v, Handler.handleAttribute (H := H) k v =
    Bridge.callAttribute h (.handleAttribute (Bridge.keyword k) (v.map Bridge.attributeValue))
  annotateTerm : ∀ t attrs, Handler.annotateTerm (H := H) t attrs =
    Bridge.callTerm h (.annotateTerm t attrs.asSlice.toList)
  startLet : ∀ bs, Handler.startLet (H := H) bs =
    Bridge.callScope h (.startLet (Bridge.pairs bs.toArray))
  endLet : ∀ s t, Handler.endLet (H := H) s t = Bridge.callTerm h (.endLet s t)
  startQuantifier : ∀ q vs, Handler.startQuantifier (H := H) q vs =
    Bridge.callScope h (.startQuantifier (Bridge.quantifier q) (Bridge.pairs vs.toArray))
  endQuantifier : ∀ q s t, Handler.endQuantifier (H := H) q s t =
    Bridge.callTerm h (.endQuantifier (Bridge.quantifier q) s t)
  startLambda : ∀ vs, Handler.startLambda (H := H) vs =
    Bridge.callScope h (.startLambda (Bridge.pairs vs.toArray))
  endLambda : ∀ s t, Handler.endLambda (H := H) s t = Bridge.callTerm h (.endLambda s t)
  startMatch : ∀ t, Handler.startMatch (H := H) t = Bridge.callUnit h (.startMatch t)
  startMatchCase : ∀ t p, Handler.startMatchCase (H := H) t p =
    Bridge.callScope h (.startMatchCase t (Bridge.pattern p))
  endMatchCase : ∀ s t b, Handler.endMatchCase (H := H) s t b =
    Bridge.callTerm h (.endMatchCase s t b)
  endMatch : ∀ t cs, Handler.endMatch (H := H) t cs =
    Bridge.callTerm h (.endMatch t (cs.toArray.toList.map fun (p, b) => (Bridge.pattern p, b)))
  setVersion : ∀ v, Handler.setVersion (H := H) v = h.setVersion (Bridge.version v)

end

section

variable {H : Type} {m : Type → Type} [Handler.CommandHandler H m]

/--
The library handler answers each call as the spec's handler `h` answers the call with the
values turned into the spec's.
-/
structure Agrees (h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H)) : Prop
    extends TermAgrees h where
  commandAssert : ∀ t, Handler.CommandHandler.commandAssert (H := H) t =
    Bridge.callUnit h (.commandAssert t)
  commandCheckSat : Handler.CommandHandler.commandCheckSat (H := H) =
    Bridge.callUnit h .commandCheckSat
  commandCheckSatAssuming : ∀ ts, Handler.CommandHandler.commandCheckSatAssuming (H := H) ts =
    Bridge.callUnit h (.commandCheckSatAssuming ts.asSlice.toList)
  commandDeclareConst : ∀ s t, Handler.CommandHandler.commandDeclareConst (H := H) s t =
    Bridge.callUnit h (.commandDeclareConst (Bridge.symbol s) t)
  startDeclareDatatype : ∀ s ps, Handler.CommandHandler.startDeclareDatatype (H := H) s ps =
    Bridge.callUnit h
      (.startDeclareDatatype (Bridge.symbol s) (ps.toArray.toList.map Bridge.symbol))
  endDeclareDatatype : ∀ cs, Handler.CommandHandler.endDeclareDatatype (H := H) cs =
    Bridge.callUnit h (.endDeclareDatatype (cs.toArray.toList.map Bridge.constructor))
  startDeclareDatatypes : ∀ ss, Handler.CommandHandler.startDeclareDatatypes (H := H) ss =
    Bridge.callUnit h (.startDeclareDatatypes
      (ss.toArray.toList.map fun (s, n) => (Bridge.symbol s, Bridge.chars n.asSlice)))
  startDatatypeDeclaration : ∀ ps,
    Handler.CommandHandler.startDatatypeDeclaration (H := H) ps =
      Bridge.callUnit h (.startDatatypeDeclaration (ps.toArray.toList.map Bridge.symbol))
  endDatatypeDeclaration : ∀ cs, Handler.CommandHandler.endDatatypeDeclaration (H := H) cs =
    Bridge.callUnit h (.endDatatypeDeclaration (cs.toArray.toList.map Bridge.constructor))
  endDeclareDatatypes : Handler.CommandHandler.endDeclareDatatypes (H := H) =
    Bridge.callUnit h .endDeclareDatatypes
  commandDeclareFun : ∀ s ps r, Handler.CommandHandler.commandDeclareFun (H := H) s ps r =
    Bridge.callUnit h (.commandDeclareFun (Bridge.symbol s) ps.asSlice.toList r)
  commandDeclareSort : ∀ s n, Handler.CommandHandler.commandDeclareSort (H := H) s n =
    Bridge.callUnit h (.commandDeclareSort (Bridge.symbol s) (Bridge.chars n.asSlice))
  commandDeclareSortParameter : ∀ s,
    Handler.CommandHandler.commandDeclareSortParameter (H := H) s =
      Bridge.callUnit h (.commandDeclareSortParameter (Bridge.symbol s))
  commandDefineConst : ∀ s t b, Handler.CommandHandler.commandDefineConst (H := H) s t b =
    Bridge.callUnit h (.commandDefineConst (Bridge.symbol s) t b)
  startDefineFun : ∀ sig, Handler.CommandHandler.startDefineFun (H := H) sig =
    Bridge.callUnit h (.startDefineFun (Bridge.signature sig))
  endDefineFun : ∀ b, Handler.CommandHandler.endDefineFun (H := H) b =
    Bridge.callUnit h (.endDefineFun b)
  startDefineFunRec : ∀ sig, Handler.CommandHandler.startDefineFunRec (H := H) sig =
    Bridge.callUnit h (.startDefineFunRec (Bridge.signature sig))
  endDefineFunRec : ∀ b, Handler.CommandHandler.endDefineFunRec (H := H) b =
    Bridge.callUnit h (.endDefineFunRec b)
  startDefineFunsRec : ∀ sigs, Handler.CommandHandler.startDefineFunsRec (H := H) sigs =
    Bridge.callUnit h (.startDefineFunsRec (sigs.toArray.toList.map Bridge.signature))
  startRecursiveBody : ∀ sig, Handler.CommandHandler.startRecursiveBody (H := H) sig =
    Bridge.callUnit h (.startRecursiveBody (Bridge.signature sig))
  endRecursiveBody : ∀ b, Handler.CommandHandler.endRecursiveBody (H := H) b =
    Bridge.callUnit h (.endRecursiveBody b)
  endDefineFunsRec : Handler.CommandHandler.endDefineFunsRec (H := H) =
    Bridge.callUnit h .endDefineFunsRec
  startDefineSort : ∀ s ps, Handler.CommandHandler.startDefineSort (H := H) s ps =
    Bridge.callUnit h (.startDefineSort (Bridge.symbol s) (ps.toArray.toList.map Bridge.symbol))
  endDefineSort : ∀ t, Handler.CommandHandler.endDefineSort (H := H) t =
    Bridge.callUnit h (.endDefineSort t)
  commandEcho : ∀ c, Handler.CommandHandler.commandEcho (H := H) c =
    Bridge.callUnit h (.commandEcho (Bridge.chars c.asSlice))
  commandExit : Handler.CommandHandler.commandExit (H := H) = Bridge.callUnit h .commandExit
  commandGetAssertions : Handler.CommandHandler.commandGetAssertions (H := H) =
    Bridge.callUnit h .commandGetAssertions
  commandGetAssignment : Handler.CommandHandler.commandGetAssignment (H := H) =
    Bridge.callUnit h .commandGetAssignment
  commandGetInfo : ∀ k, Handler.CommandHandler.commandGetInfo (H := H) k =
    Bridge.callUnit h (.commandGetInfo (Bridge.keyword k))
  commandGetModel : Handler.CommandHandler.commandGetModel (H := H) =
    Bridge.callUnit h .commandGetModel
  commandGetOption : ∀ k, Handler.CommandHandler.commandGetOption (H := H) k =
    Bridge.callUnit h (.commandGetOption (Bridge.keyword k))
  commandGetProof : Handler.CommandHandler.commandGetProof (H := H) =
    Bridge.callUnit h .commandGetProof
  commandGetUnsatAssumptions : Handler.CommandHandler.commandGetUnsatAssumptions (H := H) =
    Bridge.callUnit h .commandGetUnsatAssumptions
  commandGetUnsatCore : Handler.CommandHandler.commandGetUnsatCore (H := H) =
    Bridge.callUnit h .commandGetUnsatCore
  commandGetValue : ∀ ts, Handler.CommandHandler.commandGetValue (H := H) ts =
    Bridge.callUnit h (.commandGetValue ts.asSlice.toList)
  commandPop : ∀ n, Handler.CommandHandler.commandPop (H := H) n =
    Bridge.callUnit h (.commandPop (Bridge.chars n.asSlice))
  commandPush : ∀ n, Handler.CommandHandler.commandPush (H := H) n =
    Bridge.callUnit h (.commandPush (Bridge.chars n.asSlice))
  commandReset : Handler.CommandHandler.commandReset (H := H) = Bridge.callUnit h .commandReset
  commandResetAssertions : Handler.CommandHandler.commandResetAssertions (H := H) =
    Bridge.callUnit h .commandResetAssertions
  commandSetInfo : ∀ a, Handler.CommandHandler.commandSetInfo (H := H) a =
    Bridge.callUnit h (.commandSetInfo a)
  commandSetLogic : ∀ s, Handler.CommandHandler.commandSetLogic (H := H) s =
    Bridge.callUnit h (.commandSetLogic (Bridge.symbol s))
  commandSetOption : ∀ a, Handler.CommandHandler.commandSetOption (H := H) a =
    Bridge.callUnit h (.commandSetOption a)

end

/--
A failure of the traversal as a failure of the parser: a rejected version declaration is the
version error of the same kind.
-/
def causeOf {ε : Type} : Cause ε → Parser.ParseErrorCause ε
  | .syntax .unsupportedVersion => .version .unsupported
  | .syntax (.tooManyDeclarations limit) => .version (.tooManyDeclarations limit)
  | .handler error => .handler error


namespace Bridge

/-- The library's version for a version of the spec. -/
def libVersion : BSmtLibSpec.Lexicon.Version → Version
  | .v2_0 => .v2_0
  | .v2_5 => .v2_5
  | .v2_6 => .v2_6
  | .v2_7 => .v2_7

end Bridge

/-- The spec's policy that a posture of the parser stands for. -/
def policyOf (posture : Version.VersionPosture) : VersionPolicy :=
  { allowed := posture.allowed.toList.map Bridge.version,
    maxDeclarations := posture.maxDeclarations }

/-- How the command parser ends a command of the spec. -/
def outcomeOf (command : Tree.Command) : Parser.Command.CommandOutcome :=
  match command with
  | .exit => .exit
  | command =>
    match command.declaredVersion with
    | some version => .setVersion (Bridge.libVersion version)
    | none => .command

/-- No item is whitespace or a comment, which a parser is never handed. -/
def NoLayout (items : List Parser.Internal.Input) : Prop := ∀ token ∈ items,
    Bridge.received token ≠ none

/-- Every reserved word. -/
def allReserved : List Token.Reserved :=
  Token.Reserved.GeneralReserved.all.toList.map .general ++
      Token.Reserved.CommandNameReserved.all.toList.map .commandName

/-- The reserved word the spec spells with the characters, if there is one. -/
def decodeReserved (c : BSmtLibSpec.Regex.Chars) : Option Token.Reserved :=
  allReserved.find? fun r => decide (Bridge.reserved r = c)

namespace Rejection

/-- What a token stands for, as the parsers take it. -/
def rcv (token : Parser.Internal.Input) : Received := (Bridge.received token).getD .endOfInput

/-- A view of the characters. -/
def bytesOf (c : BSmtLibSpec.Regex.Chars) : ByteSlice := (ByteArray.mk c.toArray).toByteSlice

end Rejection

end BSmtLib.Facts.Parser.Adapters.Bridge
