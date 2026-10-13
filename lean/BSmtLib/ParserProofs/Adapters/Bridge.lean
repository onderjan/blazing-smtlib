import BSmtLib.Parser
import BSmtLib.Spec.Parser

/-!
# From the parser's values to the spec's

The parser hands over views of bytes and arrays; the spec's traversal hands over characters and
lists. The functions here turn the one into the other, and `Agrees` says that a handler of the
library (an instance of `Parser.CommandHandler`) answers each call as a handler of the spec
answers the same call with the values turned into the spec's: the link between the library's
handler class and the spec's handler structure. The theorems about the parser are stated for
such a pair, so they hold for every library handler that sees in a view only its bytes.

`Bridge.received` is what a token as the parser takes it stands for in the spec.

These definitions are adapters: the root theorems of `BSmtLib.ParserProofs` and
`BSmtLib.EndToEnd` are stated with them, so they are trusted, and are to be read with the spec.
-/

namespace BSmtLib.ParserProofs

open BSmtLib.Spec.Lexicon (Chars)
open BSmtLib.Spec.Grammar
open BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal

namespace Bridge

/-- The characters of the bytes. -/
def chars (bytes : ByteSlice) : Chars := bytes.toByteArray.toList

/-- The spec's symbol for a symbol of the parser: its characters, quoted or not. -/
def symbol (s : Parser.Symbol) : Tree.Symbol := ⟨chars s.content.asSlice, s.quoted⟩

/-- The spec's index for an index of the parser. -/
def index : Parser.Index → Tree.Index
  | .numeral digits => .numeral (chars digits.asSlice)
  | .symbol s => .symbol (symbol s)

/-- The spec's identifier for an identifier of the parser: its symbol and its indices. -/
def identifier (i : Parser.Identifier) : Tree.Identifier :=
  ⟨symbol i.symbol, i.indices.toList.map index⟩

/-- The spec's constant for a constant of the parser, of the same kind and characters. -/
def constant : Parser.SpecConstant → Tree.SpecConstant
  | .numeral d => .numeral (chars d.asSlice)
  | .decimal d => .decimal (chars d.asSlice)
  | .hexadecimal d => .hexadecimal (chars d.asSlice)
  | .binary d => .binary (chars d.asSlice)
  | .string c => .string (chars c.asSlice)

/-- The characters of a keyword. -/
def keyword (k : KeywordView) : Chars := chars k.asSlice

/-- The characters the spec spells a reserved word with. -/
def reserved (w : Reserved) : Chars := Spec.Lexicon.chars w.asStr

/-- The spec's symbol or wildcard for the parser's. -/
def symbolOrWildcard : Parser.SymbolOrWildcard → Tree.SymbolOrWildcard
  | .symbol s => .symbol (symbol s)
  | .wildcard => .wildcard

/-- The spec's pattern for a pattern of the parser. -/
def pattern : Parser.Pattern → Tree.Pattern
  | .single s => .single (symbolOrWildcard s)
  | .constructor c args => .constructor (symbol c) (args.toList.map symbolOrWildcard)

/-- The spec's quantifier for a quantifier of the parser. -/
def quantifier : Parser.Quantifier → Tree.Quantifier
  | .forall => .forall
  | .exists => .exists

/-- The spec's version for a version of the library. -/
def version : BSmtLib.Version → Spec.Lexicon.Version
  | .v2_0 => .v2_0
  | .v2_5 => .v2_5
  | .v2_6 => .v2_6
  | .v2_7 => .v2_7

/-- The pairs with their symbols turned into the spec's, as a list. -/
def pairs {α : Type} (items : Array (Parser.Symbol × α)) : List (Tree.Symbol × α) :=
  items.toList.map fun (s, a) => (symbol s, a)

/-- What a token as the parser takes it stands for in the spec: none for whitespace and
comments, which the spec has no place for. -/
def received : Parser.Input → Option Received
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
def Stands (inputs : List Parser.Input) (tokens : List Spec.Grammar.SyntaxToken) : Prop :=
  inputs.map Bridge.received = tokens.map fun token => some (.token token)

section

variable {H : Type} {m : Type → Type} [Parser.Handler H m]

/-- The values of the spec's traversal that a library handler's types make. -/
abbrev valuesOf (H : Type) {m : Type → Type} [Parser.Handler H m] : Values :=
  ⟨Parser.Handler.SExpr H, Parser.Handler.Attribute H, Parser.Handler.«Sort» H,
    Parser.Handler.Term H, Parser.Handler.Scope H⟩

namespace Bridge

/-- The spec's term node for a term node of the parser, with the handler's values. -/
def termNode : Parser.TermNode (Parser.Handler.«Sort» H) (Parser.Handler.Term H) →
    TermNode (valuesOf H)
  | .constant c => .constant (constant c)
  | .identifier i s => .identifier (identifier i) s
  | .application i s args => .application (identifier i) s args.toList

/-- The spec's S-expression node for one of the parser, with the handler's values. -/
def sExprNode : Parser.SExprNode (Parser.Handler.SExpr H) → SExprNode (valuesOf H)
  | .constant c => .constant (constant c)
  | .symbol s => .symbol (symbol s)
  | .reserved w => .reserved (reserved w)
  | .keyword k => .keyword (keyword k)
  | .list items => .list items.toList

/-- The spec's attribute value node for one of the parser, with the handler's values. -/
def attributeValue : Parser.AttributeValueNode (Parser.Handler.SExpr H) →
    AttributeValueNode (valuesOf H)
  | .constant c => .constant (constant c)
  | .symbol s => .symbol (symbol s)
  | .list items => .list items.toList

/-- The spec's signature for a signature of the parser, with the handler's sorts. -/
def signature (sig : Parser.Signature (Parser.Handler.«Sort» H)) : Signature (valuesOf H) :=
  ⟨symbol sig.symbol, pairs sig.parameters, sig.result⟩

/-- The spec's constructor for a constructor of the parser, with the handler's sorts. -/
def constructor (c : Parser.Constructor (Parser.Handler.«Sort» H)) : Constructor (valuesOf H) :=
  ⟨symbol c.symbol, pairs c.selectors⟩


/-! The spec handler's answers, with the types of the library handler's values. -/

/-- The answer of the spec's handler `h` to a call that returns a sort. -/
def callSort (h : Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H))
    (request : Call (valuesOf H) .sort) :
    ExceptT (Parser.Handler.Error H) (StateT H m) (Parser.Handler.«Sort» H) :=
  h.call request

/-- The answer of the spec's handler `h` to a call that returns an S-expression. -/
def callSExpr (h : Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H))
    (request : Call (valuesOf H) .sExpr) :
    ExceptT (Parser.Handler.Error H) (StateT H m) (Parser.Handler.SExpr H) :=
  h.call request

/-- The answer of the spec's handler `h` to a call that returns an attribute. -/
def callAttribute (h : Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H))
    (request : Call (valuesOf H) .attribute) :
    ExceptT (Parser.Handler.Error H) (StateT H m) (Parser.Handler.Attribute H) :=
  h.call request

/-- The answer of the spec's handler `h` to a call that returns a term. -/
def callTerm (h : Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H))
    (request : Call (valuesOf H) .term) :
    ExceptT (Parser.Handler.Error H) (StateT H m) (Parser.Handler.Term H) :=
  h.call request

/-- The answer of the spec's handler `h` to a call that returns a scope. -/
def callScope (h : Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H))
    (request : Call (valuesOf H) .scope) :
    ExceptT (Parser.Handler.Error H) (StateT H m) (Parser.Handler.Scope H) :=
  h.call request

/-- The answer of the spec's handler `h` to a call that returns nothing. -/
def callUnit (h : Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H))
    (request : Call (valuesOf H) .nothing) :
    ExceptT (Parser.Handler.Error H) (StateT H m) Unit :=
  h.call request

end Bridge

/--
The library handler answers each call of terms as the spec's handler `h` answers the call with
the values turned into the spec's.
-/
structure TermAgrees (h : Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H)) : Prop where
  handleSort : ∀ i args, Parser.Handler.handleSort (H := H) i args =
    Bridge.callSort h (.handleSort (Bridge.identifier i) args.toList)
  handleTerm : ∀ node, Parser.Handler.handleTerm (H := H) node =
    Bridge.callTerm h (.handleTerm (Bridge.termNode node))
  handleSExpr : ∀ node, Parser.Handler.handleSExpr (H := H) node =
    Bridge.callSExpr h (.handleSExpr (Bridge.sExprNode node))
  handleAttribute : ∀ k v, Parser.Handler.handleAttribute (H := H) k v =
    Bridge.callAttribute h (.handleAttribute (Bridge.keyword k) (v.map Bridge.attributeValue))
  annotateTerm : ∀ t attrs, Parser.Handler.annotateTerm (H := H) t attrs =
    Bridge.callTerm h (.annotateTerm t attrs.toList)
  startLet : ∀ bs, Parser.Handler.startLet (H := H) bs =
    Bridge.callScope h (.startLet (Bridge.pairs bs))
  endLet : ∀ s t, Parser.Handler.endLet (H := H) s t = Bridge.callTerm h (.endLet s t)
  startQuantifier : ∀ q vs, Parser.Handler.startQuantifier (H := H) q vs =
    Bridge.callScope h (.startQuantifier (Bridge.quantifier q) (Bridge.pairs vs))
  endQuantifier : ∀ q s t, Parser.Handler.endQuantifier (H := H) q s t =
    Bridge.callTerm h (.endQuantifier (Bridge.quantifier q) s t)
  startLambda : ∀ vs, Parser.Handler.startLambda (H := H) vs =
    Bridge.callScope h (.startLambda (Bridge.pairs vs))
  endLambda : ∀ s t, Parser.Handler.endLambda (H := H) s t = Bridge.callTerm h (.endLambda s t)
  startMatch : ∀ t, Parser.Handler.startMatch (H := H) t = Bridge.callUnit h (.startMatch t)
  startMatchCase : ∀ t p, Parser.Handler.startMatchCase (H := H) t p =
    Bridge.callScope h (.startMatchCase t (Bridge.pattern p))
  endMatchCase : ∀ s t b, Parser.Handler.endMatchCase (H := H) s t b =
    Bridge.callTerm h (.endMatchCase s t b)
  endMatch : ∀ t cs, Parser.Handler.endMatch (H := H) t cs =
    Bridge.callTerm h (.endMatch t (cs.toList.map fun (p, b) => (Bridge.pattern p, b)))
  setVersion : ∀ v, Parser.Handler.setVersion (H := H) v = h.setVersion (Bridge.version v)

end

section

variable {H : Type} {m : Type → Type} [Parser.CommandHandler H m]

/--
The library handler answers each call as the spec's handler `h` answers the call with the
values turned into the spec's.
-/
structure Agrees (h : Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H)) : Prop
    extends TermAgrees h where
  commandAssert : ∀ t, Parser.CommandHandler.commandAssert (H := H) t =
    Bridge.callUnit h (.commandAssert t)
  commandCheckSat : Parser.CommandHandler.commandCheckSat (H := H) =
    Bridge.callUnit h .commandCheckSat
  commandCheckSatAssuming : ∀ ts, Parser.CommandHandler.commandCheckSatAssuming (H := H) ts =
    Bridge.callUnit h (.commandCheckSatAssuming ts.toList)
  commandDeclareConst : ∀ s t, Parser.CommandHandler.commandDeclareConst (H := H) s t =
    Bridge.callUnit h (.commandDeclareConst (Bridge.symbol s) t)
  startDeclareDatatype : ∀ s ps, Parser.CommandHandler.startDeclareDatatype (H := H) s ps =
    Bridge.callUnit h (.startDeclareDatatype (Bridge.symbol s) (ps.toList.map Bridge.symbol))
  endDeclareDatatype : ∀ cs, Parser.CommandHandler.endDeclareDatatype (H := H) cs =
    Bridge.callUnit h (.endDeclareDatatype (cs.toList.map Bridge.constructor))
  startDeclareDatatypes : ∀ ss, Parser.CommandHandler.startDeclareDatatypes (H := H) ss =
    Bridge.callUnit h (.startDeclareDatatypes
      (ss.toList.map fun (s, n) => (Bridge.symbol s, Bridge.chars n.asSlice)))
  startDatatypeDeclaration : ∀ ps,
    Parser.CommandHandler.startDatatypeDeclaration (H := H) ps =
      Bridge.callUnit h (.startDatatypeDeclaration (ps.toList.map Bridge.symbol))
  endDatatypeDeclaration : ∀ cs, Parser.CommandHandler.endDatatypeDeclaration (H := H) cs =
    Bridge.callUnit h (.endDatatypeDeclaration (cs.toList.map Bridge.constructor))
  endDeclareDatatypes : Parser.CommandHandler.endDeclareDatatypes (H := H) =
    Bridge.callUnit h .endDeclareDatatypes
  commandDeclareFun : ∀ s ps r, Parser.CommandHandler.commandDeclareFun (H := H) s ps r =
    Bridge.callUnit h (.commandDeclareFun (Bridge.symbol s) ps.toList r)
  commandDeclareSort : ∀ s n, Parser.CommandHandler.commandDeclareSort (H := H) s n =
    Bridge.callUnit h (.commandDeclareSort (Bridge.symbol s) (Bridge.chars n.asSlice))
  commandDeclareSortParameter : ∀ s,
    Parser.CommandHandler.commandDeclareSortParameter (H := H) s =
      Bridge.callUnit h (.commandDeclareSortParameter (Bridge.symbol s))
  commandDefineConst : ∀ s t b, Parser.CommandHandler.commandDefineConst (H := H) s t b =
    Bridge.callUnit h (.commandDefineConst (Bridge.symbol s) t b)
  startDefineFun : ∀ sig, Parser.CommandHandler.startDefineFun (H := H) sig =
    Bridge.callUnit h (.startDefineFun (Bridge.signature sig))
  endDefineFun : ∀ b, Parser.CommandHandler.endDefineFun (H := H) b =
    Bridge.callUnit h (.endDefineFun b)
  startDefineFunRec : ∀ sig, Parser.CommandHandler.startDefineFunRec (H := H) sig =
    Bridge.callUnit h (.startDefineFunRec (Bridge.signature sig))
  endDefineFunRec : ∀ b, Parser.CommandHandler.endDefineFunRec (H := H) b =
    Bridge.callUnit h (.endDefineFunRec b)
  startDefineFunsRec : ∀ sigs, Parser.CommandHandler.startDefineFunsRec (H := H) sigs =
    Bridge.callUnit h (.startDefineFunsRec (sigs.toList.map Bridge.signature))
  startRecursiveBody : ∀ sig, Parser.CommandHandler.startRecursiveBody (H := H) sig =
    Bridge.callUnit h (.startRecursiveBody (Bridge.signature sig))
  endRecursiveBody : ∀ b, Parser.CommandHandler.endRecursiveBody (H := H) b =
    Bridge.callUnit h (.endRecursiveBody b)
  endDefineFunsRec : Parser.CommandHandler.endDefineFunsRec (H := H) =
    Bridge.callUnit h .endDefineFunsRec
  startDefineSort : ∀ s ps, Parser.CommandHandler.startDefineSort (H := H) s ps =
    Bridge.callUnit h (.startDefineSort (Bridge.symbol s) (ps.toList.map Bridge.symbol))
  endDefineSort : ∀ t, Parser.CommandHandler.endDefineSort (H := H) t =
    Bridge.callUnit h (.endDefineSort t)
  commandEcho : ∀ c, Parser.CommandHandler.commandEcho (H := H) c =
    Bridge.callUnit h (.commandEcho (Bridge.chars c.asSlice))
  commandExit : Parser.CommandHandler.commandExit (H := H) = Bridge.callUnit h .commandExit
  commandGetAssertions : Parser.CommandHandler.commandGetAssertions (H := H) =
    Bridge.callUnit h .commandGetAssertions
  commandGetAssignment : Parser.CommandHandler.commandGetAssignment (H := H) =
    Bridge.callUnit h .commandGetAssignment
  commandGetInfo : ∀ k, Parser.CommandHandler.commandGetInfo (H := H) k =
    Bridge.callUnit h (.commandGetInfo (Bridge.keyword k))
  commandGetModel : Parser.CommandHandler.commandGetModel (H := H) =
    Bridge.callUnit h .commandGetModel
  commandGetOption : ∀ k, Parser.CommandHandler.commandGetOption (H := H) k =
    Bridge.callUnit h (.commandGetOption (Bridge.keyword k))
  commandGetProof : Parser.CommandHandler.commandGetProof (H := H) =
    Bridge.callUnit h .commandGetProof
  commandGetUnsatAssumptions : Parser.CommandHandler.commandGetUnsatAssumptions (H := H) =
    Bridge.callUnit h .commandGetUnsatAssumptions
  commandGetUnsatCore : Parser.CommandHandler.commandGetUnsatCore (H := H) =
    Bridge.callUnit h .commandGetUnsatCore
  commandGetValue : ∀ ts, Parser.CommandHandler.commandGetValue (H := H) ts =
    Bridge.callUnit h (.commandGetValue ts.toList)
  commandPop : ∀ n, Parser.CommandHandler.commandPop (H := H) n =
    Bridge.callUnit h (.commandPop (Bridge.chars n.asSlice))
  commandPush : ∀ n, Parser.CommandHandler.commandPush (H := H) n =
    Bridge.callUnit h (.commandPush (Bridge.chars n.asSlice))
  commandReset : Parser.CommandHandler.commandReset (H := H) = Bridge.callUnit h .commandReset
  commandResetAssertions : Parser.CommandHandler.commandResetAssertions (H := H) =
    Bridge.callUnit h .commandResetAssertions
  commandSetInfo : ∀ a, Parser.CommandHandler.commandSetInfo (H := H) a =
    Bridge.callUnit h (.commandSetInfo a)
  commandSetLogic : ∀ s, Parser.CommandHandler.commandSetLogic (H := H) s =
    Bridge.callUnit h (.commandSetLogic (Bridge.symbol s))
  commandSetOption : ∀ a, Parser.CommandHandler.commandSetOption (H := H) a =
    Bridge.callUnit h (.commandSetOption a)

end

/--
A failure of the traversal as a failure of the parser: a rejected version declaration is the
syntax error of the same name.
-/
def causeOf {ε : Type} : Cause ε → Parser.ParseErrorCause ε
  | .syntax .unsupportedVersion => .syntax .unsupportedVersion
  | .syntax (.tooManyDeclarations limit) => .syntax (.tooManyVersionDeclarations limit)
  | .handler error => .handler error


namespace Bridge

/-- The library's version for a version of the spec. -/
def libVersion : Spec.Lexicon.Version → BSmtLib.Version
  | .v2_0 => .v2_0
  | .v2_5 => .v2_5
  | .v2_6 => .v2_6
  | .v2_7 => .v2_7

end Bridge

/-- The spec's policy that a posture of the parser stands for. -/
def policyOf (posture : Parser.VersionPosture) : VersionPolicy :=
  { allowed := posture.allowed.toList.map Bridge.version,
    maxDeclarations := posture.maxDeclarations }

/-- How the command parser ends a command of the spec. -/
def outcomeOf (command : Tree.Command) : Parser.CommandOutcome :=
  match command with
  | .exit => .exit
  | command =>
    match command.declaredVersion with
    | some version => .setVersion (Bridge.libVersion version)
    | none => .command

/-- No item is whitespace or a comment, which a parser is never handed. -/
def NoLayout (items : List Parser.Input) : Prop := ∀ token ∈ items, Bridge.received token ≠ none

/-- Every reserved word. -/
def allReserved : List Reserved :=
  GeneralReserved.all.toList.map .general ++ CommandNameReserved.all.toList.map .commandName

/-- The reserved word the spec spells with the characters, if there is one. -/
def decodeReserved (c : Spec.Lexicon.Chars) : Option Reserved :=
  allReserved.find? fun r => decide (Bridge.reserved r = c)

namespace Rejection

/-- What a token stands for, as the parsers take it. -/
def rcv (token : Parser.Input) : Received := (Bridge.received token).getD .endOfInput

/-- A view of the characters. -/
def bytesOf (c : Spec.Lexicon.Chars) : ByteSlice := (ByteArray.mk c.toArray).toByteSlice

end Rejection

end BSmtLib.ParserProofs
