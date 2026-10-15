module

public import BSmtLib.Facts.Proofs.Parser.Rejection.CommandParts

@[expose] public section

/-!
# What commands can still take

A command's remainder goes on past its `)`: what follows a command depends on how it ends
(`CmdEnd`): the script goes on in a version, ends after `exit`, stops after a version declaration
that names no supported version, or the input ends between commands. The remainders of the
command parser's states are given relative to what follows each such end (`follows`).

A `set-info` ends as its keyword and its value say (`setInfoEnd`), which the parser tracks with
`Parser.Declaration`.
-/

namespace BSmtLib.Facts.Proofs.Parser.Rejection.Command

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser (PM)
open BSmtLib.Parser.Category.Term (TermState)
open BSmtLib.Parser.Category.Combinator (ListState)
open BSmtLib.Parser.Command.Datatype (SortDecState DatatypeState)
open BSmtLib.Parser.Command.Standard (LiteralState Payload NamedCommand FinalCall Declaration)
open BSmtLib.Parser.Command.Function (SignatureState FunctionDecState)
open BSmtLib.Parser.Command.Definition (DefinitionEnd)
open BSmtLib.Parser.Command (CommandState CommandOutcome)
open BSmtLib.Parser.Category.Attribute (AttributeState)
open BSmtLib.Parser.Category.Sort (SortState)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Proofs.Parser.Rejection.Basic
open BSmtLib.Facts.Proofs.Parser.Rejection.CommandParts BSmtLib.Facts.Proofs.Parser.Rejection.Parts
open BSmtLib.Facts.Proofs.Parser.Rejection.SExpr BSmtLib.Facts.Proofs.Parser.Rejection.«Sort»
open BSmtLib.Facts.Proofs.Parser.Rejection.Term BSmtLib.Plain

open BSmtLib.Facts.Proofs.Parser.Rejection.Basic.Lang

/-! ## How commands end -/

/-- How a command ends, as far as what follows it goes. -/
inductive CmdEnd where
  /-- The script goes on, in the version. -/
  | next (version : BSmtLibSpec.Lexicon.Version)
  /-- `exit`: the end of the input follows. -/
  | exit
  /-- A version declaration that names no supported version: a parser stops. -/
  | refused
  /-- The input ended between commands. -/
  | endOfInput

/-- How the command ends, read in the version. -/
def cmdEnd (version : BSmtLibSpec.Lexicon.Version) (command : Tree.Command) : CmdEnd :=
  match command.modeAfter version with
  | some (.read next) => .next next
  | some .unparsed => .exit
  | none => .refused

/-- How the command parser's outcome ends the command, in the version. -/
def outcomeEnd (version : BSmtLibSpec.Lexicon.Version) : CommandOutcome → CmdEnd
  | .command => .next version
  | .setVersion declared => .next (Bridge.version declared)
  | .exit => .exit
  | .endOfInput => .endOfInput

/-- How a version declaration ends, from what follows its keyword: a supported version's number
and the `)`, or anything else. -/
def declarationEnd : List Received → CmdEnd
  | [.token (.decimal decimal), .token .parenClose] =>
    match versionOfNumber decimal with
    | some declared => .next declared
    | none => .refused
  | _ => .refused

/-- How a `set-info` ends, from what its tokens so far tell of a version declaration and the
rest of its tokens. -/
def setInfoEnd (version : BSmtLibSpec.Lexicon.Version) : Declaration → List Received → CmdEnd
  | .start, .token (.keyword name) :: rest =>
    if name = BSmtLibSpec.Regex.chars "smt-lib-version" then declarationEnd rest else .next version
  | .start, _ => .next version
  | .other, _ => .next version
  | .keyword, rest => declarationEnd rest
  | .value (some declared), _ => .next (Bridge.version declared)
  | .value none, _ => .refused

/-! ## Remainders -/

section

variable (version : BSmtLibSpec.Lexicon.Version) (follows : CmdEnd → Lang)

/-- A keyword, any. -/
def KeywordLang : Lang := fun u => ∃ name, u = [.token (.keyword name)]

/-- A string literal, any. -/
def StringLang : Lang := fun u => ∃ content, u = [.token (.string content)]

/-- A command's `)` and what follows a command that keeps the version. -/
def closeNext : Lang := cat (tok closeItem) (follows (.next version))

/-- The remainders after the symbol of the commands that start with one. -/
def namedTail : NamedCommand → Lang
  | .declareConst => cat (SortLang version) (closeNext version follows)
  | .declareDatatype => cat (DatatypeLang version) (closeNext version follows)
  | .declareFun =>
    cat (tok openItem) (cat (star (SortLang version)) (cat (tok closeItem)
      (cat (SortLang version) (closeNext version follows))))
  | .declareSort => cat NumeralLang (closeNext version follows)
  | .declareSortParameter => closeNext version follows
  | .defineConst => cat (SortLang version) (cat (TermLang version) (closeNext version follows))
  | .defineSort =>
    cat (tok openItem) (cat (star SymbolLang) (cat (tok closeItem)
      (cat (SortLang version) (closeNext version follows))))
  | .setLogic => closeNext version follows

/-- The attribute parser is where the tracker of a version declaration says: before the keyword,
before anything, and after the keyword `:smt-lib-version`, right after it. -/
def SetInfoSync : Declaration → AttributeState Nat Nat → Prop
  | .start, state => state = ⟨.start, #[]⟩
  | .keyword, state => ∃ name, state = ⟨.afterName name, #[]⟩
  | _, _ => True

/-- The remainders of `set-info`: the attribute and the `)`, then what follows as the attribute
says. -/
def setInfoRem (declaration : Declaration) (state : AttributeState Nat Nat) : Lang :=
  fun u => SetInfoSync declaration state ∧ ∃ a b, attrRem version true false state a ∧
    follows (setInfoEnd version declaration a) b ∧ u = a ++ b

/-- Sort declarations, between `lo` and `hi` of them, then as many datatype declarations. -/
def datatypesRem (state : ListState SortDecState (Nodes.Symbol × NumeralView)) : Lang :=
  fun u => ∃ n, 1 ≤ n ∧ cat (listRem sortDecRem SortDecLang .start n (some n) state)
    (cat (tok openItem) (cat (rep (DatatypeLang version) n (some n))
      (cat (tok closeItem) (closeNext version follows)))) u

/-- Function declarations, then as many bodies. -/
def funsRecRem (state : ListState (FunctionDecState Nat) (Nodes.Signature Nat)) : Lang :=
  fun u => ∃ n, 1 ≤ n ∧ cat (listRem (functionDecRem version) (FunctionDecLang version) .start n
    (some n) state) (cat (tok openItem) (cat (rep (TermLang version) n (some n))
      (cat (tok closeItem) (closeNext version follows)))) u

/-- The remainders of the payload parser's states. -/
def payloadRem : Parser.Command.Standard.Payload Nat Nat Nat Nat Nat → Lang
  | .closing final =>
    match final with
    | .exit => cat (tok closeItem) (follows .exit)
    | _ => closeNext version follows
  | .named command => cat SymbolLang (namedTail version follows command)
  | .assert state => cat (termRem version state) (closeNext version follows)
  | .checkSatAssuming state =>
    cat (listRem (termRem version) (TermLang version) .init 0 none state)
      (closeNext version follows)
  | .checkSatAssumingLiterals state =>
    cat (listRem literalRem LiteralLang .init 0 none state) (closeNext version follows)
  | .declareConst _ state => cat (sortRem version state) (closeNext version follows)
  | .declareFunParameters _ state =>
    cat (listRem (sortRem version) (SortLang version) .init 0 none state)
      (cat (SortLang version) (closeNext version follows))
  | .declareFunResult _ _ state => cat (sortRem version state) (closeNext version follows)
  | .declareSort _ => cat NumeralLang (closeNext version follows)
  | .declareDatatype _ state => cat (datatypeRem version state) (closeNext version follows)
  | .declareDatatypesSorts state => datatypesRem version follows state
  | .declareDatatypesDatatypes count state =>
    cat (listRem (datatypeRem version) (DatatypeLang version) .start count (some count) state)
      (closeNext version follows)
  | .defineSortParameters _ state =>
    cat (listRem (fun _ => SymbolLang) SymbolLang () 0 none state)
      (cat (SortLang version) (closeNext version follows))
  | .defineSortBody state => cat (sortRem version state) (closeNext version follows)
  | .defineConstSort _ state =>
    cat (sortRem version state) (cat (TermLang version) (closeNext version follows))
  | .defineSignature _ state =>
    cat (signatureRem version state) (cat (TermLang version) (closeNext version follows))
  | .defineBody _ state => cat (termRem version state) (closeNext version follows)
  | .defineFunsRecDeclarations state => funsRecRem version follows state
  | .defineFunsRecBodies signatures state =>
    cat (listRem (termRem version) (TermLang version) .init signatures.size
      (some signatures.size) state)
      (closeNext version follows)
  | .echo => cat StringLang (closeNext version follows)
  | .getInfo => cat KeywordLang (closeNext version follows)
  | .getOption => cat KeywordLang (closeNext version follows)
  | .getValue state =>
    cat (listRem (termRem version) (TermLang version) .init 1 none state)
      (closeNext version follows)
  | .pop => cat NumeralLang (closeNext version follows)
  | .push => cat NumeralLang (closeNext version follows)
  | .setInfo declaration state => setInfoRem version follows declaration state
  | .setOption state => cat (attrRem version true false state) (follows (.next version))

/-- A command of the version, then what follows it. -/
def CommandLang : Lang := fun u => ∃ (cmd : Tree.Command) (w : List Received), cmd.Valid version ∧
  follows (cmdEnd version cmd) w ∧ u = toks cmd.tokens ++ w

/-- The remainders of the command parser's states. -/
def commandRem : Parser.Command.CommandState Nat Nat Nat Nat Nat → Lang
  | .awaiting => union (CommandLang version follows) (cat (tok .endOfInput) (follows .endOfInput))
  | .opened => fun u => CommandLang version follows (openItem :: u)
  | .payload payload => payloadRem version follows payload

end

end BSmtLib.Facts.Proofs.Parser.Rejection.Command
