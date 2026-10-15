module

public import BSmtLib.Facts.Proofs.Reader.Param.Adapter
import all BSmtLib.Parser
import all BSmtLib.Parser.Adapter
import all BSmtLib.Parser.Category.Attribute
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Category.Ident
import all BSmtLib.Parser.Category.Pattern
import all BSmtLib.Parser.Category.QualifiedIdent
import all BSmtLib.Parser.Category.SExpr
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Category.SortedVar
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Command
import all BSmtLib.Parser.Command.Internal.Datatype
import all BSmtLib.Parser.Command.Internal.Function
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Parser.Script
import all BSmtLib.Token.SyntaxToken

@[expose] public section

/-!
# The parser rejects whitespace and comments

No parser takes whitespace or a comment (`Parser.Internal.Input.layout`): every step of the
script parser, from every state, fails on it (`scriptStep_layout`), and so the adapter that stops
after an action on its cursor (`Param.Stop`), handed such a token, stops with an error at it, the
cursor after the token (`takeOne_layout`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Layout

open BSmtLibSpec.Parser.Properties
open BSmtLib.Parser
open BSmtLib.Parser.Internal (PM call syntaxError)
open BSmtLib.Facts.Proofs.Parser.Cut BSmtLib.Facts.Proofs.Reader.Param.Adapter
open BSmtLib.Parser.Adapter BSmtLib.Parser.Category.Attribute BSmtLib.Parser.Category.Combinator
open BSmtLib.Parser.Category.Attribute.Internal
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Parser.Category.Ident BSmtLib.Parser.Category.Pattern
open BSmtLib.Parser.Category.Ident.Internal
open BSmtLib.Parser.Category.Pattern.Internal
open BSmtLib.Parser.Category.QualifiedIdent BSmtLib.Parser.Category.SExpr
open BSmtLib.Parser.Category.QualifiedIdent.Internal
open BSmtLib.Parser.Category.SExpr.Internal
open BSmtLib.Parser.Category.«Sort» BSmtLib.Parser.Category.SortedVar BSmtLib.Parser.Category.Term
open BSmtLib.Parser.Category.«Sort».Internal
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.Term.Internal
open BSmtLib.Parser.Category.Token BSmtLib.Parser.Command BSmtLib.Parser.Command.Internal.Datatype
open BSmtLib.Parser.Category.Token.Internal
open BSmtLib.Parser.Command.Internal
open BSmtLib.Parser.Command.Internal.Function BSmtLib.Parser.Command.Internal.Standard BSmtLib.Parser.Script
open BSmtLib.Traits

attribute [local instance high] Stop.consumeFrom

/-- A computation of the recording parser that fails, from every log. -/
def Fails {α : Type} (x : Parser.Quiet.RPM α) : Prop :=
  ∀ events, ∃ e events', x.run.run events = (.error e, events')

theorem fails_throw {α : Type} (e : ParseErrorCause Unit) : Fails (throw e : Parser.Quiet.RPM α) :=
  fun events => ⟨e, events, rfl⟩

theorem fails_syntaxError {α : Type} (kind : SyntaxErrorKind) :
    Fails (syntaxError kind : Parser.Quiet.RPM α) :=
  fails_throw _

theorem fails_bind {α β : Type} {x : Parser.Quiet.RPM α} (hx : Fails x)
    (f : α → Parser.Quiet.RPM β) :
    Fails (x >>= f) := by
  intro events
  obtain ⟨e, events', h⟩ := hx events
  exact ⟨e, events', run_bind_error h⟩

theorem fails_bind_right {α β : Type} (x : Parser.Quiet.RPM α) {f : α → Parser.Quiet.RPM β}
    (hf : ∀ a, Fails (f a)) :
    Fails (x >>= f) := by
  intro events
  rcases hx : x.run.run events with ⟨r, events'⟩
  rcases r with e | a
  · exact ⟨e, events', run_bind_error hx⟩
  · obtain ⟨e, events'', h⟩ := hf a events'
    exact ⟨e, events'', by rw [run_bind_ok hx]; exact h⟩

/-! ## Every step fails on whitespace and comments -/

/-- The recording handler. -/
abbrev LH := List Event

/-- One of the lemmas below for a parser's step on whitespace or a comment, applied. -/
syntax "fails_layout" : tactic
/-- A computation that fails: a syntax error, or a step of a parser on whitespace or a comment,
before the rest. -/
syntax "fails_tac" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| fails_layout) => `(tactic| first
    | apply identStep_layout
    | apply sortStep_layout
    | apply symbolStep_layout
    | apply sortDecStep_layout
    | apply sortedVarStep_layout
    | apply termStep_layout
    | apply literalStep_layout
    | apply functionDecStep_layout
    | apply constructorStep_layout
    | apply datatypeStep_layout
    | apply bodyStep_layout)

set_option hygiene false in
macro_rules
  | `(tactic| fails_tac) => `(tactic| first
    | exact fails_syntaxError _
    | exact fails_throw _
    | exact fails_bind (fails_syntaxError _) _
    | exact fails_bind (fails_throw _) _
    | (apply fails_bind; assumption)
    | (apply fails_bind; apply identStep_layout)
    | (apply fails_bind; apply sortStep_layout)
    | (apply fails_bind; apply sExprStep_layout)
    | (apply fails_bind; apply attributeStep_layout)
    | (apply fails_bind; apply patternStep_layout)
    | (apply fails_bind; apply qualIdentStep_layout)
    | (apply fails_bind; apply sortedVarStep_layout)
    | (apply fails_bind; apply termStep_layout)
    | (apply fails_bind; apply listStep_layout; intro; fails_layout)
    | (apply fails_bind; apply literalStep_layout)
    | (apply fails_bind; apply signatureStep_layout)
    | (apply fails_bind; apply functionDecStep_layout)
    | (apply fails_bind; apply constructorStep_layout)
    | (apply fails_bind; apply datatypeStep_layout)
    | (apply fails_bind; apply bodiesStep_layout)
    | (apply fails_bind; apply payloadStep_layout))

theorem identStep_layout (version : Token.Version) (self : IdentState) :
    Fails (IdentState.step (H := LH) (m := Id) version self .layout) := by
  cases self <;> simp only [IdentState.step, Parser.Internal.Input.isWord] <;> (try split) <;>
    first | exact fails_syntaxError _ | simp_all

theorem sortStep_layout (version : Token.Version) (self : SortState (Handler.«Sort» LH)) :
    Fails (sortStep (H := LH) (m := Id) version self .layout) := by
  obtain ⟨mode, levels⟩ := self
  unfold sortStep
  cases mode <;> dsimp only <;> (try simp only [Parser.Internal.Input.isWord, Bool.false_eq_true,
      ite_false])
  all_goals fails_tac

theorem sExprStep_layout (version : Token.Version) (self : SExprState (Handler.SExpr LH)) :
    Fails (sExprStep (H := LH) (m := Id) version self .layout) := by
  unfold sExprStep
  dsimp only
  fails_tac

theorem attributeStep_layout (single : Bool) (version : Token.Version)
    (self : AttributeState (Handler.SExpr LH) (Handler.Attribute LH)) :
    Fails (attributeStep (H := LH) (m := Id) single version self .layout) := by
  obtain ⟨mode, attributes⟩ := self
  unfold attributeStep
  cases mode <;> dsimp only <;> (try simp only [expectClose, Bool.and_eq_true])
  all_goals (try split) <;> (try split) <;> fails_tac

theorem patternStep_layout (version : Token.Version) (self : PatternState) :
    Fails (PatternState.step (H := LH) (m := Id) version self .layout) := by
  unfold PatternState.step
  cases self <;> dsimp only <;>
    (try simp only [PatternState.symbolOrWildcard?, Parser.Internal.Input.isWord, Bool.and_false,
      Bool.false_eq_true, ite_false]) <;> fails_tac

theorem qualIdentStep_layout (version : Token.Version) (self : QualIdentState (Handler.«Sort» LH)) :
    Fails (qualIdentStep (H := LH) (m := Id) version self .layout) := by
  unfold qualIdentStep
  cases self <;> dsimp only <;>
    (try simp only [Parser.Internal.Input.isWord, Bool.false_eq_true, ite_false,
        expectClose]) <;> fails_tac

theorem sortedVarStep_layout (version : Token.Version) (self : SortedVarState (Handler.«Sort» LH)) :
    Fails (sortedVarStep (H := LH) (m := Id) version self .layout) := by
  unfold sortedVarStep
  cases self <;> dsimp only <;> (try simp only [expectClose, expectOpen, expectSymbol]) <;>
    fails_tac

theorem listStep_layout {σ ρ : Type} (init : σ)
    (inner : σ → Parser.Internal.Input → Parser.Quiet.RPM (Parser.Internal.Step σ ρ))
    (hinner : ∀ s, Fails (inner s .layout)) (maximum : Option Nat) (self : ListState σ ρ) :
    Fails (ListState.step init inner maximum self .layout) := by
  unfold ListState.step
  obtain ⟨opened, outside, innerState, items⟩ := self
  cases opened <;> cases outside <;> dsimp only <;>
    (try simp only [expectOpen, Bool.not_false, Bool.not_true, ite_true, ite_false,
      Bool.false_eq_true])
  all_goals (try split) <;> (try split) <;> first | fails_tac | exact fails_bind (hinner _) _

theorem termStep_layout (version : Token.Version) (self : TermStateOf LH) :
    Fails (termStep (H := LH) (m := Id) version self .layout) := by
  obtain ⟨mode, levels⟩ := self
  unfold termStep
  cases mode <;> dsimp only <;> (try simp only [expectClose, expectOpen, expectSymbol, termOpened])
  all_goals fails_tac

theorem symbolStep_layout (u : Unit) :
    Fails (symbolStep (H := LH) (m := Id) u .layout) := by
  unfold symbolStep
  simp only [expectSymbol]
  fails_tac

theorem sortDecStep_layout (self : SortDecState) :
    Fails (SortDecState.step (H := LH) (m := Id) self .layout) := by
  unfold SortDecState.step
  cases self <;> dsimp only <;> (try simp only [expectClose, expectOpen, expectSymbol,
    expectNumeral]) <;> fails_tac

theorem literalStep_layout (version : Token.Version) (self : LiteralStateOf LH) :
    Fails (literalStep (H := LH) (m := Id) version self .layout) := by
  obtain ⟨shape, term⟩ := self
  unfold literalStep
  cases shape <;> dsimp only <;> fails_tac

theorem signatureStep_layout (version : Token.Version) (self : SignatureState (Handler.«Sort» LH)) :
    Fails (signatureStep (H := LH) (m := Id) version self .layout) := by
  unfold signatureStep
  cases self <;> dsimp only <;> (try simp only [expectSymbol]) <;> fails_tac

theorem functionDecStep_layout (version : Token.Version)
    (self : FunctionDecState (Handler.«Sort» LH)) :
    Fails (functionDecStep (H := LH) (m := Id) version self .layout) := by
  unfold functionDecStep
  cases self <;> dsimp only <;> (try simp only [expectClose, expectOpen]) <;> fails_tac

theorem constructorStep_layout (version : Token.Version)
    (self : ConstructorState (Handler.«Sort» LH)) :
    Fails (constructorStep (H := LH) (m := Id) version self .layout) := by
  unfold constructorStep
  cases self <;> dsimp only <;> (try simp only [expectOpen, expectSymbol]) <;> fails_tac

theorem datatypeStep_layout (start : Array Plain.Symbol → Parser.Quiet.RPM Unit)
    (version : Token.Version)
    (self : DatatypeState (Handler.«Sort» LH)) :
    Fails (datatypeStep (H := LH) (m := Id) start version self .layout) := by
  unfold datatypeStep
  cases self <;> dsimp only <;> (try simp only [expectClose, expectOpen,
      Parser.Internal.Input.isWord,
    Bool.false_eq_true, ite_false]) <;> fails_tac

theorem bodyStep_layout (version : Token.Version) (self : TermStateOf LH) :
    Fails (bodyStep (H := LH) (m := Id) version self .layout) := by
  unfold bodyStep
  fails_tac

theorem bodiesStep_layout (count : Nat) (version : Token.Version)
    (self : ListState (TermStateOf LH) Unit) :
    Fails (bodiesStep (H := LH) (m := Id) count version self .layout) := by
  unfold bodiesStep
  exact listStep_layout _ _ (bodyStep_layout version) _ _

theorem payloadStep_layout (version : Token.Version) (self : PayloadOf LH) :
    Fails (payloadStep (H := LH) (m := Id) version self .layout) := by
  unfold payloadStep
  cases self <;> dsimp only <;> (try simp only [expectClose, expectSymbol,
    expectNumeral, expectString, expectKeyword])
  all_goals first
    | fails_tac
    | exact fails_bind
        (listStep_layout _ _ (fun _ => fails_bind (datatypeStep_layout _ _ _) _) _ _) _

theorem commandStep_layout (version : Token.Version) (self : CommandStateOf LH) :
    Fails (commandStep (H := LH) (m := Id) version self .layout) := by
  unfold commandStep
  cases self
  -- the recording handler has no non-standard parser
  case nonstandard parser => exact Empty.elim parser
  all_goals dsimp only <;> fails_tac

theorem scriptStep_layout (version : Token.Version) (parser : ScriptParser LH) :
    Fails (ScriptParser.Internal.step (H := LH) (m := Id) version parser .layout) := by
  unfold ScriptParser.Internal.step
  exact fails_bind (commandStep_layout _ _) _

theorem ofSyntax_layout {b : Token.BatchTag} (cursor : Token.BatchCursor b) (token : Token b)
    (h : Lexer.Adapters.toHanded cursor token = none) :
    Parser.Internal.Input.ofSyntax (cursor.syntax token) = .layout := by
  unfold Lexer.Adapters.toHanded at h
  simp only [Token.BatchCursor.«syntax», Token.SyntaxToken.fromToken] at h ⊢
  generalize cursor.category token = category at h ⊢
  cases category <;> simp only [Lexer.Adapters.toTokenType, Option.map_none,
    Option.map_some, reduceCtorEq] at h <;> rfl

theorem takeOne_layout {b : Token.BatchTag} (parser : ScriptParser LH)
    (cursor next : Token.BatchCursor b) (token : Token b) (consumed : next.Consumed cursor)
    (events : List Event) (hl : Parser.Internal.Input.ofSyntax (next.syntax token) = .layout) :
    ∃ e events', (Stop.takeOne (H := LH) (m := Id) (P := ScriptParser LH)
      parser cursor token next consumed).run events =
        ((.stop (.error e) (Parser.Internal.ParseByToken.reset parser), ⟨next, consumed⟩),
            events') := by
  have hitem' : Parser.Internal.Input.ofSyntax (Token.Produce.«syntax» next token) =
      Parser.Internal.Input.ofSyntax (next.syntax token) := rfl
  obtain ⟨e, events',
      hX⟩ := fails_bind_right (Parser.Internal.ParseByToken.arrive (H := LH) parser .layout)
    (fun _ => scriptStep_layout (Token.Produce.version next) parser) events
  refine ⟨⟨e⟩, events', ?_⟩
  simp only [Stop.takeOne, StateT.run_bind]
  rw [hitem', hl]
  erw [hX]
  rfl


end BSmtLib.Facts.Proofs.Reader.Param.Layout
