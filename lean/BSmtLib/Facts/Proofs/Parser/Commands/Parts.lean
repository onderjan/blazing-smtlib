module

public import BSmtLib.Facts.Proofs.Parser.Commands.Elements
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Command.Internal.Datatype
import all BSmtLib.Parser.Command.Internal.Function

@[expose] public section

/-!
# Signatures, function declarations and constructors against the traversal

The lemmas cover the parts of commands that a sorted-variable list sits in:
- a function signature (its parameters);
- a function declaration (a signature in parentheses);
- a datatype constructor (its selectors, read as sorted variables).

Each lemma gives the program the parser runs, whose value, through the bridge, is the
traversal's.
-/

namespace BSmtLib.Facts.Proofs.Parser.Commands.Parts

open BSmtLib.Grammar.Multiple (FunctionSignature)
open BSmtLibSpec.Grammar
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.Combinator.Internal (ListState)
open BSmtLib.Parser.Command.Internal.Function
    (SignatureState FunctionDecState signatureStep functionDecStep)
open BSmtLib.Parser.Command.Internal.Datatype (ConstructorState constructorStep)
open BSmtLib.Parser.Category.SortedVar.Internal (sortedVarStep SortedVarState)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Commands.Elements BSmtLib.Facts.Proofs.Parser.Drive
open BSmtLib.Facts.Proofs.Parser.Lemmas BSmtLib.Facts.Proofs.Parser.List
open BSmtLib.Facts.Proofs.Parser.«Sort» BSmtLib.Facts.Proofs.Parser.TermParts
open BSmtLib.Facts.Proofs.Parser.Tokens

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
variable {points : Points (StateT H m)} {σ ρ : Type}

omit [LawfulMonad m] in
/-- Inside an element, the list steps as the inner parser. -/
theorem ListState.step_inside {init : σ} {inner : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)}
    {maximum : Option Nat} (found : Array ρ) (state : σ) (token : Parser.Internal.Input) :
    ListState.step init inner maximum
        { opened := true, outside := false, inner := state, items := found } token =
      inner state token >>= Parser.Internal.Step.wrap
        (fun state => ({ opened := true, outside := false, inner := state, items := found } :
          ListState σ ρ))
        fun item => pure (.more (ListState.between init (found.push item))) := by
  simp only [ListState.step, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
variable {points : Points (StateT H m)} {version : Version}
variable {h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H)}

theorem specPairs_toArray {S : Type} (l : List (Lexicon.Value.Symbol × S)) :
    Bridge.pairs l.toArray = Bridge.specPairs l := by
  simp [Bridge.pairs, Bridge.specPairs]

/-! ## Signatures -/

/-- The signature parser reads ⟨symbol⟩ `(` ⟨sorted_var⟩∗ `)` ⟨sort⟩. -/
theorem signature_runs (hA : TermAgrees h) (name : Tree.Symbol)
    (parameters : List Tree.SortedVar) (result : Tree.«Sort»)
    (hparameters : ∀ var ∈ parameters, var.Valid (Bridge.version version))
    (hresult : result.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (.symbol name :: paren (parameters.flatMap Tree.SortedVar.tokens) ++
      result.tokens)) :
    ∃ program : PM H (FunctionSignature (Handler.«Sort» H)),
      Bridge.signature <$> program =
        adaptRun (Traversal.signature points h name parameters result) ∧
      Runs points (signatureStep version) .start tokens program fun r => pure (.done r) := by
  obtain ⟨symbolToken, rest, rfl, hsymbolToken, hrest⟩ := Stands.split_cons hs
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbolToken
  obtain ⟨listTokens, sortTokens, rfl, hlist, hsort⟩ := Stands.split hrest
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hlist
  obtain ⟨program, hprogram, hruns⟩ := sortedVars_runs (points := points) hA parameters
    hparameters hinner
  have hlistRuns : Runs points (ListState.step .start (sortedVarStep version) none)
      (ListState.paren .start) (.parenOpen :: (inner ++ [.parenClose]))
      (do
        tick points .parenOpen
        let handled ← program
        tick points .parenClose
        pure handled)
      fun handled => pure (.done (#[] ++ handled.toArray)) :=
    Runs.append (first := [.parenOpen]) ListState.open_runs fun _ =>
      Runs.append (hruns #[]) fun handled =>
        Runs.token (program := pure handled)
          (next := fun handled => pure (.done (#[] ++ handled.toArray)))
          (by simp [ListState.step, ListState.between])
  have hlistEmbed := Runs.embed (outer := signatureStep version)
    (fun state => SignatureState.parameters symbol state)
    (fun parameters => pure (.more (.result symbol parameters .init)))
    (fun state token => by
      simp only [signatureStep]
      congr 1
      funext step
      cases step <;> rfl) hlistRuns
  have hsortEmbed : ∀ parameters, Runs points (signatureStep version)
      (.result symbol parameters .init) sortTokens
      (adaptRun (Traversal.sort points h result))
      fun r => pure (.done (FunctionSignature.Internal.new symbol parameters r)) :=
    fun parameters =>
    (Runs.embed (outer := signatureStep version)
      (fun state => SignatureState.result symbol parameters state)
      (fun r => pure (.done (FunctionSignature.Internal.new symbol parameters r)))
      (fun state token => by
        simp only [signatureStep]
        congr 1
        funext step
        cases step <;> rfl) (sort_runs hA result hresult hsort [])).congr rfl
        (by funext; simp [sortPush, Parser.Internal.Step.wrap])
  refine ⟨do
      tick points (.symbol symbol)
      tick points .parenOpen
      let handled ← program
      tick points .parenClose
      let r ← adaptRun (Traversal.sort points h result)
      pure (FunctionSignature.Internal.new symbol handled.toArray r), ?_, ?_⟩
  · simp only [Traversal.signature, adaptRun_bind, takeAll,
      adaptRun_take (token := .parenClose) rfl, ← hprogram]
    simp [Bridge.signature, specPairs_toArray, adaptRun_take (token := .symbol symbol) rfl,
      adaptRun_take (token := .parenOpen) rfl]
  · rw [show Parser.Internal.Input.symbol symbol :: (Parser.Internal.Input.parenOpen ::
      (inner ++ [.parenClose]) ++ sortTokens) =
      [.symbol symbol] ++ ((Parser.Internal.Input.parenOpen ::
          (inner ++ [.parenClose])) ++ sortTokens) by simp]
    refine (Runs.append (middle := fun _ =>
        SignatureState.parameters symbol (ListState.paren .start))
      (Runs.token_more (by simp [signatureStep,
          Parser.Category.Token.Internal.expectSymbol])) fun _ =>
      Runs.append (middle := fun handled =>
          SignatureState.result symbol (#[] ++ handled.toArray) .init)
        (hlistEmbed.congr rfl (by funext; simp [Parser.Internal.Step.wrap])) fun handled =>
        Runs.map_program (f := fun r =>
          (FunctionSignature.Internal.new symbol (#[] ++ handled.toArray) r :
          FunctionSignature _)) (hsortEmbed _)).congr ?_ rfl
    simp

/-- The parser of a function declaration reads `(` signature `)`. -/
theorem functionDec_element (hA : TermAgrees h) :
    ElementRuns points (functionDecStep version) .start Tree.FunctionDec.tokens
      (Tree.FunctionDec.Valid (Bridge.version version))
      (fun declaration => adaptRun (do
        take points .parenOpen
        let handled ← Traversal.signature points h declaration.symbol declaration.parameters
          declaration.result
        take points .parenClose
        pure handled))
      Bridge.signature := by
  intro ⟨name, parameters, result⟩ hvalid tokens hs
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
  obtain ⟨program, hprogram, hruns⟩ := signature_runs (points := points) hA name parameters
    result hvalid.1 hvalid.2 hinner
  have hembed := Runs.embed (outer := functionDecStep version)
    (fun state => FunctionDecState.signature state)
    (fun signature => pure (.more (.close signature)))
    (fun state token => by
      simp only [functionDecStep]
      congr 1
      funext step
      cases step <;> rfl) hruns
  refine ⟨⟨_, _, rfl, by simp⟩, do
      tick points .parenOpen
      let signature ← program
      tick points .parenClose
      pure signature, ?_, ?_⟩
  · simp only [adaptRun_bind, adaptRun_take (token := .parenOpen) rfl,
      adaptRun_take (token := .parenClose) rfl, ← hprogram]
    simp
  · refine (Runs.append (first := [.parenOpen]) (middle := fun _ => FunctionDecState.signature
      .start)
      (Runs.token_more (by simp [functionDecStep,
          Parser.Category.Token.Internal.expectOpen])) fun _ =>
      Runs.append (middle := fun signature => FunctionDecState.close signature)
        (hembed.congr rfl (by funext; simp [Parser.Internal.Step.wrap])) fun signature =>
        Runs.token (program := pure signature) (next := fun r => pure (.done r))
          (by simp [functionDecStep, Parser.Category.Token.Internal.expectClose])).congr ?_ rfl
    simp

/-! ## Constructors -/

/-- A selector as the sorted variable it is written as. -/
def selectorVar (selector : Tree.SelectorDec) : Tree.SortedVar := ⟨selector.symbol, selector.sort⟩

omit [LawfulMonad m] in
theorem selectors_eq (selectors : List Tree.SelectorDec) :
    Traversal.selectors points h selectors =
      Traversal.sortedVars points h (selectors.map selectorVar) := by
  induction selectors with
  | nil => rfl
  | cons selector selectors ih =>
    simp only [Traversal.selectors, Traversal.sortedVars, List.map_cons, ih]
    rfl

theorem selectors_tokens (selectors : List Tree.SelectorDec) :
    selectors.flatMap Tree.SelectorDec.tokens =
      (selectors.map selectorVar).flatMap Tree.SortedVar.tokens := by
  induction selectors with
  | nil => rfl
  | cons selector selectors ih =>
    simp only [List.flatMap_cons, List.map_cons, ih]
    rfl

/-- From after its `(`, the constructor parser reads ⟨symbol⟩ ⟨selector_dec⟩∗ `)`. -/
theorem constructor_runs_opened (hA : TermAgrees h) (constructor : Tree.ConstructorDec)
    (hvalid : constructor.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (.symbol constructor.symbol ::
      (constructor.selectors.flatMap Tree.SelectorDec.tokens ++ [.parenClose]))) :
    ∃ program : PM H (Lexicon.Value.Symbol × Grammar.Multiple.SortedVars (Handler.«Sort» H)),
      Bridge.constructor <$> program = adaptRun (constructorAfterOpen points h constructor) ∧
      Runs points (constructorStep version) .opened tokens program fun r => pure (.done r) := by
  obtain ⟨symbolToken, rest, rfl, hsymbolToken, hrest⟩ := Stands.split_cons hs
  obtain ⟨symbol, rfl, hsymbol⟩ := Parser.Internal.Input.received_symbol hsymbolToken
  obtain ⟨inner, closing, rfl, hinner, hclosing⟩ := Stands.split hrest
  obtain ⟨close, rfl, hclose⟩ := Stands.split_single hclosing
  have hclose := Parser.Internal.Input.received_parenClose hclose
  subst hclose
  rw [selectors_tokens] at hinner
  obtain ⟨program, hprogram, hruns⟩ := sortedVars_runs (points := points) hA
    (constructor.selectors.map selectorVar)
    (fun var hvar => by
      obtain ⟨selector, hselector, rfl⟩ := List.mem_map.mp hvar
      exact hvalid selector hselector) hinner
  have hlistRuns : Runs points (ListState.step .start (sortedVarStep version) none)
      (ListState.closed .start) (inner ++ [.parenClose])
      (do
        let handled ← program
        tick points .parenClose
        pure handled)
      fun handled => pure (.done (#[] ++ handled.toArray)) :=
    Runs.append (hruns #[]) fun handled =>
      Runs.token (program := pure handled)
        (next := fun handled => pure (.done (#[] ++ handled.toArray)))
        (by simp [ListState.step, ListState.between])
  have hembed := Runs.embed (outer := constructorStep version)
    (fun state => ConstructorState.selectors symbol state)
    (fun selectors => pure (.done (symbol, (Grammar.Multiple.NamedValues.Internal.new selectors))))
    (fun state token => by
      simp only [constructorStep]
      congr 1
      funext step
      cases step <;> rfl) hlistRuns
  refine ⟨do
      tick points (.symbol symbol)
      let handled ← program
      tick points .parenClose
      pure (symbol, (Grammar.Multiple.NamedValues.Internal.new handled.toArray)), ?_, ?_⟩
  · simp only [constructorAfterOpen, adaptRun_bind, ← hsymbol,
      adaptRun_take (token := .symbol symbol) rfl, adaptRun_take (token := .parenClose) rfl,
      selectors_eq, ← hprogram]
    simp [Bridge.constructor, specPairs_toArray]
  · refine (Runs.append (first := [.symbol symbol])
      (middle := fun _ => ConstructorState.selectors symbol (ListState.closed .start))
      (Runs.token_more (state := ConstructorState.opened)
        (by simp [constructorStep, Parser.Category.Token.Internal.expectSymbol])) fun _ =>
      Runs.map_program (f := fun handled => ((symbol, (Grammar.Multiple.NamedValues.Internal.new
        (#[] ++ handled.toArray))) :
          Lexicon.Value.Symbol × Grammar.Multiple.SortedVars _))
        (hembed.congr rfl (by funext; simp [Parser.Internal.Step.wrap]))).congr ?_ rfl
    simp

/-- The constructor parser reads `(` ⟨symbol⟩ ⟨selector_dec⟩∗ `)`. -/
theorem constructor_element (hA : TermAgrees h) :
    ElementRuns points (constructorStep version) .start Tree.ConstructorDec.tokens
      (Tree.ConstructorDec.Valid (Bridge.version version))
      (fun constructor => adaptRun (do
        take points .parenOpen
        constructorAfterOpen points h constructor))
      Bridge.constructor := by
  intro constructor hvalid tokens hs
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
  have hclose : Stands [Parser.Internal.Input.parenClose]
      [.parenClose] := Stands.cons rfl Stands.nil
  have hinner' := Stands.append hinner hclose
  rw [List.cons_append] at hinner'
  obtain ⟨program, hprogram, hruns⟩ := constructor_runs_opened (points := points) hA constructor
    hvalid hinner'
  refine ⟨⟨_, _, rfl, by simp⟩, do tick points .parenOpen; program, ?_, ?_⟩
  · simp [adaptRun_take (token := .parenOpen) rfl, ← hprogram]
  · exact Runs.append (first := [.parenOpen]) (middle := fun _ => ConstructorState.opened)
      (Runs.token_more (by simp [constructorStep,
          Parser.Category.Token.Internal.expectOpen])) fun _ => hruns

end

end BSmtLib.Facts.Proofs.Parser.Commands.Parts
