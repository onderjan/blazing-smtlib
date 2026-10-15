module

public import BSmtLib.Facts.Proofs.Parser.Commands.Parts
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Command.Internal.Datatype
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# Datatype declarations against the traversal

A datatype declaration in either form: `(` ⟨constructor_dec⟩+ `)`, whose start comes at the `(`
of its first constructor, and `(` `par` `(` ⟨symbol⟩+ `)` `(` ⟨constructor_dec⟩+ `)` `)`, whose
start comes at the `)` of its parameters. The parser's checks that there are parameters and
constructors are decided by the length of the programs' values.

Lists of symbols and of sort declarations hand over only views of their tokens, so their
programs are the ticks of the tokens, and their values the views.
-/

namespace BSmtLib.Facts.Proofs.Parser.Commands.Datatypes

open BSmtLibSpec.Grammar
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.Combinator.Internal (ListState)
open BSmtLib.Parser.Command.Internal.Datatype
    (DatatypeState ConstructorState datatypeStep constructorStep
    SortDecState)
open BSmtLib.Parser.Category.Token.Internal (symbolStep)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Commands.Elements
open BSmtLib.Facts.Proofs.Parser.Commands.Elements.Runs BSmtLib.Facts.Proofs.Parser.Commands.Parts
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Lemmas
open BSmtLib.Facts.Proofs.Parser.List BSmtLib.Facts.Proofs.Parser.Reserved
open BSmtLib.Facts.Proofs.Parser.Tokens BSmtLib.Plain

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser.Equations (datatype_plain datatype_par)

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {points : Points (StateT H m)} {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

/-! ## Symbols and sort declarations -/

/-- The symbols, from between elements: their views, appended to those found so far. -/
theorem symbols_runs : (names : List Tree.Symbol) → ∀ {tokens : List Parser.Internal.Input},
    Stands tokens (names.map .symbol) →
    ∃ symbols : List Nodes.Symbol, symbols.map Bridge.symbol = names ∧
      tokens = symbols.map .symbol ∧
      ∀ found : Array Nodes.Symbol,
      Runs points (ListState.step (H := H) () symbolStep none) (ListState.between () found) tokens
        (ticks points tokens) fun _ => pure (.more
            (ListState.between () (found ++ symbols.toArray)))
  | [], _, hs => by
    have := Stands.eq_nil hs
    subst this
    exact ⟨[], rfl, rfl, fun found => (Runs.nil () (by simp)).congr (by simp) rfl⟩
  | name :: names, _, hs => by
    obtain ⟨token, rest, rfl, htoken, hrest⟩ := Stands.split_cons hs
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
    obtain ⟨symbols, hsymbols, rfl, hruns⟩ := symbols_runs names hrest
    refine ⟨symbol :: symbols, by simp [hsymbols], rfl, fun found => ?_⟩
    have hitem := ListState.item_runs_done (H := H) (points := points) (maximum := none)
      (inner := symbolStep) (init := ()) found (token := .symbol symbol) (tokens := [])
      (by simp) (by simp)
      (Runs.token (program := pure symbol) (by simp [symbolStep,
          Parser.Category.Token.Internal.expectSymbol]))
    refine (Runs.append (first := [.symbol symbol]) (Runs.of_bind_pure (value := symbol)
      (next := fun r => pure (.more (ListState.between () (found.push r)))) hitem) fun _ =>
      hruns (found.push symbol)).congr ?_ (by funext; simp)
    simp

/-- The sort declarations, from between elements: their views. -/
theorem sortDecs_runs : (sortDecs : List Tree.SortDec) → ∀ {tokens : List Parser.Internal.Input},
    Stands tokens (sortDecs.flatMap Tree.SortDec.tokens) →
    ∃ views : List (Nodes.Symbol × NumeralView),
      views.map (fun (symbol, arity) => (Bridge.symbol symbol, Bridge.chars arity.asSlice)) =
        sortDecs.map (fun sortDec => (sortDec.symbol, sortDec.arity)) ∧
      views.length = sortDecs.length ∧
      ∀ found : Array (Nodes.Symbol × NumeralView),
      Runs points (ListState.step (H := H) .start SortDecState.step none)
        (ListState.between .start found) tokens
        (ticks points tokens) fun _ => pure (.more
            (ListState.between .start (found ++ views.toArray)))
  | [], _, hs => by
    have := Stands.eq_nil hs
    subst this
    exact ⟨[], rfl, rfl, fun found => (Runs.nil () (by simp)).congr (by simp) rfl⟩
  | sortDec :: sortDecs, _, hs => by
    simp only [List.flatMap_cons] at hs
    obtain ⟨first, rest, rfl, hs₁, hs₂⟩ := Stands.split hs
    obtain ⟨symbol, arity, first', rfl, hview, hruns⟩ := sortDec_runs (points := points) sortDec hs₁
    obtain ⟨views, hviews, hlength, hrestRuns⟩ := sortDecs_runs sortDecs hs₂
    refine
        ⟨(symbol, arity) :: views, by simp only [List.map_cons, hviews, hview], by simp [hlength],
      fun found => ?_⟩
    have hitem := ListState.item_runs_done (H := H) (points := points) (maximum := none)
      (inner := SortDecState.step) (init := .start) found (by simp) (by simp)
      (Runs.bind_next (following := fun _ => pure (symbol, arity))
        (hruns.congr rfl (by funext; simp)))
    refine (Runs.append (Runs.of_bind_pure (value := (symbol, arity))
      (next := fun (r : Nodes.Symbol × NumeralView) =>
        pure (.more (ListState.between .start (found.push r)))) hitem) fun _ =>
      hrestRuns (found.push (symbol, arity))).congr ?_
      (by funext; simp)
    simp [ticks_append]
/-! ## The datatype parser -/

/-- The sort of the handler. -/
local notation "S" => Traits.Handler.«Sort» H

/-- What the datatype parser does when its constructors end. -/
def constructorsDone (parametric : Bool) (constructors : Array (Nodes.Constructor S)) :
    PM H (Parser.Internal.Step (DatatypeState S) (Array (Nodes.Constructor S))) := do
  if constructors.isEmpty then Parser.Internal.syntaxError .emptyDatatypeConstructors
  if parametric then return .more (.close constructors)
  else return .done constructors

/-- What the datatype parser does when its parameters end. -/
def parametersDone (start : Array Nodes.Symbol → PM H Unit) (parameters : Array Nodes.Symbol) :
    PM H (Parser.Internal.Step (DatatypeState S) (Array (Nodes.Constructor S))) := do
  if parameters.isEmpty then Parser.Internal.syntaxError .emptyDatatypeParameters
  start parameters
  return .more .constructorsOpen

omit [LawfulMonad m] in
theorem datatypeStep_constructors (start : Array Nodes.Symbol → PM H Unit) (parametric : Bool)
    (state : ListState (ConstructorState S) (Nodes.Constructor S)) (token : Parser.Internal.Input) :
    datatypeStep start version (.constructors parametric state) token =
      state.step .start (constructorStep version) none token >>=
        Parser.Internal.Step.wrap (.constructors parametric) (constructorsDone parametric) := by
  simp only [datatypeStep]
  congr 1
  funext step
  cases step <;> rfl

omit [LawfulMonad m] in
theorem datatypeStep_parameters (start : Array Nodes.Symbol → PM H Unit)
    (state : ListState Unit Nodes.Symbol) (token : Parser.Internal.Input) :
    datatypeStep start version (.parameters state) token =
      state.step () symbolStep none token >>= Parser.Internal.Step.wrap DatatypeState.parameters
        (parametersDone start) := by
  simp only [datatypeStep]
  congr 1
  funext step
  cases step <;> rfl

variable (start : Array Nodes.Symbol → PM H Unit)
variable {start' : List Tree.Symbol → Run (StateT H m) (Traits.Handler.Error H) Unit}

/-- A datatype declaration without `par`. -/
theorem datatype_plain_runs (hA : TermAgrees h)
    (hstart : ∀ parameters : Array Nodes.Symbol,
      start parameters = adaptRun (start' (parameters.toList.map Bridge.symbol)))
    (first : Tree.ConstructorDec) (rest : List Tree.ConstructorDec)
    (hvalid : ∀ constructor ∈ first :: rest, constructor.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input} (hs : Stands tokens (Tree.DatatypeDec.tokens ⟨[],
        first :: rest⟩)) :
    ∃ program : PM H (Array (Nodes.Constructor S)),
      (fun cs => cs.toList.map Bridge.constructor) <$> program =
        adaptRun (Traversal.datatype points h start' ⟨[], first :: rest⟩) ∧
      Runs points (datatypeStep start version) .start tokens program
        fun cs => pure (.done cs) := by
  change Stands tokens (paren (first.tokens ++ rest.flatMap Tree.ConstructorDec.tokens)) at hs
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
  obtain ⟨firstTokens, restTokens, rfl, hs₁, hs₂⟩ := Stands.split hinner
  obtain ⟨firstInner, rfl, hfirstInner⟩ := Stands.split_paren hs₁
  have hclose : Stands [Parser.Internal.Input.parenClose]
      [.parenClose] := Stands.cons rfl Stands.nil
  have hfirstInner' := Stands.append hfirstInner hclose
  rw [List.cons_append] at hfirstInner'
  obtain ⟨program, hprogram, hruns⟩ := constructor_runs_opened (points := points) hA first
    (hvalid first (List.mem_cons_self ..)) hfirstInner'
  obtain ⟨others, hothers, -, hothersRuns⟩ := items_runs (maximum := none)
    (constructor_element (points := points) (version := version) hA) rest
    (fun c hc => hvalid c (List.mem_cons_of_mem _ hc)) hs₂
  have hfirstList := Runs.embed
    (outer := ListState.step .start (constructorStep version) none)
    (fun state => ({ opened := true, outside := false, inner := state, items := #[] } :
      ListState (ConstructorState S) (Nodes.Constructor S)))
    (fun c => pure (.more (ListState.between .start (#[].push c))))
    (ListState.step_inside #[]) hruns
  have hfirstDatatype := Runs.embed (outer := datatypeStep start version)
    (DatatypeState.constructors false) (constructorsDone false)
    (datatypeStep_constructors start false) hfirstList
  have hothersDatatype : ∀ c : Nodes.Constructor S, Runs points (datatypeStep start version)
      (.constructors false (ListState.between .start (#[].push c))) restTokens others
      fun cs => pure (.more (.constructors false
        (ListState.between .start ((#[].push c) ++ (cs : List _).toArray)))) := fun c =>
    (Runs.embed (outer := datatypeStep start version)
      (DatatypeState.constructors false) (constructorsDone false)
      (datatypeStep_constructors start false)
      (hothersRuns (#[].push c) (by simp))).congr rfl (by funext; simp [Parser.Internal.Step.wrap])
  refine ⟨do
      tick points .parenOpen
      tick points .parenOpen
      start #[]
      let c ← program
      let cs ← others
      tick points .parenClose
      pure ((#[].push c) ++ cs.toArray), ?_, ?_⟩
  · rw [datatype_plain]
    simp only [adaptRun_bind, takeAll, Traversal.constructors,
      adaptRun_mapM, adaptRun_take (token := .parenOpen) rfl,
      adaptRun_take (token := .parenClose) rfl] at hothers ⊢
    simp [← hothers, ← hprogram, hstart, adaptRun_take (token := .parenOpen) rfl]
  · rw [show Parser.Internal.Input.parenOpen :: (Parser.Internal.Input.parenOpen ::
      (firstInner ++ [.parenClose]) ++ restTokens ++
        [.parenClose]) =
      [.parenOpen] ++ ([.parenOpen] ++ ((firstInner ++ [.parenClose]) ++ (restTokens ++
        [.parenClose]))) by simp]
    refine (Runs.append (middle := fun _ => (.kind : DatatypeState S))
      (Runs.token_more (by simp [datatypeStep, Parser.Category.Token.Internal.expectOpen])) fun _ =>
      Runs.append (middle := fun _ => (.constructors false
          { opened := true, outside := false, inner := .opened, items := #[] } : DatatypeState S))
        (Runs.token (program := start #[]) (by simp [datatypeStep])) fun _ =>
      Runs.append (middle := fun c => (.constructors false (ListState.between .start (#[].push c)) :
          DatatypeState S))
        (hfirstDatatype.congr rfl (by funext; simp [Parser.Internal.Step.wrap])) fun c =>
      Runs.append (hothersDatatype c) fun cs =>
        Runs.token (program := pure ((#[].push c) ++ (cs : List _).toArray))
          (next := fun cs => pure (.done cs)) (by
            rw [datatypeStep_constructors]
            simp [ListState.step, ListState.between, constructorsDone,
                Parser.Internal.Step.wrap])).congr ?_ rfl
    simp
theorem datatype_par_tokens (parameter : Tree.Symbol) (parameters : List Tree.Symbol)
    (constructors : List Tree.ConstructorDec) :
    Tree.DatatypeDec.tokens ⟨parameter :: parameters, constructors⟩ =
      paren (word "par" :: paren ((parameter :: parameters).map .symbol) ++
        paren (constructors.flatMap Tree.ConstructorDec.tokens)) := rfl

/-- A datatype declaration with `par`. -/
theorem datatype_par_runs (hA : TermAgrees h)
    (hstart : ∀ parameters : Array Nodes.Symbol,
      start parameters = adaptRun (start' (parameters.toList.map Bridge.symbol)))
    (parameter : Tree.Symbol) (parameters : List Tree.Symbol)
    (constructors : List Tree.ConstructorDec) (hne : constructors ≠ [])
    (hvalid : ∀ constructor ∈ constructors, constructor.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (Tree.DatatypeDec.tokens ⟨parameter :: parameters, constructors⟩)) :
    ∃ program : PM H (Array (Nodes.Constructor S)),
      (fun cs => cs.toList.map Bridge.constructor) <$> program =
        adaptRun (Traversal.datatype points h start' ⟨parameter :: parameters, constructors⟩) ∧
      Runs points (datatypeStep start version) .start tokens program
        fun cs => pure (.done cs) := by
  rw [datatype_par_tokens] at hs
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
  obtain ⟨parToken, rest, rfl, hparToken, hrest⟩ := Stands.split_cons hinner
  rw [Parser.Internal.Input.received_word (word := .general .par) hparToken]
  obtain ⟨parameterList, constructorList, rfl, hparameterList, hconstructorList⟩ :=
    Stands.split hrest
  obtain ⟨parameterInner, rfl, hparameterInner⟩ := Stands.split_paren hparameterList
  obtain ⟨constructorInner, rfl, hconstructorInner⟩ := Stands.split_paren hconstructorList
  obtain ⟨symbols, hsymbols, rfl, hsymbolsRuns⟩ := symbols_runs (H := H) (points := points)
    (parameter :: parameters) hparameterInner
  obtain ⟨symbol, symbols, rfl⟩ : ∃ symbol rest, symbols = symbol :: rest := by
    cases symbols with
    | nil => simp at hsymbols
    | cons symbol rest => exact ⟨symbol, rest, rfl⟩
  have hparametersList : Runs points (ListState.step () symbolStep none) (ListState.paren ())
      (.parenOpen :: ((symbol :: symbols).map .symbol ++ [.parenClose]))
      (ticks points (.parenOpen :: ((symbol :: symbols).map .symbol ++ [.parenClose])))
      fun _ => pure (.done (#[] ++ (symbol :: symbols).toArray)) := by
    refine (Runs.append (first := [.parenOpen]) ListState.open_runs fun _ =>
      Runs.append (hsymbolsRuns #[]) fun _ =>
        Runs.token (program := pure ())
          (next := fun _ => pure (.done (#[] ++ (symbol :: symbols).toArray)))
          (by simp [ListState.step, ListState.between])).congr ?_ rfl
    simp [ticks_append]
  have hparametersDatatype := Runs.bind_next
    (following := fun _ => start (#[] ++ (symbol :: symbols).toArray))
    (next := fun _ => pure (.more (DatatypeState.constructorsOpen : DatatypeState S)))
    ((Runs.embed (outer := datatypeStep start version) DatatypeState.parameters
      (parametersDone start) (datatypeStep_parameters start) hparametersList).congr rfl
      (by funext; simp [Parser.Internal.Step.wrap, parametersDone]))
  obtain ⟨found, hfound, hfoundLength, hfoundRuns⟩ := closedList_runs (maximum := none)
    (constructor_element (points := points) (version := version) hA) constructors hvalid
    hconstructorInner (by simp)
  have hconstructorsDatatype := Runs.congr_length (Runs.embed (outer := datatypeStep start version)
    (DatatypeState.constructors true) (constructorsDone true)
    (datatypeStep_constructors start true) hfoundRuns)
      (HasLength.bind_pure hfoundLength _)
      (next' := fun l => pure (.more (DatatypeState.close l.toArray)))
      (fun l hl => by
        have : l ≠ [] := by
          rintro rfl
          exact hne (List.length_eq_zero_iff.mp hl.symm)
        simp [Parser.Internal.Step.wrap, constructorsDone, this])
  refine ⟨do
      tick points .parenOpen
      tick points (.reserved (.general .par))
      ticks points (.parenOpen :: ((symbol :: symbols).map .symbol ++ [.parenClose]))
      start (#[] ++ (symbol :: symbols).toArray)
      tick points .parenOpen
      let cs ← (do let l ← found; tick points .parenClose; pure l)
      tick points .parenClose
      pure cs.toArray, ?_, ?_⟩
  · rw [datatype_par]
    simp only [adaptRun_bind, Traversal.constructors, adaptRun_mapM,
      adaptRun_take (token := .parenOpen) rfl, adaptRun_take (token := .parenClose) rfl]
      at hfound ⊢
    rw [adaptRun_takeAll hparameterInner, ← hsymbols]
    simp [takeAll, ← hfound, hstart, ticks_append, adaptRun_take (token := .parenOpen) rfl,
      adaptRun_take (token := .parenClose) rfl,
      adaptRun_take (token := .reserved (.general .par)) (syntaxToken := word "par") rfl]
  · rw [show Parser.Internal.Input.parenOpen :: (Parser.Internal.Input.reserved (.general .par) ::
        (Parser.Internal.Input.parenOpen :: ((symbol :: symbols).map .symbol ++ [.parenClose]) ++
          Parser.Internal.Input.parenOpen ::
              (constructorInner ++ [.parenClose])) ++ [.parenClose]) =
      [.parenOpen] ++ ([.reserved (.general .par)] ++
        ((Parser.Internal.Input.parenOpen :: ((symbol :: symbols).map .symbol ++ [.parenClose])) ++
          ([.parenOpen] ++ ((constructorInner ++ [.parenClose]) ++ [.parenClose])))) by simp]
    refine (Runs.append (middle := fun _ => (.kind : DatatypeState S))
      (Runs.token_more (by simp [datatypeStep, Parser.Category.Token.Internal.expectOpen])) fun _ =>
      Runs.append (middle := fun _ => (.parameters (ListState.paren ()) : DatatypeState S))
        (Runs.token_more (by simp [datatypeStep])) fun _ =>
      Runs.append (middle := fun _ => (.constructorsOpen : DatatypeState S))
        hparametersDatatype fun _ =>
      Runs.append (middle := fun _ =>
          (.constructors true (ListState.closed .start) : DatatypeState S))
        (Runs.token_more (by simp [datatypeStep,
            Parser.Category.Token.Internal.expectOpen])) fun _ =>
      Runs.append (middle := fun cs => (.close (cs : List _).toArray : DatatypeState S))
        hconstructorsDatatype fun cs =>
        Runs.token (program := pure (cs : List _).toArray) (next := fun cs => pure (.done cs))
          (by simp [datatypeStep, Parser.Category.Token.Internal.expectClose])).congr ?_ rfl
    simp

/-- A datatype declaration, in either form. -/
theorem datatype_runs (hA : TermAgrees h)
    (hstart : ∀ parameters : Array Nodes.Symbol,
      start parameters = adaptRun (start' (parameters.toList.map Bridge.symbol)))
    (declaration : Tree.DatatypeDec) (hvalid : declaration.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input} (hs : Stands tokens declaration.tokens) :
    (∃ rest, tokens = .parenOpen :: rest) ∧
    ∃ program : PM H (Array (Nodes.Constructor S)),
      (fun cs => cs.toList.map Bridge.constructor) <$> program =
        adaptRun (Traversal.datatype points h start' declaration) ∧
      Runs points (datatypeStep start version) .start tokens program
        fun cs => pure (.done cs) := by
  obtain ⟨hne, hconstructors⟩ := hvalid
  match declaration, hs, hne, hconstructors with
  | ⟨[], first :: rest⟩, hs, _, hconstructors =>
    refine ⟨?_, datatype_plain_runs start hA hstart first rest hconstructors hs⟩
    obtain ⟨inner, rfl, -⟩ := Stands.split_paren hs
    exact ⟨_, rfl⟩
  | ⟨parameter :: parameters, constructors⟩, hs, hne, hconstructors =>
    refine ⟨?_, datatype_par_runs start hA hstart parameter parameters constructors hne
      hconstructors hs⟩
    rw [datatype_par_tokens] at hs
    obtain ⟨inner, rfl, -⟩ := Stands.split_paren hs
    exact ⟨_, rfl⟩

end

end BSmtLib.Facts.Proofs.Parser.Commands.Datatypes
