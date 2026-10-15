module

public import BSmtLib.Facts.Proofs.Parser.Category.CursorS
public import BSmtLib.Facts.Proofs.Parser.Sort
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Ident
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# The identifier and sort parsers' steps, keeping where they stop

The lemmas of `Facts.Proofs.Parser.Sort`, for `RunsS`: the same runs, now also saying that the
steps raise no syntax error on the tokens of a valid identifier or sort.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.StepsSort

open BSmtLibSpec.Grammar
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.Ident.Internal (IdentState)
open BSmtLib.Parser.Category.Sort.Internal (SortState SortMode SortLevel sortStep sortComplete)
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser.Equations (sort_nil sort_cons)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Lemmas
open BSmtLib.Facts.Proofs.Parser.Reserved BSmtLib.Facts.Proofs.Parser.SExpr
open BSmtLib.Facts.Proofs.Parser.Tokens BSmtLib.Facts.Proofs.Parser.Tokens.Stands
open BSmtLib.Facts.Proofs.Parser.Category.Steps
open BSmtLib.Facts.Proofs.Parser.«Sort» (sortPush sortComplete_eq identifier_tokens_indexed
  Stands.indexed)

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {points : Points (StateT H m)} {version : Token.Version}

/-! ## Identifiers -/

/--
From the state after an identifier's symbol, the identifier parser reads the tokens of indices
and appends them to those found so far.
-/
theorem indices_runs : (indices : List Tree.Index) →
    (∀ index ∈ indices, index.Valid (Bridge.version version)) →
    ∀ {tokens : List Parser.Internal.Input}, Stands tokens (indices.flatMap Tree.Index.tokens) →
    ∀ (symbol : Plain.Symbol) (found : Array Nodes.Index),
    ∃ parsed : Array Nodes.Index, parsed.toList.map Bridge.index = indices ∧
      RunsS points (IdentState.step (H := H) version) (.indices symbol found) tokens
        (ticks points tokens) fun _ => pure (.more (.indices symbol (found ++ parsed)))
  | [], _, _, hs, symbol, found => by
    have := Stands.eq_nil hs
    subst this
    exact ⟨#[], rfl, (RunsS.nil () (by simp)).congr (by simp) rfl⟩
  | first :: rest, hvalid, _, hs, symbol, found => by
    simp only [List.flatMap_cons] at hs
    obtain ⟨tokens₁, tokens₂, rfl, hs₁, hs₂⟩ := Stands.split hs
    have hrest := fun index hindex => hvalid index (List.mem_cons_of_mem _ hindex)
    cases first with
    | numeral digits =>
      obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs₁
      obtain ⟨view, rfl, rfl⟩ := Parser.Internal.Input.received_numeral htoken
      obtain ⟨parsed, hmap, hruns⟩ :=
        indices_runs rest hrest hs₂ symbol (found.push (.numeral view))
      refine ⟨#[.numeral view] ++ parsed, by simp [hmap, Bridge.index], ?_⟩
      refine (RunsS.append (middle := fun _ => .indices symbol (found.push (.numeral view)))
        (RunsS.token_more (by simp [IdentState.step])) fun _ => hruns).congr ?_ ?_
      · simp
      · funext
        simp
    | symbol name =>
      have hversion := hvalid (.symbol name) (List.mem_cons_self ..)
      obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs₁
      obtain ⟨index, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
      obtain ⟨parsed, hmap, hruns⟩ :=
        indices_runs rest hrest hs₂ symbol (found.push (.symbol index))
      refine ⟨#[.symbol index] ++ parsed, by simp [hmap, Bridge.index], ?_⟩
      refine (RunsS.append (middle := fun _ => .indices symbol (found.push (.symbol index)))
        (RunsS.token_more (by simp [IdentState.step,
          versionAtLeast_v2_5 (by simpa [Tree.Index.Valid] using hversion)]))
        fun _ => hruns).congr ?_ ?_
      · simp
      · funext
        simp

/--
From the state after `(` `_`, the identifier parser reads the symbol, the indices and the `)`
of an indexed identifier, and ends with it.
-/
theorem indexed_runs {name : Tree.Symbol} {indices : List Tree.Index}
    (hvalid : ∀ index ∈ indices, index.Valid (Bridge.version version)) (hne : indices ≠ [])
    {symbolToken : Parser.Internal.Input} {tokens : List Parser.Internal.Input}
    (hsymbol : Bridge.received symbolToken = some (.token (.symbol name)))
    (hs : Stands tokens (indices.flatMap Tree.Index.tokens)) :
    ∃ head : Nodes.Ident, Bridge.identifier head = ⟨name, indices⟩ ∧
      RunsS points (IdentState.step (H := H) version) .afterUnderscore
        (symbolToken :: (tokens ++ [.parenClose]))
        (ticks points (symbolToken :: (tokens ++ [.parenClose])))
        fun _ => pure (.done head) := by
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbol
  obtain ⟨parsed, hmap, hruns⟩ := indices_runs (H := H) (points := points) indices hvalid hs
    symbol #[]
  have hparsed : parsed.isEmpty = false := by
    cases parsed using Array.recOn with
    | mk list => cases list <;> simp_all
  refine ⟨⟨symbol, #[] ++ parsed⟩, by simp [Bridge.identifier, hmap], ?_⟩
  have hclose : RunsS points (IdentState.step (H := H) version)
      (.indices symbol (#[] ++ parsed)) [.parenClose] (do tick points .parenClose; pure ())
      fun _ => pure (.done ⟨symbol, #[] ++ parsed⟩) :=
    RunsS.token (by simp [IdentState.step, hparsed])
  refine (RunsS.append (middle := fun _ => .indices symbol #[])
    (RunsS.token_more (state := .afterUnderscore) (token := .symbol symbol)
      (by simp [IdentState.step])) fun _ =>
      RunsS.append hruns fun _ => hclose).congr ?_ rfl
  simp [ticks_append]

variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

/--
From the state after an application's `(`, the sort parser reads the tokens of its head, an
identifier, and opens the application.
-/
theorem head_runs {name : Tree.Identifier} (hname : name.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input} (hs : Stands tokens name.tokens)
    (levels : List (SortLevel (Traits.Handler.«Sort» H))) :
    ∃ head : Nodes.Ident, Bridge.identifier head = name ∧
      RunsS points (sortStep version) { mode := .opened, levels } tokens
        (ticks points tokens)
        fun _ => pure (.more { mode := .start, levels := ⟨head, #[]⟩ :: levels }) := by
  match name with
  | ⟨symbolName, []⟩ =>
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
    refine ⟨⟨symbol, #[]⟩, by simp [Bridge.identifier], ?_⟩
    exact (RunsS.token_more (step := sortStep version) (state := { mode := .opened, levels })
      (token := .symbol symbol) (by simp [Parser.Category.«Sort».Internal.sortStep.eq_def])).congr
          (by simp) rfl
  | ⟨symbolName, index :: indices⟩ =>
    obtain ⟨symbolToken, rest, rfl, hsymbol, hrest⟩ := Stands.indexed (List.cons_ne_nil _ _) hs
    obtain ⟨head, hhead, hruns⟩ := indexed_runs (H := H) (points := points) hname
      (List.cons_ne_nil _ _) hsymbol hrest
    refine ⟨head, hhead, ?_⟩
    have hembed := RunsS.embed (outer := sortStep version)
      (fun state => ({ mode := .startingIdent state, levels } : SortState _))
      (fun head => pure (.more { mode := .start, levels := ⟨head, #[]⟩ :: levels }))
      (fun state token => by
        simp only [Parser.Category.«Sort».Internal.sortStep.eq_def]
        congr 1
        funext step
        cases step <;> rfl)
      (RunsS.append (middle := fun _ => IdentState.afterUnderscore)
        (RunsS.token_more (step := IdentState.step (H := H) version) (state := .opened)
          (token := .reserved (.general .underscore)) (by simp [IdentState.step]))
        fun _ => hruns)
    refine (RunsS.append (middle := fun _ => ({ mode := .startingIdent .opened, levels } :
        SortState _))
      (RunsS.token_more (step := sortStep version) (state := { mode := .opened, levels })
        (token := .parenOpen) (by simp [Parser.Category.«Sort».Internal.sortStep.eq_def])) fun _ =>
            hembed).congr ?_ ?_
    · simp
    · funext
      simp [Parser.Internal.Step.wrap]

mutual

/--
From any stack of open applications, the sort parser reads the tokens of a sort with the
traversal's effects, then completes the sort on that stack.
-/
theorem sort_runs (hA : TermAgrees h) : (sort : Tree.«Sort») → sort.Valid (Bridge.version version) →
    ∀ {tokens : List Parser.Internal.Input}, Stands tokens sort.tokens →
    ∀ levels : List (SortLevel (Traits.Handler.«Sort» H)),
    RunsS points (sortStep version) { mode := .start, levels } tokens
      (adaptRun (Traversal.sort points h sort))
      fun r => pure (sortPush levels r)
  | .mk ⟨symbolName, []⟩ [], _, _, hs, levels => by
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
    refine (RunsS.token (step := sortStep version) (state := { mode := .start, levels })
      (token := .symbol symbol)
      (program := Parser.Internal.call (Traits.Handler.handleSort ⟨symbol, #[]⟩ (.new #[])))
      (by simp [Parser.Category.«Sort».Internal.sortStep.eq_def, sortComplete_eq])).congr ?_ rfl
    simp [sort_nil, Tree.Identifier.tokens, adaptRun_takeAll (Stands.cons htoken nil),
      hA.handleSort,
      Bridge.identifier]
  | .mk ⟨symbolName, index :: indices⟩ [], hvalid, _, hs, levels => by
    obtain ⟨symbolToken, rest, rfl, hsymbol, hrest⟩ := Stands.indexed (List.cons_ne_nil _ _) hs
    obtain ⟨head, hhead, hruns⟩ := indexed_runs (H := H) (points := points) hvalid.1
      (List.cons_ne_nil _ _) hsymbol hrest
    have hembed := RunsS.embed (outer := sortStep version)
      (fun state => ({ mode := .identOnly state, levels } : SortState _))
      (fun head => sortComplete levels head #[])
      (fun state token => by
        simp only [Parser.Category.«Sort».Internal.sortStep.eq_def]
        congr 1
        funext step
        cases step <;> rfl)
      hruns
    have hident := RunsS.bind_next
      (following := fun _ => Parser.Internal.call (Traits.Handler.handleSort head (.new #[])))
      (next := fun r => pure (sortPush levels r)) (hembed.congr rfl (by
        funext
        simp [Parser.Internal.Step.wrap, sortComplete_eq]))
    refine (RunsS.append (middle := fun _ => ({ mode := .opened, levels } : SortState _))
      (RunsS.token_more (step := sortStep version) (state := { mode := .start, levels })
        (token := .parenOpen) (by simp [Parser.Category.«Sort».Internal.sortStep.eq_def])) fun _ =>
        RunsS.append (middle := fun _ => ({ mode := .identOnly .afterUnderscore, levels } :
            SortState _))
          (RunsS.token_more (step := sortStep version) (state := { mode := .opened, levels })
            (token := .reserved (.general .underscore))
            (by simp [Parser.Category.«Sort».Internal.sortStep.eq_def])) fun _ => hident).congr ?_ rfl
    simp [sort_nil, adaptRun_takeAll
      (show Stands _ (Tree.Identifier.tokens ⟨symbolName, index :: indices⟩) from hs),
      hA.handleSort, hhead, ticks_append]
  | .mk name (first :: rest), hvalid, _, hs, levels => by
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    obtain ⟨headTokens, argumentTokens, rfl, hsHead, hsArguments⟩ := Stands.split hinner
    obtain ⟨head, hhead, hheadRuns⟩ := head_runs (H := H) (points := points) hvalid.1 hsHead
      levels
    obtain ⟨firstTokens, restTokens, rfl, hs₁, hs₂⟩ := Stands.split hsArguments
    have hclose : ∀ r (handled : List (Traits.Handler.«Sort» H)),
        RunsS points (sortStep version)
          { mode := .start, levels := ⟨head, #[].push r ++ handled.toArray⟩ :: levels }
          [.parenClose]
          (do tick points .parenClose
              Parser.Internal.call (Traits.Handler.handleSort head (.new
                (#[].push r ++ handled.toArray))))
          fun r => pure (sortPush levels r) :=
      fun r handled => RunsS.token (by simp [Parser.Category.«Sort».Internal.sortStep.eq_def,
          sortComplete_eq])
    have hargs := RunsS.append (middle := fun r =>
        ({ mode := .start, levels := ⟨head, #[].push r⟩ :: levels } : SortState _))
      (sort_runs hA first hvalid.2.1 hs₁ (⟨head, #[]⟩ :: levels)) fun r =>
        RunsS.append (sorts_runs hA rest hvalid.2.2 hs₂ head (#[].push r) levels) fun handled =>
          hclose r handled
    rw [show Parser.Internal.Input.parenOpen :: (headTokens ++
        (firstTokens ++ restTokens) ++ [.parenClose]) =
      [.parenOpen] ++ (headTokens ++ (firstTokens ++ (restTokens ++ [.parenClose]))) by simp]
    refine (RunsS.append (middle := fun _ => ({ mode := .opened, levels } : SortState _))
      (RunsS.token_more (step := sortStep version)
        (state := { mode := .start, levels }) (token := .parenOpen)
        (by simp [Parser.Category.«Sort».Internal.sortStep.eq_def])) fun _ =>
        RunsS.append hheadRuns fun _ => hargs).congr ?_ rfl
    simp [sort_cons, Traversal.sorts, adaptRun_take (token := .parenOpen) rfl,
      adaptRun_take (token := .parenClose) rfl, adaptRun_takeAll hsHead, hA.handleSort, hhead]

/--
From a stack whose innermost application has the arguments found so far, the sort parser reads
the tokens of sorts with the traversal's effects, and appends them to those arguments.
-/
theorem sorts_runs (hA : TermAgrees h) : (sorts : List Tree.«Sort») →
    Tree.«Sort».ValidAll (Bridge.version version) sorts →
    ∀ {tokens : List Parser.Internal.Input}, Stands tokens (Tree.«Sort».tokensAll sorts) →
    ∀ (head : Nodes.Ident) (found : Array (Traits.Handler.«Sort» H))
      (levels : List (SortLevel (Traits.Handler.«Sort» H))),
    RunsS points (sortStep version)
      { mode := .start, levels := ⟨head, found⟩ :: levels } tokens
      (adaptRun (Traversal.sorts points h sorts))
      fun handled =>
        pure (.more { mode := .start, levels := ⟨head, found ++ handled.toArray⟩ :: levels })
  | [], _, _, hs, head, found, levels => by
    have := Stands.eq_nil hs
    subst this
    exact (RunsS.nil [] (by simp)).congr (by simp [Traversal.sorts]) rfl
  | first :: rest, hvalid, _, hs, head, found, levels => by
    obtain ⟨tokens₁, tokens₂, rfl, hs₁, hs₂⟩ := Stands.split hs
    have htail : ∀ r, RunsS points (sortStep version)
        { mode := .start, levels := ⟨head, found.push r⟩ :: levels } tokens₂
        ((r :: ·) <$> adaptRun (Traversal.sorts points h rest))
        fun handled =>
          pure (.more { mode := .start, levels := ⟨head, found ++ handled.toArray⟩ :: levels }) :=
      fun r => RunsS.map_program ((sorts_runs hA rest hvalid.2 hs₂ head (found.push r)
        levels).congr rfl (by funext handled; simp))
    refine (RunsS.append
      (middle := fun r => { mode := .start, levels := ⟨head, found.push r⟩ :: levels })
      (sort_runs hA first hvalid.1 hs₁ _) htail).congr ?_ rfl
    simp [Traversal.sorts]

end

end

end BSmtLib.Facts.Proofs.Parser.Category.StepsSort
