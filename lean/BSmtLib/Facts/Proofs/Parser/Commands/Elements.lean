module

public import BSmtLib.Facts.Proofs.Parser.Commands.Bytes
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Command.Datatype

@[expose] public section

/-!
# Lists of elements against the traversal

`ListState.step` runs an inner parser for each element of a list up to a `)`. Given what the
inner parser does on one element (`ElementRuns`: from its initial state it reads the element's
tokens with a program whose value, through a bridge, is the spec's, and ends with it), the list
parser reads the tokens of the elements with the programs one after another, collecting the
values. A program's values are lists of a known length (`HasLength`), so that the list parser's
checks of the number of elements are decided by it.

The first token of each element is taken from the state between elements, which steps on it as
the inner parser's initial state does (`Runs.first`), since it is no `)`.
-/

namespace BSmtLib.Facts.Proofs.Parser.Commands.Elements

open BSmtLibSpec.Grammar
open BSmtLib.Parser (PM)
open BSmtLib.Parser.Category.Combinator (ListState)
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.List
open BSmtLib.Facts.Proofs.Parser.«Sort» BSmtLib.Facts.Proofs.Parser.Term
open BSmtLib.Facts.Proofs.Parser.Tokens BSmtLib.Plain

/-! ## First tokens -/

/-- Tokens that stand for tokens starting with one other than `)` start with one other than `)`. -/
theorem Stands.first_ne {tokens : List Parser.Internal.Input}
    {first : BSmtLibSpec.Grammar.SyntaxToken}
    {rest : List BSmtLibSpec.Grammar.SyntaxToken}
    (hs : Stands tokens (first :: rest)) (hfirst : first ≠ .parenClose) :
    ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose := by
  obtain ⟨token, tokens', rfl, htoken, -⟩ := Stands.split_cons hs
  refine ⟨token, tokens', rfl, ?_⟩
  rintro rfl
  simp only [Bridge.received, Option.some.injEq, Received.token.injEq] at htoken
  exact hfirst htoken.symm

theorem identifier_tokens_first (identifier : Tree.Identifier) :
    ∃ first rest, identifier.tokens = first :: rest ∧ first ≠ .parenClose := by
  match identifier with
  | ⟨name, []⟩ => exact ⟨_, _, rfl, by simp⟩
  | ⟨name, index :: indices⟩ =>
    exact ⟨_, _, identifier_tokens_indexed name (List.cons_ne_nil index indices), by simp⟩

theorem sort_first (sort : Tree.«Sort») :
    ∃ first rest, sort.tokens = first :: rest ∧ first ≠ .parenClose := by
  match sort with
  | .mk identifier [] => exact identifier_tokens_first identifier
  | .mk identifier (argument :: arguments) => exact ⟨_, _, rfl, by simp⟩

theorem term_first (term : Tree.Term) :
    ∃ first rest, term.tokens = first :: rest ∧ first ≠ .parenClose := by
  match term with
  | .constant constant => exact ⟨_, _, rfl, by cases constant <;> simp [Tree.SpecConstant.token]⟩
  | .identifier (.plain identifier) => exact identifier_tokens_first identifier
  | .identifier (.as _ _) | .application _ _ | .let _ _ | .lambda _ _ | .quantified _ _ _
  | .match _ _ | .annotated _ _ => exact ⟨_, _, rfl, by simp⟩

theorem Stands.first_of {tokens : List Parser.Internal.Input}
    {syntaxTokens : List BSmtLibSpec.Grammar.SyntaxToken}
    (hfirst : ∃ first rest, syntaxTokens = first :: rest ∧ first ≠ .parenClose)
    (hs : Stands tokens syntaxTokens) :
    ∃ token tokens', tokens = token :: tokens' ∧ token ≠ .parenClose := by
  obtain ⟨first, rest, rfl, hne⟩ := hfirst
  exact Stands.first_ne hs hne

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {points : Points (StateT H m)} {σ ρ X Y : Type}

/-! ## Programs whose values have a known length -/

/--
The program's values are lists of the length: what follows it may be changed on other lists.
A list parser's checks of the number of elements are decided by this.
-/
def HasLength {α : Type} (program : PM H (List α)) (length : Nat) : Prop :=
  ∀ {β : Type} (K K' : List α → PM H β), (∀ l, l.length = length → K l = K' l) →
    program >>= K = program >>= K'

theorem HasLength.nil {α : Type} : HasLength (pure [] : PM H (List α)) 0 := by
  intro _ K K' hK
  simp [hK [] rfl]

theorem HasLength.cons {α : Type} {first : PM H α} {rest : PM H (List α)} {length : Nat}
    (h : HasLength rest length) :
    HasLength (first >>= fun r => (r :: ·) <$> rest) (length + 1) := by
  intro _ K K' hK
  simp only [bind_assoc, bind_map_left]
  congr 1
  funext r
  exact h (fun l => K (r :: l)) (fun l => K' (r :: l)) fun l hl => hK (r :: l) (by simp [hl])

theorem HasLength.after {α : Type} {program : PM H (List α)} {length : Nat}
    (h : HasLength program length) (effect : PM H Unit) :
    HasLength (effect >>= fun _ => program) length := by
  intro _ K K' hK
  simp only [bind_assoc]
  congr 1
  funext _
  exact h K K' hK

theorem HasLength.bind_pure {α : Type} {program : PM H (List α)} {length : Nat}
    (h : HasLength program length) (effect : PM H Unit) :
    HasLength (program >>= fun l => effect >>= fun _ => pure l) length := by
  intro _ K K' hK
  simp only [bind_assoc, pure_bind]
  exact h (fun l => effect >>= fun _ => K l) (fun l => effect >>= fun _ => K' l)
    fun l hl => by rw [hK l hl]

omit [LawfulMonad m] in
/-- A run goes on as another continuation that agrees on lists of the program's length. -/
theorem Runs.congr_length {τ : Type} {step : τ → Parser.Internal.Input → PM H
    (Parser.Internal.Step τ ρ)} {state : τ}
    {tokens : List Parser.Internal.Input} {α : Type} {program : PM H (List α)} {length : Nat}
    {next next' : List α → PM H
        (Parser.Internal.Step τ ρ)} {arrival : τ → Parser.Internal.Input → PM H Unit}
    (h : Runs points step state tokens program next arrival)
    (hlength : HasLength program length) (hnext : ∀ l, l.length = length → next l = next' l) :
    Runs points step state tokens program next' arrival := by
  intro rest
  rw [h rest]
  exact hlength _ _ fun l hl => by rw [hnext l hl]

/-- A run whose program ends with a value fixed in advance goes on with that value. -/
theorem Runs.of_bind_pure {τ α : Type} {step : τ → Parser.Internal.Input → PM H
    (Parser.Internal.Step τ ρ)} {state : τ}
    {tokens : List Parser.Internal.Input} {program : PM H Unit} {value : α} {next : α → PM H
        (Parser.Internal.Step τ ρ)}
    {arrival : τ → Parser.Internal.Input → PM H Unit}
    (h : Runs points step state tokens (program >>= fun _ => pure value) next arrival) :
    Runs points step state tokens program (fun _ => next value) arrival := by
  intro rest
  rw [h rest]
  simp

/-! ## Elements -/

/--
The inner parser reads an element whose value stands for the spec's through `bridge`: for every
element valid as `valid` says, the tokens that stand for its tokens start with a token other
than `)`, and from the initial state the inner parser reads them with a program whose values,
bridged, are the spec program's.
-/
def ElementRuns (points : Points (StateT H m)) (inner : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)) (init : σ)
    (tokensOf : X → List BSmtLibSpec.Grammar.SyntaxToken) (valid : X → Prop) (spec : X → PM H Y)
    (bridge : ρ → Y) :
    Prop :=
  ∀ element, valid element → ∀ {tokens : List Parser.Internal.Input},
      Stands tokens (tokensOf element) →
    (∃ token rest, tokens = token :: rest ∧ token ≠ .parenClose) ∧
    ∃ program : PM H ρ, bridge <$> program = spec element ∧
      Runs points inner init tokens program fun r => pure (.done r)

variable {init : σ} {inner : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)} {maximum : Option Nat}
variable {tokensOf : X → List BSmtLibSpec.Grammar.SyntaxToken} {valid : X → Prop}
    {spec : X → PM H Y}
variable {bridge : ρ → Y}

/-- The elements, from between elements: appended to those found so far. -/
theorem items_runs (helement : ElementRuns points inner init tokensOf valid spec bridge) :
    (elements : List X) → (∀ element ∈ elements, valid element) →
    ∀ {tokens : List Parser.Internal.Input}, Stands tokens (elements.flatMap tokensOf) →
    ∃ program : PM H (List ρ), List.map bridge <$> program = elements.mapM spec ∧
    HasLength program elements.length ∧
    ∀ found : Array ρ, (∀ limit, maximum = some limit → found.size + elements.length ≤ limit) →
    Runs points (ListState.step init inner maximum) (ListState.between init found) tokens
      program fun handled => pure (.more (ListState.between init (found ++ handled.toArray)))
  | [], _, _, hs => by
    have := Stands.eq_nil hs
    subst this
    exact ⟨pure [], by simp, HasLength.nil, fun found _ =>
      (Runs.nil [] (by simp)).congr rfl rfl⟩
  | element :: elements, hvalid, _, hs => by
    simp only [List.flatMap_cons] at hs
    obtain ⟨first, rest, rfl, hs₁, hs₂⟩ := Stands.split hs
    obtain ⟨⟨token, tokens', rfl, htoken⟩, program, hprogram, hruns⟩ :=
      helement element (hvalid element (List.mem_cons_self ..)) hs₁
    obtain ⟨tail, htailProgram, htailLength, htailRuns⟩ := items_runs helement elements
      (fun e he => hvalid e (List.mem_cons_of_mem _ he)) hs₂
    refine ⟨program >>= fun r => (r :: ·) <$> tail, ?_, HasLength.cons htailLength,
      fun found hfits => ?_⟩
    · rw [List.mapM_cons, ← hprogram, ← htailProgram]
      simp
    · have hitem := ListState.item_runs_done (maximum := maximum) found htoken
        (fun limit hlimit => by have := hfits limit hlimit; simp at this; omega) hruns
      have htail : ∀ r, Runs points (ListState.step init inner maximum)
          (ListState.between init (found.push r)) rest ((r :: ·) <$> tail)
          fun handled => pure (.more (ListState.between init (found ++ handled.toArray))) :=
        fun r => Runs.map_program ((htailRuns (found.push r) (fun limit hlimit => by
          have := hfits limit hlimit
          simp at this ⊢
          omega)).congr rfl (by funext handled; simp))
      exact Runs.append (middle := fun r => ListState.between init (found.push r)) hitem htail

/-- A list whose `(` is consumed already: its elements, then its `)`. -/
theorem closedList_runs (helement : ElementRuns points inner init tokensOf valid spec bridge)
    (elements : List X) (hvalid : ∀ element ∈ elements,
        valid element) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (elements.flatMap tokensOf))
    (hfits : ∀ limit, maximum = some limit → elements.length ≤ limit) :
    ∃ program : PM H (List ρ), List.map bridge <$> program = elements.mapM spec ∧
    HasLength program elements.length ∧
    Runs points (ListState.step init inner maximum) (ListState.between init #[])
      (tokens ++ [.parenClose])
      (do let handled ← program; tick points .parenClose; pure handled)
      fun handled => pure (.done handled.toArray) := by
  obtain ⟨program, hprogram, hlength, hruns⟩ := items_runs (maximum := maximum) helement
    elements hvalid hs
  refine ⟨program, hprogram, hlength, (Runs.append
    (middle := fun (handled : List ρ) => ListState.between init (#[] ++ handled.toArray))
    (hruns #[] (by simpa using hfits)) fun handled =>
      Runs.token (program := pure handled) (next := fun handled => pure (.done handled.toArray))
        (by simp [ListState.step, ListState.between])).congr rfl rfl⟩

/-- A list with its own `(`: the `(`, its elements, then its `)`. -/
theorem parenList_runs (helement : ElementRuns points inner init tokensOf valid spec bridge)
    (elements : List X) (hvalid : ∀ element ∈ elements,
        valid element) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (elements.flatMap tokensOf))
    (hfits : ∀ limit, maximum = some limit → elements.length ≤ limit) :
    ∃ program : PM H (List ρ), List.map bridge <$> program = elements.mapM spec ∧
    HasLength program elements.length ∧
    Runs points (ListState.step init inner maximum) (ListState.paren init)
      (.parenOpen :: (tokens ++ [.parenClose]))
      (do tick points .parenOpen; let handled ← program; tick points .parenClose; pure handled)
      fun handled => pure (.done handled.toArray) := by
  obtain ⟨program, hprogram, hlength, hruns⟩ := closedList_runs (maximum := maximum) helement
    elements hvalid hs hfits
  exact ⟨program, hprogram, hlength,
    Runs.append (first := [.parenOpen]) ListState.open_runs fun _ => hruns⟩

end

/-! ## Simple elements -/

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {points : Points (StateT H m)} {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

theorem adaptRun_mapM {X Y : Type} (f : X → Run (StateT H m) (Traits.Handler.Error H) Y)
    (items : List X) : adaptRun (items.mapM f) = items.mapM fun item => adaptRun (f item) := by
  induction items with
  | nil => simp
  | cons item items ih => simp [ih]

theorem sorts_eq_mapM (sorts : List Tree.«Sort») :
    Traversal.sorts points h sorts = sorts.mapM (Traversal.sort points h) := by
  induction sorts with
  | nil => simp [Traversal.sorts]
  | cons sort sorts ih => simp [Traversal.sorts, ih]

theorem terms_eq_mapM (terms : List Tree.Term) :
    Traversal.terms points h terms = terms.mapM (Traversal.term points h) := by
  induction terms with
  | nil => simp [Traversal.terms]
  | cons term terms ih => simp [Traversal.terms, ih]

theorem sort_tokensAll (sorts : List Tree.«Sort») :
    Tree.«Sort».tokensAll sorts = sorts.flatMap Tree.«Sort».tokens := by
  induction sorts with
  | nil => rfl
  | cons sort sorts ih => simp [Tree.«Sort».tokensAll, ih]

theorem term_tokensAll (terms : List Tree.Term) :
    Tree.Term.tokensAll terms = terms.flatMap Tree.Term.tokens := by
  induction terms with
  | nil => rfl
  | cons term terms ih => simp [Tree.Term.tokensAll, ih]

theorem sort_validAll {sorts : List Tree.«Sort»} (h : Tree.«Sort».ValidAll
    (Bridge.version version) sorts) :
    ∀ sort ∈ sorts, sort.Valid (Bridge.version version) := by
  induction sorts with
  | nil => simp
  | cons sort sorts ih =>
    simp only [Tree.«Sort».ValidAll] at h
    simpa [h.1] using ih h.2

theorem term_validAll {terms : List Tree.Term} (h : Tree.Term.ValidAll
    (Bridge.version version) terms) :
    ∀ term ∈ terms, term.Valid (Bridge.version version) := by
  induction terms with
  | nil => simp
  | cons term terms ih =>
    simp only [Tree.Term.ValidAll] at h
    simpa [h.1] using ih h.2

/-- The sort parser reads a sort from its initial state, and ends with it. -/
theorem sort_element (hA : TermAgrees h) :
    ElementRuns points (Parser.Category.«Sort».sortStep version)
        Parser.Category.«Sort».SortState.init Tree.«Sort».tokens
      (Tree.«Sort».Valid (Bridge.version version))
      (fun sort => adaptRun (Traversal.sort points h sort)) id := by
  intro sort hvalid tokens hs
  exact ⟨Stands.first_of (sort_first sort) hs, _, by simp, sort_runs hA sort hvalid hs []⟩

/-- The term parser reads a term from its initial state, and ends with it. -/
theorem term_element (hA : TermAgrees h) :
    ElementRuns points (Parser.Category.Term.termStep version) Parser.Category.Term.TermState.init
        Tree.Term.tokens
      (Tree.Term.Valid (Bridge.version version))
      (fun term => adaptRun (Traversal.term points h term)) id := by
  intro term hvalid tokens hs
  exact ⟨Stands.first_of (term_first term) hs, _, by simp, term_runs_init hA term hvalid hs⟩

/-- The parser of a sort declaration reads one: its symbol's and its numeral's views. -/
theorem sortDec_runs (sortDec : Tree.SortDec) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens sortDec.tokens) :
    ∃ (symbol : Nodes.Symbol) (arity : NumeralView) (rest : List Parser.Internal.Input),
      tokens = .parenOpen :: rest ∧
      (Bridge.symbol symbol, Bridge.chars arity.asSlice) = (sortDec.symbol, sortDec.arity) ∧
      Runs (H := H) points Parser.Command.Datatype.SortDecState.step .start tokens
          (ticks points tokens)
        fun _ => pure (.done (symbol, arity)) := by
  obtain ⟨name, arity⟩ := sortDec
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
  obtain ⟨symbolToken, rest, rfl, hsymbolToken, hrest⟩ := Stands.split_cons hinner
  obtain ⟨numeralToken, rfl, hnumeralToken⟩ := Stands.split_single hrest
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbolToken
  obtain ⟨digits, rfl, rfl⟩ := Parser.Internal.Input.received_numeral hnumeralToken
  refine ⟨symbol, digits, _, rfl, rfl, ?_⟩
  rw [show Parser.Internal.Input.parenOpen :: ([.symbol symbol,
      .constant (.numeral digits)] ++ [.parenClose]) =
    [.parenOpen] ++ ([.symbol symbol] ++ ([.constant (.numeral digits)] ++ [.parenClose])) by rfl]
  refine (Runs.append (middle := fun _ => Parser.Command.Datatype.SortDecState.opened)
    (Runs.token_more (by simp [Parser.Command.Datatype.SortDecState.step,
    Parser.Category.Token.expectOpen]))
    fun _ => Runs.append (middle := fun _ => .arity symbol) (Runs.token_more
      (by simp [Parser.Command.Datatype.SortDecState.step, Parser.Category.Token.expectSymbol]))
          fun _ =>
        Runs.append (middle := fun _ => .close symbol digits) (Runs.token_more
        (by simp [Parser.Command.Datatype.SortDecState.step, Parser.Category.Token.expectNumeral]))
            fun _ =>
          Runs.token (program := pure ())
            (by simp [Parser.Command.Datatype.SortDecState.step,
                Parser.Category.Token.expectClose])).congr ?_ rfl
  simp

end

end BSmtLib.Facts.Proofs.Parser.Commands.Elements
