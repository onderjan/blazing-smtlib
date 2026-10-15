module

public import BSmtLib.Facts.Proofs.Parser.Rejection.SExpr
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Category.Pattern
import all BSmtLib.Parser.Category.QualifiedIdent
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Category.SortedVar
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# What patterns, qualified identifiers, sorted variables and lists can still take

The parts that terms and commands are built from, and the list parser that reads elements up to
a `)`, with at least `lo` and at most `hi` of them.
-/

namespace BSmtLib.Facts.Proofs.Parser.Rejection.Parts

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser.Category.Pattern.Internal (PatternState)
open BSmtLib.Parser.Category.QualifiedIdent.Internal (QualIdentState qualIdentStep)
open BSmtLib.Parser.Category.SortedVar.Internal (SortedVarState sortedVarStep)
open BSmtLib.Parser.Category.Combinator.Internal (ListState)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Proofs.Parser.Rejection.Basic
open BSmtLib.Facts.Proofs.Parser.Rejection.«Sort»

open BSmtLib.Facts.Proofs.Parser.Rejection.Basic.Lang

/-! ## Patterns -/

section

variable (version : BSmtLibSpec.Lexicon.Version)

/-- A symbol or the wildcard, in the version. -/
def SymbolOrWildcardLang : Lang :=
  fun u => ∃ s : Tree.SymbolOrWildcard, s.Valid version ∧ u = [.token s.token]

/-- A pattern of the version. -/
def PatternLang : Lang :=
  fun u => ∃ pattern : Tree.Pattern, pattern.Valid version ∧ u = toks pattern.tokens

/-- The remainders of the pattern parser's states. -/
def patternRem : PatternState → Lang
  | .start => PatternLang version
  | .opened => cat SymbolLang (cat (plus (SymbolOrWildcardLang version)) (tok closeItem))
  | .arguments _ found =>
    cat (rep (SymbolOrWildcardLang version) (if found.isEmpty then 1 else 0) none)
      (tok closeItem)

theorem symbolOrWildcardLang_nonempty : ∃ u, SymbolOrWildcardLang version u :=
  ⟨_, ⟨.symbol ⟨[], false⟩, trivial, rfl⟩⟩

theorem patternRem_nonempty (state : PatternState) : ∃ u, patternRem version state u := by
  cases state with
  | start => exact ⟨_, ⟨.single (.symbol ⟨[], false⟩), trivial, rfl⟩⟩
  | opened =>
    exact cat_nonempty symbolLang_nonempty (cat_nonempty
      (rep_nonempty (symbolOrWildcardLang_nonempty version) 1 none (by simp)) ⟨_, tok_intro _⟩)
  | arguments _ found =>
    exact cat_nonempty (rep_nonempty (symbolOrWildcardLang_nonempty version) _ none (by simp))
      ⟨_, tok_intro _⟩

end

theorem symbolOrWildcard?_some {version : Token.Version} {token : Parser.Internal.Input}
    {s : Nodes.SymbolOrWildcard}
    (h : PatternState.symbolOrWildcard? version token = some s) :
    Bridge.received token = some (.token (Bridge.symbolOrWildcard s).token) ∧
      (Bridge.symbolOrWildcard s).Valid (Bridge.version version) := by
  unfold PatternState.symbolOrWildcard? at h
  split at h
  · cases h
    exact ⟨rfl, trivial⟩
  · split at h
    · rename_i hword
      cases h
      simp only [PatternState.wildcardAllowed, Bool.and_eq_true, decide_eq_true_eq] at hword
      obtain ⟨hversion, hword⟩ := hword
      rw [isWord_eq hword]
      exact ⟨rfl, atLeast_v2_7_of_ge' hversion⟩
    · cases h

/-- Every step of the pattern parser advances. -/
theorem patternStep_advances (version : Token.Version) :
    StepsAdvance version (PatternState.step (H := List Event) version)
      (patternRem (Bridge.version version))
      fun state _ => patternRem (Bridge.version version) state := by
  intro state token item hitem _
  cases state with
  | start =>
    simp only [PatternState.step]
    split
    · item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => ?_, patternRem_nonempty _ _⟩
      obtain ⟨_, _, ⟨name, rfl⟩, ⟨p, _, hp, rfl, rfl⟩, rfl⟩ := hu
      obtain ⟨arguments, hvalid, hlen, -, rfl⟩ := rep_trees hp
      refine ⟨.constructor name arguments, ⟨by rintro rfl; simp at hlen, hvalid⟩, ?_⟩
      simp [Tree.Pattern.tokens, paren, toks, flatten_singletons, Function.comp_def]
    · split
      · rename_i s hs
        obtain ⟨hreceived, hvalid⟩ := symbolOrWildcard?_some hs
        rw [hreceived, Option.some.injEq] at hitem
        subst hitem
        exact Sound.pure fun _ => ⟨.single _, hvalid, rfl⟩
      · fail_step
  | opened =>
    cases token <;> simp only [PatternState.step] <;> try fail_step
    item_of hitem
    refine Sound.pure fun _ => ⟨fun u hu => ?_, patternRem_nonempty _ _⟩
    exact cat_intro' (symbolLang_intro _) (by simpa [patternRem] using hu) rfl
  | arguments c found =>
    simp only [PatternState.step]
    split
    · item_of hitem
      split
      · fail_step
      · rename_i hne
        refine Sound.pure fun _ => ?_
        show patternRem _ (.arguments c found) [_]
        simp only [patternRem, hne]
        exact cat_intro' rep_nil (tok_intro _) rfl
    · split
      · rename_i s hs
        obtain ⟨hreceived, hvalid⟩ := symbolOrWildcard?_some hs
        rw [hreceived, Option.some.injEq] at hitem
        subst hitem
        refine Sound.pure fun _ => ⟨fun u hu => ?_, patternRem_nonempty _ _⟩
        obtain ⟨a, b, ha, hb, rfl⟩ := hu
        simp only [patternRem, push_isEmpty, Bool.false_eq_true, ite_false] at ha ⊢
        rw [← List.cons_append]
        exact cat_intro (rep_cons (a := [_]) ⟨_, hvalid, rfl⟩ (by split <;> simpa using ha)
          (by simp)) hb
      · fail_step

/-! ## Qualified identifiers -/

section

variable (version : BSmtLibSpec.Lexicon.Version)

/-- A qualified identifier of the version. -/
def QualLang : Lang :=
  fun u => ∃ q : Tree.QualIdentifier, q.Valid version ∧ u = toks q.tokens

/-- The remainders of the qualified identifier parser's states. -/
def qualRem : QualIdentState Nat → Lang
  | .start => QualLang version
  | .opened =>
    union (identRem version .opened)
      (cat (tok (wordItem "as")) (cat (IdentLang version) (cat (SortLang version)
        (tok closeItem))))
  | .indexed ident => identRem version ident
  | .qualifiedIdent ident =>
    cat (identRem version ident) (cat (SortLang version) (tok closeItem))
  | .sort _ sort => cat (sortRem version sort) (tok closeItem)
  | .close _ _ => tok closeItem

theorem qualRem_nonempty (state : QualIdentState Nat) : ∃ u, qualRem version state u := by
  cases state with
  | start => exact ⟨_, ⟨.plain ⟨⟨[], false⟩, []⟩, by simp [Tree.QualIdentifier.Valid,
      Tree.Identifier.Valid], rfl⟩⟩
  | opened => exact (identRem_nonempty version .opened).elim fun u hu => ⟨u, Or.inl hu⟩
  | indexed ident => exact identRem_nonempty version ident
  | qualifiedIdent ident =>
    exact cat_nonempty (identRem_nonempty version ident)
      (cat_nonempty (sortLang_nonempty version) ⟨_, tok_intro _⟩)
  | sort _ sort => exact cat_nonempty (sortRem_nonempty version sort) ⟨_, tok_intro _⟩
  | close _ _ => exact ⟨_, tok_intro _⟩

/-- After a qualified identifier's `(`, the rest of it. -/
theorem qualLang_of_opened {a : List Received} (h : qualRem version .opened a) :
    QualLang version (openItem :: a) := by
  rcases h with h | ⟨_, _, rfl, ⟨i, _, ⟨identifier, hident, rfl⟩, ⟨s, _, ⟨sort, hsort, rfl⟩,
    rfl, rfl⟩, rfl⟩, rfl⟩
  · obtain ⟨identifier, hident, htokens⟩ := identLang_indexed h
    exact ⟨.plain identifier, hident, htokens⟩
  · exact ⟨.as identifier sort, ⟨hident, hsort⟩, by
      simp [Tree.QualIdentifier.tokens, paren, word, toks]⟩

end

/-- Every step of the qualified identifier parser advances. -/
theorem qualIdentStep_advances (version : Token.Version) :
    StepsAdvance version (qualIdentStep (H := List Event) version)
      (qualRem (Bridge.version version)) fun state _ => qualRem (Bridge.version version) state := by
  intro state token item hitem hlex
  cases state with
  | start =>
    cases token <;> simp only [qualIdentStep] <;> try fail_step
    · item_of hitem
      exact Sound.pure fun _ => ⟨fun u hu => qualLang_of_opened _ hu, qualRem_nonempty _ _⟩
    · item_of hitem
      exact Sound.pure fun _ => ⟨.plain ⟨_, []⟩, by simp [Tree.QualIdentifier.Valid,
        Tree.Identifier.Valid], rfl⟩
  | opened =>
    simp only [qualIdentStep]
    split
    · rename_i hword
      rw [isWord_eq hword] at hitem
      item_of hitem
      exact Sound.pure fun _ => ⟨fun u hu => Or.inl (cat_tok hu), qualRem_nonempty _ _⟩
    · split
      · rename_i hword
        rw [isWord_eq hword] at hitem
        item_of hitem
        exact Sound.pure fun _ => ⟨fun u hu => Or.inr (cat_tok hu), qualRem_nonempty _ _⟩
      · fail_step
  | indexed ident =>
    simp only [qualIdentStep]
    refine Sound.bind (identStep_advances version ident token item hitem hlex) fun r hr => ?_
    replace hr := hr.from (identRem_nonempty _ _)
    cases r with
    | more ident' => exact Sound.pure fun _ => ⟨fun u hu => hr.1 u hu, qualRem_nonempty _ _⟩
    | done identifier => exact Sound.pure fun _ => hr
  | qualifiedIdent ident =>
    simp only [qualIdentStep]
    refine Sound.bind (identStep_advances version ident token item hitem hlex) fun r hr => ?_
    replace hr := hr.from (identRem_nonempty _ _)
    cases r with
    | more ident' =>
      refine Sound.pure fun _ => ⟨fun u hu => ?_, qualRem_nonempty _ _⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := hu
      exact cat_intro' (hr.1 a ha) hb rfl
    | done identifier =>
      refine Sound.pure fun _ => ⟨fun u hu => ?_, qualRem_nonempty _ _⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := hu
      refine cat_intro' hr (cat_intro' ?_ hb rfl) rfl
      simpa [sortRem, Parser.Category.«Sort».Internal.SortState.init] using ha
  | sort identifier sort =>
    simp only [qualIdentStep]
    refine Sound.bind (sortStep_advances version sort token item hitem hlex) fun r hr => ?_
    replace hr := hr.from (sortRem_nonempty _ _)
    cases r with
    | more sort' =>
      refine Sound.pure fun _ => ⟨fun u hu => ?_, qualRem_nonempty _ _⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := hu
      exact cat_intro' (hr.1 a ha) hb rfl
    | done handled =>
      exact Sound.pure fun _ => ⟨fun u hu => cat_intro' hr hu rfl, qualRem_nonempty _ _⟩
  | close identifier handled =>
    cases token <;> simp only [qualIdentStep, Parser.Category.Token.Internal.expectClose,
        pure_bind] <;> try
        fail_step
    item_of hitem
    exact Sound.pure fun _ => tok_intro _

/-! ## Sorted variables -/

section

variable (version : BSmtLibSpec.Lexicon.Version)

/-- A sorted variable of the version. -/
def SortedVarLang : Lang :=
  fun u => ∃ var : Tree.SortedVar, var.Valid version ∧ u = toks var.tokens

/-- The remainders of the sorted variable parser's states. -/
def sortedVarRem : SortedVarState Nat → Lang
  | .start => SortedVarLang version
  | .opened => cat SymbolLang (cat (SortLang version) (tok closeItem))
  | .sort _ sort => cat (sortRem version sort) (tok closeItem)
  | .close _ _ => tok closeItem

theorem sortedVarLang_nonempty : ∃ u, SortedVarLang version u :=
  ⟨_, ⟨⟨⟨[], false⟩, ⟨⟨⟨[], false⟩, []⟩, []⟩⟩, by
    simp [Tree.SortedVar.Valid, Tree.«Sort».Valid, Tree.«Sort».ValidAll, Tree.Identifier.Valid],
    rfl⟩⟩

theorem sortedVarRem_nonempty (state : SortedVarState Nat) :
    ∃ u, sortedVarRem version state u := by
  cases state with
  | start => exact sortedVarLang_nonempty version
  | opened =>
    exact cat_nonempty symbolLang_nonempty (cat_nonempty (sortLang_nonempty version)
      ⟨_, tok_intro _⟩)
  | sort _ sort => exact cat_nonempty (sortRem_nonempty version sort) ⟨_, tok_intro _⟩
  | close _ _ => exact ⟨_, tok_intro _⟩

end

/-- Every step of the sorted variable parser advances. -/
theorem sortedVarStep_advances (version : Token.Version) :
    StepsAdvance version (sortedVarStep (H := List Event) version)
      (sortedVarRem (Bridge.version version))
      fun state _ => sortedVarRem (Bridge.version version) state := by
  intro state token item hitem hlex
  cases state with
  | start =>
    cases token <;> simp only [sortedVarStep, Parser.Category.Token.Internal.expectOpen,
        pure_bind] <;> try
        fail_step
    item_of hitem
    refine Sound.pure fun _ => ⟨fun u hu => ?_, sortedVarRem_nonempty _ _⟩
    obtain ⟨_, _, ⟨name, rfl⟩, ⟨s, _, ⟨sort, hsort, rfl⟩, rfl, rfl⟩, rfl⟩ := hu
    exact ⟨⟨name, sort⟩, hsort, by simp [Tree.SortedVar.tokens, paren, toks]⟩
  | opened =>
    cases token <;> simp only [sortedVarStep, Parser.Category.Token.Internal.expectSymbol,
        bind_pure_comp]
        <;>
      try fail_step
    item_of hitem
    refine Sound.pure fun _ => ⟨fun u hu => ?_, sortedVarRem_nonempty _ _⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := hu
    exact cat_intro' (symbolLang_intro _)
      (cat_intro' (by simpa [sortRem,
          Parser.Category.«Sort».Internal.SortState.init] using ha) hb rfl) rfl
  | sort symbol sort =>
    simp only [sortedVarStep]
    refine Sound.bind (sortStep_advances version sort token item hitem hlex) fun r hr => ?_
    replace hr := hr.from (sortRem_nonempty _ _)
    cases r with
    | more sort' =>
      refine Sound.pure fun _ => ⟨fun u hu => ?_, sortedVarRem_nonempty _ _⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := hu
      exact cat_intro' (hr.1 a ha) hb rfl
    | done handled =>
      exact Sound.pure fun _ => ⟨fun u hu => cat_intro' hr hu rfl, sortedVarRem_nonempty _ _⟩
  | close symbol handled =>
    cases token <;> simp only [sortedVarStep, Parser.Category.Token.Internal.expectClose,
        pure_bind] <;> try
        fail_step
    item_of hitem
    exact Sound.pure fun _ => tok_intro _

/-! ## Lists -/

section

variable {σ ρ : Type} (inner : σ → Lang) (element : Lang) (init : σ)

/-- The remainders of a list whose `(` is consumed, of at least `lo` and at most `hi` elements,
whose elements start from the inner parser's `init`: between elements, the `)` if there are
enough elements, or another element if there may be one more; inside an element, its remainder;
then further elements and the `)`. Between elements the inner parser is at `init`; a state where
it is not has no remainder. -/
def listOpenRem (lo : Nat) (hi : Option Nat) (state : ListState σ ρ) : Lang :=
  let more := cat (rep element (lo - (state.items.size + 1))
    (hi.map (· - (state.items.size + 1)))) (tok closeItem)
  let room := ∀ limit, hi = some limit → state.items.size < limit
  if state.outside then
    fun u => state.inner = init ∧
      union (fun u => u = [closeItem] ∧ lo ≤ state.items.size ∧
          ∀ limit, hi = some limit → state.items.size ≤ limit)
        (fun u => room ∧ cat (inner state.inner) more u) u
  else fun u => room ∧ cat (inner state.inner) more u

/-- The remainders of a list's states: its `(` first if it is still to come. -/
def listRem (lo : Nat) (hi : Option Nat) (state : ListState σ ρ) : Lang :=
  if state.opened then listOpenRem inner element init lo hi state
  else cat (tok openItem) (listOpenRem inner element init lo hi state)

end

section

variable {σ ρ : Type} {inner : σ → Lang} {element : Lang} {init : σ}

theorem more_nonempty (helement : ∃ u, element u) (lo : Nat) (hi : Option Nat) (k : Nat)
    (hlohi : ∀ limit, hi = some limit → lo ≤ limit) :
    ∃ u, cat (rep element (lo - (k + 1)) (hi.map (· - (k + 1)))) (tok closeItem) u :=
  cat_nonempty (rep_nonempty helement _ _ fun limit hlimit => by
    cases hi with
    | none => simp at hlimit
    | some l =>
      simp only [Option.map_some, Option.some.injEq] at hlimit
      have := hlohi l rfl
      omega) ⟨_, tok_intro _⟩

/-- A list between elements, with the inner parser at its start, has a remainder. -/
theorem listOpenRem_outside_nonempty (hinit : ∃ u, inner init u) (helement : ∃ u, element u)
    {lo : Nat} {hi : Option Nat} (hlohi : ∀ limit, hi = some limit → lo ≤ limit)
    (opened : Bool) (items : Array ρ)
    (hroom : (lo ≤ items.size ∧ ∀ limit, hi = some limit → items.size ≤ limit) ∨
      ∀ limit, hi = some limit → items.size < limit) :
    ∃ u, listOpenRem inner element init lo hi ⟨opened, true, init, items⟩ u := by
  have hmore := more_nonempty helement lo hi items.size hlohi
  simp only [listOpenRem, ite_true]
  rcases hroom with h | h
  · exact ⟨_, trivial, Or.inl ⟨rfl, h⟩⟩
  · obtain ⟨u, hu⟩ := cat_nonempty hinit hmore
    exact ⟨u, trivial, Or.inr ⟨h, hu⟩⟩

/-- A list inside an element with a remainder, with room for it, has a remainder. -/
theorem listOpenRem_inside_nonempty (helement : ∃ u, element u) {lo : Nat} {hi : Option Nat}
    (hlohi : ∀ limit, hi = some limit → lo ≤ limit) (opened : Bool) (current : σ)
    (items : Array ρ) (hcurrent : ∃ u, inner current u)
    (hroom : ∀ limit, hi = some limit → items.size < limit) :
    ∃ u, listOpenRem inner element init lo hi ⟨opened, false, current, items⟩ u := by
  obtain ⟨u, hu⟩ := cat_nonempty hcurrent (more_nonempty helement lo hi items.size hlohi)
  exact ⟨u, hroom, hu⟩

/-- The remainders of a list before its `(` are its elements between `(` and `)`. -/
theorem listRem_paren (hinit : ∀ u, inner init u → element u) {lo : Nat} {u : List Received}
    (h : listRem inner element init lo none (ListState.paren (ρ := ρ) init) u) :
    ∃ w, rep element lo none w ∧ u = openItem :: (w ++ [closeItem]) := by
  simp only [listRem, ListState.paren, Bool.false_eq_true] at h
  obtain ⟨_, o, rfl, ho, rfl⟩ := h
  simp only [listOpenRem, ite_true, List.size_toArray, List.length_nil] at ho
  rcases ho with ⟨-, ⟨rfl, hlo, -⟩ | ⟨-, a, b, ha, ⟨r, c, hr, rfl, rfl⟩, rfl⟩⟩
  · exact ⟨[], by simpa [show lo = 0 by omega] using (rep_nil (A := element) (hi := none)), rfl⟩
  · refine ⟨a ++ r, rep_cons (hinit a ha) (by simpa using hr) (by simp), by simp⟩

/-- A list before its `(` has a remainder. -/
theorem listRem_paren_nonempty (hinit : ∃ u, inner init u) (helement : ∃ u, element u)
    {lo : Nat} {hi : Option Nat} (hlohi : ∀ limit, hi = some limit → lo ≤ limit) :
    ∃ u, listRem inner element init lo hi (ListState.paren (ρ := ρ) init) u := by
  simp only [listRem, ListState.paren, Bool.false_eq_true]
  refine cat_nonempty ⟨_, tok_intro _⟩ (listOpenRem_outside_nonempty hinit helement hlohi false
    #[] ?_)
  by_cases h : lo = 0
  · left
    exact ⟨by simp [h], fun _ _ => by simp⟩
  · right
    intro limit hlimit
    have := hlohi limit hlimit
    simp only [List.size_toArray, List.length_nil]
    omega

end

/-- A list state that an input can lead to: between elements, the inner parser is at its start,
and the inner parser's state has a remainder. -/
def ListWF {σ ρ : Type} (inner : σ → Lang) (init : σ) (state : ListState σ ρ) : Prop :=
  (state.outside = true → state.inner = init) ∧ ∃ u, inner state.inner u

theorem listWF_of_rem {σ ρ : Type} {inner : σ → Lang} {element : Lang} {init : σ} {lo : Nat}
    {hi : Option Nat} (hinit : ∃ u, inner init u) {state : ListState σ ρ}
    (h : ∃ u, listRem inner element init lo hi state u) : ListWF inner init state := by
  obtain ⟨opened, outside, current, items⟩ := state
  obtain ⟨u, hu⟩ := h
  have hopen : ∃ u, listOpenRem inner element init lo hi ⟨opened, outside, current, items⟩ u := by
    simp only [listRem] at hu
    split at hu
    · exact ⟨u, hu⟩
    · obtain ⟨_, o, -, ho, -⟩ := hu
      exact ⟨o, ho⟩
  obtain ⟨u, hu⟩ := hopen
  simp only [listOpenRem] at hu
  cases outside with
  | true =>
    simp only [ite_true] at hu
    obtain ⟨rfl, -⟩ := hu
    exact ⟨fun _ => rfl, hinit⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hu
    obtain ⟨-, a, -, ha, -, -⟩ := hu
    exact ⟨nofun, a, ha⟩

/-- What a step of the list parser says of the remainders of lists of at least `lo` and at most
`hi` elements, from a state that an input can lead to: going on, every remainder of the new
state, after the item, is one of the old state, the new state is one an input can lead to, and
where the parser's own maximum is `hi`, it has a remainder if the old one has; finishing at the
`)`, with enough elements and not too many, the `)` completes the list. -/
def ListAdvances {σ ρ : Type} (inner : σ → Lang) (element : Lang) (init : σ) (lo : Nat)
    (hi : Option Nat) (maximum : Option Nat) (state : ListState σ ρ) (item : Received) :
    Parser.Internal.Step (ListState σ ρ) (Array ρ) → Prop
  | .more state' => ListWF inner init state →
    (∀ u, listRem inner element init lo hi state' u →
      listRem inner element init lo hi state (item :: u)) ∧ ListWF inner init state' ∧
      state'.opened = true ∧
      (maximum = hi → (∃ u, listRem inner element init lo hi state u) →
        ∃ u, listRem inner element init lo hi state' u)
  | .done items => ListWF inner init state → lo ≤ items.size →
      (∀ limit, hi = some limit → items.size ≤ limit) →
      listRem inner element init lo hi state [item]

/-- A step of the list parser advances, for lists of at least `lo` and at most `hi` elements,
whatever its own maximum. -/
theorem listStep_implies {σ ρ : Type} (version : Token.Version) (init : σ)
    {step : σ → Parser.Internal.Input → Quiet.RPM
        (Parser.Internal.Step σ ρ)} {inner : σ → Lang} {element : Lang}
    (hstep : StepsAdvance version step inner fun state _ => inner state)
    (hinitElement : ∀ u, inner init u → element u) (hinit : ∃ u, inner init u)
    (helement : ∃ u, element u) (lo : Nat) (hi : Option Nat)
    (hlohi : ∀ limit, hi = some limit → lo ≤ limit) (maximum : Option Nat)
    (state : ListState σ ρ) {token : Parser.Internal.Input} {item : Received}
    (hitem : Bridge.received token = some item) (hlex : item.OfVersion (Bridge.version version)) :
    Sound (ListAdvances inner element init lo hi maximum state item) Benign
      (ListState.step init step maximum state token) := by
  obtain ⟨opened, outside, current, items⟩ := state
  simp only [ListState.step]
  cases opened with
  | false =>
    cases token <;> simp only [Parser.Category.Token.Internal.expectOpen, pure_bind, Bool.not_false,
        ite_true] <;>
      try fail_step
    item_of hitem
    refine Sound.pure fun hwf => ⟨fun u hu => ?_, hwf, rfl, fun _ h => ?_⟩
    · simp only [listRem, Bool.false_eq_true, ite_false]
      exact cat_tok hu
    · obtain ⟨u, hu⟩ := h
      simp only [listRem, Bool.false_eq_true, ite_false] at hu
      obtain ⟨_, o, rfl, ho, rfl⟩ := hu
      exact ⟨o, ho⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    have hinside : (∀ limit, maximum = some limit → limit = hi.getD 0 →
        outside = true → items.size < limit) →
        Sound (ListAdvances inner element init lo hi maximum ⟨true, outside, current, items⟩ item)
          Benign
          (step current token >>= fun r => match r with
            | .more state' => pure (Parser.Internal.Step.more ⟨true, false, state', items⟩)
            | .done result => pure (Parser.Internal.Step.more ⟨true, true, init,
                items.push result⟩)) := by
      intro hchecked
      have wrap : ∀ {u}, (outside = true → current = init) →
          (∀ limit, hi = some limit → items.size < limit) →
          cat (inner current) (cat (rep element (lo - (items.size + 1))
            (hi.map (· - (items.size + 1)))) (tok closeItem)) u →
          listRem inner element init lo hi ⟨true, outside, current, items⟩ u := by
        intro u hcur hroom hu
        simp only [listRem, listOpenRem, ite_true]
        split
        · rename_i houtside
          exact ⟨hcur houtside, Or.inr ⟨hroom, hu⟩⟩
        · exact ⟨hroom, hu⟩
      -- where the parser's maximum is `hi`, a state with a remainder has room for the element
      -- the parser reads
      have hroom : maximum = hi → (∃ u, listRem inner element init lo hi
          ⟨true, outside, current, items⟩ u) → ∀ limit, hi = some limit → items.size < limit := by
        intro hmax hne limit hlimit
        cases outside with
        | true =>
          exact hchecked limit (hmax ▸ hlimit) (by simp [hlimit]) rfl
        | false =>
          obtain ⟨u, hu⟩ := hne
          simp only [listRem, listOpenRem, ite_true, Bool.false_eq_true, ite_false] at hu
          exact hu.1 limit hlimit
      refine Sound.bind (hstep current token item hitem hlex) fun r hr => ?_
      cases r with
      | more current' =>
        refine Sound.pure fun hwf => ?_
        have hr := hr hwf.2
        refine ⟨fun u hu => ?_, ⟨nofun, hr.2⟩, rfl, fun hmax hne => ?_⟩
        · simp only [listRem, listOpenRem, ite_true, Bool.false_eq_true, ite_false] at hu
          obtain ⟨hroom', a, b, ha, hb, rfl⟩ := hu
          exact wrap hwf.1 hroom' (cat_intro' (hr.1 a ha) hb rfl)
        · simp only [listRem, ite_true]
          exact listOpenRem_inside_nonempty helement hlohi true current' items hr.2
            (hroom hmax hne)
      | done result =>
        refine Sound.pure fun hwf => ?_
        have hr := hr hwf.2
        refine ⟨fun u hu => ?_, ⟨fun _ => rfl, hinit⟩, rfl, fun hmax hne => ?_⟩
        · simp only [listRem, listOpenRem, ite_true, Array.size_push] at hu
          rcases hu with ⟨-, ⟨rfl, hlo, hhi⟩ | ⟨hroom', a, b, ha, ⟨r, c, hr', hc, rfl⟩, rfl⟩⟩
          · refine wrap hwf.1 (fun limit hl => by have := hhi limit hl; omega)
              (cat_intro' hr ?_ rfl)
            have : lo - (items.size + 1) = 0 := by omega
            exact cat_intro' (by rw [this]; exact rep_nil) (tok_intro _) rfl
          · refine wrap hwf.1 (fun limit hl => by have := hroom' limit hl; omega)
              (cat_intro' hr ?_ rfl)
            rw [show a.append (r ++ c) = (a ++ r) ++ c from (List.append_assoc a r c).symm]
            refine cat_intro (rep_cons (hinitElement a ha) ?_ ?_) hc
            · have : lo - (items.size + 1) - 1 = lo - (items.size + 1 + 1) := by omega
              rw [this]
              cases hi with
              | none => simpa using hr'
              | some l =>
                have : l - (items.size + 1) - 1 = l - (items.size + 1 + 1) := by omega
                simpa [this] using hr'
            · intro limit hl
              cases hi with
              | none => simp at hl
              | some l =>
                simp only [Option.map_some, Option.some.injEq] at hl
                subst hl
                have := hroom' l rfl
                omega
        · have hroom' := hroom hmax hne
          simp only [listRem, ite_true]
          refine listOpenRem_outside_nonempty hinit helement hlohi true _ ?_
          by_cases h : lo ≤ items.size + 1
          · left
            refine ⟨by simpa using h, fun limit hl => ?_⟩
            have := hroom' limit hl
            simp only [Array.size_push]
            omega
          · right
            intro limit hlimit
            have := hlohi limit hlimit
            simp only [Array.size_push]
            omega
    cases outside with
    | false => exact hinside fun _ _ _ h => by cases h
    | true =>
      simp only [ite_true]
      cases token
      case parenClose =>
        item_of hitem
        exact Sound.pure fun hwf hlo hhi => by
          simp only [listRem, listOpenRem, ite_true]
          exact ⟨hwf.1 rfl, Or.inl ⟨rfl, hlo, hhi⟩⟩
      all_goals
        simp only
        cases maximum with
        | none => exact hinside fun _ h => by cases h
        | some limit =>
          simp only
          split
          · fail_step
          · rename_i hlimit
            exact hinside fun l h _ _ => by
              cases h
              omega

/-- Every step of the list parser advances, for lists of at least `lo` and at most `maximum`
elements: it finishes, at the `)`, with its elements, and where they are at least `lo`, and not
too many, the `)` completes the list. -/
theorem listStep_advances {σ ρ : Type} (version : Token.Version) (init : σ)
    {step : σ → Parser.Internal.Input → Quiet.RPM
        (Parser.Internal.Step σ ρ)} {inner : σ → Lang} {element : Lang}
    (hstep : StepsAdvance version step inner fun state _ => inner state)
    (hinitElement : ∀ u, inner init u → element u) (hinit : ∃ u, inner init u)
    (helement : ∃ u, element u) (lo : Nat) (maximum : Option Nat)
    (hlohi : ∀ limit, maximum = some limit → lo ≤ limit) :
    StepsAdvance version (ListState.step init step maximum)
      (listRem inner element init lo maximum)
      fun state (items : Array ρ) u => lo ≤ items.size →
        (∀ limit, maximum = some limit → items.size ≤ limit) →
        listRem inner element init lo maximum state u := by
  intro state token item hitem hlex
  refine (listStep_implies version init hstep hinitElement hinit helement lo maximum hlohi maximum
    state hitem hlex).mono (fun r hr => ?_) fun _ h => h
  cases r with
  | more state' =>
    exact fun hne => ⟨(hr (listWF_of_rem hinit hne)).1,
      (hr (listWF_of_rem hinit hne)).2.2.2 rfl hne⟩
  | done items => exact fun hne => hr (listWF_of_rem hinit hne)

/-- The remainders of a list of at least `lo` and at most `hi` elements before its `(` are its
elements between `(` and `)`. -/
theorem listRem_paren_hi {σ ρ : Type} {inner : σ → Lang} {element : Lang} {init : σ}
    (hinit : ∀ u, inner init u → element u) {lo : Nat} {hi : Option Nat} {u : List Received}
    (h : listRem inner element init lo hi (ListState.paren (ρ := ρ) init) u) :
    ∃ w, rep element lo hi w ∧ u = openItem :: (w ++ [closeItem]) := by
  simp only [listRem, ListState.paren, Bool.false_eq_true] at h
  obtain ⟨_, o, rfl, ho, rfl⟩ := h
  simp only [listOpenRem, ite_true, List.size_toArray, List.length_nil] at ho
  rcases ho with ⟨-, ⟨rfl, hlo, -⟩ | ⟨hroom, a, b, ha, ⟨r, c, hr, rfl, rfl⟩, rfl⟩⟩
  · refine ⟨[], ?_, rfl⟩
    rw [show lo = 0 by omega]
    exact rep_nil
  · refine ⟨a ++ r, rep_cons (hinit a ha) (by simpa using hr) hroom, by simp⟩

/-- A list state that an input can lead to, whose `(` is consumed, has a remainder for some
number of elements in all. -/
theorem listRem_counted_nonempty {σ ρ : Type} {inner : σ → Lang} {element : Lang} {init : σ}
    (hinit : ∃ u, inner init u) (helement : ∃ u, element u) {state : ListState σ ρ}
    (hwf : ListWF inner init state) (hopened : state.opened = true) :
    ∃ n, 1 ≤ n ∧ ∃ u, listRem inner element init n (some n) state u := by
  obtain ⟨opened, outside, current, items⟩ := state
  simp only at hopened
  subst hopened
  simp only [listRem, ite_true]
  cases outside with
  | true =>
    obtain ⟨hcur, -⟩ := hwf
    obtain rfl : current = init := hcur rfl
    by_cases h : items.size = 0
    · exact ⟨1, Nat.le_refl _, listOpenRem_outside_nonempty hinit helement (by simp) true items
        (Or.inr fun l hl => by cases hl; omega)⟩
    · exact ⟨items.size, by omega, listOpenRem_outside_nonempty hinit helement (by simp) true items
        (Or.inl ⟨Nat.le_refl _, fun l hl => by cases hl; omega⟩)⟩
  | false =>
    exact ⟨items.size + 1, by omega, listOpenRem_inside_nonempty helement (by simp) true current
      items hwf.2 (fun l hl => by cases hl; omega)⟩

/-- The list parser finishes only at the `)`, without a call. -/
theorem listStep_done_silent {σ ρ : Type} (init : σ) (step : σ → Parser.Internal.Input → Quiet.RPM
    (Parser.Internal.Step σ ρ))
    (maximum : Option Nat) (state : ListState σ ρ) (token : Parser.Internal.Input) :
    ∀ events items events',
      (ListState.step init step maximum state token).run.run events = (.ok (.done items), events') →
      events' = events := by
  intro events items events' h
  have more : ∀ (g : σ → ListState σ ρ) (k : ρ → ListState σ ρ) b ev ev' items,
      ((match b with
        | Parser.Internal.Step.more state => pure (Parser.Internal.Step.more (g state))
        | Parser.Internal.Step.done item => pure (Parser.Internal.Step.more (k item)) :
          Quiet.RPM (Parser.Internal.Step (ListState σ ρ) (Array ρ)))).run.run
        ev ≠ (.ok (.done items), ev') := by
    intro g k b ev ev' items
    cases b <;> exact more_ne_done _ _ _ _
  obtain ⟨opened, outside, inner, its⟩ := state
  cases opened <;> cases outside <;>
    simp only [ListState.step, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true,
      ite_false] at h
  · exact absurd h (never_done fun _ _ _ _ => more_ne_done _ _ _ _)
  · exact absurd h (never_done fun _ _ _ _ => more_ne_done _ _ _ _)
  · exact absurd h (never_done (more _ _))
  · cases token
    case parenClose =>
      exact pure_done_run h
    all_goals
      simp only at h
      split at h
      · split at h
        · exact absurd h (never_done fun _ _ _ _ => never_done (more _ _))
        · exact absurd h (never_done (more _ _))
      · exact absurd h (never_done (more _ _))

/-- The list parser writes no event where it finishes, as `Sound.bindOn` takes it. -/
theorem listStep_quiet {σ ρ : Type} (init : σ) (step : σ → Parser.Internal.Input → Quiet.RPM
    (Parser.Internal.Step σ ρ))
    (maximum : Option Nat) (state : ListState σ ρ) (token : Parser.Internal.Input) :
    ∀ events b events', (ListState.step init step maximum state token).run.run events =
      (.ok b, events') → (∃ v, b = .done v) → events' = events :=
  fun _ _ _ hrun ⟨_, hv⟩ => by
    subst hv
    exact listStep_done_silent _ _ _ _ _ _ _ _ hrun

end BSmtLib.Facts.Proofs.Parser.Rejection.Parts
