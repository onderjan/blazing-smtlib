import BSmtLib.Facts.Proofs.Parser.Sort

/-!
# The list combinator against the traversal

`ListState.step` reads a list of elements, each by an inner parser, up to a `)`. Its lemmas are
one for each part of a list: the `(` that opens it (if it has its own), one element from
between elements, and the `)` that ends it. A proof of a particular list goes by induction over
its elements, joining these with `Runs.append`, as `sExprs_runs` does for the items of an
s-expression list.

An element is read by the inner parser from its initial state; the list takes the element's
first token over from the state between elements (`Runs.first`), which is why that token must
not be a `)`, and why the list must be below its maximum.
-/

namespace BSmtLib.Facts.Proofs.Parser.List

open BSmtLib.Parser (Input PM Step)
open BSmtLib.Parser.Category.Combinator (ListState)
open BSmtLibSpec.Parser.Traversal (Points)
open BSmtLib.Facts.Parser.Adapters.Run BSmtLib.Facts.Proofs.Parser.Drive

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {points : Points (StateT H m)} {σ ρ α : Type}

omit [LawfulMonad m] in
/-- Two states that step alike on the first token, with the same calls due at its arrival,
read alike. -/
theorem _root_.BSmtLib.Facts.Proofs.Parser.Drive.Runs.first {step : σ → Input → PM H (Step σ ρ)}
    {state state' : σ} {token : Input}
    {tokens : List Input} {program : PM H α} {next : α → PM H (Step σ ρ)}
    {arrival : σ → Input → PM H Unit}
    (heq : step state token = step state' token)
    (h : Runs points step state' (token :: tokens) program next arrival)
    (harr : arrival state token = arrival state' token := by intros; rfl) :
    Runs points step state (token :: tokens) program next arrival := by
  intro rest
  have := h rest
  simp only [List.cons_append, drive_cons', arrivalTick, heq, harr] at this ⊢
  exact this

variable {init : σ} {inner : σ → Input → PM H (Step σ ρ)} {maximum : Option Nat}

/-- The list between elements, its `(` consumed, with the elements so far. -/
def ListState.between (init : σ) (items : Array ρ) : ListState σ ρ :=
  { opened := true, outside := true, inner := init, items }

/-- The `(` of a list that opens with its own. -/
theorem ListState.open_runs :
    Runs points (ListState.step init inner maximum) (ListState.paren init) [.parenOpen]
      (tick points .parenOpen) fun _ => pure (.more (ListState.between init #[])) :=
  Runs.token_more (by simp [ListState.step, ListState.paren, ListState.between,
    Parser.Category.Token.expectOpen])

/-- The `)` that ends a list, between elements. -/
theorem ListState.close_runs (items : Array ρ) :
    Runs points (ListState.step init inner maximum) (ListState.between init items) [.parenClose]
      (do tick points .parenClose; pure items) fun items => pure (.done items) :=
  Runs.token (by simp [ListState.step, ListState.between])

/--
One element, from between elements: the inner parser reads it from its initial state, and the
list appends it. Its first token is not a `)`, and the list is below its maximum.
-/
theorem ListState.item_runs {token : Input} {tokens : List Input} {program : PM H α}
    {next : α → PM H (Step σ ρ)} (items : Array ρ) (hfirst : token ≠ .parenClose)
    (hmaximum : ∀ limit, maximum = some limit → items.size < limit)
    (h : Runs points inner init (token :: tokens) program next) :
    Runs points (ListState.step init inner maximum) (ListState.between init items)
      (token :: tokens) program fun a => next a >>= Step.wrap
        (fun state => ({ opened := true, outside := false, inner := state, items } :
          ListState σ ρ))
        (fun item => pure (.more (ListState.between init (items.push item)))) := by
  have hembed := Runs.embed (outer := ListState.step init inner maximum)
    (fun state => ({ opened := true, outside := false, inner := state, items } : ListState σ ρ))
    (fun item => pure (.more (ListState.between init (items.push item))))
    (fun state token => by
      simp only [ListState.step]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rfl)
    h
  refine Runs.first (state' := { opened := true, outside := false, inner := init, items }) ?_
    hembed
  cases hmax : maximum with
  | none =>
    cases token <;> first | exact absurd rfl hfirst | simp [ListState.step, ListState.between]
  | some limit =>
    have hlt := Nat.not_le.mpr (hmaximum limit hmax)
    cases token <;> first | exact absurd rfl hfirst |
      simp [ListState.step, ListState.between, hlt]

/--
One element, from between elements, read by an inner parser that ends with it: the list
appends it and is between elements again.
-/
theorem ListState.item_runs_done {token : Input} {tokens : List Input} {program : PM H ρ}
    (items : Array ρ) (hfirst : token ≠ .parenClose)
    (hmaximum : ∀ limit, maximum = some limit → items.size < limit)
    (h : Runs points inner init (token :: tokens) program fun r => pure (.done r)) :
    Runs points (ListState.step init inner maximum) (ListState.between init items)
      (token :: tokens) program fun r => pure (.more (ListState.between init (items.push r))) :=
  (ListState.item_runs items hfirst hmaximum h).congr rfl (by funext; simp [Step.wrap])

end

end BSmtLib.Facts.Proofs.Parser.List
