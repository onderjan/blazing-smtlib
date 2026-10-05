import BSmtLib.Spec.Grammar

/-!
# Items and how a sequence of tokens splits into them

Every syntactic rule accepts tokens that are a single item, or a few items in a row: a token
other than a parenthesis, or a balanced group in parentheses. An item ends where it can be
told to end without looking past it: an atom after its one token, a group at the `)` that
brings the depth back to zero. So when two items start one sequence of tokens they are the
same item (`Item.prefix_eq`), and a sequence splits in at most one way into items that each
rule accepts (`Each.unique`).

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Grammar

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar

/-- A token other than a parenthesis. -/
def Atomic (t : SyntaxToken) : Prop := t ≠ .parenOpen ∧ t ≠ .parenClose

/-- A sequence of items, each an atom or a group of a balanced sequence in parentheses. -/
inductive Balanced : List SyntaxToken → Prop
  | nil : Balanced []
  | atom : Atomic t → Balanced rest → Balanced (t :: rest)
  | group : Balanced inner → Balanced rest → Balanced (paren inner ++ rest)

/-- One item: an atom, or a group of a balanced sequence in parentheses. -/
inductive Item : List SyntaxToken → Prop
  | atom : Atomic t → Item [t]
  | group : Balanced inner → Item (paren inner)

/-! ## Where the first item ends -/

/--
`scan d tokens`: inside `d + 1` open groups, the number of tokens up to and including the
`)` that closes the outermost of them.
-/
def scan : Nat → List SyntaxToken → Option Nat
  | _, [] => none
  | d, .parenOpen :: rest => (scan (d + 1) rest).map (· + 1)
  | 0, .parenClose :: _ => some 1
  | d + 1, .parenClose :: rest => (scan d rest).map (· + 1)
  | d, _ :: rest => (scan d rest).map (· + 1)

/-- The number of tokens of the item that the tokens start with. -/
def firstLength : List SyntaxToken → Option Nat
  | [] => none
  | .parenOpen :: rest => (scan 0 rest).map (· + 1)
  | .parenClose :: _ => none
  | _ :: _ => some 1

theorem scan_atom {d : Nat} {t : SyntaxToken} {rest : List SyntaxToken} (ht : Atomic t) :
    scan d (t :: rest) = (scan d rest).map (· + 1) := by
  obtain ⟨h₁, h₂⟩ := ht
  cases t <;> cases d <;> simp_all [scan]

/-- A balanced sequence leaves the depth as it was. -/
theorem scan_balanced {l : List SyntaxToken} (h : Balanced l) :
    ∀ d r, scan d (l ++ r) = (scan d r).map (· + l.length) := by
  induction h with
  | nil => intro d r; simp
  | atom ht _ ih =>
    intro d r
    rw [List.cons_append, scan_atom ht, ih, Option.map_map]
    rfl
  | @group inner rest _ _ ihi ihr =>
    intro d r
    simp only [paren, List.cons_append, List.nil_append, List.append_assoc, scan]
    rw [ihi, scan, ihr, Option.map_map, Option.map_map, Option.map_map]
    congr 1
    funext x
    simp only [Function.comp, List.length_cons, List.length_append]
    omega

theorem Item.firstLength {a : List SyntaxToken} (h : Item a) (b : List SyntaxToken) :
    firstLength (a ++ b) = some a.length := by
  cases h with
  | atom ht =>
    obtain ⟨h₁, h₂⟩ := ht
    rename_i t
    cases t <;> simp_all [Grammar.firstLength]
  | @group inner hi =>
    simp only [paren, List.cons_append, List.nil_append, List.append_assoc,
      Grammar.firstLength]
    rw [scan_balanced hi, scan]
    simp only [Option.map_some, List.length_cons, List.length_append, List.length_nil]
    congr 1
    omega

/-- Two items that one sequence of tokens starts with are the same item. -/
theorem Item.prefix_eq {a a' b b' : List SyntaxToken} (h : Item a) (h' : Item a')
    (heq : a ++ b = a' ++ b') : a = a' ∧ b = b' := by
  have hl : a.length = a'.length := by
    have := h.firstLength b
    rw [heq, h'.firstLength b'] at this
    exact (Option.some.inj this).symm
  exact List.append_inj heq hl

theorem Item.ne_nil {a : List SyntaxToken} (h : Item a) : a ≠ [] := by
  cases h <;> simp [paren]

/-! ## Building balanced sequences -/

theorem Item.balanced {a : List SyntaxToken} (h : Item a) : Balanced a := by
  cases h with
  | atom ht => exact .atom ht .nil
  | group hi => simpa using Balanced.group hi .nil

theorem Balanced.append {a b : List SyntaxToken} (ha : Balanced a) (hb : Balanced b) :
    Balanced (a ++ b) := by
  induction ha with
  | nil => exact hb
  | atom ht _ ih => exact .atom ht ih
  | group hi _ _ ih => simpa only [List.append_assoc] using Balanced.group hi ih

theorem Balanced.item {a b : List SyntaxToken} (ha : Item a) (hb : Balanced b) :
    Balanced (a ++ b) :=
  ha.balanced.append hb

theorem Balanced.cons {t : SyntaxToken} {b : List SyntaxToken} (ht : Atomic t)
    (hb : Balanced b) : Balanced (t :: b) :=
  .atom ht hb

theorem Item.paren {inner : List SyntaxToken} (h : Balanced inner) : Item (paren inner) :=
  .group h

theorem Atomic.item {t : SyntaxToken} (h : Atomic t) : Item [t] := .atom h

/-! ## Sequences of items -/

/-- What `Each` holds of a sequence of tokens, taken apart. -/
theorem Each.inv {α : Type} {rule : List SyntaxToken → α → Prop} {tokens : List SyntaxToken}
    {items : List α} (h : Each rule tokens items) :
    (tokens = [] ∧ items = []) ∨
      ∃ first rest item items', tokens = first ++ rest ∧ items = item :: items' ∧
        rule first item ∧ Each rule rest items' := by
  cases h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons h₁ h₂ => exact Or.inr ⟨_, _, _, _, rfl, rfl, h₁, h₂⟩

/--
The tokens of items in a row, each of which a rule accepts and every acceptance of which is
an item, are balanced. The rule need only make items of up to `n` tokens.
-/
theorem Each.balanced {α : Type} {rule : List SyntaxToken → α → Prop} {n : Nat}
    (hitem : ∀ t x, t.length ≤ n → rule t x → Item t) {tokens : List SyntaxToken}
    {items : List α} (h : Each rule tokens items) (hn : tokens.length ≤ n) :
    Balanced tokens := by
  induction h with
  | nil => exact .nil
  | cons h₁ _ ih =>
    simp only [List.length_append] at hn
    exact (hitem _ _ (by omega) h₁).balanced.append (ih (by omega))

/-- `Each.balanced`, for a rule all of whose acceptances are items. -/
theorem Each.balanced' {α : Type} {rule : List SyntaxToken → α → Prop}
    (hitem : ∀ t x, rule t x → Item t) {tokens : List SyntaxToken}
    {items : List α} (h : Each rule tokens items) : Balanced tokens :=
  Each.balanced (n := tokens.length) (fun t x _ => hitem t x) h (Nat.le_refl _)

/--
A sequence of tokens splits in at most one way into items that a rule accepts, when every
acceptance is an item and the rule leaves at most one tree for each item. The rule need only
have these properties for up to `n` tokens.
-/
theorem Each.unique {α : Type} {rule : List SyntaxToken → α → Prop} {n : Nat}
    (hitem : ∀ t x, t.length ≤ n → rule t x → Item t)
    (huniq : ∀ t x x', t.length ≤ n → rule t x → rule t x' → x = x')
    {tokens : List SyntaxToken} {items items' : List α}
    (h : Each rule tokens items) (h' : Each rule tokens items') (hn : tokens.length ≤ n) :
    items = items' := by
  induction h generalizing items' with
  | nil =>
    rcases Each.inv h' with ⟨-, rfl⟩ | ⟨first, rest, _, _, heq, -, h₁, -⟩
    · rfl
    · have hl := congrArg List.length heq
      simp only [List.length_nil, List.length_append] at hl hn
      exact absurd (List.eq_nil_of_length_eq_zero (by omega)) (hitem _ _ (by omega) h₁).ne_nil
  | @cons first rest _ _ h₁ _ ih =>
    simp only [List.length_append] at hn
    have hi₁ := hitem _ _ (by omega) h₁
    rcases Each.inv h' with ⟨heq, -⟩ | ⟨first', rest', _, _, heq, rfl, h₁', h₂'⟩
    · exact absurd (List.append_eq_nil_iff.mp heq).1 hi₁.ne_nil
    · have hl' : first'.length ≤ n := by
        have := congrArg List.length heq
        simp only [List.length_append] at this
        omega
      obtain ⟨rfl, rfl⟩ := hi₁.prefix_eq (hitem _ _ hl' h₁') heq
      rw [huniq _ _ _ (by omega) h₁ h₁', ih h₂' (by omega)]

/-- `Each.unique`, for a rule that has its properties for every number of tokens. -/
theorem Each.unique' {α : Type} {rule : List SyntaxToken → α → Prop}
    (hitem : ∀ t x, rule t x → Item t) (huniq : ∀ t x x', rule t x → rule t x' → x = x')
    {tokens : List SyntaxToken} {items items' : List α}
    (h : Each rule tokens items) (h' : Each rule tokens items') : items = items' :=
  Each.unique (n := tokens.length) (fun t x _ => hitem t x) (fun t x x' _ => huniq t x x')
    h h' (Nat.le_refl _)

/-- `Each.unique`, for a rule that leaves at most one tree for fewer than `n` tokens. -/
theorem Each.unique_lt {α : Type} {rule : List SyntaxToken → α → Prop} {n : Nat}
    (hitem : ∀ t x, rule t x → Item t)
    (huniq : ∀ t, t.length < n → ∀ x x', rule t x → rule t x' → x = x')
    {tokens : List SyntaxToken} {items items' : List α}
    (h : Each rule tokens items) (h' : Each rule tokens items') (hn : tokens.length < n) :
    items = items' :=
  Each.unique (n := tokens.length) (fun t x _ => hitem t x)
    (fun t x x' ht => huniq t (by omega) x x') h h' (Nat.le_refl _)

/-! ## Parentheses -/

@[simp] theorem length_paren (tokens : List SyntaxToken) :
    (paren tokens).length = tokens.length + 2 := by
  simp [paren]

theorem paren_inj {a b : List SyntaxToken} : paren a = paren b ↔ a = b := by
  constructor
  · intro h
    simpa [paren] using h
  · intro h
    rw [h]

theorem paren_ne_nil (a : List SyntaxToken) : paren a ≠ [] := by
  simp [paren]

end BSmtLib.SpecChecks.Grammar
