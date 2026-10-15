module

public import BSmtLib.Facts.Proofs.Parser.Rejection.Sort
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Attribute
import all BSmtLib.Parser.Category.SExpr
import all BSmtLib.Parser.Category.Token

@[expose] public section

/-!
# What s-expressions and attributes can still take

The s-expression parser's state is its open lists, innermost first; after an s-expression in the
innermost open list come the list's further items and its `)`, then what follows that list in
turn (`sExprAfter`). The attribute parser reads attributes up to the `)` after them: exactly one
for `set-info` and `set-option`, any number for an annotation, which wants at least one
(`need`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Rejection.SExpr

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser.Category.SExpr.Internal (SExprState sExprStep sExprComplete)
open BSmtLib.Parser.Category.Attribute.Internal (AttributeState AttributeMode attributeStep)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Proofs.Parser.Rejection.Basic
open BSmtLib.Facts.Proofs.Parser.Rejection.«Sort» BSmtLib.Plain

open BSmtLib.Facts.Proofs.Parser.Rejection.Basic.Lang

/-! ## S-expressions -/

section

variable (version : BSmtLibSpec.Lexicon.Version)

/-- An s-expression of the version. -/
def SExprLang : Lang :=
  fun u => ∃ item : Tree.SExpr, item.Valid version ∧ u = toks item.tokens

/-- What follows an s-expression in the innermost open list: the list's further items and its
`)`, then what follows the list, outwards. -/
def sExprAfter : List (Array Nat) → Lang
  | [] => eps
  | _ :: outer => cat (star (SExprLang version)) (cat (tok closeItem) (sExprAfter outer))

/-- The remainders of the s-expression parser's states. -/
def sExprRem : SExprState Nat → Lang
  | [] => SExprLang version
  | level :: outer => sExprAfter version (level :: outer)

theorem sExprLang_nonempty : ∃ u, SExprLang version u :=
  ⟨_, ⟨.symbol ⟨[], false⟩, trivial, rfl⟩⟩

theorem sExprAfter_nonempty (levels : List (Array Nat)) : ∃ u, sExprAfter version levels u := by
  induction levels with
  | nil => exact ⟨[], rfl⟩
  | cons _ outer ih => exact cat_nonempty ⟨[], rep_nil⟩ (cat_nonempty ⟨_, tok_intro _⟩ ih)

theorem sExprRem_nonempty (levels : SExprState Nat) : ∃ u, sExprRem version levels u := by
  cases levels with
  | nil => exact sExprLang_nonempty version
  | cons level outer => exact sExprAfter_nonempty version (level :: outer)

/-- An s-expression, then what follows it, is a remainder of the parser before it. -/
theorem sExprRem_item {levels : SExprState Nat} {w v : List Received}
    (hw : SExprLang version w) (hv : sExprAfter version levels v) :
    sExprRem version levels (w ++ v) := by
  cases levels with
  | nil =>
    simp only [sExprAfter, eps] at hv
    subst hv
    simpa [sExprRem] using hw
  | cons level outer =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hv
    rw [← List.append_assoc]
    exact cat_intro (star_cons hw ha) hb

end

theorem sExprTokensAll_eq (items : List Tree.SExpr) :
    Tree.SExpr.tokensAll items = (items.map Tree.SExpr.tokens).flatten := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp [Tree.SExpr.tokensAll, ih]

theorem sExprValidAll_of {version : BSmtLibSpec.Lexicon.Version} {items : List Tree.SExpr}
    (h : ∀ item ∈ items, item.Valid version) : Tree.SExpr.ValidAll version items := by
  induction items with
  | nil => trivial
  | cons first rest ih =>
    exact ⟨h first (by simp), ih fun item hitem => h item (by simp [hitem])⟩

/-- S-expressions, one after another, as a repetition. -/
theorem sExprs_rep {version : BSmtLibSpec.Lexicon.Version} {lo : Nat} {hi : Option Nat}
    {u : List Received} (h : rep (SExprLang version) lo hi u) :
    ∃ items : List Tree.SExpr, Tree.SExpr.ValidAll version items ∧ lo ≤ items.length ∧
      u = toks (Tree.SExpr.tokensAll items) := by
  obtain ⟨items, hvalid, hlo, -, rfl⟩ := rep_trees h
  exact ⟨items, sExprValidAll_of hvalid, hlo, by simp [sExprTokensAll_eq, Function.comp_def]⟩

/-- A list's items and its `)`, after its `(`, are an s-expression. -/
theorem sExprLang_list {version : BSmtLibSpec.Lexicon.Version} {a : List Received}
    (h : star (SExprLang version) a) : SExprLang version (openItem :: (a ++ [closeItem])) := by
  obtain ⟨items, hvalid, -, rfl⟩ := sExprs_rep h
  exact ⟨.list items, hvalid, by simp [Tree.SExpr.tokens, paren, toks]⟩

/-- The s-expression parser's step at the end of an s-expression: it is the result, or the next
item of the innermost open list. -/
theorem sExprComplete_advances {version : BSmtLibSpec.Lexicon.Version} {state : SExprState Nat}
    {item : Received} (levels : SExprState Nat) (handled : Nat)
    (h : ∀ v, sExprAfter version levels v → sExprRem version state (item :: v)) :
    Advances (sExprRem version) (fun state _ => sExprRem version state) state item
      (sExprComplete levels handled) := by
  cases levels with
  | nil => exact fun _ => h [] rfl
  | cons level outer => exact fun _ => ⟨fun u hu => h u hu, sExprRem_nonempty version _⟩

/-- Every step of the s-expression parser advances. -/
theorem sExprStep_advances (version : Token.Version) :
    StepsAdvance version (sExprStep (H := List Event) version)
      (sExprRem (Bridge.version version))
      fun state _ => sExprRem (Bridge.version version) state := by
  intro state token item hitem hlex
  have atom : ∀ (node : Nodes.SExpr Nat) (x : Received),
      SExprLang (Bridge.version version) [x] →
      Sound (Advances (sExprRem (Bridge.version version))
        (fun state _ => sExprRem (Bridge.version version) state) state x) Benign
        (do
          let handled ← Parser.Internal.call (Traits.Handler.handleSExpr (H := List Event) node)
          pure (sExprComplete state handled)) := fun node x hx => by
    call_step
    exact Sound.pure (sExprComplete_advances _ _ fun v hv =>
      sExprRem_item _ (w := [x]) hx hv)
  cases token <;> simp only [sExprStep, pure_bind]
  · item_of hitem
    refine Sound.pure fun _ => ⟨fun u hu => ?_, sExprRem_nonempty _ _⟩
    obtain ⟨a, _, ha, ⟨c, r, rfl, hr, rfl⟩, rfl⟩ := hu
    have := sExprRem_item _ (sExprLang_list ha) hr
    simpa using this
  · cases state with
    | nil => fail_step
    | cons items outer =>
      item_of hitem
      call_step
      refine Sound.pure (sExprComplete_advances _ _ fun v hv => ?_)
      exact cat_intro' rep_nil (cat_intro (tok_intro _) hv) rfl
  · item_of hitem
    exact atom _ _ ⟨.constant _, trivial, rfl⟩
  · item_of hitem
    exact atom _ _ ⟨.symbol _, trivial, rfl⟩
  · item_of hitem
    exact atom _ _ ⟨.keyword _, trivial, rfl⟩
  · split
    · rename_i hversion
      item_of hitem
      exact atom _ _ ⟨.reserved _, ⟨atLeast_v2_6_of_ge hversion, hlex⟩, rfl⟩
    · fail_step
  · fail_step
  · fail_step

/-! ## Attributes -/

section

variable (version : BSmtLibSpec.Lexicon.Version)

/-- An attribute value of the version. -/
def ValueLang : Lang :=
  fun u => ∃ value : Tree.AttributeValue, value.Valid version ∧ u = toks value.tokens

/-- An attribute of the version. -/
def AttrLang : Lang :=
  fun u => ∃ attr : Tree.Attribute, attr.Valid version ∧ u = toks attr.tokens

/-- What follows an attribute: the `)` for a single attribute, otherwise further attributes and
the `)`. -/
def attrTail (single : Bool) : Lang :=
  if single then tok closeItem else cat (star (AttrLang version)) (tok closeItem)

/-- What follows an item of a list value: the list's further items, its `)`, and what follows
the attribute. -/
def valueRest (single : Bool) : Lang :=
  cat (star (SExprLang version)) (cat (tok closeItem) (attrTail version single))

/-- The remainders of the attribute parser's states: for a single attribute, or for
attributes, at least one if `need`. -/
def attrRem (single need : Bool) (state : AttributeState Nat Nat) : Lang :=
  match state.mode with
  | .start =>
    if single then
      if state.attributes.isEmpty then cat (AttrLang version) (tok closeItem) else tok closeItem
    else
      cat (rep (AttrLang version) (if need && state.attributes.isEmpty then 1 else 0) none)
        (tok closeItem)
  | .afterName _ => cat (union (ValueLang version) eps) (attrTail version single)
  | .inside _ _ sExpr outside =>
    if outside then
      union (cat (tok closeItem) (attrTail version single))
        (cat (sExprRem version sExpr) (valueRest version single))
    else cat (sExprRem version sExpr) (valueRest version single)

theorem attrLang_nonempty : ∃ u, AttrLang version u := ⟨_, ⟨⟨[], none⟩, trivial, rfl⟩⟩

theorem attrTail_nonempty (single : Bool) : ∃ u, attrTail version single u := by
  unfold attrTail
  split
  · exact ⟨_, tok_intro _⟩
  · exact cat_nonempty ⟨[], rep_nil⟩ ⟨_, tok_intro _⟩

theorem attrRem_nonempty (single need : Bool) (state : AttributeState Nat Nat) :
    ∃ u, attrRem version single need state u := by
  obtain ⟨mode, attributes⟩ := state
  have hrest := cat_nonempty ⟨[], rep_nil (A := SExprLang version) (hi := none)⟩
    (cat_nonempty ⟨_, tok_intro closeItem⟩ (attrTail_nonempty version single))
  cases mode with
  | start =>
    simp only [attrRem]
    split
    · split
      · exact cat_nonempty (attrLang_nonempty version) ⟨_, tok_intro _⟩
      · exact ⟨_, tok_intro _⟩
    · exact cat_nonempty (rep_nonempty (attrLang_nonempty version) _ none (by simp))
        ⟨_, tok_intro _⟩
  | afterName _ =>
    exact cat_nonempty ⟨[], Or.inr rfl⟩ (attrTail_nonempty version single)
  | inside _ _ sExpr outside =>
    simp only [attrRem]
    split
    · exact (cat_nonempty (sExprRem_nonempty version sExpr) hrest).elim fun u hu => ⟨u, Or.inr hu⟩
    · exact cat_nonempty (sExprRem_nonempty version sExpr) hrest

/-- After an attribute, the parser is where `attrTail` follows. -/
theorem attrRem_after (single need : Bool) (attributes : Array Nat) (handled : Nat)
    {u : List Received}
    (h : attrTail version single u) :
    attrRem version single need { mode := .start, attributes := attributes.push handled } u := by
  unfold attrTail at h
  simp only [attrRem, push_isEmpty, Bool.and_false, Bool.false_eq_true, ite_false]
  split
  · simpa [*] using h
  · simpa [*] using h

/-- An attribute, then what follows it. -/
theorem attrTail_cons {a u : List Received} (ha : AttrLang version a)
    (hu : attrTail version false u) : attrTail version false (a ++ u) := by
  unfold attrTail at hu ⊢
  obtain ⟨s, c, hs, hc, rfl⟩ := hu
  rw [← List.append_assoc]
  exact cat_intro (star_cons ha hs) hc

/-- A keyword and its value, if it has one, are an attribute. -/
theorem attrLang_keyword (name : BSmtLibSpec.Regex.Chars) {v : List Received}
    (hv : union (ValueLang version) eps v) : AttrLang version (.token (.keyword name) :: v) := by
  rcases hv with ⟨value, hvalid, rfl⟩ | rfl
  · exact ⟨⟨name, some value⟩, hvalid, rfl⟩
  · exact ⟨⟨name, none⟩, trivial, rfl⟩

/-- The items of a list value and its `)`, after its `(`, are a value. -/
theorem valueLang_list {a : List Received} (h : star (SExprLang version) a) :
    ValueLang version (openItem :: (a ++ [closeItem])) := by
  obtain ⟨items, hvalid, -, rfl⟩ := sExprs_rep h
  exact ⟨.list items, hvalid, by simp [Tree.AttributeValue.tokens, paren, toks]⟩

end

/-- In a list value, the s-expression parser's step, with its result in the attribute parser's
state. -/
theorem inside_advances (version : Token.Version) (single need : Bool)
    (keyword : Keyword) (items : Array Nat) (sExpr : SExprState Nat) (outside : Bool)
    (attributes : Array Nat) {item : Received} (r : Parser.Internal.Step (SExprState Nat) Nat)
    (hr : Advances (sExprRem (Bridge.version version))
      (fun state _ => sExprRem (Bridge.version version) state) sExpr item r) :
    Advances (attrRem (Bridge.version version) single need)
        (fun state (result : Array Nat) u => (need = true → result.isEmpty = false) →
          attrRem (Bridge.version version) single need state u)
        ⟨.inside keyword items sExpr outside, attributes⟩ item
      (match r with
        | .more sExpr' => .more ⟨.inside keyword items sExpr' false, attributes⟩
        | .done handled => .more ⟨.inside keyword (items.push handled) [] true, attributes⟩) := by
  have wrap : ∀ {u}, cat (sExprRem (Bridge.version version) sExpr)
      (valueRest (Bridge.version version) single) u →
      attrRem (Bridge.version version) single need ⟨.inside keyword items sExpr outside, attributes⟩
        u := by
    intro u hu
    simp only [attrRem]
    split
    · exact Or.inr hu
    · exact hu
  replace hr := hr.from (sExprRem_nonempty _ _)
  cases r with
  | more sExpr' =>
    refine fun _ => ⟨fun u hu => ?_, attrRem_nonempty _ _ _ _⟩
    simp only [attrRem, Bool.false_eq_true, ite_false] at hu
    obtain ⟨a, b, ha, hb, rfl⟩ := hu
    exact wrap (cat_intro' (hr.1 a ha) hb rfl)
  | done handled =>
    refine fun _ => ⟨fun u hu => ?_, attrRem_nonempty _ _ _ _⟩
    simp only [attrRem, ite_true] at hu
    refine wrap (cat_intro' hr ?_ rfl)
    rcases hu with ⟨c, t, rfl, ht, rfl⟩ | ⟨w, r, hw, ⟨s, t, hs, ht, rfl⟩, rfl⟩
    · exact cat_intro' rep_nil (cat_intro (tok_intro _) ht) rfl
    · rw [← List.append_assoc]
      exact cat_intro (star_cons hw hs) ht

/-- After an attribute: the remainders of the parser in its start state. -/
theorem attrRem_after_iff (version : BSmtLibSpec.Lexicon.Version) (single need : Bool)
    (attributes : Array Nat) (handled : Nat) {u : List Received}
    (h : attrRem version single need ⟨.start, attributes.push handled⟩ u) :
    attrTail version single u := by
  simp only [attrRem, push_isEmpty] at h
  unfold attrTail
  split <;> simp_all

/-- Every step of the attribute parser advances; it finishes with at least one attribute where
one is needed, and the remainders say so. -/
theorem attributeStep_advances (version : Token.Version) (single need : Bool) :
    StepsAdvance version (attributeStep (H := List Event) single version)
      (attrRem (Bridge.version version) single need)
      fun state (result : Array Nat) u => (need = true → result.isEmpty = false) →
        attrRem (Bridge.version version) single need state u := by
  intro ⟨mode, attributes⟩ token item hitem hlex
  cases mode with
  | start =>
    cases token <;> simp only [attributeStep, pure_bind, Parser.Category.Token.Internal.expectClose]
    case parenClose =>
      item_of hitem
      split
      · rename_i hsingle
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hsingle
        obtain ⟨rfl, hne⟩ := hsingle
        simp only [Bool.true_and, hne, Bool.false_eq_true, ite_false]
        refine Sound.pure fun _ _ => ?_
        simp only [attrRem, hne, Bool.false_eq_true, ite_true, ite_false]
        exact tok_intro _
      · rename_i hsingle
        split
        · fail_step
        · rename_i hsingle'
          refine Sound.pure fun _ hneed => ?_
          simp only [attrRem]
          split
          · rename_i hs
            subst hs
            simp_all
          · have : (need && attributes.isEmpty) = false := by
              cases need <;> simp_all
            simp only [this, Bool.false_eq_true, ite_false]
            exact cat_intro' rep_nil (tok_intro _) rfl
    case keyword name =>
      item_of hitem
      split
      · fail_step
      · rename_i hsingle
        refine Sound.pure fun _ => ⟨fun u hu => ?_, attrRem_nonempty _ _ _ _⟩
        obtain ⟨v, t, hv, ht, rfl⟩ := hu
        have hattr := attrLang_keyword _ (Bridge.keyword name) hv
        simp only [attrRem]
        split
        · rename_i hs
          subst hs
          have hne : attributes.isEmpty = true := by simpa using hsingle
          simp only [attrTail, ite_true] at ht
          simp only [hne, ite_true]
          exact cat_intro' hattr ht (by simp)
        · rename_i hs
          simp only [attrTail, hs, Bool.false_eq_true, ite_false] at ht
          obtain ⟨s, c, hs', hc, rfl⟩ := ht
          refine cat_intro' (rep_cons hattr (by split <;> simpa using hs') (by simp)) hc ?_
          simp
    all_goals (split <;> fail_step)
  | afterName keyword =>
    cases token <;> simp only [attributeStep] <;> try fail_step
    · item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => ?_, attrRem_nonempty _ _ _ _⟩
      simp only [attrRem, ite_true] at hu ⊢
      cases hu with
      | inl h =>
        obtain ⟨c, t, rfl, ht, rfl⟩ := h
        exact cat_intro' (Or.inl (valueLang_list _ (a := []) rep_nil)) ht (by simp)
      | inr h =>
        obtain ⟨w, r, hw, ⟨s, t, hs, ⟨c, t', rfl, ht', rfl⟩, rfl⟩, rfl⟩ := h
        exact cat_intro' (Or.inl (valueLang_list _ (star_cons hw hs))) ht' (by simp)
    · item_of hitem
      call_step
      split
      · rename_i hempty
        simp at hempty
      · refine Sound.pure fun _ _ => ?_
        refine cat_intro' (Or.inr rfl) ?_ rfl
        unfold attrTail
        split
        · exact tok_intro _
        · exact cat_intro' rep_nil (tok_intro _) rfl
    · item_of hitem
      call_step
      refine Sound.pure fun _ => ⟨fun u hu => ?_, attrRem_nonempty _ _ _ _⟩
      exact cat_intro' (Or.inl ⟨.constant _, trivial, rfl⟩) (attrRem_after_iff _ _ _ _ _ hu) rfl
    · item_of hitem
      call_step
      refine Sound.pure fun _ => ⟨fun u hu => ?_, attrRem_nonempty _ _ _ _⟩
      exact cat_intro' (Or.inl ⟨.symbol _, trivial, rfl⟩) (attrRem_after_iff _ _ _ _ _ hu) rfl
    · item_of hitem
      split
      · fail_step
      · rename_i hsingle
        simp only [Bool.not_eq_true] at hsingle
        subst hsingle
        call_step
        refine Sound.pure fun _ => ⟨fun u hu => ?_, attrRem_nonempty _ _ _ _⟩
        obtain ⟨v, t, hv, ht, rfl⟩ := hu
        exact cat_intro' (a := []) (Or.inr rfl)
          (by rw [← List.cons_append]; exact attrTail_cons _ (attrLang_keyword _ _ hv) ht) rfl
  | inside keyword items sExpr outside =>
    cases outside <;> cases token <;> simp only [attributeStep, ite_true,
      Bool.false_eq_true, ite_false]
    case true.parenClose =>
      item_of hitem
      call_step
      refine Sound.pure fun _ => ⟨fun u hu => ?_, attrRem_nonempty _ _ _ _⟩
      exact Or.inl (cat_tok (attrRem_after_iff _ _ _ _ _ hu))
    all_goals
      refine Sound.bind (sExprStep_advances version sExpr _ item hitem hlex) fun r hr => ?_
      cases r <;>
        exact Sound.pure (inside_advances version single need keyword items sExpr _ attributes _ hr)

/-- The attribute parser finishes with no attribute only without a call. -/
theorem attributeStep_done_silent (single : Bool) (version : Token.Version)
    (state : AttributeState Nat Nat) (token : Parser.Internal.Input) :
    ∀ events attrs events',
      (attributeStep (H := List Event) single version state token).run.run events =
        (.ok (.done attrs), events') → attrs.isEmpty = true → events' = events := by
  intro events attrs events' h hempty
  obtain ⟨mode, attributes⟩ := state
  cases mode with
  | start =>
    simp only [attributeStep] at h
    split at h
    · obtain ⟨_, ev₁, h₁, h₂⟩ := run_bind_ok_inv h
      have : ev₁ = events := by
        cases token <;> first | (cases h₁; rfl) | cases h₁
      subst this
      split at h₂ <;> cases h₂
      rfl
    · cases token
      case parenClose =>
        generalize instDecidableEqBool _ _ = d at h
        cases d <;> cases h
        rfl
      all_goals cases h
  | afterName keyword =>
    cases token <;> simp only [attributeStep] at h
    case parenClose =>
      obtain ⟨b, ev₁, -, h₂⟩ := run_bind_ok_inv h
      split at h₂ <;> cases h₂
      simp at hempty
    case keyword =>
      split at h
      · obtain ⟨b, ev₁, h₁, -⟩ := run_bind_ok_inv h
        cases h₁
      · obtain ⟨b, ev₁, -, h₂⟩ := run_bind_ok_inv h
        cases h₂
    case constant =>
      obtain ⟨b, ev₁, -, h₂⟩ := run_bind_ok_inv h
      cases h₂
    case symbol =>
      obtain ⟨b, ev₁, -, h₂⟩ := run_bind_ok_inv h
      cases h₂
    all_goals cases h
  | inside keyword items sExpr outside =>
    simp only [attributeStep] at h
    split at h
    · cases token
      case parenClose =>
        obtain ⟨b, ev₁, -, h₂⟩ := run_bind_ok_inv h
        cases h₂
      all_goals
        obtain ⟨b, ev₁, -, h₂⟩ := run_bind_ok_inv h
        cases b <;> cases h₂
    · obtain ⟨b, ev₁, -, h₂⟩ := run_bind_ok_inv h
      cases b <;> cases h₂

/-- The attribute parser writes no event where it finishes with no attribute, as
`Sound.bindOn` takes it. -/
theorem attributeStep_quiet (single : Bool) (version : Token.Version)
    (state : AttributeState Nat Nat) (token : Parser.Internal.Input) :
    ∀ events b events',
      (attributeStep (H := List Event) single version state token).run.run events =
      (.ok b, events') → (∃ a, b = .done a ∧ a.isEmpty = true) → events' = events :=
  fun _ _ _ hrun ⟨_, hv, he⟩ => by
    subst hv
    exact attributeStep_done_silent _ _ _ _ _ _ _ hrun he

theorem isEmpty_of_none {α : Type} {a : Array α} (h : ∀ x, a[0]? = some x → False) :
    a.isEmpty = true := by
  cases h' : a[0]? with
  | some x => exact absurd h' (h x)
  | none =>
    simp only [Array.getElem?_eq_none_iff] at h'
    rw [Array.isEmpty_iff_size_eq_zero]
    omega

end BSmtLib.Facts.Proofs.Parser.Rejection.SExpr
