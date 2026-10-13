import BSmtLib.SpecChecks.Parser.Recovery
import BSmtLib.SpecChecks.Parser.Simulation

/-!
# The traversal with a rebuilding handler

A handler that rebuilds as it is called (`rebuildHandler`): each call does what `Recovery.step`
does with it and returns the call's number, as a recording handler does. Run with it, the
traversal of a tree leaves at the number it returns what the tree is (`Built`), and the
traversal of a script leaves its commands.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Parser

open BSmtLibSpec BSmtLibSpec.Lexicon BSmtLibSpec.Grammar BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLibSpec.Lexicon.Properties
open BSmtLibSpec.Regex (Chars chars)
open BSmtLibSpec.Parser.Traversal Recovery

/-- The monad of a rebuilding run. -/
abbrev Rebuilding := StateM Recovery.State

/-- A handler that rebuilds as it is called, and fails where the calls do not rebuild. -/
def rebuildHandler : Handler Rebuilding Unit Recorded where
  call {returns} request := ExceptT.mk fun state =>
    match state.call request with
    | some next => (.ok (recordedValue returns state.env.length), next)
    | none => (.error (), state)
  setVersion version := modify fun state => { state.push .none with version }

/-- The points of a rebuilding run, which do nothing. -/
def rebuildPoints : Points Rebuilding := ⟨fun _ => pure (), fun _ => pure ()⟩

/-- The producer of a rebuilding run, which never refuses and does nothing. -/
def rebuildProducer : Producer Rebuilding := ⟨fun _ => pure (), pure ()⟩

/-- A run of the rebuilding handler. -/
abbrev RRun (α : Type) := Run Rebuilding Unit α

/-- The run from the state ends in the state with the result. -/
def Yields {α : Type} (x : RRun α) (state : Recovery.State) (a : α)
    (state' : Recovery.State) : Prop :=
  x.run.run state = (.ok a, state')

/-- The state is the earlier one with more fragments. -/
def Extends (state state' : Recovery.State) : Prop :=
  state'.version = state.version ∧ state'.pending = state.pending ∧
    state'.commands = state.commands ∧ ∃ more, state'.env = state.env ++ more

theorem Extends.refl (state : Recovery.State) : Extends state state :=
  ⟨rfl, rfl, rfl, [], by simp⟩

theorem Extends.trans {s₁ s₂ s₃ : Recovery.State} (h₁ : Extends s₁ s₂) (h₂ : Extends s₂ s₃) :
    Extends s₁ s₃ := by
  obtain ⟨v₁, p₁, c₁, m₁, e₁⟩ := h₁
  obtain ⟨v₂, p₂, c₂, m₂, e₂⟩ := h₂
  exact ⟨v₂.trans v₁, p₂.trans p₁, c₂.trans c₁, m₁ ++ m₂, by rw [e₂, e₁, List.append_assoc]⟩

theorem yields_bind {α β : Type} {x : RRun α} {f : α → RRun β} {s s' s'' : Recovery.State}
    {a : α} {b : β} (hx : Yields x s a s') (hf : Yields (f a) s' b s'') :
    Yields (x >>= f) s b s'' := by
  simp only [Yields, ExceptT.run_bind, StateT.run_bind] at hx hf ⊢
  rw [hx]
  exact hf

theorem yields_pure {α : Type} (a : α) (s : Recovery.State) : Yields (pure a) s a s := rfl

theorem yields_receive (item : Received) (s : Recovery.State) :
    Yields (Traversal.receive rebuildPoints item) s () s := rfl

theorem yields_take (token : SyntaxToken) (s : Recovery.State) :
    Yields (take rebuildPoints token) s () s := rfl

theorem yields_takeAll (tokens : List SyntaxToken) (s : Recovery.State) :
    Yields (takeAll rebuildPoints tokens) s () s := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    simp only [takeAll] at ih ⊢
    exact yields_bind (yields_take token s) ih

/-- The points of a rebuilding run do nothing, so an item's arrival makes only the calls due at
it. -/
theorem receive_rebuild (item : Received) (atArrival : RRun Unit) :
    Traversal.receive rebuildPoints item atArrival = atArrival := by
  simp [Traversal.receive, rebuildPoints]

theorem takeAllArriving_rebuild (atArrival : RRun Unit) (first : SyntaxToken)
    (rest : List SyntaxToken) :
    takeAllArriving rebuildPoints atArrival (first :: rest) =
      (atArrival >>= fun _ => takeAll rebuildPoints rest) := by
  simp [takeAllArriving, receive_rebuild]

theorem yields_takeAllArriving_pure (tokens : List SyntaxToken) (s : Recovery.State) :
    Yields (takeAllArriving rebuildPoints (pure ()) tokens) s () s := by
  cases tokens with
  | nil => rfl
  | cons token tokens =>
    rw [takeAllArriving_rebuild, pure_bind]
    exact yields_takeAll tokens s

theorem yields_call {returns : Returns} (request : Call Recorded returns) {s s' : Recovery.State}
    (h : s.call request = some s') :
    Yields (Traversal.call rebuildHandler request) s (recordedValue returns s.env.length) s' := by
  unfold Yields Traversal.call ExceptT.adapt
  simp only [rebuildHandler, ExceptT.run, ExceptT.mk, StateT.run, Functor.map, StateT.map, h]
  rfl

/-! ## Looking up what earlier calls stand for -/

theorem getElem?_append_of_some {β : Type} {l more : List β} {i : Nat} {x : β}
    (h : l[i]? = some x) : (l ++ more)[i]? = some x := by
  have hi : i < l.length := by
    rcases Nat.lt_or_ge i l.length with hi | hi
    · exact hi
    · simp [List.getElem?_eq_none hi] at h
  rw [List.getElem?_append_left hi, h]

theorem Env.sort_append {env more : Env} {i : Nat} {x : Tree.Sort} (h : env.sort i = some x) :
    (env ++ more).sort i = some x := by
  unfold Env.sort at h ⊢
  cases hi : env[i]? with
  | none => simp [hi] at h
  | some fragment => rw [getElem?_append_of_some hi]; simpa [hi] using h

theorem Env.sExpr_append {env more : Env} {i : Nat} {x : Tree.SExpr} (h : env.sExpr i = some x) :
    (env ++ more).sExpr i = some x := by
  unfold Env.sExpr at h ⊢
  cases hi : env[i]? with
  | none => simp [hi] at h
  | some fragment => rw [getElem?_append_of_some hi]; simpa [hi] using h

theorem Env.attribute_append {env more : Env} {i : Nat} {x : Tree.Attribute}
    (h : env.«attribute» i = some x) : (env ++ more).«attribute» i = some x := by
  unfold Env.«attribute» at h ⊢
  cases hi : env[i]? with
  | none => simp [hi] at h
  | some fragment => rw [getElem?_append_of_some hi]; simpa [hi] using h

theorem Env.term_append {env more : Env} {i : Nat} {x : Tree.Term} (h : env.term i = some x) :
    (env ++ more).term i = some x := by
  unfold Env.term at h ⊢
  cases hi : env[i]? with
  | none => simp [hi] at h
  | some fragment => rw [getElem?_append_of_some hi]; simpa [hi] using h

theorem Env.bindings_append {env more : Env} {i : Nat} {x : List (Tree.Symbol × Tree.Term)}
    (h : env.bindings i = some x) : (env ++ more).bindings i = some x := by
  unfold Env.bindings at h ⊢
  cases hi : env[i]? with
  | none => simp [hi] at h
  | some fragment => rw [getElem?_append_of_some hi]; simpa [hi] using h

theorem Env.variables_append {env more : Env} {i : Nat} {x : List Tree.SortedVar}
    (h : env.variables i = some x) : (env ++ more).variables i = some x := by
  unfold Env.variables at h ⊢
  cases hi : env[i]? with
  | none => simp [hi] at h
  | some fragment => rw [getElem?_append_of_some hi]; simpa [hi] using h

/-- Lookups of a list in an environment give the same in a longer one. -/
theorem mapM_append {α β : Type} {lookup : Env → α → Option β}
    (hl : ∀ env more i x, lookup env i = some x → lookup (env ++ more) i = some x)
    {env more : Env} {list : List α} {xs : List β} (h : list.mapM (lookup env) = some xs) :
    list.mapM (lookup (env ++ more)) = some xs := by
  induction list generalizing xs with
  | nil => simpa using h
  | cons i list ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind] at h ⊢
    cases hi : lookup env i with
    | none => simp [hi] at h
    | some x =>
      cases hr : list.mapM (lookup env) with
      | none => simp [hi, hr] at h
      | some rest =>
        simp [hi, hr] at h
        simp [hl _ _ _ _ hi, ih hr, ← h]

theorem push_env (s : Recovery.State) (fragment : Fragment) :
    (s.push fragment).env = s.env ++ [fragment] := rfl

theorem extends_push (s : Recovery.State) (fragment : Fragment) : Extends s (s.push fragment) :=
  ⟨rfl, rfl, rfl, [fragment], rfl⟩

theorem push_getElem (s : Recovery.State) (fragment : Fragment) :
    (s.push fragment).env[s.env.length]? = some fragment := by
  simp [push_env]

/-! ## Sorts -/

/-- The traversal of a sort, with the rebuilding handler. -/
abbrev rSort := sort (ε := Unit) rebuildPoints rebuildHandler

theorem built_sort : ∀ n (t : Tree.Sort) (s : Recovery.State), sizeOf t < n →
    ∃ (i : Nat) (s' : Recovery.State),
    Yields (rSort t) s i s' ∧ Extends s s' ∧ s'.env.sort i = some t
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, ⟨identifier, arguments⟩, s, h => by
    simp only [Tree.Sort.mk.sizeOf_spec] at h
    cases arguments with
    | nil =>
      refine ⟨s.env.length, s.push (.sort ⟨identifier, []⟩), ?_, extends_push _ _, ?_⟩
      · rw [rSort, sort_nil]
        exact yields_bind (yields_takeAll _ s) (yields_call _ (by
          simp [State.call, Env.fragment]; exact ⟨[], rfl, rfl⟩))
      · simp [Env.sort, push_getElem]
    | cons first others =>
      -- the sorts of the arguments, one after another
      have hargs : ∀ (list : List Tree.Sort) (s : Recovery.State), sizeOf list < n →
          ∃ (is : List Nat) (s' : Recovery.State),
           Yields (sorts (ε := Unit) rebuildPoints rebuildHandler list) s is s' ∧
            Extends s s' ∧ is.mapM s'.env.sort = some list := by
        intro list
        induction list with
        | nil => intro s _; exact ⟨[], s, rfl, Extends.refl s, rfl⟩
        | cons a list ih =>
          intro s hl
          simp only [List.cons.sizeOf_spec] at hl
          obtain ⟨i, s₁, h₁, e₁, d₁⟩ := built_sort n a s (by omega)
          obtain ⟨is, s₂, h₂, e₂, d₂⟩ := ih s₁ (by omega)
          refine ⟨i :: is, s₂, ?_, e₁.trans e₂, ?_⟩
          · simp only [sorts]
            exact yields_bind h₁ (yields_bind h₂ (yields_pure _ _))
          · obtain ⟨-, -, -, more, hm⟩ := e₂
            rw [hm] at d₂ ⊢
            simp [Env.sort_append d₁, d₂]
      obtain ⟨is, s₁, h₁, e₁, d₁⟩ := hargs (first :: others) s (by omega)
      refine ⟨s₁.env.length, s₁.push (.sort ⟨identifier, first :: others⟩), ?_,
        e₁.trans (extends_push _ _), ?_⟩
      · rw [rSort, sort_cons]
        refine yields_bind (yields_take _ s) (yields_bind (yields_takeAll _ s)
          (yields_bind h₁ (yields_bind (yields_take _ s₁) (yields_call _ ?_))))
        simp [State.call, Env.fragment, d₁]
      · simp [Env.sort, push_getElem]

/-! ## Lists -/

/-- A run over a list, each element of which rebuilds to what it denotes, rebuilds the list. -/
theorem mapM_some_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l.length = l'.length
  | [], l', h => by
    simp only [List.mapM_nil] at h
    cases h
    rfl
  | a :: l, l', h => by
    simp only [List.mapM_cons] at h
    cases hb : f a with
    | none => simp [hb] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hb, hl] at h
      | some bs =>
        simp [hb, hl] at h
        subst h
        simp [mapM_some_length hl]

theorem built_mapM {α β γ : Type} (F : β → RRun α) (look : Env → α → Option γ)
    (hmono : ∀ env more a x, look env a = some x → look (env ++ more) a = some x)
    (denote : β → γ) :
    ∀ (list : List β), (∀ b ∈ list, ∀ s, ∃ (a : α) (s' : Recovery.State),
      Yields (F b) s a s' ∧ Extends s s' ∧ look s'.env a = some (denote b)) →
    ∀ s, ∃ (as : List α) (s' : Recovery.State), Yields (list.mapM F) s as s' ∧ Extends s s' ∧
      as.mapM (look s'.env) = some (list.map denote)
  | [], _, s => ⟨[], s, rfl, Extends.refl s, rfl⟩
  | b :: list, hb, s => by
    obtain ⟨a, s₁, h₁, e₁, d₁⟩ := hb b (by simp) s
    obtain ⟨as, s₂, h₂, e₂, d₂⟩ :=
      built_mapM F look hmono denote list (fun b' hb' => hb b' (by simp [hb'])) s₁
    refine ⟨a :: as, s₂, ?_, e₁.trans e₂, ?_⟩
    · simp only [List.mapM_cons]
      exact yields_bind h₁ (yields_bind h₂ (yields_pure _ _))
    · obtain ⟨-, -, -, more, hm⟩ := e₂
      rw [hm] at d₂ ⊢
      simp [hmono _ _ _ _ d₁, d₂]

/-! ## S-expressions and attributes -/

/-- The traversal of an s-expression, with the rebuilding handler. -/
abbrev rSExpr := sExpr (ε := Unit) rebuildPoints rebuildHandler

theorem yields_value_call {returns : Returns} (request : Call Recorded returns)
    (s : Recovery.State) {fragment : Fragment} (h : s.env.fragment request = some fragment)
    (hr : returns ≠ .nothing) :
    Yields (Traversal.call rebuildHandler request) s (recordedValue returns s.env.length)
      (s.push fragment) := by
  apply yields_call
  cases returns <;> first | exact absurd rfl hr | simp [State.call, h]

theorem built_sExpr : ∀ n (t : Tree.SExpr) (s : Recovery.State), sizeOf t < n →
    ∃ (i : Nat) (s' : Recovery.State), Yields (rSExpr t) s i s' ∧ Extends s s' ∧
      s'.env.sExpr i = some t
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, t, s, h => by
    cases t with
    | list items =>
      simp only [Tree.SExpr.list.sizeOf_spec] at h
      obtain ⟨is, s₁, h₁, e₁, d₁⟩ := built_mapM (rSExpr) Env.sExpr
        (fun _ _ _ _ h => Env.sExpr_append h) id items
        (fun b hb s => built_sExpr n b s (by have := List.sizeOf_lt_of_mem hb; omega)) s
      refine ⟨s₁.env.length, s₁.push (.sExpr (.list items)), ?_, e₁.trans (extends_push _ _),
        by simp [Env.sExpr, push_getElem]⟩
      rw [rSExpr, sExpr_list, sExprs_eq]
      refine yields_bind (yields_take _ s) (yields_bind h₁ (yields_bind (yields_take _ s₁)
        (yields_value_call _ _ ?_ (by intro h; cases h))))
      simp only [List.map_id] at d₁
      simp [Env.fragment, Env.sExprNode]
      exact d₁
    | constant constant =>
      refine ⟨s.env.length, s.push (.sExpr (.constant constant)), ?_, extends_push _ _,
        by simp [Env.sExpr, push_getElem]⟩
      rw [rSExpr, sExpr_constant]
      exact yields_bind (yields_take _ s) (yields_value_call _ _ rfl (by intro h; cases h))
    | symbol symbol =>
      refine ⟨s.env.length, s.push (.sExpr (.symbol symbol)), ?_, extends_push _ _,
        by simp [Env.sExpr, push_getElem]⟩
      rw [rSExpr, sExpr_symbol]
      exact yields_bind (yields_take _ s) (yields_value_call _ _ rfl (by intro h; cases h))
    | reserved w =>
      refine ⟨s.env.length, s.push (.sExpr (.reserved w)), ?_, extends_push _ _,
        by simp [Env.sExpr, push_getElem]⟩
      rw [rSExpr, sExpr_reserved]
      exact yields_bind (yields_take _ s) (yields_value_call _ _ rfl (by intro h; cases h))
    | keyword name =>
      refine ⟨s.env.length, s.push (.sExpr (.keyword name)), ?_, extends_push _ _,
        by simp [Env.sExpr, push_getElem]⟩
      rw [rSExpr, sExpr_keyword]
      exact yields_bind (yields_take _ s) (yields_value_call _ _ rfl (by intro h; cases h))

theorem built_sExprs (items : List Tree.SExpr) (s : Recovery.State) :
    ∃ (is : List Nat) (s' : Recovery.State),
      Yields (sExprs (ε := Unit) rebuildPoints rebuildHandler items) s is s' ∧ Extends s s' ∧
        is.mapM s'.env.sExpr = some items := by
  rw [sExprs_eq]
  obtain ⟨is, s', h, e, d⟩ := built_mapM rSExpr Env.sExpr
    (fun _ _ _ _ h => Env.sExpr_append h) id items
    (fun b _ s => built_sExpr (sizeOf b + 1) b s (by omega)) s
  exact ⟨is, s', h, e, by simp at d; exact d⟩

theorem valueNode_append {env more : Env} {node : AttributeValueNode Recorded}
    {value : Tree.AttributeValue} (h : env.valueNode node = some value) :
    (env ++ more).valueNode node = some value := by
  cases node with
  | list items =>
    simp only [Env.valueNode, Option.map_eq_some_iff] at h ⊢
    obtain ⟨xs, hx, rfl⟩ := h
    exact ⟨xs, mapM_append (fun _ _ _ _ h => Env.sExpr_append h) hx, rfl⟩
  | _ => simpa [Env.valueNode] using h

theorem built_attributeValue (value : Tree.AttributeValue) (s : Recovery.State) :
    ∃ (node : AttributeValueNode Recorded) (s' : Recovery.State),
      Yields (attributeValue (ε := Unit) rebuildPoints rebuildHandler value) s node s' ∧
        Extends s s' ∧ s'.env.valueNode node = some value := by
  cases value with
  | constant constant =>
    exact ⟨.constant constant, s, yields_bind (yields_take _ s) (yields_pure _ _),
      Extends.refl s, rfl⟩
  | symbol symbol =>
    exact ⟨.symbol symbol, s, yields_bind (yields_take _ s) (yields_pure _ _),
      Extends.refl s, rfl⟩
  | list items =>
    obtain ⟨is, s₁, h₁, e₁, d₁⟩ := built_sExprs items s
    refine ⟨.list is, s₁, ?_, e₁, by simp [Env.valueNode, d₁]⟩
    simp only [attributeValue]
    exact yields_bind (yields_take _ s) (yields_bind h₁ (yields_bind (yields_take _ s₁)
      (yields_pure _ _)))

/-- The traversal of an attribute after its keyword, with the rebuilding handler. -/
theorem built_attributeThen (keyword : Chars) (following : SyntaxToken)
    (value : Option Tree.AttributeValue) (s : Recovery.State) :
    ∃ (i : Nat) (s' : Recovery.State),
      Yields (attributeThen (ε := Unit) rebuildPoints rebuildHandler keyword following value)
        s i s' ∧ Extends s s' ∧ s'.env.«attribute» i = some ⟨keyword, value⟩ := by
  cases value with
  | none =>
    refine ⟨s.env.length, s.push (.«attribute» ⟨keyword, none⟩), ?_, extends_push _ _,
      by simp [Env.«attribute», push_getElem]⟩
    rw [attributeThen_none]
    exact yields_bind (yields_take _ s) (yields_value_call _ _ rfl (by intro h; cases h))
  | some value =>
    obtain ⟨node, s₁, h₁, e₁, d₁⟩ := built_attributeValue value s
    refine ⟨s₁.env.length, s₁.push (.«attribute» ⟨keyword, some value⟩), ?_,
      e₁.trans (extends_push _ _), by simp [Env.«attribute», push_getElem]⟩
    rw [attributeThen_some]
    exact yields_bind h₁ (yields_bind
      (yields_value_call _ _ (by simp [Env.fragment, d₁]) (by intro h; cases h))
      (yields_bind (yields_take _ _) (yields_pure _ _)))

theorem built_attributesThen : ∀ (attributes : List Tree.Attribute) (keyword : Chars)
    (value : Option Tree.AttributeValue) (s : Recovery.State),
    ∃ (is : List Nat) (s' : Recovery.State),
      Yields (attributesThen (ε := Unit) rebuildPoints rebuildHandler keyword value attributes)
        s is s' ∧ Extends s s' ∧ is.mapM s'.env.«attribute» = some (⟨keyword, value⟩ :: attributes)
  | [], keyword, value, s => by
    obtain ⟨i, s₁, h₁, e₁, d₁⟩ := built_attributeThen keyword .parenClose value s
    refine ⟨[i], s₁, ?_, e₁, by simp [d₁]⟩
    simp only [attributesThen]
    exact yields_bind h₁ (yields_pure _ _)
  | ⟨next, nextValue⟩ :: attributes, keyword, value, s => by
    obtain ⟨i, s₁, h₁, e₁, d₁⟩ := built_attributeThen keyword (.keyword next) value s
    obtain ⟨is, s₂, h₂, e₂, d₂⟩ := built_attributesThen attributes next nextValue s₁
    refine ⟨i :: is, s₂, ?_, e₁.trans e₂, ?_⟩
    · simp only [attributesThen]
      exact yields_bind h₁ (yields_bind h₂ (yields_pure _ _))
    · obtain ⟨-, -, -, more, hm⟩ := e₂
      rw [hm] at d₂ ⊢
      simp [Env.attribute_append d₁, d₂]

/-! ## Terms -/

theorem yields_unit_call (request : Call Recorded .nothing) {s : Recovery.State}
    (h : (s.push .none).command request = some (s.push .none)) :
    Yields (Traversal.call rebuildHandler request) s () (s.push .none) :=
  yields_call request (by simp [State.call, h])

theorem qualIdentifier_append {env more : Env} {identifier : Tree.Identifier}
    {sort : Option Nat} {qualified : Tree.QualIdentifier}
    (h : env.qualIdentifier identifier sort = some qualified) :
    (env ++ more).qualIdentifier identifier sort = some qualified := by
  cases sort with
  | none => simpa [Env.qualIdentifier] using h
  | some i =>
    simp only [Env.qualIdentifier, Option.map_eq_some_iff] at h ⊢
    obtain ⟨x, hx, rfl⟩ := h
    exact ⟨x, Env.sort_append hx, rfl⟩

theorem built_qualIdentifier (qualified : Tree.QualIdentifier) (s : Recovery.State) :
    ∃ (result : Tree.Identifier × Option Nat) (s' : Recovery.State),
      Yields (qualIdentifier (ε := Unit) rebuildPoints rebuildHandler qualified) s result s' ∧
        Extends s s' ∧ s'.env.qualIdentifier result.1 result.2 = some qualified := by
  cases qualified with
  | plain identifier =>
    exact ⟨(identifier, none), s,
      yields_bind (yields_takeAllArriving_pure _ s) (yields_pure _ _),
      Extends.refl s, rfl⟩
  | as identifier sort =>
    obtain ⟨i, s₁, h₁, e₁, d₁⟩ := built_sort (sizeOf sort + 1) sort s (by omega)
    refine ⟨(identifier, some i), s₁, ?_, e₁, by simp [Env.qualIdentifier, d₁]⟩
    simp only [qualIdentifier]
    exact yields_bind (yields_takeAllArriving_pure _ s) (yields_bind (yields_takeAll _ s)
      (yields_bind h₁ (yields_bind (yields_take _ s₁) (yields_pure _ _))))

/-- What a sorted variable is in an environment, from its symbol and the number of its sort. -/
def sortedVarOf (env : Env) (variable' : Tree.Symbol × Nat) : Option Tree.SortedVar :=
  (env.sort variable'.2).map fun sort => ⟨variable'.1, sort⟩

theorem sortedVarOf_append {env more : Env} {variable' : Tree.Symbol × Nat}
    {x : Tree.SortedVar} (h : sortedVarOf env variable' = some x) :
    sortedVarOf (env ++ more) variable' = some x := by
  simp only [sortedVarOf, Option.map_eq_some_iff] at h ⊢
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨y, Env.sort_append hy, rfl⟩

theorem sortedVars_eq_mapM (env : Env) (list : List (Tree.Symbol × Nat)) :
    env.sortedVars list = list.mapM (sortedVarOf env) := rfl

theorem built_sortedVars (variables : List Tree.SortedVar) (s : Recovery.State) :
    ∃ (handled : List (Tree.Symbol × Nat)) (s' : Recovery.State),
      Yields (sortedVars (ε := Unit) rebuildPoints rebuildHandler variables) s handled s' ∧
        Extends s s' ∧ s'.env.sortedVars handled = some variables := by
  rw [sortedVars_eq]
  obtain ⟨handled, s', h, e, d⟩ := built_mapM (α := Tree.Symbol × Nat)
    (sortedVarRun (ε := Unit) (points := rebuildPoints) (handler := rebuildHandler)) sortedVarOf
    (fun _ _ _ _ h => sortedVarOf_append h) id variables (fun ⟨symbol, sort⟩ _ s => by
      obtain ⟨i, s₁, h₁, e₁, d₁⟩ := built_sort (sizeOf sort + 1) sort s (by omega)
      refine ⟨(symbol, i), s₁, ?_, e₁, by simp [sortedVarOf, d₁]⟩
      simp only [sortedVarRun]
      exact yields_bind (yields_takeAll _ s) (yields_bind h₁ (yields_bind (yields_take _ s₁)
        (yields_pure _ _)))) s
  exact ⟨handled, s', h, e, by rw [sortedVars_eq_mapM]; simpa using d⟩

/-- What a binding is in an environment, from its symbol and the number of its term. -/
def bindingOf (env : Env) (binding : Tree.Symbol × Nat) : Option (Tree.Symbol × Tree.Term) :=
  (env.term binding.2).map (binding.1, ·)

/-- What a case is in an environment, from its pattern and the number of its body. -/
def caseOf (env : Env) (matchCase : Tree.Pattern × Nat) : Option (Tree.Pattern × Tree.Term) :=
  (env.term matchCase.2).map (matchCase.1, ·)

theorem bindingOf_append {env more : Env} {b : Tree.Symbol × Nat} {x : Tree.Symbol × Tree.Term}
    (h : bindingOf env b = some x) : bindingOf (env ++ more) b = some x := by
  simp only [bindingOf, Option.map_eq_some_iff] at h ⊢
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨y, Env.term_append hy, rfl⟩

theorem caseOf_append {env more : Env} {c : Tree.Pattern × Nat} {x : Tree.Pattern × Tree.Term}
    (h : caseOf env c = some x) : caseOf (env ++ more) c = some x := by
  simp only [caseOf, Option.map_eq_some_iff] at h ⊢
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨y, Env.term_append hy, rfl⟩

/-- The traversal of a term, with the rebuilding handler. -/
abbrev rTerm := term (ε := Unit) rebuildPoints rebuildHandler

/-- What `built_term` proves for terms smaller than `n`. -/
def TermsBuilt (n : Nat) : Prop :=
  ∀ (t : Tree.Term) (s : Recovery.State), sizeOf t < n →
    ∃ (i : Nat) (s' : Recovery.State), Yields (rTerm t) s i s' ∧ Extends s s' ∧
      s'.env.term i = some t

theorem built_terms {n : Nat} (ih : TermsBuilt n) (list : List Tree.Term) (h : sizeOf list < n)
    (s : Recovery.State) :
    ∃ (is : List Nat) (s' : Recovery.State),
      Yields (terms (ε := Unit) rebuildPoints rebuildHandler list) s is s' ∧ Extends s s' ∧
        is.mapM s'.env.term = some list := by
  rw [terms_eq]
  obtain ⟨is, s', hy, e, d⟩ := built_mapM (α := Nat) rTerm Env.term
    (fun _ _ _ _ h => Env.term_append h) id list
    (fun b hb s => ih b s (by have := List.sizeOf_lt_of_mem hb; omega)) s
  exact ⟨is, s', hy, e, by simp at d; exact d⟩

theorem built_bindings {n : Nat} (ih : TermsBuilt n) (list : List (Tree.Symbol × Tree.Term))
    (h : sizeOf list < n) (s : Recovery.State) :
    ∃ (handled : List (Tree.Symbol × Nat)) (s' : Recovery.State),
      Yields (bindings (ε := Unit) rebuildPoints rebuildHandler list) s handled s' ∧
        Extends s s' ∧ handled.mapM (bindingOf s'.env) = some list := by
  rw [bindings_eq]
  obtain ⟨handled, s', hy, e, d⟩ := built_mapM (α := Tree.Symbol × Nat)
    (bindingRun (ε := Unit) (points := rebuildPoints) (handler := rebuildHandler)) bindingOf
    (fun _ _ _ _ h => bindingOf_append h) id list (fun ⟨symbol, t⟩ hb s => by
      have hb' := List.sizeOf_lt_of_mem hb
      simp only [Prod.mk.sizeOf_spec] at hb'
      obtain ⟨i, s₁, h₁, e₁, d₁⟩ := ih t s (by omega)
      refine ⟨(symbol, i), s₁, ?_, e₁, by simp [bindingOf, d₁]⟩
      simp only [bindingRun]
      exact yields_bind (yields_takeAll _ s) (yields_bind h₁ (yields_bind (yields_take _ s₁)
        (yields_pure _ _)))) s
  exact ⟨handled, s', hy, e, by simpa using d⟩

theorem built_cases {n : Nat} (ih : TermsBuilt n) (scrutinee : Recorded.term)
    (list : List (Tree.Pattern × Tree.Term)) (h : sizeOf list < n) (s : Recovery.State) :
    ∃ (handled : List (Tree.Pattern × Nat)) (s' : Recovery.State),
      Yields (cases (ε := Unit) rebuildPoints rebuildHandler scrutinee list) s handled s' ∧
        Extends s s' ∧ handled.mapM (caseOf s'.env) = some list := by
  rw [cases_eq]
  obtain ⟨handled, s', hy, e, d⟩ := built_mapM (α := Tree.Pattern × Nat)
    (caseRun (ε := Unit) (points := rebuildPoints) (handler := rebuildHandler) scrutinee) caseOf
    (fun _ _ _ _ h => caseOf_append h) id list (fun ⟨pattern, t⟩ hb s => by
      have hb' := List.sizeOf_lt_of_mem hb
      simp only [Prod.mk.sizeOf_spec] at hb'
      obtain ⟨i, s₁, h₁, e₁, d₁⟩ := ih t (s.push (.pattern pattern)) (by omega)
      refine ⟨(pattern, s₁.env.length), s₁.push (.term t), ?_,
        (extends_push _ _).trans (e₁.trans (extends_push _ _)),
        by simp [caseOf, Env.term, push_getElem]⟩
      simp only [caseRun]
      exact yields_bind (yields_take _ s) (yields_bind (yields_takeAll _ s)
        (yields_bind (yields_value_call _ _ rfl (by intro h; cases h))
          (yields_bind h₁ (yields_bind (yields_take _ s₁)
            (yields_bind (yields_value_call _ _ (by simp [Env.fragment, d₁])
              (by intro h; cases h)) (yields_pure _ _))))))) s
  exact ⟨handled, s', hy, e, by simpa using d⟩

/-- What is looked up in an earlier state is the same in a later one. -/
theorem Extends.look {β : Type} {look : Env → Option β}
    (hmono : ∀ env more x, look env = some x → look (env ++ more) = some x)
    {s s' : Recovery.State} (e : Extends s s') {x : β} (h : look s.env = some x) :
    look s'.env = some x := by
  obtain ⟨-, -, -, more, hm⟩ := e
  rw [hm]
  exact hmono _ _ _ h

theorem Extends.term {s s' : Recovery.State} (e : Extends s s') {i : Nat} {x : Tree.Term}
    (h : s.env.term i = some x) : s'.env.term i = some x :=
  e.look (look := fun env => env.term i) (fun _ _ _ h => Env.term_append h) h

theorem Extends.terms {s s' : Recovery.State} (e : Extends s s') {is : List Nat}
    {xs : List Tree.Term} (h : is.mapM s.env.term = some xs) : is.mapM s'.env.term = some xs :=
  e.look (look := fun env => is.mapM env.term)
    (fun _ _ _ h => mapM_append (fun _ _ _ _ h => Env.term_append h) h) h

theorem built_term : ∀ n, TermsBuilt n
  | 0 => fun _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => by
    have ih := built_term n
    intro t s h
    cases t with
    | constant constant =>
      refine ⟨s.env.length, s.push (.term (.constant constant)), ?_, extends_push _ _,
        by simp [Env.term, push_getElem]⟩
      rw [rTerm, term_constant]
      exact yields_bind (yields_take _ s) (yields_value_call _ _ rfl (by intro h; cases h))
    | identifier qualified =>
      obtain ⟨⟨identifier, sort⟩, s₁, h₁, e₁, d₁⟩ := built_qualIdentifier qualified s
      refine ⟨s₁.env.length, s₁.push (.term (.identifier qualified)), ?_,
        e₁.trans (extends_push _ _), by simp [Env.term, push_getElem]⟩
      rw [rTerm, term_identifier]
      exact yields_bind h₁ (yields_value_call _ _ (by simp [Env.fragment, Env.termNode, d₁])
        (by intro h; cases h))
    | application function arguments =>
      simp only [Tree.Term.application.sizeOf_spec] at h
      obtain ⟨⟨identifier, sort⟩, s₁, h₁, e₁, d₁⟩ := built_qualIdentifier function s
      obtain ⟨is, s₂, h₂, e₂, d₂⟩ := built_terms ih arguments (by omega) s₁
      refine ⟨s₂.env.length, s₂.push (.term (.application function arguments)), ?_,
        e₁.trans (e₂.trans (extends_push _ _)), by simp [Env.term, push_getElem]⟩
      rw [rTerm, term_application]
      refine yields_bind (yields_take _ s) (yields_bind h₁ (yields_bind h₂
        (yields_bind (yields_take _ s₂) (yields_value_call _ _ ?_ (by intro h; cases h)))))
      have d₁' := e₂.look (look := fun env => env.qualIdentifier identifier sort)
        (fun _ _ _ h => qualIdentifier_append h) d₁
      simp only [Env.fragment, Env.termNode, d₁', Option.bind_eq_bind, Option.bind_some]
      erw [d₂]
      rfl
    | «let» bindingList body =>
      simp only [Tree.Term.let.sizeOf_spec] at h
      obtain ⟨handled, s₁, h₁, e₁, d₁⟩ := built_bindings ih bindingList (by omega) s
      obtain ⟨i, s₂, h₂, e₂, d₂⟩ := ih body (s₁.push (.bindings bindingList)) (by omega)
      refine ⟨s₂.env.length, s₂.push (.term (.«let» bindingList body)), ?_,
        e₁.trans ((extends_push _ _).trans (e₂.trans (extends_push _ _))),
        by simp [Env.term, push_getElem]⟩
      rw [rTerm, term_let]
      refine yields_bind (yields_takeAll _ s) (yields_bind h₁ (yields_bind (yields_take _ s₁)
        (yields_bind (yields_value_call _ _ ?_ (by intro h; cases h)) (yields_bind h₂
          (yields_bind (yields_take _ s₂) (yields_value_call _ _ ?_ (by intro h; cases h)))))))
      · simp [Env.fragment]
        exact d₁
      · have hb : s₂.env.bindings s₁.env.length = some bindingList :=
          e₂.look (look := fun env => env.bindings s₁.env.length)
            (fun _ _ _ h => Env.bindings_append h) (by simp [Env.bindings, push_getElem])
        simp [Env.fragment, recordedValue, hb, d₂]
    | lambda variables body =>
      simp only [Tree.Term.lambda.sizeOf_spec] at h
      obtain ⟨handled, s₁, h₁, e₁, d₁⟩ := built_sortedVars variables s
      obtain ⟨i, s₂, h₂, e₂, d₂⟩ := ih body (s₁.push (.variables variables)) (by omega)
      refine ⟨s₂.env.length, s₂.push (.term (.lambda variables body)), ?_,
        e₁.trans ((extends_push _ _).trans (e₂.trans (extends_push _ _))),
        by simp [Env.term, push_getElem]⟩
      rw [rTerm, term_lambda]
      refine yields_bind (yields_takeAll _ s) (yields_bind h₁ (yields_bind (yields_take _ s₁)
        (yields_bind (yields_value_call _ _ ?_ (by intro h; cases h)) (yields_bind h₂
          (yields_bind (yields_take _ s₂) (yields_value_call _ _ ?_ (by intro h; cases h)))))))
      · simp [Env.fragment, d₁]
      · have hv : s₂.env.variables s₁.env.length = some variables :=
          e₂.look (look := fun env => env.variables s₁.env.length)
            (fun _ _ _ h => Env.variables_append h) (by simp [Env.variables, push_getElem])
        simp [Env.fragment, recordedValue, hv, d₂]
    | quantified quantifier variables body =>
      simp only [Tree.Term.quantified.sizeOf_spec] at h
      obtain ⟨handled, s₁, h₁, e₁, d₁⟩ := built_sortedVars variables s
      obtain ⟨i, s₂, h₂, e₂, d₂⟩ := ih body (s₁.push (.variables variables)) (by omega)
      refine ⟨s₂.env.length, s₂.push (.term (.quantified quantifier variables body)), ?_,
        e₁.trans ((extends_push _ _).trans (e₂.trans (extends_push _ _))),
        by simp [Env.term, push_getElem]⟩
      rw [rTerm, term_quantified]
      refine yields_bind (yields_takeAll _ s) (yields_bind h₁ (yields_bind (yields_take _ s₁)
        (yields_bind (yields_value_call _ _ ?_ (by intro h; cases h)) (yields_bind h₂
          (yields_bind (yields_take _ s₂) (yields_value_call _ _ ?_ (by intro h; cases h)))))))
      · simp [Env.fragment, d₁]
      · have hv : s₂.env.variables s₁.env.length = some variables :=
          e₂.look (look := fun env => env.variables s₁.env.length)
            (fun _ _ _ h => Env.variables_append h) (by simp [Env.variables, push_getElem])
        simp [Env.fragment, recordedValue, hv, d₂]
    | «match» scrutinee caseList =>
      simp only [Tree.Term.match.sizeOf_spec] at h
      obtain ⟨i, s₁, h₁, e₁, d₁⟩ := ih scrutinee s (by omega)
      obtain ⟨handled, s₂, h₂, e₂, d₂⟩ := built_cases ih i caseList (by omega) (s₁.push .none)
      refine ⟨s₂.env.length, s₂.push (.term (.«match» scrutinee caseList)), ?_,
        e₁.trans ((extends_push _ _).trans (e₂.trans (extends_push _ _))),
        by simp [Env.term, push_getElem]⟩
      rw [rTerm, term_match]
      refine yields_bind (yields_takeAll _ s) (yields_bind h₁ (yields_bind
        (yields_unit_call _ rfl) (yields_bind (yields_take _ _) (yields_bind h₂
          (yields_bind (yields_takeAll _ s₂) (yields_value_call _ _ ?_
            (by intro h; cases h)))))))
      have hs := ((extends_push s₁ .none).trans e₂).term d₁
      have d₂' : List.mapM (α := Tree.Pattern × Recorded.term)
          (fun ((pattern, i) : Tree.Pattern × Nat) => (s₂.env.term i).map (pattern, ·)) handled =
          some caseList := d₂
      simp [Env.fragment, hs, d₂']
    | annotated annotated attributes =>
      simp only [Tree.Term.annotated.sizeOf_spec] at h
      obtain ⟨i, s₁, h₁, e₁, d₁⟩ := ih annotated s (by omega)
      cases attributes with
      | nil =>
        refine ⟨s₁.env.length, s₁.push (.term (.annotated annotated [])), ?_,
          e₁.trans (extends_push _ _), by simp [Env.term, push_getElem]⟩
        rw [rTerm, term_annotated]
        dsimp only
        exact yields_bind (yields_takeAll _ s) (yields_bind h₁ (yields_bind (yields_take _ s₁)
          (yields_bind (yields_pure _ _)
            (yields_value_call _ _ (by simp [Env.fragment, d₁]; rfl) (by intro h; cases h)))))
      | cons first others =>
        obtain ⟨keyword, value⟩ := first
        obtain ⟨is, s₂, h₂, e₂, d₂⟩ := built_attributesThen others keyword value s₁
        refine ⟨s₂.env.length, s₂.push (.term (.annotated annotated (⟨keyword, value⟩ ::
          others))), ?_, e₁.trans (e₂.trans (extends_push _ _)),
          by simp [Env.term, push_getElem]⟩
        rw [rTerm, term_annotated]
        dsimp only
        refine yields_bind (yields_takeAll _ s) (yields_bind h₁ (yields_bind (yields_take _ s₁)
          (yields_bind h₂ (yields_value_call _ _ ?_ (by intro h; cases h)))))
        simp only [Env.fragment, e₂.term d₁, Option.bind_eq_bind, Option.bind_some]
        erw [d₂]
        rfl

/-! ## The parts of commands -/

theorem Env.sortedVars_append {env more : Env} {list : List (Tree.Symbol × Nat)}
    {x : List Tree.SortedVar} (h : env.sortedVars list = some x) :
    (env ++ more).sortedVars list = some x :=
  mapM_append (lookup := sortedVarOf) (fun _ _ _ _ h => sortedVarOf_append h) h

theorem signature_append {env more : Env} {signature : Signature Recorded}
    {x : Tree.FunctionDec} (h : env.signature signature = some x) :
    (env ++ more).signature signature = some x := by
  simp only [Env.signature, Option.bind_eq_bind] at h ⊢
  cases hp : env.sortedVars signature.parameters with
  | none => simp [hp] at h
  | some parameters =>
    cases hr : env.sort signature.result with
    | none => simp [hp, hr] at h
    | some result =>
      have hp' : (env ++ more).sortedVars signature.parameters = some parameters :=
        Env.sortedVars_append hp
      simp [hp, hr] at h
      simp [hp', Env.sort_append hr, ← h]

theorem built_signature (symbol : Tree.Symbol) (parameters : List Tree.SortedVar)
    (result : Tree.Sort) (s : Recovery.State) :
    ∃ (handled : Signature Recorded) (s' : Recovery.State),
      Yields (signature (ε := Unit) rebuildPoints rebuildHandler symbol parameters result) s
        handled s' ∧ Extends s s' ∧
          s'.env.signature handled = some ⟨symbol, parameters, result⟩ := by
  obtain ⟨handled, s₁, h₁, e₁, d₁⟩ := built_sortedVars parameters s
  obtain ⟨i, s₂, h₂, e₂, d₂⟩ := built_sort (sizeOf result + 1) result s₁ (by omega)
  have d₁' := e₂.look (look := fun env => env.sortedVars handled)
    (fun _ _ _ h => Env.sortedVars_append h) d₁
  refine ⟨⟨symbol, handled, i⟩, s₂, ?_, e₁.trans e₂, by simp [Env.signature, d₁', d₂]⟩
  simp only [signature]
  exact yields_bind (yields_takeAll _ s) (yields_bind h₁ (yields_bind (yields_take _ s₁)
    (yields_bind h₂ (yields_pure _ _))))

/-- What a selector is in an environment, from its symbol and the number of its sort. -/
def selectorOf (env : Env) (selector : Tree.Symbol × Nat) : Option Tree.SelectorDec :=
  (env.sort selector.2).map fun sort => ⟨selector.1, sort⟩

theorem selectorOf_append {env more : Env} {p : Tree.Symbol × Nat} {x : Tree.SelectorDec}
    (h : selectorOf env p = some x) : selectorOf (env ++ more) p = some x := by
  simp only [selectorOf, Option.map_eq_some_iff] at h ⊢
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨y, Env.sort_append hy, rfl⟩

theorem selectorOf_mapM (env : Env) (list : List (Tree.Symbol × Nat))
    (selectors : List Tree.SelectorDec)
    (h : list.mapM (sortedVarOf env) = some (selectors.map selectorVar)) :
    list.mapM (selectorOf env) = some selectors := by
  induction list generalizing selectors with
  | nil =>
    cases selectors with
    | nil => rfl
    | cons => simp at h
  | cons p list ih =>
    cases selectors with
    | nil =>
      simp only [List.mapM_cons, List.map_nil, Option.bind_eq_bind] at h
      cases h₁ : sortedVarOf env p <;> cases h₂ : list.mapM (sortedVarOf env) <;>
        simp [h₁, h₂] at h
    | cons selector selectors =>
      simp only [List.mapM_cons, List.map_cons, Option.bind_eq_bind] at h ⊢
      cases h₁ : sortedVarOf env p with
      | none => simp [h₁] at h
      | some v =>
        cases h₂ : list.mapM (sortedVarOf env) with
        | none => simp [h₁, h₂] at h
        | some vs =>
          simp [h₁, h₂] at h
          obtain ⟨rfl, rfl⟩ := h
          have hs : selectorOf env p = some selector := by
            simp only [sortedVarOf, Option.map_eq_some_iff] at h₁
            obtain ⟨y, hy, hv⟩ := h₁
            obtain ⟨symbol, sort⟩ := selector
            simp [selectorVar] at hv
            simp [selectorOf, hy, hv]
          simp [hs, ih _ h₂]

theorem constructor_append {env more : Env} {constructor : Constructor Recorded}
    {x : Tree.ConstructorDec} (h : env.constructor constructor = some x) :
    (env ++ more).constructor constructor = some x := by
  simp only [Env.constructor, Option.map_eq_some_iff] at h ⊢
  obtain ⟨selectors, hs, rfl⟩ := h
  exact ⟨selectors, mapM_append (lookup := selectorOf) (fun _ _ _ _ h => selectorOf_append h) hs,
    rfl⟩

theorem built_constructorAfterOpen (constructor : Tree.ConstructorDec) (s : Recovery.State) :
    ∃ (handled : Constructor Recorded) (s' : Recovery.State),
      Yields (Traversal.constructorAfterOpen (ε := Unit) rebuildPoints rebuildHandler
        constructor) s handled s' ∧ Extends s s' ∧
          s'.env.constructor handled = some constructor := by
  obtain ⟨symbol, selectors⟩ := constructor
  rw [Traversal.constructorAfterOpen, selectors_eq]
  obtain ⟨handled, s₁, h₁, e₁, d₁⟩ := built_sortedVars (selectors.map selectorVar) s
  refine ⟨⟨symbol, handled⟩, s₁, yields_bind (yields_take _ s) (yields_bind h₁
    (yields_bind (yields_take _ s₁) (yields_pure _ _))), e₁, ?_⟩
  have := selectorOf_mapM s₁.env handled selectors d₁
  simp only [Env.constructor, Option.map_eq_some_iff]
  exact ⟨selectors, this, rfl⟩

theorem built_constructors (list : List Tree.ConstructorDec) (s : Recovery.State) :
    ∃ (handled : List (Constructor Recorded)) (s' : Recovery.State),
      Yields (constructors (ε := Unit) rebuildPoints rebuildHandler list) s handled s' ∧
        Extends s s' ∧ handled.mapM s'.env.constructor = some list := by
  obtain ⟨handled, s', h, e, d⟩ := built_mapM (α := Constructor Recorded)
    (fun constructor => do
      take (ε := Unit) rebuildPoints .parenOpen
      Traversal.constructorAfterOpen rebuildPoints rebuildHandler constructor)
    Env.constructor (fun _ _ _ _ h => constructor_append h) id list (fun c _ s => by
      obtain ⟨handled, s₁, h₁, e₁, d₁⟩ := built_constructorAfterOpen c s
      exact ⟨handled, s₁, yields_bind (yields_take _ s) h₁, e₁, d₁⟩) s
  exact ⟨handled, s', h, e, by simpa using d⟩

/-- A datatype declaration, given a start that leaves the state `next parameters state`. -/
theorem built_datatype (start : List Tree.Symbol → RRun Unit)
    (next : List Tree.Symbol → Recovery.State → Recovery.State)
    (declaration : Tree.DatatypeDec) (s : Recovery.State)
    (hstart : ∀ parameters, Yields (start parameters) s () (next parameters s)) :
    ∃ (handled : List (Constructor Recorded)) (s' : Recovery.State),
      Yields (datatype (ε := Unit) rebuildPoints rebuildHandler start declaration) s handled s' ∧
        Extends (next declaration.parameters s) s' ∧
        handled.mapM s'.env.constructor = some declaration.constructors := by
  obtain ⟨parameters, list⟩ := declaration
  cases parameters with
  | nil =>
    cases list with
    | nil =>
      refine ⟨[], next [] s, ?_, Extends.refl _, rfl⟩
      rw [datatype_empty]
      exact yields_bind (yields_takeAll _ s) (yields_bind (hstart []) (yields_pure _ _))
    | cons first others =>
      obtain ⟨c, s₁, h₁, e₁, d₁⟩ := built_constructorAfterOpen first (next [] s)
      obtain ⟨cs, s₂, h₂, e₂, d₂⟩ := built_constructors others s₁
      refine ⟨c :: cs, s₂, ?_, e₁.trans e₂, ?_⟩
      · rw [datatype_plain]
        exact yields_bind (yields_takeAll _ s) (yields_bind (hstart []) (yields_bind h₁
          (yields_bind h₂ (yields_bind (yields_take _ s₂) (yields_pure _ _)))))
      · have d₁' := e₂.look (look := fun env => env.constructor c)
          (fun _ _ _ h => constructor_append h) d₁
        simp [d₁', d₂]
  | cons parameter parameters =>
    obtain ⟨cs, s₁, h₁, e₁, d₁⟩ := built_constructors list (next (parameter :: parameters) s)
    refine ⟨cs, s₁, ?_, e₁, d₁⟩
    rw [datatype_par]
    exact yields_bind (yields_takeAll _ s) (yields_bind (yields_takeAll _ s) (yields_bind
      (yields_take _ s) (yields_bind (hstart _) (yields_bind (yields_take _ _)
        (yields_bind h₁ (yields_bind (yields_takeAll _ s₁) (yields_pure _ _)))))))

/-! ## Commands -/

theorem literalOf_asTerms (literals : List Tree.PropLiteral) :
    (literals.map Tree.PropLiteral.asTerm).mapM literalOf = some literals := by
  induction literals with
  | nil => rfl
  | cons literal literals ih =>
    cases literal <;> simp [Tree.PropLiteral.asTerm, literalOf, ih]

/-- The command is added to the commands, from a state with no command pending. -/
def Adds (s s' : Recovery.State) (command : Tree.Command) : Prop :=
  s'.commands = s.commands ++ [command] ∧ s'.pending = .none ∧ s'.version = s.version ∧
    ∃ more, s'.env = s.env ++ more

theorem yields_opening {s s₀ : Recovery.State} (ha : Yields (pure ()) s () s₀) (name : String) :
    Yields (opening rebuildPoints name) s () s₀ := by
  obtain rfl : s = s₀ := congrArg Prod.snd ha
  exact yields_bind (yields_take _ s) (yields_take _ s)

theorem yields_command_call (request : Call Recorded .nothing) {t t' : Recovery.State}
    (h : (t.push .none).command request = some t') :
    Yields (Traversal.call rebuildHandler request) t () t' :=
  yields_call request (by simp [State.call, h])

/-- Steps through a traversal: binds, tokens, the opening of a command, and hypotheses. -/
macro "chain" : tactic =>
  `(tactic| repeat'
    (first
      | with_reducible_and_instances exact (yields_take _ _)
      | with_reducible_and_instances exact (yields_takeAll _ _)
      | with_reducible_and_instances exact (yields_opening (by assumption) _)
      | assumption
      | with_reducible apply yields_bind))

theorem adds_of {s s₀ t : Recovery.State} (e₀ : Extends s s₀) (e : Extends s₀ t)
    (hp : s.pending = .none) (command : Tree.Command) :
    Adds s ((t.push .none).add command) command := by
  obtain ⟨v₀, p₀, c₀, m₀, h₀⟩ := e₀
  obtain ⟨v, p, c, m, h⟩ := e
  refine ⟨by simp [State.add, State.push, c, c₀], by simp [State.add, State.push, p, p₀, hp],
    by simp [State.add, State.push, v, v₀], m₀ ++ m ++ [.none], ?_⟩
  simp [State.add, State.push, h, h₀]

/-- The later state has the same version and commands, and more fragments. -/
def Same (s s' : Recovery.State) : Prop :=
  s'.version = s.version ∧ s'.commands = s.commands ∧ ∃ more, s'.env = s.env ++ more

theorem Extends.same {s s' : Recovery.State} (e : Extends s s') : Same s s' :=
  ⟨e.1, e.2.2.1, e.2.2.2⟩

theorem Same.trans {s₁ s₂ s₃ : Recovery.State} (h₁ : Same s₁ s₂) (h₂ : Same s₂ s₃) :
    Same s₁ s₃ := by
  obtain ⟨v₁, c₁, m₁, e₁⟩ := h₁
  obtain ⟨v₂, c₂, m₂, e₂⟩ := h₂
  exact ⟨v₂.trans v₁, c₂.trans c₁, m₁ ++ m₂, by rw [e₂, e₁, List.append_assoc]⟩

theorem Same.pending {s t : Recovery.State} (h : Same s t) (pending : Pending) :
    Same s { t.push .none with pending } := by
  obtain ⟨v, c, m, e⟩ := h
  exact ⟨v, c, m ++ [.none], by simp [State.push, e]⟩

theorem Same.push {s t : Recovery.State} (h : Same s t) : Same s (t.push .none) := by
  obtain ⟨v, c, m, e⟩ := h
  exact ⟨v, c, m ++ [.none], by simp [State.push, e]⟩

theorem adds_end {s t : Recovery.State} (h : Same s t) (command : Tree.Command) :
    Adds s { (t.push .none).add command with pending := .none } command := by
  obtain ⟨v, c, m, e⟩ := h
  exact ⟨by simp [State.add, State.push, c], rfl, v, m ++ [.none], by simp [State.add, State.push,
    e]⟩

/-- Looks up in the state with one more fragment of a call that returns nothing. -/
theorem push_term {t : Recovery.State} {i : Nat} {x : Tree.Term} (h : t.env.term i = some x) :
    (t.push .none).env.term i = some x := Env.term_append h

theorem push_attribute {t : Recovery.State} {i : Nat} {x : Tree.Attribute}
    (h : t.env.«attribute» i = some x) : (t.push .none).env.«attribute» i = some x :=
  Env.attribute_append h

theorem push_sort {t : Recovery.State} {i : Nat} {x : Tree.Sort} (h : t.env.sort i = some x) :
    (t.push .none).env.sort i = some x := Env.sort_append h

theorem qualIdentifier_rebuild (qualified : Tree.QualIdentifier) (atArrival : RRun Unit) :
    qualIdentifier (ε := Unit) rebuildPoints rebuildHandler qualified atArrival =
      (atArrival >>= fun _ => qualIdentifier rebuildPoints rebuildHandler qualified) := by
  cases qualified with
  | plain identifier =>
    obtain ⟨symbol, indices⟩ := identifier
    cases indices <;>
      simp [qualIdentifier, Tree.Identifier.tokens, paren, takeAllArriving_rebuild]
  | as identifier sort => simp [qualIdentifier, takeAllArriving_rebuild]

/-- In a rebuilding run, the calls due at the arrival of a term's first item come before the
term. -/
theorem term_rebuild (t : Tree.Term) (atArrival : RRun Unit) :
    term (ε := Unit) rebuildPoints rebuildHandler t atArrival =
      (atArrival >>= fun _ => term rebuildPoints rebuildHandler t) := by
  cases t with
  | identifier qualified =>
    simp only [term_identifier]
    rw [qualIdentifier_rebuild qualified atArrival, bind_assoc]
  | _ =>
    simp only [term_constant, term_application, term_let, term_lambda, term_quantified,
      term_match, term_annotated, receive_rebuild, takeAllArriving_rebuild, bind_assoc,
      pure_bind]

theorem built_recursiveBodies : ∀ (pairs : List (Signature Recorded × Tree.Term))
    (t : Recovery.State) (declarations : List Tree.FunctionDec) (done : List Tree.Term),
    t.pending = .defineFunsRec declarations done →
    ∃ t',
    Yields (Traversal.recursiveBodies (ε := Unit) rebuildPoints rebuildHandler pairs) t () t' ∧
      Same t t' ∧ t'.pending = .defineFunsRec declarations (done ++ pairs.map Prod.snd)
  | [], t, _, _, hp => ⟨t, rfl, ⟨rfl, rfl, [], by simp⟩, by simpa using hp⟩
  | (signature, body) :: pairs, t, declarations, done, hp => by
    obtain ⟨i, s₁, h₁, e₁, d₁⟩ := built_term (sizeOf body + 1) body (t.push .none) (by omega)
    have hp₁ : (s₁.push .none).pending = .defineFunsRec declarations done := by
      rw [← hp]; exact e₁.2.1
    obtain ⟨t', h₂, m₂, p₂⟩ := built_recursiveBodies pairs
      { (s₁.push .none) with pending := .defineFunsRec declarations (done ++ [body]) }
      declarations (done ++ [body]) rfl
    refine ⟨t', ?_, (Same.push ⟨rfl, rfl, [], by simp⟩).trans (e₁.same.trans
      ((Same.pending ⟨rfl, rfl, [], by simp⟩ _).trans m₂)), by simpa using p₂⟩
    rw [recursiveBodies_cons, term_rebuild, bind_assoc]
    refine yields_bind (yields_command_call _ (t' := t.push .none) rfl) (yields_bind h₁
      (yields_bind (yields_command_call _ ?_) h₂))
    simp [State.command, hp₁, push_term d₁]

theorem built_declarations : ∀ (declarations : List Tree.DatatypeDec) (t : Recovery.State)
    (sorts : List Tree.SortDec) (done : List Tree.DatatypeDec),
    t.pending = .declareDatatypes sorts done [] →
    ∃ t', Yields (declarations.forM fun declaration => do
        let handled ← datatype (ε := Unit) rebuildPoints rebuildHandler
          (fun parameters => Program.callUnit rebuildHandler
            (.startDatatypeDeclaration parameters)) declaration
        Program.callUnit rebuildHandler (.endDatatypeDeclaration handled)) t () t' ∧
      Same t t' ∧ t'.pending = .declareDatatypes sorts (done ++ declarations) []
  | [], t, _, _, hp => ⟨t, rfl, ⟨rfl, rfl, [], by simp⟩, by simpa using hp⟩
  | declaration :: declarations, t, sorts, done, hp => by
    obtain ⟨cs, s₁, h₁, e₁, d₁⟩ := built_datatype
      (fun parameters => Program.callUnit rebuildHandler (.startDatatypeDeclaration parameters))
      (fun parameters t => { t.push .none with
        pending := .declareDatatypes sorts done parameters })
      declaration t (fun parameters => yields_command_call _ (by simp [State.command, State.push,
        hp]))
    have hp₁ : (s₁.push .none).pending = .declareDatatypes sorts done declaration.parameters :=
      e₁.2.1
    have d₁' : List.mapM (α := Constructor Recorded) (s₁.push .none).env.constructor cs =
        some declaration.constructors :=
      mapM_append (lookup := Env.constructor) (fun _ _ _ _ h => constructor_append h) d₁
    obtain ⟨t', h₂, m₂, p₂⟩ := built_declarations declarations
      { s₁.push .none with pending := .declareDatatypes sorts (done ++ [declaration]) [] }
      sorts (done ++ [declaration]) rfl
    refine ⟨t', ?_, ((Same.pending ⟨rfl, rfl, [], by simp⟩ _).trans e₁.same |>.pending _).trans m₂,
      by simpa using p₂⟩
    simp only [List.forM]
    refine yields_bind (yields_bind h₁ (yields_command_call _ ?_)) h₂
    simp only [State.command, hp₁, Option.bind_eq_bind]
    erw [d₁']
    rfl

theorem sortDecs_roundTrip (sorts : List Tree.SortDec) :
    ((sorts.map fun sortDec => (sortDec.symbol, sortDec.arity)).map
      fun ((symbol, arity) : Tree.Symbol × Chars) => (⟨symbol, arity⟩ : Tree.SortDec)) =
      sorts := by
  induction sorts with
  | nil => rfl
  | cons s sorts ih => simpa using ih

set_option maxHeartbeats 4000000 in
theorem built_command' (command : Tree.Command) (s : Recovery.State)
    (hp : s.pending = .none) (hv : command.Valid s.version)
    {s₀ : Recovery.State} (ha : Yields (pure ()) s () s₀) (he : Extends s s₀) :
    ∃ s', Yields (Traversal.command rebuildPoints rebuildHandler command) s () s' ∧
      Adds s s' command := by
  cases command with
  | checkSat =>
    refine ⟨(s₀.push .none).add .checkSat, ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_checkSat]
    chain
    exact yields_command_call _ rfl
  | assert t =>
    obtain ⟨i, s₁, h₁, e₁, d₁⟩ := built_term (sizeOf t + 1) t s₀ (by omega)
    refine ⟨(s₁.push .none).add (.assert t), ?_, adds_of he e₁ hp _⟩
    rw [command_assert]
    chain
    exact yields_command_call _ (by simp [State.command, push_term d₁])
  | getAssertions =>
    refine ⟨(s₀.push .none).add .getAssertions, ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_getAssertions]
    chain
    exact yields_command_call _ rfl
  | getAssignment =>
    refine ⟨(s₀.push .none).add .getAssignment, ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_getAssignment]
    chain
    exact yields_command_call _ rfl
  | getModel =>
    refine ⟨(s₀.push .none).add .getModel, ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_getModel]
    chain
    exact yields_command_call _ rfl
  | getProof =>
    refine ⟨(s₀.push .none).add .getProof, ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_getProof]
    chain
    exact yields_command_call _ rfl
  | getUnsatAssumptions =>
    refine ⟨(s₀.push .none).add .getUnsatAssumptions, ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_getUnsatAssumptions]
    chain
    exact yields_command_call _ rfl
  | getUnsatCore =>
    refine ⟨(s₀.push .none).add .getUnsatCore, ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_getUnsatCore]
    chain
    exact yields_command_call _ rfl
  | reset =>
    refine ⟨(s₀.push .none).add .reset, ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_reset]
    chain
    exact yields_command_call _ rfl
  | resetAssertions =>
    refine ⟨(s₀.push .none).add .resetAssertions, ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_resetAssertions]
    chain
    exact yields_command_call _ rfl
  | exit =>
    refine ⟨(s₀.push .none).add .exit, ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_exit]
    chain
    exact yields_command_call _ rfl
  | declareSort symbol arity =>
    refine ⟨(s₀.push .none).add (.declareSort symbol arity), ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_declareSort]
    chain
    exact yields_command_call _ rfl
  | declareSortParameter symbol =>
    refine ⟨(s₀.push .none).add (.declareSortParameter symbol), ?_,
      adds_of he (Extends.refl _) hp _⟩
    rw [command_declareSortParameter]
    chain
    exact yields_command_call _ rfl
  | echo content =>
    refine ⟨(s₀.push .none).add (.echo content), ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_echo]
    chain
    exact yields_command_call _ rfl
  | getInfo flag =>
    refine ⟨(s₀.push .none).add (.getInfo flag), ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_getInfo]
    chain
    exact yields_command_call _ rfl
  | getOption keyword =>
    refine ⟨(s₀.push .none).add (.getOption keyword), ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_getOption]
    chain
    exact yields_command_call _ rfl
  | pop count =>
    refine ⟨(s₀.push .none).add (.pop count), ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_pop]
    chain
    exact yields_command_call _ rfl
  | push count =>
    refine ⟨(s₀.push .none).add (.push count), ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_push]
    chain
    exact yields_command_call _ rfl
  | setLogic symbol =>
    refine ⟨(s₀.push .none).add (.setLogic symbol), ?_, adds_of he (Extends.refl _) hp _⟩
    rw [command_setLogic]
    chain
    exact yields_command_call _ rfl
  | checkSatAssuming terms =>
    obtain ⟨is, s₁, h₁, e₁, d₁⟩ := built_terms (built_term (sizeOf terms + 1)) terms
      (by omega) s₀
    refine ⟨(s₁.push .none).add (.checkSatAssuming terms), ?_, adds_of he e₁ hp _⟩
    rw [command_checkSatAssuming]
    chain
    have hver : (s₁.push .none).version = s.version := by
      simp [State.push, e₁.1, he.1]
    have d₁' : List.mapM (α := Recorded.term) (s₁.push .none).env.term is = some terms :=
      (extends_push s₁ .none).terms d₁
    have h27 : Version.v2_7 ∈ (s₁.push .none).version.upTo := by rw [hver]; exact hv.1
    exact yields_command_call _ (by simp only [State.command, h27, ite_true]; erw [d₁']; rfl)
  | checkSatAssumingLiterals literals =>
    obtain ⟨is, s₁, h₁, e₁, d₁⟩ := built_terms (built_term
      (sizeOf (literals.map Tree.PropLiteral.asTerm) + 1)) (literals.map Tree.PropLiteral.asTerm)
      (by omega) s₀
    refine ⟨(s₁.push .none).add (.checkSatAssumingLiterals literals), ?_, adds_of he e₁ hp _⟩
    rw [command_checkSatAssumingLiterals]
    chain
    have hver : (s₁.push .none).version = s.version := by
      simp [State.push, e₁.1, he.1]
    have d₁' : List.mapM (α := Recorded.term) (s₁.push .none).env.term is =
        some (literals.map Tree.PropLiteral.asTerm) := (extends_push s₁ .none).terms d₁
    have h27 : ¬ Version.v2_7 ∈ (s₁.push .none).version.upTo := by rw [hver]; exact hv.2.1
    exact yields_command_call _ (by
      simp only [State.command, h27, ite_false]
      erw [d₁']
      show (some _ >>= _) = _
      simp only [Option.bind_eq_bind, Option.bind_some]
      show (Option.bind _ _) = _
      rw [literalOf_asTerms]; rfl)
  | declareConst symbol sort =>
    obtain ⟨i, s₁, h₁, e₁, d₁⟩ := built_sort (sizeOf sort + 1) sort s₀ (by omega)
    refine ⟨(s₁.push .none).add (.declareConst symbol sort), ?_, adds_of he e₁ hp _⟩
    rw [command_declareConst]
    chain
    exact yields_command_call _ (by simp [State.command, push_sort d₁])
  | declareFun symbol parameters result =>
    obtain ⟨is, s₁, h₁, e₁, d₁⟩ := built_mapM (α := Nat) rSort Env.sort
      (fun _ _ _ _ h => Env.sort_append h) id parameters
      (fun b _ s => built_sort (sizeOf b + 1) b s (by omega)) s₀
    obtain ⟨i, s₂, h₂, e₂, d₂⟩ := built_sort (sizeOf result + 1) result s₁ (by omega)
    refine ⟨(s₂.push .none).add (.declareFun symbol parameters result), ?_,
      adds_of he (e₁.trans e₂) hp _⟩
    rw [command_declareFun, sorts_eq]
    chain
    have d₁' : List.mapM (α := Recorded.sort) (s₂.push .none).env.sort is = some parameters := by
      have := ((e₂.trans (extends_push s₂ .none)).look (look := fun env => is.mapM env.sort)
        (fun _ _ _ h => mapM_append (fun _ _ _ _ h => Env.sort_append h) h) d₁)
      exact (List.map_id parameters) ▸ this
    exact yields_command_call _ (by
      simp only [State.command, Option.bind_eq_bind]
      erw [d₁']
      simp [push_sort d₂])
  | defineConst symbol sort body =>
    obtain ⟨i, s₁, h₁, e₁, d₁⟩ := built_sort (sizeOf sort + 1) sort s₀ (by omega)
    obtain ⟨j, s₂, h₂, e₂, d₂⟩ := built_term (sizeOf body + 1) body s₁ (by omega)
    refine ⟨(s₂.push .none).add (.defineConst symbol sort body), ?_,
      adds_of he (e₁.trans e₂) hp _⟩
    rw [command_defineConst]
    chain
    have d₁' := (e₂.trans (extends_push s₂ .none)).look (look := fun env => env.sort i)
      (fun _ _ _ h => Env.sort_append h) d₁
    exact yields_command_call _ (by simp [State.command, d₁', push_term d₂])
  | getValue terms =>
    obtain ⟨is, s₁, h₁, e₁, d₁⟩ := built_terms (built_term (sizeOf terms + 1)) terms
      (by omega) s₀
    refine ⟨(s₁.push .none).add (.getValue terms), ?_, adds_of he e₁ hp _⟩
    rw [command_getValue]
    chain
    have d₁' : List.mapM (α := Recorded.term) (s₁.push .none).env.term is = some terms :=
      (extends_push s₁ .none).terms d₁
    exact yields_command_call _ (by simp only [State.command]; erw [d₁']; rfl)
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    obtain ⟨i, s₁, h₁, e₁, d₁⟩ := built_attributeThen keyword .parenClose value s₀
    refine ⟨(s₁.push .none).add (.setInfo ⟨keyword, value⟩), ?_, adds_of he e₁ hp _⟩
    rw [command_setInfo]
    chain
    exact yields_command_call _ (by simp [State.command, push_attribute d₁])
  | setOption option =>
    obtain ⟨keyword, value⟩ := option
    obtain ⟨i, s₁, h₁, e₁, d₁⟩ := built_attributeThen keyword .parenClose value s₀
    refine ⟨(s₁.push .none).add (.setOption ⟨keyword, value⟩), ?_, adds_of he e₁ hp _⟩
    rw [command_setOption]
    chain
    exact yields_command_call _ (by simp [State.command, push_attribute d₁])
  | defineFun definition =>
    obtain ⟨symbol, parameters, result, body⟩ := definition
    obtain ⟨handled, s₁, h₁, e₁, d₁⟩ := built_signature symbol parameters result s₀
    obtain ⟨j, s₂, h₂, e₂, d₂⟩ := built_term (sizeOf body + 1) body
      { s₁.push .none with pending := .defineFun ⟨symbol, parameters, result⟩ } (by omega)
    refine ⟨{ (s₂.push .none).add (.defineFun ⟨symbol, parameters, result, body⟩) with
      pending := .none }, ?_, adds_end ((he.same.trans e₁.same).pending _ |>.trans e₂.same) _⟩
    rw [command_defineFun]
    chain
    · exact yields_command_call _ (by
        simp [State.command, signature_append (more := [.none]) d₁, State.push])
    · have hp₂ : (s₂.push .none).pending = .defineFun ⟨symbol, parameters, result⟩ := e₂.2.1
      exact yields_command_call _ (by simp [State.command, hp₂, push_term d₂])
  | defineFunRec definition =>
    obtain ⟨symbol, parameters, result, body⟩ := definition
    obtain ⟨handled, s₁, h₁, e₁, d₁⟩ := built_signature symbol parameters result s₀
    obtain ⟨j, s₂, h₂, e₂, d₂⟩ := built_term (sizeOf body + 1) body
      { s₁.push .none with pending := .defineFunRec ⟨symbol, parameters, result⟩ } (by omega)
    refine ⟨{ (s₂.push .none).add (.defineFunRec ⟨symbol, parameters, result, body⟩) with
      pending := .none }, ?_, adds_end ((he.same.trans e₁.same).pending _ |>.trans e₂.same) _⟩
    rw [command_defineFunRec]
    chain
    · exact yields_command_call _ (by
        simp [State.command, signature_append (more := [.none]) d₁, State.push])
    · have hp₂ : (s₂.push .none).pending = .defineFunRec ⟨symbol, parameters, result⟩ := e₂.2.1
      exact yields_command_call _ (by simp [State.command, hp₂, push_term d₂])
  | defineSort symbol parameters sort =>
    obtain ⟨i, s₁, h₁, e₁, d₁⟩ := built_sort (sizeOf sort + 1) sort
      { s₀.push .none with pending := .defineSort symbol parameters } (by omega)
    refine ⟨{ (s₁.push .none).add (.defineSort symbol parameters sort) with pending := .none },
      ?_, adds_end ((he.same.pending _).trans e₁.same) _⟩
    rw [command_defineSort]
    chain
    · exact yields_command_call _ rfl
    · have hp₁ : (s₁.push .none).pending = .defineSort symbol parameters := e₁.2.1
      exact yields_command_call _ (by simp [State.command, hp₁, push_sort d₁])
  | declareDatatype symbol declaration =>
    obtain ⟨cs, s₁, h₁, e₁, d₁⟩ := built_datatype
      (fun parameters => Program.callUnit rebuildHandler (.startDeclareDatatype symbol parameters))
      (fun parameters t => { t.push .none with pending := .declareDatatype symbol parameters })
      declaration s₀ (fun parameters => yields_command_call _ rfl)
    refine ⟨{ (s₁.push .none).add (.declareDatatype symbol declaration) with pending := .none },
      ?_, adds_end ((he.same.pending _).trans e₁.same) _⟩
    rw [command_declareDatatype]
    chain
    have hp₁ : (s₁.push .none).pending = .declareDatatype symbol declaration.parameters :=
      e₁.2.1
    have d₁' : List.mapM (α := Constructor Recorded) (s₁.push .none).env.constructor cs =
        some declaration.constructors :=
      mapM_append (lookup := Env.constructor) (fun _ _ _ _ h => constructor_append h) d₁
    exact yields_command_call _ (by
      simp only [State.command, hp₁, Option.bind_eq_bind]
      erw [d₁']
      rfl)
  | declareDatatypes sorts declarations =>
    have hsorts := sortDecs_roundTrip sorts
    obtain ⟨t', h₁, m₁, p₁⟩ := built_declarations declarations
      { s₀.push .none with pending := .declareDatatypes sorts [] [] } sorts [] rfl
    refine ⟨{ (t'.push .none).add (.declareDatatypes sorts declarations) with pending := .none },
      ?_, adds_end ((he.same.pending _).trans m₁) _⟩
    rw [command_declareDatatypes]
    refine yields_bind (yields_opening ha _) (yields_bind (yields_take _ s₀) (yields_bind
      (yields_takeAll _ s₀) (yields_bind (yields_take _ s₀) (yields_bind
        (yields_command_call _ ?_) (yields_bind (yields_take _ _) (yields_bind h₁
          (yields_bind (yields_takeAll _ t') (yields_command_call _ ?_))))))))
    · simp only [State.command, hsorts]
    · simp [State.command, State.push, p₁]
  | defineFunsRec declarations bodies =>
    obtain ⟨-, -, hlen, -⟩ := hv
    obtain ⟨sigs, s₁, h₁, e₁, d₁⟩ := built_mapM (α := Signature Recorded)
      (fun declaration => do
        take (ε := Unit) rebuildPoints .parenOpen
        let handled ← signature rebuildPoints rebuildHandler declaration.symbol
          declaration.parameters declaration.result
        take rebuildPoints .parenClose
        pure handled)
      Env.signature (fun _ _ _ _ h => signature_append h) id declarations
      (fun ⟨symbol, parameters, result⟩ _ s => by
        obtain ⟨handled, s₁, h₁, e₁, d₁⟩ := built_signature symbol parameters result s
        exact ⟨handled, s₁, yields_bind (yields_take _ s) (yields_bind h₁
          (yields_bind (yields_take _ s₁) (yields_pure _ _))), e₁, d₁⟩) s₀
    have hz : (sigs.zip bodies).map Prod.snd = bodies :=
      List.map_snd_zip
        (by rw [mapM_some_length d₁, List.length_map, hlen]; exact Nat.le_refl _)
    obtain ⟨t', h₂, m₂, p₂⟩ := built_recursiveBodies (sigs.zip bodies)
      { s₁.push .none with pending := .defineFunsRec declarations [] } declarations [] rfl
    refine ⟨{ (t'.push .none).add (.defineFunsRec declarations bodies) with pending := .none },
      ?_, adds_end ((he.same.trans e₁.same |>.pending _).trans m₂) _⟩
    rw [command_defineFunsRec]
    have d₁' : List.mapM (α := Signature Recorded) (s₁.push .none).env.signature sigs =
        some declarations := by
      have := mapM_append (lookup := Env.signature) (more := [.none])
        (fun _ _ _ _ h => signature_append h) d₁
      exact (List.map_id declarations) ▸ this
    refine yields_bind (yields_opening ha _) (yields_bind (yields_take _ s₀) (yields_bind h₁
      (yields_bind (yields_take _ s₁) (yields_bind (yields_command_call _ ?_)
        (yields_bind (yields_take _ _) (yields_bind h₂
          (yields_bind (yields_takeAll _ t') (yields_command_call _ ?_))))))))
    · simp only [State.command]
      erw [d₁']
      rfl
    · simp [State.command, State.push, p₂, hz]


/-- A command, with the rebuilding handler, adds itself to the commands. -/
theorem built_command (command : Tree.Command) (s : Recovery.State)
    (hp : s.pending = .none) (hv : command.Valid s.version) :
    ∃ s', Yields (Traversal.command rebuildPoints rebuildHandler command) s () s' ∧
      Adds s s' command :=
  built_command' command s hp hv (yields_pure () s) (Extends.refl s)

/-! ## Scripts -/

theorem yields_setVersion (version : Version) (s : Recovery.State) :
    Yields (ExceptT.lift (rebuildHandler.setVersion version)) s () { s.push .none with version } :=
  rfl

theorem yields_discard (s : Recovery.State) :
    Yields (ExceptT.lift rebuildProducer.discardRest) s () s := rfl

theorem unrestricted_ok (declarations : Nat) (version : Version) :
    VersionPolicy.unrestricted.check declarations version = .ok () := by
  cases version <;> rfl

theorem yields_switch (declarations : Nat) (version : Version) (s : Recovery.State) :
    Yields (switchVersion rebuildHandler rebuildProducer VersionPolicy.unrestricted declarations
      version) s () { s.push .none with version } := by
  simp only [switchVersion, unrestricted_ok]
  exact yields_bind
    (x := ExceptT.adapt (fun _ => Cause.syntax .unsupportedVersion)
      (rebuildProducer.setVersion version)) rfl
    (yields_setVersion version s)

theorem modeAfter_read {version next : Version} {command : Tree.Command}
    (h : command.modeAfter version = some (.read next)) :
    (command.declaredVersion = none ∧ next = version) ∨ command.declaredVersion = some next := by
  cases command with
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    simp only [Tree.Command.modeAfter] at h
    simp only [Tree.Command.declaredVersion]
    split at h
    · rename_i hk
      split at h
      · rename_i decimal
        right
        cases hv : versionOfNumber decimal <;> simp_all
      · left
        simp_all
    · left
      refine ⟨?_, by simpa [eq_comm] using h⟩
      split <;> simp_all
  | exit => simp [Tree.Command.modeAfter] at h
  | _ =>
    left
    simp only [Tree.Command.modeAfter, Option.some.injEq, Mode.read.injEq] at h
    exact ⟨rfl, h.symm⟩

theorem commands_cons_none {command : Tree.Command} (hne : command ≠ .exit)
    (hd : command.declaredVersion = none) (hn : command.namesNoVersion = false)
    (declarations : Nat) (commands : List Tree.Command) :
    Traversal.commands rebuildPoints rebuildHandler rebuildProducer VersionPolicy.unrestricted
        declarations (command :: commands) =
      (Traversal.command rebuildPoints rebuildHandler command >>= fun _ =>
        Traversal.commands rebuildPoints rebuildHandler rebuildProducer
          VersionPolicy.unrestricted declarations commands) := by
  cases command <;> first | exact absurd rfl hne | simp [Traversal.commands, hd, hn]

theorem commands_cons_some {command : Tree.Command} (hne : command ≠ .exit) {version : Version}
    (hd : command.declaredVersion = some version) (declarations : Nat)
    (commands : List Tree.Command) :
    Traversal.commands rebuildPoints rebuildHandler rebuildProducer VersionPolicy.unrestricted
        declarations (command :: commands) =
      (Traversal.command rebuildPoints rebuildHandler command >>= fun _ =>
        switchVersion rebuildHandler rebuildProducer VersionPolicy.unrestricted declarations
          version >>= fun _ =>
        Traversal.commands rebuildPoints rebuildHandler rebuildProducer
          VersionPolicy.unrestricted (declarations + 1) commands) := by
  cases command <;> first | exact absurd rfl hne | simp [Traversal.commands, hd]

theorem built_commands : ∀ (commands : List Tree.Command) (version : Version)
    (s : Recovery.State) (declarations : Nat),
    Script version commands → s.version = version → s.pending = .none →
    ∃ s', Yields (Traversal.commands rebuildPoints rebuildHandler rebuildProducer
      VersionPolicy.unrestricted declarations commands) s () s' ∧
      s'.commands = s.commands ++ commands
  | [], _, s, _, _, _, _ => by
    refine ⟨s, ?_, by simp⟩
    simp only [Traversal.commands]
    exact yields_receive _ s
  | command :: commands, version, s, declarations, hs, hver, hp => by
    cases hs with
    | stop hv hm =>
      obtain rfl := modeAfter_unparsed hm
      obtain ⟨s', h', a'⟩ := built_command .exit s hp (hver ▸ hv)
      refine ⟨s', ?_, a'.1⟩
      simp only [Traversal.commands]
      exact yields_bind h' (yields_bind (yields_discard s') (yields_receive _ s'))
    | command hv hm hrest =>
      rename_i next
      have hne : command ≠ .exit := by
        rintro rfl
        simp [Tree.Command.modeAfter] at hm
      obtain ⟨s', h', a'⟩ := built_command command s hp (hver ▸ hv)
      rcases modeAfter_read hm with ⟨hd, hn⟩ | hd
      · obtain ⟨s'', h'', c''⟩ := built_commands commands next s' declarations hrest
          (a'.2.2.1.trans (hver.trans hn.symm)) a'.2.1
        refine ⟨s'', ?_, by simp [c'', a'.1]⟩
        rw [commands_cons_none hne hd (namesNoVersion_eq_false hm)]
        exact yields_bind h' h''
      · obtain ⟨s'', h'', c''⟩ := built_commands commands next
          { s'.push .none with version := next } (declarations + 1) hrest rfl
          (by simp [State.push, a'.2.1])
        refine ⟨s'', ?_, by simp [c'', State.push, a'.1]⟩
        rw [commands_cons_some hne hd]
        exact yields_bind h' (yields_bind (yields_switch declarations next s') h'')


/-- The traversal of a script, with the rebuilding handler from the start of a rebuilding,
leaves the script's commands. -/
theorem built_script (version : Version) (commands : List Tree.Command)
    (h : Script version commands) :
    ∃ s', Yields (script rebuildPoints rebuildHandler rebuildProducer VersionPolicy.unrestricted
      version commands) (initial version) () s' ∧ s'.commands = commands := by
  obtain ⟨s', h', c'⟩ := built_commands commands version
    { (initial version).push .none with version } 0 h rfl rfl
  exact ⟨s', yields_bind (yields_setVersion version _) h',
    by simpa [initial, State.push] using c'⟩

end BSmtLib.SpecChecks.Parser
