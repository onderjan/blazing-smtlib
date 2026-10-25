module

public import BSmtLib.Facts.Proofs.Parser.Quiet
import all BSmtLib.Parser

@[expose] public section

/-!
# What a parser state can still take

The converse of the parser's correctness: a parser takes an item only if some valid construct
goes on with it. Each parser state is given its remainders (`rem`): the sequences of items that
complete the construct the parser is in, as the spec writes it. A step that takes an item
advances (`Advances`): every remainder of the new state, after the item, is a remainder of the
old state, and the new state has a remainder; a step that finishes takes the item as the last
one of a remainder. Then the items a parser takes from its initial state are the start of a
valid construct, by induction over the items.

The remainders are sets of item lists (`Lang`), built by concatenation and repetition. The steps
are run in a recording run (`RPM`), whose handler never fails, so a step fails only on a syntax
error or a non-standard command. `Sound P Q x` says that every result of `x` satisfies `P` and
every failure `Q`; a step's lemma is a `Sound` with `Advances` for its results.
-/

open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Handler

namespace BSmtLib.Facts.Proofs.Parser.Rejection.Basic

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser (ParseErrorCause SyntaxErrorKind VersionErrorKind)

/-! ## Sets of item lists -/

/-- A set of lists of items. -/
abbrev Lang := List Received → Prop

namespace Lang

/-- The lists of one list of `A` followed by one of `B`. -/
def cat (A B : Lang) : Lang := fun u => ∃ a b, A a ∧ B b ∧ u = a ++ b

/-- The empty list alone. -/
def eps : Lang := fun u => u = []

/-- The single item. -/
def tok (x : Received) : Lang := fun u => u = [x]

/-- Lists of lists of `A`, between `lo` and `hi` of them, one after another. -/
def rep (A : Lang) (lo : Nat) (hi : Option Nat) : Lang := fun u =>
  ∃ ws : List (List Received), (∀ w ∈ ws, A w) ∧ lo ≤ ws.length ∧
    (∀ limit, hi = some limit → ws.length ≤ limit) ∧ u = ws.flatten

/-- Any number of lists of `A`, one after another. -/
abbrev star (A : Lang) : Lang := rep A 0 none

/-- One list of `A` or more, one after another. -/
abbrev plus (A : Lang) : Lang := rep A 1 none

/-- Either. -/
def union (A B : Lang) : Lang := fun u => A u ∨ B u


/-- The lists of tokens, as items. -/
abbrev toks (tokens : List BSmtLibSpec.Grammar.SyntaxToken) : List Received := tokens.map .token

theorem cat_intro {A B : Lang} {a b : List Received} (ha : A a) (hb : B b) : cat A B (a ++ b) :=
  ⟨a, b, ha, hb, rfl⟩

theorem cat_intro' {A B : Lang} {a b u : List Received} (ha : A a) (hb : B b) (hu : u = a ++ b) :
    cat A B u :=
  ⟨a, b, ha, hb, hu⟩

theorem tok_intro (x : Received) : tok x [x] := rfl

theorem eps_intro : eps [] := rfl

theorem cat_tok {B : Lang} {x : Received} {b : List Received} (hb : B b) :
    cat (tok x) B (x :: b) :=
  ⟨[x], b, rfl, hb, rfl⟩

theorem cat_tok_iff {B : Lang} {x : Received} {u : List Received} :
    cat (tok x) B u ↔ ∃ b, B b ∧ u = x :: b := by
  constructor
  · rintro ⟨a, b, rfl, hb, rfl⟩
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact cat_tok hb

theorem cat_assoc {A B C : Lang} {u : List Received} :
    cat (cat A B) C u ↔ cat A (cat B C) u := by
  constructor
  · rintro ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩
    exact ⟨a, b ++ c, ha, ⟨b, c, hb, hc, rfl⟩, by simp⟩
  · rintro ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩
    exact ⟨a ++ b, c, ⟨a, b, ha, hb, rfl⟩, hc, by simp⟩

theorem cat_mono {A A' B B' : Lang} (hA : ∀ u, A u → A' u) (hB : ∀ u, B u → B' u)
    {u : List Received} (h : cat A B u) : cat A' B' u := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  exact ⟨a, b, hA a ha, hB b hb, rfl⟩

theorem cat_nonempty {A B : Lang} (hA : ∃ a, A a) (hB : ∃ b, B b) : ∃ u, cat A B u := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨a ++ b, cat_intro ha hb⟩

theorem rep_nil {A : Lang} {hi : Option Nat} : rep A 0 hi [] :=
  ⟨[], by simp, Nat.le_refl _, fun _ _ => Nat.zero_le _, rfl⟩

theorem rep_cons {A : Lang} {lo : Nat} {hi : Option Nat} {a u : List Received} (ha : A a)
    (hu : rep A (lo - 1) (hi.map (· - 1)) u) (hhi : ∀ limit, hi = some limit → 0 < limit) :
    rep A lo hi (a ++ u) := by
  obtain ⟨ws, hws, hlo, hhi', rfl⟩ := hu
  refine ⟨a :: ws, ?_, ?_, ?_, by simp⟩
  · intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ha
    · exact hws w hw
  · simp only [List.length_cons]; omega
  · intro limit hlimit
    have := hhi' (limit - 1) (by simp [hlimit])
    have := hhi limit hlimit
    simp only [List.length_cons]; omega

theorem rep_uncons {A : Lang} {lo : Nat} {hi : Option Nat} {u : List Received}
    (h : rep A lo hi u) :
    (u = [] ∧ lo = 0) ∨ ∃ a v, A a ∧ rep A (lo - 1) (hi.map (· - 1)) v ∧ u = a ++ v ∧
      ∀ limit, hi = some limit → 0 < limit := by
  obtain ⟨ws, hws, hlo, hhi, rfl⟩ := h
  cases ws with
  | nil => left; simp at hlo ⊢; omega
  | cons w ws =>
    right
    refine ⟨w, ws.flatten, hws w (by simp), ⟨ws, fun w' hw' => hws w' (by simp [hw']),
      by simp at hlo; omega, ?_, rfl⟩, by simp, ?_⟩
    · intro limit hlimit
      cases hi with
      | none => simp at hlimit
      | some l =>
        simp only [Option.map_some, Option.some.injEq] at hlimit
        have := hhi l rfl
        simp at this; omega
    · intro limit hlimit
      have := hhi limit hlimit
      simp at this; omega

theorem rep_nonempty {A : Lang} (hA : ∃ a, A a) (lo : Nat) (hi : Option Nat)
    (h : ∀ limit, hi = some limit → lo ≤ limit) : ∃ u, rep A lo hi u := by
  obtain ⟨a, ha⟩ := hA
  refine ⟨(List.replicate lo a).flatten, List.replicate lo a, ?_, by simp, ?_, rfl⟩
  · intro w hw
    rw [(List.mem_replicate.mp hw).2]
    exact ha
  · intro limit hlimit
    simpa using h limit hlimit

theorem star_cons {A : Lang} {a u : List Received} (ha : A a) (hu : star A u) :
    star A (a ++ u) :=
  rep_cons ha (by simpa using hu) (by simp)

theorem plus_of_star {A : Lang} {a u : List Received} (ha : A a) (hu : star A u) :
    plus A (a ++ u) :=
  rep_cons ha (by simpa using hu) (by simp)

theorem star_of_plus {A : Lang} {u : List Received} (h : plus A u) : star A u := by
  obtain ⟨ws, hws, -, hhi, rfl⟩ := h
  exact ⟨ws, hws, Nat.zero_le _, hhi, rfl⟩

theorem union_left {A B : Lang} {u : List Received} (h : A u) : union A B u := Or.inl h

theorem union_right {A B : Lang} {u : List Received} (h : B u) : union A B u := Or.inr h

end Lang

open Lang

/-! ## Results and failures of a recording run -/

/-- The failure is no rejection of a version declaration. -/
def Benign : ParseErrorCause Unit → Prop
  | .version _ => False
  | _ => True

/-- The failures that `Q` allows and that are rejections of a version declaration. -/
def Firm (Q : ParseErrorCause Unit → Prop) (e : ParseErrorCause Unit) : Prop :=
  Q e ∧ ¬ Benign e

/--
Every result of the action, in a recording run, satisfies `P`, and every failure `Q`; and a
failure that is no rejection of a version declaration writes no event: the action makes no call
before it rejects.
-/
structure Sound {α : Type} (P : α → Prop) (Q : ParseErrorCause Unit → Prop) (x : Quiet.RPM α) :
    Prop where
  ok : ∀ events a events', x.run.run events = (.ok a, events') → P a
  error : ∀ events e events', x.run.run events = (.error e, events') → Q e
  quiet : ∀ events e events', x.run.run events = (.error e, events') → Benign e → events' = events

/-- The action writes no event when it succeeds. -/
def SilentOk {α : Type} (x : Quiet.RPM α) : Prop :=
  ∀ events a events', x.run.run events = (.ok a, events') → events' = events

section

variable {α β : Type} {P P' : α → Prop} {Q Q' : ParseErrorCause Unit → Prop}

theorem Sound.pure {a : α} (h : P a) : Sound P Q (Pure.pure a : Quiet.RPM α) :=
  ⟨fun _ _ _ hrun => (by cases hrun; exact h), fun _ _ _ hrun => (by cases hrun),
    fun _ _ _ hrun => (by cases hrun)⟩

theorem Sound.throw {e : ParseErrorCause Unit} (h : Q e) : Sound P Q (throw e : Quiet.RPM α) :=
  ⟨fun _ _ _ hrun => (by cases hrun), fun _ _ _ hrun => (by cases hrun; exact h),
    fun _ _ _ hrun _ => (by cases hrun; rfl)⟩

theorem Sound.syntaxError {kind : SyntaxErrorKind} (h : Q (.syntax kind)) :
    Sound P Q (Parser.Internal.syntaxError kind : Quiet.RPM α) :=
  Sound.throw h

theorem Sound.versionError {kind : VersionErrorKind} (h : Q (.version kind)) :
    Sound P Q (Parser.Internal.versionError kind : Quiet.RPM α) :=
  Sound.throw h

theorem SilentOk.pure {a : α} : SilentOk (Pure.pure a : Quiet.RPM α) := fun _ _ _ hrun => by
  cases hrun; rfl

theorem SilentOk.throw {e : ParseErrorCause Unit} : SilentOk (throw e : Quiet.RPM α) :=
  fun _ _ _ hrun => by cases hrun

theorem SilentOk.syntaxError {kind : SyntaxErrorKind} :
    SilentOk (Parser.Internal.syntaxError kind : Quiet.RPM α) :=
  SilentOk.throw

/-- The results and failures of an action and then another, where the second rejects nothing:
an action that writes an event, such as a call, is followed only by actions that make no
rejection. -/
theorem Sound.bind {R : β → Prop} {x : Quiet.RPM β} {f : β → Quiet.RPM α} (hx : Sound R Q x)
    (hf : ∀ b, R b → Sound P (Firm Q) (f b)) : Sound P Q (x >>= f) := by
  constructor
  · intro events a events' hrun
    simp only [ExceptT.run_bind, StateT.run_bind] at hrun
    rcases hx' : x.run.run events with ⟨result, events₁⟩
    rw [hx'] at hrun
    cases result with
    | error e => cases hrun
    | ok b => exact (hf b (hx.ok _ _ _ hx')).ok _ _ _ hrun
  · intro events e events' hrun
    simp only [ExceptT.run_bind, StateT.run_bind] at hrun
    rcases hx' : x.run.run events with ⟨result, events₁⟩
    rw [hx'] at hrun
    cases result with
    | error e' =>
      cases hrun
      exact hx.error _ _ _ hx'
    | ok b => exact ((hf b (hx.ok _ _ _ hx')).error _ _ _ hrun).1
  · intro events e events' hrun hb
    simp only [ExceptT.run_bind, StateT.run_bind] at hrun
    rcases hx' : x.run.run events with ⟨result, events₁⟩
    rw [hx'] at hrun
    cases result with
    | error e' =>
      cases hrun
      exact hx.quiet _ _ _ hx' hb
    | ok b => exact absurd hb ((hf b (hx.ok _ _ _ hx')).error _ _ _ hrun).2

/-- The results and failures of an action that writes no event when it succeeds, and then
another. -/
theorem Sound.bindS {R : β → Prop} {x : Quiet.RPM β} {f : β → Quiet.RPM α} (hx : Sound R Q x)
    (hs : SilentOk x) (hf : ∀ b, R b → Sound P Q (f b)) : Sound P Q (x >>= f) := by
  constructor
  · intro events a events' hrun
    simp only [ExceptT.run_bind, StateT.run_bind] at hrun
    rcases hx' : x.run.run events with ⟨result, events₁⟩
    rw [hx'] at hrun
    cases result with
    | error e => cases hrun
    | ok b => exact (hf b (hx.ok _ _ _ hx')).ok _ _ _ hrun
  · intro events e events' hrun
    simp only [ExceptT.run_bind, StateT.run_bind] at hrun
    rcases hx' : x.run.run events with ⟨result, events₁⟩
    rw [hx'] at hrun
    cases result with
    | error e' =>
      cases hrun
      exact hx.error _ _ _ hx'
    | ok b => exact (hf b (hx.ok _ _ _ hx')).error _ _ _ hrun
  · intro events e events' hrun hb
    simp only [ExceptT.run_bind, StateT.run_bind] at hrun
    rcases hx' : x.run.run events with ⟨result, events₁⟩
    rw [hx'] at hrun
    cases result with
    | error e' =>
      cases hrun
      exact hx.quiet _ _ _ hx' hb
    | ok b =>
      rw [(hf b (hx.ok _ _ _ hx')).quiet _ _ _ hrun hb]
      exact hs _ _ _ hx'

/-- The results and failures of an action and then another, where the action writes no event
for the results `quiet` holds of, and after its other results the second rejects nothing. -/
theorem Sound.bindOn {R : β → Prop} {x : Quiet.RPM β} {f : β → Quiet.RPM α} (hx : Sound R Q x)
    (quiet : β → Prop)
    (hs : ∀ events b events', x.run.run events = (.ok b, events') → quiet b → events' = events)
    (hf : ∀ b, R b → Sound P (fun e => Q e ∧ (¬ quiet b → ¬ Benign e)) (f b)) :
    Sound P Q (x >>= f) := by
  constructor
  · intro events a events' hrun
    simp only [ExceptT.run_bind, StateT.run_bind] at hrun
    rcases hx' : x.run.run events with ⟨result, events₁⟩
    rw [hx'] at hrun
    cases result with
    | error e => cases hrun
    | ok b => exact (hf b (hx.ok _ _ _ hx')).ok _ _ _ hrun
  · intro events e events' hrun
    simp only [ExceptT.run_bind, StateT.run_bind] at hrun
    rcases hx' : x.run.run events with ⟨result, events₁⟩
    rw [hx'] at hrun
    cases result with
    | error e' =>
      cases hrun
      exact hx.error _ _ _ hx'
    | ok b => exact ((hf b (hx.ok _ _ _ hx')).error _ _ _ hrun).1
  · intro events e events' hrun hb
    simp only [ExceptT.run_bind, StateT.run_bind] at hrun
    rcases hx' : x.run.run events with ⟨result, events₁⟩
    rw [hx'] at hrun
    cases result with
    | error e' =>
      cases hrun
      exact hx.quiet _ _ _ hx' hb
    | ok b =>
      by_cases hq : quiet b
      · rw [(hf b (hx.ok _ _ _ hx')).quiet _ _ _ hrun hb]
        exact hs _ _ _ hx' hq
      · exact absurd hb (((hf b (hx.ok _ _ _ hx')).error _ _ _ hrun).2 hq)

theorem Sound.mono {x : Quiet.RPM α} (h : Sound P Q x) (hP : ∀ a, P a → P' a)
    (hQ : ∀ e, Q e → Q' e) : Sound P' Q' x :=
  ⟨fun events a events' hrun => hP a (h.ok events a events' hrun),
    fun events e events' hrun => hQ e (h.error events e events' hrun), h.quiet⟩

/-- The rest after a result of `Sound.bindOn` that is written without events. -/
theorem Sound.quietly {β : Type} {quiet : β → Prop} {b : β} {y : Quiet.RPM α} (h : Sound P Q y)
    (hb : quiet b) : Sound P (fun e => Q e ∧ (¬ quiet b → ¬ Benign e)) y :=
  h.mono (fun _ h => h) fun _ he => ⟨he, fun hn => absurd hb hn⟩

/-- The rest after any result of `Sound.bindOn`, if it rejects nothing. -/
theorem Sound.loudly {β : Type} {quiet : β → Prop} {b : β} {y : Quiet.RPM α}
    (h : Sound P (Firm Q) y) :
    Sound P (fun e => Q e ∧ (¬ quiet b → ¬ Benign e)) y :=
  h.mono (fun _ h => h) fun _ he => ⟨he.1, fun _ => he.2⟩

/-- An action whose failures `Q` allows all reject a version declaration is sound with them as
its firm ones. -/
theorem Sound.firm {x : Quiet.RPM α} (h : Sound P Q x) (hQ : ∀ e, Q e → ¬ Benign e) :
    Sound P (Firm Q) x :=
  ⟨h.ok, fun events e events' hrun => ⟨h.error events e events' hrun,
    hQ e (h.error events e events' hrun)⟩, h.quiet⟩

/-- An action that adds events and never fails. -/
theorem Sound.lift {x : StateM (List Event) α} : Sound (fun _ => True) Q
    (ExceptT.lift x : Quiet.RPM α) :=
  ⟨fun _ _ _ _ => trivial, fun events e events' hrun => (by
    simp only [ExceptT.run_lift, StateT.run_map] at hrun
    cases hrun), fun events e events' hrun => (by
    simp only [ExceptT.run_lift, StateT.run_map] at hrun
    cases hrun)⟩

/-- A call of the recording handler never fails. -/
theorem Sound.call {returns : Returns} (request : Call Recorded returns) :
    Sound (fun _ => True) Q (Parser.Internal.call (recordingCall request) : Quiet.RPM (Recorded.of returns))
        :=
  ⟨fun _ _ _ _ => trivial, fun events e events' hrun => (by cases hrun),
    fun events e events' hrun => (by cases hrun)⟩

end

/-! ## Results and failures of a driver's run

The driver writes the arrival and the processing of each item before the step takes it, so a run
of it can reject after it wrote events: what it writes before a rejection is said where it is
used. -/

/-- Every result of the action, in a recording run, satisfies `P`, and every failure `Q`. -/
structure RunSound {α : Type} (P : α → Prop) (Q : ParseErrorCause Unit → Prop) (x : Quiet.RPM α) :
    Prop where
  ok : ∀ events a events', x.run.run events = (.ok a, events') → P a
  error : ∀ events e events', x.run.run events = (.error e, events') → Q e

section

variable {α β : Type} {P P' : α → Prop} {Q Q' : ParseErrorCause Unit → Prop}

theorem Sound.run {x : Quiet.RPM α} (h : Sound P Q x) : RunSound P Q x := ⟨h.ok, h.error⟩

theorem RunSound.pure {a : α} (h : P a) : RunSound P Q (Pure.pure a : Quiet.RPM α) :=
  (Sound.pure h).run

theorem RunSound.bind {R : β → Prop} {x : Quiet.RPM β} {f : β → Quiet.RPM α} (hx : RunSound R Q x)
    (hf : ∀ b, R b → RunSound P Q (f b)) : RunSound P Q (x >>= f) := by
  constructor
  · intro events a events' hrun
    simp only [ExceptT.run_bind, StateT.run_bind] at hrun
    rcases hx' : x.run.run events with ⟨result, events₁⟩
    rw [hx'] at hrun
    cases result with
    | error e => cases hrun
    | ok b => exact (hf b (hx.ok _ _ _ hx')).ok _ _ _ hrun
  · intro events e events' hrun
    simp only [ExceptT.run_bind, StateT.run_bind] at hrun
    rcases hx' : x.run.run events with ⟨result, events₁⟩
    rw [hx'] at hrun
    cases result with
    | error e' =>
      cases hrun
      exact hx.error _ _ _ hx'
    | ok b => exact (hf b (hx.ok _ _ _ hx')).error _ _ _ hrun

theorem RunSound.mono {x : Quiet.RPM α} (h : RunSound P Q x) (hP : ∀ a, P a → P' a)
    (hQ : ∀ e, Q e → Q' e) : RunSound P' Q' x :=
  ⟨fun events a events' hrun => hP a (h.ok events a events' hrun),
    fun events e events' hrun => hQ e (h.error events e events' hrun)⟩

theorem RunSound.lift {x : StateM (List Event) α} :
    RunSound (fun _ => True) Q (ExceptT.lift x : Quiet.RPM α) :=
  Sound.lift.run

end

/-! ## Steps that advance -/

/--
What a step's result says of the remainders, from a state that has a remainder: going on in a new
state, every remainder of the new state, after the item, is one of the old state, and the new
state has one; finishing with a result, the item alone completes `fin` of the old state and the
result. A state without a remainder is one no input leads to; its steps are not looked at.
-/
def Advances {σ ρ : Type} (rem : σ → Lang) (fin : σ → ρ → Lang) (state : σ) (item : Received) :
    Parser.Internal.Step σ ρ → Prop
  | .more next => (∃ u, rem state u) → (∀ u, rem next u → rem state (item :: u)) ∧ ∃ u, rem next u
  | .done result => (∃ u, rem state u) → fin state result [item]

/-- `Advances` from a state known to have a remainder. -/
def Advanced {σ ρ : Type} (rem : σ → Lang) (fin : σ → ρ → Lang) (state : σ) (item : Received) :
    Parser.Internal.Step σ ρ → Prop
  | .more next => (∀ u, rem next u → rem state (item :: u)) ∧ ∃ u, rem next u
  | .done result => fin state result [item]

theorem Advances.from {σ ρ : Type} {rem : σ → Lang} {fin : σ → ρ → Lang} {state : σ}
    {item : Received} {r : Parser.Internal.Step σ ρ} (h : Advances rem fin state item r)
    (hne : ∃ u, rem state u) : Advanced rem fin state item r := by
  cases r with
  | more next => exact h hne
  | done result => exact h hne

/--
Every step of the parser, in the version, advances: on every token that stands for an item that
a lexer of the version can hand over, its results advance with that item, and its failures are no
rejection of a version declaration.
-/
def StepsAdvance {σ ρ : Type} (version : Version)
    (step : σ → Parser.Internal.Input → Quiet.RPM (Parser.Internal.Step σ ρ)) (rem : σ → Lang)
        (fin : σ → ρ → Lang) : Prop :=
  ∀ state token item, Bridge.received token = some item →
    item.OfVersion (Bridge.version version) →
    Sound (Advances rem fin state item) Benign (step state token)


/-! ## Repetitions of trees -/

section

variable {T : Type} {P : T → Prop} {f : T → List Received}

/-- A repetition of lists that are each written by a tree is the trees, one after another. -/
theorem rep_trees {lo : Nat} {hi : Option Nat} {u : List Received}
    (h : rep (fun w => ∃ t, P t ∧ w = f t) lo hi u) :
    ∃ ts : List T, (∀ t ∈ ts, P t) ∧ lo ≤ ts.length ∧
      (∀ limit, hi = some limit → ts.length ≤ limit) ∧ u = (ts.map f).flatten := by
  obtain ⟨ws, hws, hlo, hhi, rfl⟩ := h
  have : ∀ ws : List (List Received), (∀ w ∈ ws, ∃ t, P t ∧ w = f t) →
      ∃ ts : List T, (∀ t ∈ ts, P t) ∧ ts.length = ws.length ∧ ws.flatten = (ts.map f).flatten := by
    intro ws hws
    induction ws with
    | nil => exact ⟨[], by simp, rfl, rfl⟩
    | cons w ws ih =>
      obtain ⟨t, ht, rfl⟩ := hws w (by simp)
      obtain ⟨ts, hts, hlen, heq⟩ := ih fun w hw => hws w (by simp [hw])
      refine ⟨t :: ts, ?_, by simp [hlen], by simp [heq]⟩
      intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact ht
      · exact hts t' ht'
  obtain ⟨ts, hts, hlen, heq⟩ := this ws hws
  exact ⟨ts, hts, hlen ▸ hlo, fun limit hl => hlen ▸ hhi limit hl, heq⟩

/-- Trees, one after another, are a repetition of the lists they are written as. -/
theorem trees_rep {lo : Nat} {hi : Option Nat} (ts : List T) (hts : ∀ t ∈ ts, P t)
    (hlo : lo ≤ ts.length) (hhi : ∀ limit, hi = some limit → ts.length ≤ limit) :
    rep (fun w => ∃ t, P t ∧ w = f t) lo hi (ts.map f).flatten :=
  ⟨ts.map f, by simpa using fun t ht => ⟨t, hts t ht, rfl⟩, by simpa using hlo,
    fun limit hl => by simpa using hhi limit hl, rfl⟩

end

/-! ## Versions -/

section

variable {version : Version}

theorem atLeast_v2_5_of_ge (h : version ≥ .v2_5) :
    versionAtLeast (Bridge.version version) .v2_5 := by
  cases version <;> simp_all [versionAtLeast, Bridge.version, BSmtLibSpec.Lexicon.Version.upTo] <;>
    exact absurd h (by decide)

theorem atLeast_v2_6_of_ge (h : version ≥ .v2_6) :
    versionAtLeast (Bridge.version version) .v2_6 := by
  cases version <;> simp_all [versionAtLeast, Bridge.version, BSmtLibSpec.Lexicon.Version.upTo] <;>
    exact absurd h (by decide)

theorem atLeast_v2_7_of_ge' (h : version ≥ .v2_7) :
    versionAtLeast (Bridge.version version) .v2_7 := by
  cases version <;> simp_all [versionAtLeast, Bridge.version, BSmtLibSpec.Lexicon.Version.upTo] <;>
    exact absurd h (by decide)

theorem not_atLeast_v2_7_of_lt (h : ¬ version ≥ .v2_7) :
    ¬ versionAtLeast (Bridge.version version) .v2_7 := by
  cases version <;> simp_all [versionAtLeast, Bridge.version, BSmtLibSpec.Lexicon.Version.upTo] <;>
    exact h (by decide)

end

/-- The item the token stands for, from `h : Bridge.received token = some item`. -/
macro "item_of " h:ident : tactic =>
  `(tactic| ((set_option linter.unusedSimpArgs false in
    simp only [Bridge.received, Bridge.constant, Tree.SpecConstant.token, Option.some.injEq]
      at $h:ident); subst $h:ident))

theorem push_isEmpty {α : Type} (array : Array α) (a : α) : (array.push a).isEmpty = false := by
  simp [Array.isEmpty]

/-- A handler call that never fails, as every call of the recording handler. -/
theorem Sound.ofCall {α : Type} {Q : ParseErrorCause Unit → Prop}
    {x : ExceptT Unit (StateT (List Event) Id) α}
    (hx : ∀ events, ∃ a events', x.run.run events = (.ok a, events')) :
    Sound (fun _ => True) Q (Parser.Internal.call x : Quiet.RPM α) := by
  constructor
  · intros; trivial
  · intro events e events' hrun
    obtain ⟨a, events'', hx'⟩ := hx events
    simp only [Parser.Internal.call, ExceptT.run_adapt, StateT.run_map, hx'] at hrun
    cases hrun
  · intro events e events' hrun
    obtain ⟨a, events'', hx'⟩ := hx events
    simp only [Parser.Internal.call, ExceptT.run_adapt, StateT.run_map, hx'] at hrun
    cases hrun

/-- A failure that is no rejection of a version declaration. -/
macro "benign" : tactic => `(tactic| first | trivial | (split <;> trivial) | simp [Benign] |
  (left; first | trivial | (split <;> trivial)))

/-- A step that fails. -/
macro "fail_step" : tactic => `(tactic| first
  | exact Sound.syntaxError (by benign)
  | exact Sound.throw (by benign)
  | exact Sound.bindS (Sound.syntaxError (P := fun _ => False) (by benign)) SilentOk.syntaxError
      fun _ h => h.elim
  | exact Sound.bindS (Sound.throw (P := fun _ => False) trivial) SilentOk.throw
      fun _ h => h.elim)

/-- A handler call, then the rest of the step. -/
macro "call_step" : tactic =>
  `(tactic| refine Sound.bind (Sound.ofCall fun _ => ⟨_, _, rfl⟩) fun _ _ => ?_)

theorem flatten_singletons {T : Type} (f : T → Received) (l : List T) :
    (l.map fun t => [f t]).flatten = l.map f := by
  induction l <;> simp_all

namespace Lang

/-- The item, then the rest of a list of `A` followed by one of `B`, from the item and the rest
of the list of `A`. -/
theorem cat_left {A A' B : Lang} {x : Received} {u : List Received}
    (h : ∀ a, A a → A' (x :: a)) (hu : cat A B u) : cat A' B (x :: u) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hu
  exact ⟨x :: a, b, h a ha, hb, rfl⟩

theorem star_of_rep {A : Lang} {lo : Nat} {u : List Received} (h : rep A lo Option.none u) :
    star A u := by
  obtain ⟨ws, hws, -, hhi, rfl⟩ := h
  exact ⟨ws, hws, Nat.zero_le _, hhi, rfl⟩

end Lang
namespace Lang

theorem cat_nonempty_left {A B : Lang} (h : ∃ u, cat A B u) : ∃ a, A a := by
  obtain ⟨_, a, _, ha, _, _⟩ := h
  exact ⟨a, ha⟩

theorem cat_nonempty_right {A B : Lang} (h : ∃ u, cat A B u) : ∃ b, B b := by
  obtain ⟨_, _, b, _, hb, _⟩ := h
  exact ⟨b, hb⟩

end Lang

/-- Results of an action that satisfy each of a family of properties. -/
theorem Sound.forall {ι α : Type} {P : ι → α → Prop} {Q : ParseErrorCause Unit → Prop}
    {x : Quiet.RPM α} (i₀ : ι) (h : ∀ i, Sound (P i) Q x) : Sound (fun a => ∀ i, P i a) Q x :=
  ⟨fun events a events' hrun i => (h i).ok events a events' hrun,
    fun events e events' hrun => (h i₀).error events e events' hrun, (h i₀).quiet⟩

/-- Results and failures that satisfy two descriptions satisfy both. -/
theorem Sound.and {α : Type} {P P' : α → Prop} {Q Q' : ParseErrorCause Unit → Prop}
    {x : Quiet.RPM α}
    (h : Sound P Q x) (h' : Sound P' Q' x) : Sound (fun a => P a ∧ P' a) (fun e => Q e ∧ Q' e) x :=
  ⟨fun events a events' hrun => ⟨h.ok events a events' hrun, h'.ok events a events' hrun⟩,
    fun events e events' hrun => ⟨h.error events e events' hrun, h'.error events e events' hrun⟩,
    h.quiet⟩

/-! ## Runs that write no event -/

theorem run_bind_of_error {α β : Type} {x : Quiet.RPM β} {f : β → Quiet.RPM α} {ev ev₁ : List Event}
    {e : ParseErrorCause Unit} (hx : x.run.run ev = (.error e, ev₁)) :
    (x >>= f).run.run ev = (.error e, ev₁) := by
  simp only [ExceptT.run_bind, StateT.run_bind, hx]
  rfl

theorem run_bind_of_ok {α β : Type} {x : Quiet.RPM β} {f : β → Quiet.RPM α} {ev ev₁ : List Event}
    {b : β}
    (hx : x.run.run ev = (.ok b, ev₁)) : (x >>= f).run.run ev = (f b).run.run ev₁ := by
  simp only [ExceptT.run_bind, StateT.run_bind, hx]
  rfl

theorem run_bind_ok_inv {α β : Type} {x : Quiet.RPM β} {f : β → Quiet.RPM α} {ev ev' : List Event}
    {a : α}
    (h : (x >>= f).run.run ev = (.ok a, ev')) :
    ∃ b ev₁, x.run.run ev = (.ok b, ev₁) ∧ (f b).run.run ev₁ = (.ok a, ev') := by
  rcases hx : x.run.run ev with ⟨_ | b, ev₁⟩
  · rw [run_bind_of_error hx] at h
    cases h
  · rw [run_bind_of_ok hx] at h
    exact ⟨b, ev₁, rfl, h⟩

/-- An action whose second part never finishes does not finish. -/
theorem never_done {β σ ρ : Type} {x : Quiet.RPM β} {f : β → Quiet.RPM (Parser.Internal.Step σ ρ)}
    (hf : ∀ b ev ev' items, (f b).run.run ev ≠ (.ok (.done items), ev')) {ev ev' : List Event}
    {items : ρ} : (x >>= f).run.run ev ≠ (.ok (.done items), ev') := by
  rcases hx : x.run.run ev with ⟨_ | b, ev₁⟩
  · rw [run_bind_of_error hx]
    nofun
  · rw [run_bind_of_ok hx]
    exact hf b ev₁ ev' items

theorem more_ne_done {σ τ : Type} (s : σ) (ev ev' : List Event) (items : τ) :
    (pure (Parser.Internal.Step.more s) : Quiet.RPM (Parser.Internal.Step σ τ)).run.run ev ≠ (.ok
        (.done items), ev') :=
  nofun

theorem pure_done_run {σ τ : Type} {its items : τ} {ev ev' : List Event}
    (h : (pure (Parser.Internal.Step.done its) : Quiet.RPM
        (Parser.Internal.Step σ τ)).run.run ev = (.ok (.done items), ev')) :
    ev' = ev := by
  cases h
  rfl

end BSmtLib.Facts.Proofs.Parser.Rejection.Basic
