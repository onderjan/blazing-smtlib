import BSmtLibSpec.Lexer

/-!
# A lexer and its consumers

Checks of what `BSmtLibSpec.Lexer` says about a lexer and its consumers: what a lexer does with a
consumer is determined (`runs_unique`), so a held result, where discarding began, and the
version in force are each determined by the input and the consumer; locating a token of an input
read on its own after what came before agrees with locating it in the whole input
(`locate_after`), so the locations of the input after a switch of the version are those of the
whole input; and the collector meets the obligation of every consumer.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Lexer

open BSmtLibSpec BSmtLibSpec.Lexicon BSmtLibSpec.Lexer
open BSmtLibSpec.Lexicon.Properties
open BSmtLibSpec.Regex (Chars chars)

/-! ## Locations -/

theorem takeWhile_append_of_all {p : UInt8 → Bool} {l : List UInt8} (h : ∀ x ∈ l, p x = true)
    (l' : List UInt8) : (l ++ l').takeWhile p = l ++ l'.takeWhile p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.cons_append, List.takeWhile_cons, h x (by simp), ↓reduceIte,
      ih (fun y hy => h y (by simp [hy]))]

theorem takeWhile_append_of_not {p : UInt8 → Bool} {l : List UInt8} {x : UInt8} (hx : x ∈ l)
    (h : p x = false) (l' : List UInt8) : (l ++ l').takeWhile p = l.takeWhile p := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.cons_append, List.takeWhile_cons]
    by_cases hy : p y = true
    · simp only [hy, ↓reduceIte, List.cons.injEq, true_and]
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [h] at hy
      · exact ih hx
    · simp [hy]

/-- An input read on its own after `before`, located in it, is located as in the whole input. -/
theorem locate_after (before input : Chars) (offset : Nat) :
    locate (before ++ input) (before.length + offset) = (locate input offset).after before := by
  simp only [locate, Location.after, List.take_append, List.take_length,
    Nat.add_sub_cancel_left, List.count_append]
  rw [List.take_of_length_le (by omega : before.length ≤ before.length + offset)]
  simp only [List.reverse_append, Location.mk.injEq, true_and]
  split
  · rename_i hz
    rw [List.count_eq_zero] at hz
    have hall : ∀ x ∈ (input.take offset).reverse, (fun x : UInt8 => decide (x ≠ 10)) x = true :=
      fun x hx => by
        have : x ≠ 10 := fun e => hz (e ▸ List.mem_reverse.mp hx)
        simpa using this
    have hself := takeWhile_append_of_all hall ([] : List UInt8)
    rw [List.takeWhile_nil, List.append_nil] at hself
    rw [takeWhile_append_of_all hall, List.length_append, hself]
    omega
  · rename_i hz
    obtain ⟨x, hx, rfl⟩ : ∃ x ∈ (input.take offset).reverse, x = 10 := by
      have := List.count_pos_iff.mp (Nat.pos_of_ne_zero hz)
      exact ⟨10, List.mem_reverse.mpr this, rfl⟩
    rw [takeWhile_append_of_not hx (by simp)]

theorem location_after_nil (location : Location) : location.after [] = location := by
  cases location
  simp only [Location.after, List.length_nil, Nat.zero_add, Location.mk.injEq, true_and]
  refine ⟨by simp [locate], ?_⟩
  split <;> simp_all [locate]

/-- The tokens ready from the start of the input are those `feed` hands over. -/
theorem segment_zero (feed : Version → List Chars → Bool → Fed) (version : Version)
    (input : Chars) (ended : Bool) :
    segment feed version input ended 0 = feed version [input] ended := by
  have : Handed.after [] = id := funext fun handed => by
    simp [Handed.after, location_after_nil]
  unfold segment
  simp [this]

/-! ## What a lexer does with a consumer -/

theorem afterBreak_unique {α ε : Type} {result : α} {location : Location} {ready : List Handed}
    {failed : Bool} {outcome outcome' : Outcome α ε}
    (h : AfterBreak result location ready failed outcome)
    (h' : AfterBreak result location ready failed outcome') :
    outcome = outcome' := by
  cases h <;> cases h' <;> simp_all

/-- What a lexer does with a consumer from a point on is determined. -/
theorem runs_unique {feed : Version → List Chars → Bool → Fed} {consumer : Consumer}
    {start : Version} {input : Chars} {ended : Bool} {version : Version} {ready : List Handed}
    {failed : Bool} {taken : List Handed} {session session' : Session consumer.Result consumer.Error}
    (h : Runs feed consumer start input ended version ready failed taken session)
    (h' : Runs feed consumer start input ended version ready failed taken session') :
    session = session' := by
  induction h generalizing session' with
  | continues _ _ _ _ ih =>
    cases h' <;> simp_all
    exact ih ‹_›
  | breaks _ _ _ hb =>
    cases h' <;> simp_all
    rw [afterBreak_unique hb ‹_›]
  | _ => cases h' <;> simp_all

/-- The collector breaks at the end of the input. -/
theorem collector_breaksAtEnd : collector.BreaksAtEnd := by
  intro taken token h
  simp [collector, h]

end BSmtLib.SpecChecks.Lexer
