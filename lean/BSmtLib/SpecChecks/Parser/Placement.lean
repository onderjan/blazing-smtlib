import BSmtLib.SpecChecks.Parser.Calls

/-!
# What a parser has done before an item

A program decides what to do next only from what it has received, so what its trace shows
before the arrival of an item depends only on the items before it (`eventsBefore_trace`), and
what it shows before the processing of an item only on the items before it and on whether the
item is there at all (`eventsBeforeProcessing_trace`). What a parser receives for a valid script
is never a proper start of what it receives for another (`received_not_prefix`), so the
recordings of two scripts agree before an item when what is received for them agrees before it.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Parser

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal

theorem take_cons_succ {x x' : Received} {s s' : List Received} {k : Nat}
    (h : (x :: s).take (k + 1) = (x' :: s').take (k + 1)) : x = x' ∧ s.take k = s'.take k := by
  simpa using h

theorem eventsBefore_trace {α : Type} (p : Program Recorded α) :
    ∀ (items items' : List Received) (count k : Nat), items.take k = items'.take k →
      eventsBefore k (trace p items count) = eventsBefore k (trace p items' count) := by
  induction p with
  | done => intros; rfl
  | receive start next ih =>
    intro items items' count k h
    cases items with
    | nil =>
      cases items' with
      | nil => rfl
      | cons x' s' =>
        cases k with
        | zero => cases start <;> simp [trace, eventsBefore]
        | succ k => simp at h
    | cons x s =>
      cases items' with
      | nil =>
        cases k with
        | zero => cases start <;> simp [trace, eventsBefore]
        | succ k => simp at h
      | cons x' s' =>
        cases k with
        | zero => cases start <;> simp [trace, eventsBefore]
        | succ k =>
          obtain ⟨rfl, h'⟩ := take_cons_succ h
          cases start <;> simp [trace, eventsBefore, ih x s s' _ k h']
  | call request next ih =>
    intro items items' count k h
    cases k <;> simp [trace, eventsBefore, ih _ items items' _ _ h]
  | endScript next ih =>
    intro items items' count k h
    cases k <;> simp [trace, eventsBefore, ih items items' _ _ h]
  | switch declarations version next ih =>
    intro items items' count k h
    cases k <;> simp [trace, eventsBefore, ih items items' _ _ h]
  | stuck => intros; rfl

theorem eventsBeforeProcessing_trace {α : Type} (p : Program Recorded α) :
    ∀ (items items' : List Received) (count k : Nat), items.take k = items'.take k →
      (k < items.length ↔ k < items'.length) →
      eventsBeforeProcessing k (trace p items count) =
        eventsBeforeProcessing k (trace p items' count) := by
  induction p with
  | done => intros; rfl
  | receive start next ih =>
    intro items items' count k h hl
    cases items with
    | nil =>
      cases items' with
      | nil => rfl
      | cons x' s' => cases k <;> simp at h hl
    | cons x s =>
      cases items' with
      | nil => cases k <;> simp at h hl
      | cons x' s' =>
        cases k with
        | zero => cases start <;> simp [trace, eventsBeforeProcessing]
        | succ k =>
          obtain ⟨rfl, h'⟩ := take_cons_succ h
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hl
          cases start <;> simp [trace, eventsBeforeProcessing, ih x s s' _ k h' hl]
  | call request next ih =>
    intro items items' count k h hl
    cases k <;> simp [trace, eventsBeforeProcessing, ih _ items items' _ _ h hl]
  | endScript next ih =>
    intro items items' count k h hl
    cases k <;> simp [trace, eventsBeforeProcessing, ih items items' _ _ h hl]
  | switch declarations version next ih =>
    intro items items' count k h hl
    cases k <;> simp [trace, eventsBeforeProcessing, ih items items' _ _ h hl]
  | stuck => intros; rfl

/-- The recording run of `parseScript` on what a parser receives for a script, followed by
anything, succeeds and leaves what follows. -/
theorem parse_leaves {version : Version} {commands : List Tree.Command}
    (h : Script version commands) {n : Nat} (hn : 10 * sizeOf commands < n)
    (rest : List Received) :
    ((runRecording (parseScript n) (received commands ++ rest)).run.run []).1 = .ok ((), rest) := by
  have hm := fun rest => run_script (points := recordingPoints) (handler := recordingHandler)
    (producerSwitch := recordingSwitch) (policy := VersionPolicy.unrestricted)
    version commands rest h hn
  obtain ⟨-, hok⟩ := parse_rebuilds h hn
  have h₀ := hm []
  rw [List.append_nil] at h₀
  simp only [runRecording] at hok ⊢
  rw [h₀, recording_bind_run] at hok
  rw [hm rest, recording_bind_run]
  revert hok
  rcases (script recordingPoints recordingHandler recordingSwitch VersionPolicy.unrestricted
    commands).run.run [] with ⟨e, events⟩
  cases e with
  | error e => intro hok; cases hok
  | ok u => intro _; rfl

/-- What a parser receives for a valid script is not a proper start of what it receives for
another valid script. -/
theorem received_not_prefix {version version' : Version} {commands commands' : List Tree.Command}
    (h : Script version commands) (h' : Script version' commands') {rest : List Received}
    (heq : received commands = received commands' ++ rest) : rest = [] := by
  let n := 10 * (sizeOf commands + sizeOf commands') + 1
  have h₁ := parse_leaves h (n := n) (by omega) []
  have h₂ := parse_leaves h' (n := n) (by omega) rest
  rw [List.append_nil, heq, h₂] at h₁
  simpa using h₁.symm

theorem received_length {version version' : Version} {commands commands' : List Tree.Command}
    (h : Script version commands) (h' : Script version' commands') {k : Nat}
    (ht : (received commands).take k = (received commands').take k) :
    (k < (received commands).length ↔ k < (received commands').length) := by
  have one : ∀ {v v' : Version} {c c' : List Tree.Command}, Script v c → Script v' c' →
      (received c).take k = (received c').take k → k < (received c).length →
      k < (received c').length := by
    intro v v' c c' hc hc' ht hk
    refine Nat.lt_of_not_le fun hk' => ?_
    have hp : received c = received c' ++ (received c).drop k := by
      rw [← List.take_of_length_le hk', ← ht, List.take_append_drop]
    have := received_not_prefix hc hc' hp
    rw [List.drop_eq_nil_iff] at this
    omega
  exact ⟨one h h' ht, one h' h ht.symm⟩

end BSmtLib.SpecChecks.Parser
