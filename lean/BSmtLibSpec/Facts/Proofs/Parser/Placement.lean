module

public import BSmtLibSpec.Facts.Proofs.Parser.Calls

@[expose] public section

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

namespace BSmtLibSpec.Facts.Proofs.Parser.Placement

open BSmtLibSpec.Lexicon BSmtLibSpec.Grammar BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser.Calls BSmtLibSpec.Facts.Proofs.Parser.Parse
open BSmtLibSpec.Facts.Proofs.Parser.Rebuild BSmtLibSpec.Facts.Proofs.Parser.Recording
open BSmtLibSpec.Facts.Proofs.Parser.Simulation

theorem take_cons_succ {x x' : Received} {s s' : List Received} {k : Nat}
    (h : (x :: s).take (k + 1) = (x' :: s').take (k + 1)) : x = x' ∧ s.take k = s'.take k := by
  simpa using h

theorem eventsBefore_trace {α : Type} (p : Program Recorded α) :
    ∀ (items items' : List Received) (count k : Nat), items.take k = items'.take k →
      eventsBefore k (trace p items count) = eventsBefore k (trace p items' count) := by
  induction p with
  | done => intros; rfl
  | receive atArrival next ih =>
    intro items items' count k h
    cases items with
    | nil =>
      cases items' with
      | nil => rfl
      | cons x' s' =>
        cases k with
        | zero => cases atArrival <;> simp [trace, eventsBefore]
        | succ k => simp at h
    | cons x s =>
      cases items' with
      | nil =>
        cases k with
        | zero => cases atArrival <;> simp [trace, eventsBefore]
        | succ k => simp at h
      | cons x' s' =>
        cases k with
        | zero => cases atArrival <;> simp [trace, eventsBefore]
        | succ k =>
          obtain ⟨rfl, h'⟩ := take_cons_succ h
          cases atArrival <;> simp [trace, eventsBefore, ih x s s' _ k h']
  | call request next ih =>
    intro items items' count k h
    cases k <;> simp [trace, eventsBefore, ih _ items items' _ _ h]
  | setVersion version next ih =>
    intro items items' count k h
    cases k <;> simp [trace, eventsBefore, ih items items' _ _ h]
  | discard next ih =>
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
  | receive atArrival next ih =>
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
        | zero => cases atArrival <;> simp [trace, eventsBeforeProcessing]
        | succ k =>
          obtain ⟨rfl, h'⟩ := take_cons_succ h
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hl
          cases atArrival <;> simp [trace, eventsBeforeProcessing, ih x s s' _ k h' hl]
  | call request next ih =>
    intro items items' count k h hl
    cases k <;> simp [trace, eventsBeforeProcessing, ih _ items items' _ _ h hl]
  | setVersion version next ih =>
    intro items items' count k h hl
    cases k <;> simp [trace, eventsBeforeProcessing, ih items items' _ _ h hl]
  | discard next ih =>
    intro items items' count k h hl
    cases k <;> simp [trace, eventsBeforeProcessing, ih items items' _ _ h hl]
  | switch declarations version next ih =>
    intro items items' count k h hl
    cases k <;> simp [trace, eventsBeforeProcessing, ih items items' _ _ h hl]
  | stuck => intros; rfl

/-- The recording run of the commands of `parseScript`, after the handler's switch to the starting
version, on what a parser receives for a script, followed by anything, succeeds from any events
with one call and leaves what follows. -/
theorem parse_leaves {version : Version} {commands : List Tree.Command}
    (h : Script version commands) {n : Nat} (hn : 10 * sizeOf commands < n)
    (rest : List Received) (events : List Event) (he : calls events = 1) :
    ((runRecording (commandsFrom n 0) (received commands ++ rest)).run.run events).1 =
      .ok ((), rest) := by
  obtain ⟨s', h', -⟩ := built_commands commands version
    { (Recovery.initial version).push .none with version } 0 h rfl rfl
  have hm := run_commands (points := rebuildPoints) (handler := rebuildHandler)
    (producer := rebuildProducer) (policy := VersionPolicy.unrestricted)
    commands version 0 rest h hn
  have hr : (runRebuild (commandsFrom n 0) (received commands ++ rest)).run.run
      { (Recovery.initial version).push .none with version } = (.ok ((), rest), s') := by
    simp only [runRebuild, hm]
    exact yields_bind h' (yields_pure _ _)
  obtain ⟨-, hrec⟩ := rebuild_trace _ _ _ _ _ hr
  exact hrec events (by simp [he, Recovery.initial, Recovery.State.push])

/-- What a parser receives for a valid script is not a proper start of what it receives for
another valid script. -/
theorem received_not_prefix {version version' : Version} {commands commands' : List Tree.Command}
    (h : Script version commands) (h' : Script version' commands') {rest : List Received}
    (heq : received commands = received commands' ++ rest) : rest = [] := by
  let n := 10 * (sizeOf commands + sizeOf commands') + 1
  have he : calls [.handlerSwitch version] = 1 := rfl
  have h₁ := parse_leaves h (n := n) (by omega) [] _ he
  have h₂ := parse_leaves h' (n := n) (by omega) rest _ he
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

end BSmtLibSpec.Facts.Proofs.Parser.Placement
