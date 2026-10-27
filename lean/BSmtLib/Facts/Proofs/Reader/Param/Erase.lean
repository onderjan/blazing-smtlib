module

public import BSmtLib.Facts.Proofs.Parser.QuietSteps
import all BSmtLib.Parser

@[expose] public section

/-!
# The parser's steps read the log only by its calls

In a recording run of the library's parser (the handler `recordingLibrary`, whose state is the
log), a step reads the log only through the handler, which counts the calls in it. So a step run
from the log with every event that is not a call left out does what it does from the whole log,
and leaves the log with its events that are not calls left out (`Erasing`). The parse adapter
runs the parser with no token points and acts on its producer itself, so its handler's log is
the recording run's with the token points and the producer's events left out.

As for `Facts.Proofs.Parser.Quiet`, Lean does not give this free theorem: it is proved for each step
from how it is built, by the closure lemmas below and the tactic `erasing_step`.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Erase

open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser
open BSmtLib.Facts.Parser.Adapters.Handler

/-- The log with the events that are not calls left out. -/
abbrev calls (events : List Event) : List Event := events.filter Event.isCall

/-- Run from the log with its events that are not calls left out, the action does what it does
from the whole log, and leaves the log with those events left out; it adds only calls to the
log; its results satisfy `P`. -/
structure Erasing {α : Type} (P : α → Prop) (x : Parser.Quiet.RPM α) : Prop where
  erase : ∀ events, x.run.run (calls events) = ((x.run.run events).1, calls (x.run.run events).2)
  adds : ∀ events, ∃ added, (x.run.run events).2 = added ++ events ∧ ∀ e ∈ added, e.isCall = true
  post : ∀ events a, (x.run.run events).1 = .ok a → P a

/-- `Erasing` with no condition on the result. -/
abbrev Erases {α : Type} (x : Parser.Quiet.RPM α) : Prop := Erasing (fun _ => True) x

section

variable {α β : Type} {P Q : α → Prop}

theorem Erasing.pure {a : α} (h : P a) : Erasing P (Pure.pure a : Parser.Quiet.RPM α) :=
  ⟨fun _ => rfl, fun _ => ⟨[], rfl, by simp⟩, fun _ a' ha' => by cases ha'; exact h⟩

theorem Erasing.throw (e : Parser.ParseErrorKind Unit) :
    Erasing P (MonadExcept.throw e : Parser.Quiet.RPM α) :=
  ⟨fun _ => rfl, fun _ => ⟨[], rfl, by simp⟩, fun _ _ h => by cases h⟩

theorem Erasing.bind {P : β → Prop} {x : Parser.Quiet.RPM α} {f : α → Parser.Quiet.RPM β}
    (hx : Erasing Q x)
    (hf : ∀ a, Q a → Erasing P (f a)) : Erasing P (x >>= f) := by
  constructor
  · intro events
    simp only [ExceptT.run_bind, StateT.run_bind]
    rw [hx.erase events]
    rcases hrun : x.run.run events with ⟨result, events'⟩
    cases result with
    | error e => rfl
    | ok a =>
      have hq := hx.post events a (by rw [hrun])
      exact (hf a hq).erase events'
  · intro events
    simp only [ExceptT.run_bind, StateT.run_bind]
    obtain ⟨added, hadded, hcalls⟩ := hx.adds events
    rcases hrun : x.run.run events with ⟨result, events'⟩
    rw [hrun] at hadded
    simp only at hadded
    cases result with
    | error e => exact ⟨added, hadded, hcalls⟩
    | ok a =>
      obtain ⟨added', hadded', hcalls'⟩ := (hf a (hx.post events a (by rw [hrun]))).adds events'
      refine ⟨added' ++ added, ?_, ?_⟩
      · change ((f a).run.run events').2 = _
        rw [hadded', hadded, List.append_assoc]
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hcalls' e he
        · exact hcalls e he
  · intro events b hb
    simp only [ExceptT.run_bind, StateT.run_bind] at hb
    rcases hrun : x.run.run events with ⟨result, events'⟩
    rw [hrun] at hb
    cases result with
    | error e => cases hb
    | ok a => exact (hf a (hx.post events a (by rw [hrun]))).post events' b hb

theorem Erasing.bind_erases {P : β → Prop} {x : Parser.Quiet.RPM α} {f : α → Parser.Quiet.RPM β}
    (hx : Erases x)
    (hf : ∀ a, Erasing P (f a)) : Erasing P (x >>= f) :=
  Erasing.bind hx fun a _ => hf a

theorem Erasing.mono {x : Parser.Quiet.RPM α} (h : Erasing Q x)
    (himp : ∀ a, Q a → P a) : Erasing P x :=
  ⟨h.erase, h.adds, fun events a ha => himp a (h.post events a ha)⟩

theorem Erasing.erases {x : Parser.Quiet.RPM α} (h : Erasing P x) : Erases x := h.mono fun _ _ =>
    trivial

theorem countP_calls (events : List Event) :
    (calls events).countP Event.isCall = events.countP Event.isCall := by
  simp only [calls, List.countP_eq_length_filter, List.filter_filter, Bool.and_self]

theorem calls_cons_call {event : Event} (h : event.isCall = true) (events : List Event) :
    calls (event :: events) = event :: calls events :=
  List.filter_cons_of_pos h

/-- A call of the recording handler counts the calls of the log and writes one. -/
theorem erases_call {returns : Returns} (request : Call Recorded returns) :
    Erases (Parser.Internal.call (recordingCall request) : Parser.Quiet.RPM
        (Recorded.of returns)) := by
  constructor
  · intro events
    show (Except.ok (recordedValue returns ((calls events).countP Event.isCall)),
        Event.call returns request :: calls events) =
      (Except.ok (recordedValue returns (events.countP Event.isCall)),
        calls (Event.call returns request :: events))
    rw [countP_calls, calls_cons_call rfl]
  · intro events; exact ⟨[_], rfl, by simp [Event.isCall]⟩
  · intro _ _ _; trivial

/-- The recording handler's version switch writes one call. -/
theorem erases_setVersion (version : BSmtLibSpec.Lexicon.Version) :
    Erases (ExceptT.lift (recordingHandler.setVersion version) : Parser.Quiet.RPM Unit) := by
  constructor
  · intro events
    show (Except.ok (), Event.handlerSwitch version :: calls events) =
      (Except.ok (), calls (Event.handlerSwitch version :: events))
    rw [calls_cons_call rfl]
  · intro events; exact ⟨[_], rfl, by simp [Event.isCall]⟩
  · intro _ _ _; trivial

end

end BSmtLib.Facts.Proofs.Reader.Param.Erase
