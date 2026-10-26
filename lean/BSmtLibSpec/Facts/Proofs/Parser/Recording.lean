module

public import BSmtLibSpec.Facts.Proofs.Parser.Program

@[expose] public section

/-!
# Programs in a recording run

What a program writes down in a recording run (`BSmtLibSpec.Parser.Properties.record`), as a list
computed from the program and its items (`trace`): the run writes down that list
(`runRecording_state`), and a run that succeeds has received the items it took, each arriving and
then processed, in order (`trace_items`). What the list shows before an item is in `Placement`
(`eventsBefore_trace`, `eventsBeforeProcessing_trace`).

Not trusted: everything here is proved.
-/

namespace BSmtLibSpec.Facts.Proofs.Parser.Recording

open BSmtLibSpec.Lexicon BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal Program

/-- A program run in a recording run. -/
abbrev runRecording {α : Type} (p : Program Recorded α) (items : List Received) :
    Run Recording Empty (α × List Received) :=
  Program.run recordingPoints recordingHandler recordingProducer VersionPolicy.unrestricted p items

/-- The events a program writes down in a recording run on the items, in order, given the
number of calls written down before. -/
def trace {α : Type} : Program Recorded α → List Received → Nat → List Event
  | .done _, _, _ => []
  | .receive none next, item :: items, count =>
    .arrive item :: .process item :: trace (next item) items count
  | .receive (some request) next, item :: items, count =>
    .arrive item :: .call .nothing request :: .process item :: trace (next item) items (count + 1)
  | .receive _ _, [], _ => []
  | .call request next, items, count =>
    .call _ request :: trace (next (recordedValue _ count)) items (count + 1)
  | .setVersion version next, items, count =>
    .handlerSwitch version :: trace next items (count + 1)
  | .discard next, items, count => .producerDiscard :: trace next items count
  | .switch _ version next, items, count =>
    .producerSwitch version :: .handlerSwitch version :: trace next items (count + 1)
  | .stuck, _, _ => []

/-- The number of calls among events. -/
abbrev calls (events : List Event) : Nat := events.countP Event.isCall

theorem unrestricted_check (declarations : Nat) (version : Version) :
    VersionPolicy.unrestricted.check declarations version = .ok () := by
  cases version <;> rfl

/-- A step of a recording run that succeeds goes on with what follows it. -/
theorem bind_run {α β : Type} {x : Run Recording Empty α} {f : α → Run Recording Empty β}
    {state state' : List Event} {a : α} (h : x.run.run state = (.ok a, state')) :
    (x >>= f).run.run state = (f a).run.run state' := by
  simp only [ExceptT.run_bind, StateT.run_bind, h]
  rfl

theorem receive_run (item : Received) (atArrival : Option (Call Recorded .nothing))
    (state : List Event) :
    (Traversal.receive (ε := Empty) recordingPoints item
        (arrival recordingHandler atArrival)).run.run state =
      (.ok (), (match atArrival with
        | none => [.process item, .arrive item]
        | some request => [.process item, .call .nothing request, .arrive item]) ++ state) := by
  cases atArrival <;> rfl

theorem call_run {returns : Returns} (request : Call Recorded returns) (state : List Event) :
    (Traversal.call recordingHandler request).run.run state =
      (.ok (recordedValue returns (calls state)), .call returns request :: state) := rfl

theorem setVersion_run (version : Version) (state : List Event) :
    (ExceptT.lift (recordingHandler.setVersion version) : Run Recording Empty Unit).run.run
        state =
      (.ok (), .handlerSwitch version :: state) := rfl

theorem discard_run (state : List Event) :
    (ExceptT.lift recordingProducer.discardRest : Run Recording Empty Unit).run.run state =
      (.ok (), .producerDiscard :: state) := rfl

theorem switch_run (declarations : Nat) (version : Version) (state : List Event) :
    (switchVersion recordingHandler recordingProducer VersionPolicy.unrestricted declarations
        version).run.run state =
      (.ok (), .handlerSwitch version :: .producerSwitch version :: state) := by
  simp only [switchVersion, unrestricted_check]
  rfl

/-- A program run in a recording run writes down its trace. -/
theorem runRecording_state {α : Type} (p : Program Recorded α) :
    ∀ (items : List Received) (state : List Event),
      ((runRecording p items).run.run state).2 =
        (trace p items (calls state)).reverse ++ state := by
  simp only [runRecording]
  induction p with
  | done => intro items state; rfl
  | receive atArrival next ih =>
    intro items state
    cases items with
    | nil => cases atArrival <;> rfl
    | cons item items =>
      rw [Program.run, bind_run (receive_run item atArrival state), ih]
      cases atArrival <;> simp [trace, calls, Event.isCall, List.countP_cons]
  | call request next ih =>
    intro items state
    rw [Program.run, bind_run (call_run request state), ih]
    simp [trace, calls, Event.isCall, List.countP_cons]
  | setVersion version next ih =>
    intro items state
    rw [Program.run, bind_run (setVersion_run version state), ih]
    simp [trace, calls, Event.isCall, List.countP_cons]
  | discard next ih =>
    intro items state
    rw [Program.run, bind_run (discard_run state), ih]
    simp [trace, calls, Event.isCall]
  | switch declarations version next ih =>
    intro items state
    rw [Program.run, bind_run (switch_run declarations version state), ih]
    simp [trace, calls, Event.isCall, List.countP_cons]
  | stuck => intro items state; rfl

theorem recording_bind_run {α β : Type} (x : Run Recording Empty α) (f : α → Run Recording Empty β)
    (events : List Event) :
    (x >>= f).run.run events =
      match x.run.run events with
      | (.ok a, events') => (f a).run.run events'
      | (.error e, events') => (.error e, events') := by
  simp only [ExceptT.run_bind, StateT.run_bind]
  rcases x.run.run events with ⟨e, events'⟩
  cases e <;> rfl

/-- A program whose recording run succeeds receives in its trace, arriving and then processed,
the items it took, in order. -/
theorem trace_items {α : Type} (p : Program Recorded α) :
    ∀ (items : List Received) (events : List Event) (a : α) (rest : List Received),
      ((runRecording p items).run.run events).1 = .ok (a, rest) →
      (trace p items (calls events)).filterMap Event.arrived ++ rest = items ∧
        (trace p items (calls events)).filterMap Event.processed ++ rest = items := by
  simp only [runRecording]
  induction p with
  | done => intro items events a rest h; cases h; simp [trace]
  | receive atArrival next ih =>
    intro items events a rest h
    cases items with
    | nil => cases atArrival <;> cases h
    | cons item items =>
      rw [Program.run, recording_bind_run, receive_run item atArrival events] at h
      have := ih item items _ a rest h
      cases atArrival with
      | none =>
        have hc : calls ([.process item, .arrive item] ++ events) = calls events := by
          simp [calls, Event.isCall]
        rw [hc] at this
        simp only [trace]
        refine ⟨?_, ?_⟩ <;>
          simp only [List.filterMap_cons, Event.arrived, Event.processed, List.cons_append] <;>
          simp [this.1, this.2]
      | some request =>
        have hc : calls ([.process item, .call .nothing request, .arrive item] ++ events) =
            calls events + 1 := by simp [calls, Event.isCall, List.countP_cons]
        rw [hc] at this
        simp only [trace]
        refine ⟨?_, ?_⟩ <;>
          simp only [List.filterMap_cons, Event.arrived, Event.processed, List.cons_append] <;>
          simp [this.1, this.2]
  | call request next ih =>
    intro items events a rest h
    rw [Program.run, recording_bind_run, call_run request events] at h
    have := ih _ items _ a rest h
    have hc : calls (.call _ request :: events) = calls events + 1 := by
      simp [calls, Event.isCall, List.countP_cons]
    rw [hc] at this
    simp only [trace]
    refine ⟨?_, ?_⟩ <;>
      simp only [List.filterMap_cons, Event.arrived, Event.processed] <;>
      simp [this.1, this.2]
  | setVersion version next ih =>
    intro items events a rest h
    rw [Program.run, recording_bind_run, setVersion_run version events] at h
    have := ih items _ a rest h
    have hc : calls (.handlerSwitch version :: events) = calls events + 1 := by
      simp [calls, Event.isCall, List.countP_cons]
    rw [hc] at this
    simp only [trace]
    refine ⟨?_, ?_⟩ <;>
      simp only [List.filterMap_cons, Event.arrived, Event.processed] <;>
      simp [this.1, this.2]
  | discard next ih =>
    intro items events a rest h
    rw [Program.run, recording_bind_run, discard_run events] at h
    have := ih items _ a rest h
    have hc : calls (.producerDiscard :: events) = calls events := by
      simp [calls, Event.isCall]
    rw [hc] at this
    simp only [trace]
    refine ⟨?_, ?_⟩ <;>
      simp only [List.filterMap_cons, Event.arrived, Event.processed] <;>
      simp [this.1, this.2]
  | switch declarations version next ih =>
    intro items events a rest h
    rw [Program.run, recording_bind_run, switch_run declarations version events] at h
    have := ih items _ a rest h
    have hc : calls (.handlerSwitch version :: .producerSwitch version :: events) =
        calls events + 1 := by simp [calls, Event.isCall, List.countP_cons]
    rw [hc] at this
    simp only [trace]
    refine ⟨?_, ?_⟩ <;>
      simp only [List.filterMap_cons, Event.arrived, Event.processed] <;>
      simp [this.1, this.2]
  | stuck => intro items events a rest h; cases h

end BSmtLibSpec.Facts.Proofs.Parser.Recording
