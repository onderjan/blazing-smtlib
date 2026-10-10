import BSmtLib.SpecChecks.Parser.Rebuild
import BSmtLib.SpecChecks.Parser.Recording

/-!
# What a recording shows

The recording of a script is the trace of `parseScript` on what a parser receives for it
(`record_eq_trace`). Run with the rebuilding handler, the same program does what the steps of
`Recovery.recover` do with the trace, and it rebuilds the script (`built_script`), so the
recording's calls rebuild the script (`recover_record`); and the recording run succeeds,
receiving every item (`record_items`).

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Parser

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal Recovery

theorem command_env {state state' : Recovery.State} {request : Call Recorded .nothing}
    (h : state.command request = some state') : state'.env = state.env := by
  revert h
  cases request <;> simp only [State.command] <;> (try split) <;>
    (try simp [State.add, Option.map_eq_some_iff, Option.bind_eq_some_iff]) <;>
    (try split) <;> (try simp) <;> (intros; subst_vars; rfl)

theorem call_length {state state' : Recovery.State} {returns : Returns}
    {request : Call Recorded returns} (h : state.call request = some state') :
    state'.env.length = state.env.length + 1 := by
  cases returns
  case nothing =>
    simp only [State.call] at h
    rw [command_env h]
    simp [State.push]
  all_goals
    simp only [State.call, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    simp [State.push]

theorem run_bind_eq {α β : Type} (x : RRun α) (f : α → RRun β) (s : Recovery.State) :
    (x >>= f).run.run s =
      match x.run.run s with
      | (.ok a, s') => (f a).run.run s'
      | (.error e, s') => (.error e, s') := by
  simp only [ExceptT.run_bind, StateT.run_bind]
  rcases x.run.run s with ⟨e, s'⟩
  cases e <;> rfl

theorem bind_ok_inv {α β : Type} {x : RRun α} {f : α → RRun β} {s s'' : Recovery.State}
    {r : β} (h : (x >>= f).run.run s = (.ok r, s'')) :
    ∃ a s', x.run.run s = (.ok a, s') ∧ (f a).run.run s' = (.ok r, s'') := by
  rw [run_bind_eq] at h
  revert h
  rcases x.run.run s with ⟨e, s'⟩
  cases e with
  | error e => intro h; cases h
  | ok a => intro h; exact ⟨a, s', rfl, h⟩

theorem throw_not_ok {α : Type} {s s' : Recovery.State} {r : α} :
    (throw stuckFailure : RRun α).run.run s ≠ (.ok r, s') := by
  intro h
  cases h

/-- The rebuilding run of a program. -/
abbrev runRebuild {α : Type} (p : Program Recorded α) (items : List Received) :
    RRun (α × List Received) :=
  Program.run rebuildPoints rebuildHandler rebuildSwitch VersionPolicy.unrestricted p items

/-- A rebuilding run that succeeds is what the steps of the recovery do with the program's
trace, and the program's recording run succeeds with it. -/
theorem rebuild_trace {α : Type} (p : Program Recorded α) :
    ∀ (items : List Received) (state state' : Recovery.State) (result : α × List Received),
      (runRebuild p items).run.run state = (.ok result, state') →
      (trace p items state.env.length).foldlM step state = some state' ∧
      ∀ events, calls events = state.env.length →
        ((runRecording p items).run.run events).1 = .ok result := by
  induction p with
  | done a =>
    intro items state state' result h
    simp only [runRebuild, Program.run] at h
    cases h
    exact ⟨rfl, fun _ _ => rfl⟩
  | receive start next ih =>
    intro items state state' result h
    cases items with
    | nil => exact absurd h throw_not_ok
    | cons item items =>
      simp only [runRebuild, Program.run] at h ih
      obtain ⟨u, s₁, h₁, h₂⟩ := bind_ok_inv h
      cases start
      · simp only [↓reduceIte, Bool.false_eq_true] at h₁
        rw [yields_receive_at item (yields_pure () state)] at h₁
        cases h₁
        obtain ⟨hf, hrec⟩ := ih item items _ _ _ h₂
        refine ⟨by simpa [trace, List.foldlM_cons, step] using hf, fun events he => ?_⟩
        simp only [runRecording, Program.run]
        rw [bind_run (receive_run item false events)]
        exact hrec _ (by simpa [calls, List.countP_cons, Event.isCall] using he)
      · simp only [↓reduceIte] at h₁
        rw [yields_receive_at item (yields_startScript state)] at h₁
        cases h₁
        obtain ⟨hf, hrec⟩ := ih item items _ _ _ h₂
        have hl : (state.push .none).env.length = state.env.length + 1 := by simp [State.push]
        rw [hl] at hf hrec
        refine ⟨by simpa [trace, List.foldlM_cons, step] using hf, fun events he => ?_⟩
        have hr : (Traversal.receive (ε := Empty) recordingPoints item
            (ExceptT.lift recordingHandler.startScript)).run.run events =
            (.ok (), [.process item, .startScript, .arrive item] ++ events) := rfl
        simp only [runRecording, Program.run, ↓reduceIte]
        rw [bind_run hr]
        exact hrec _ (by simp [calls, List.countP_cons, Event.isCall] at he ⊢; omega)
  | call request next ih =>
    intro items state state' result h
    simp only [runRebuild, Program.run] at h ih
    obtain ⟨v, s₁, h₁, h₂⟩ := bind_ok_inv h
    cases hc : state.call request with
    | none =>
      have : (Traversal.call rebuildHandler request).run.run state = (.error (.handler ()),
        state) := by
        unfold Traversal.call ExceptT.adapt
        simp only [rebuildHandler, ExceptT.run, ExceptT.mk, StateT.run, Functor.map, StateT.map, hc]
        rfl
      rw [this] at h₁
      cases h₁
    | some s₁' =>
      rw [yields_call request hc] at h₁
      cases h₁
      obtain ⟨hf, hrec⟩ := ih _ items _ _ _ h₂
      rw [call_length hc] at hf
      refine ⟨by simpa [trace, List.foldlM_cons, step, hc] using hf, fun events he => ?_⟩
      simp only [runRecording, Program.run]
      rw [bind_run (call_run request events), he]
      rw [call_length hc] at hrec
      exact hrec _ (by simp [calls, List.countP_cons, Event.isCall] at he ⊢; omega)
  | endScript next ih =>
    intro items state state' result h
    simp only [runRebuild, Program.run] at h ih
    obtain ⟨u, s₁, h₁, h₂⟩ := bind_ok_inv h
    rw [yields_endScript state] at h₁
    cases h₁
    obtain ⟨hf, hrec⟩ := ih items _ _ _ h₂
    have hl : (state.push .none).env.length = state.env.length + 1 := by simp [State.push]
    rw [hl] at hf hrec
    refine ⟨by simpa [trace, List.foldlM_cons, step] using hf, fun events he => ?_⟩
    simp only [runRecording, Program.run]
    rw [bind_run (endScript_run events)]
    exact hrec _ (by simp [calls, List.countP_cons, Event.isCall] at he ⊢; omega)
  | switch declarations version next ih =>
    intro items state state' result h
    simp only [runRebuild, Program.run] at h ih
    obtain ⟨u, s₁, h₁, h₂⟩ := bind_ok_inv h
    rw [yields_switch declarations version state] at h₁
    cases h₁
    obtain ⟨hf, hrec⟩ := ih items _ _ _ h₂
    have hl : ({ state.push .none with version } : Recovery.State).env.length =
        state.env.length + 1 := by simp [State.push]
    rw [hl] at hf hrec
    refine ⟨by simpa [trace, List.foldlM_cons, step, State.call, State.command] using hf,
      fun events he => ?_⟩
    simp only [runRecording, Program.run]
    rw [bind_run (switch_run declarations version events)]
    exact hrec _ (by simp [calls, List.countP_cons, Event.isCall] at he ⊢; omega)
  | stuck =>
    intro items state state' result h
    exact absurd h throw_not_ok

/-! ## The recording of a script -/

theorem recording_bind_pure_state {α β : Type} (x : Run Recording Empty α) (b : β)
    (events : List Event) :
    ((x >>= fun _ => pure b).run.run events).2 = (x.run.run events).2 := by
  rw [recording_bind_run]
  rcases x.run.run events with ⟨e, events'⟩
  cases e <;> rfl

/-- The recording of a script is the trace of `parseScript` on what a parser receives for it. -/
theorem record_eq_trace {version : Version} {commands : List Tree.Command}
    (h : Script version commands) {n : Nat} (hn : 10 * sizeOf commands < n) :
    record commands = trace (parseScript n) (received commands) 0 := by
  have hm := run_script (points := recordingPoints) (handler := recordingHandler)
    (producerSwitch := recordingSwitch) (policy := VersionPolicy.unrestricted)
    version commands [] h hn
  rw [List.append_nil] at hm
  have hs := runRecording_state (parseScript n) (received commands) []
  simp only [runRecording] at hs
  rw [hm, recording_bind_pure_state] at hs
  simp only [record, Id.run]
  rw [hs]
  simp [calls]

/-- The recording run of `parseScript` on what a parser receives for a script succeeds, takes
every item, and its trace rebuilds the script. -/
theorem parse_rebuilds {version : Version} {commands : List Tree.Command}
    (h : Script version commands) {n : Nat} (hn : 10 * sizeOf commands < n) :
    (∃ s', (trace (parseScript n) (received commands) 0).foldlM step (initial version) = some s' ∧
      s'.commands = commands) ∧
    ((runRecording (parseScript n) (received commands)).run.run []).1 = .ok ((), []) := by
  obtain ⟨s', h', c'⟩ := built_script version commands h
  have hm := run_script (points := rebuildPoints) (handler := rebuildHandler)
    (producerSwitch := rebuildSwitch) (policy := VersionPolicy.unrestricted)
    version commands [] h hn
  rw [List.append_nil] at hm
  have hr : (runRebuild (parseScript n) (received commands)).run.run (initial version) =
      (.ok ((), []), s') := by
    simp only [runRebuild, hm]
    exact yields_bind h' (yields_pure _ _)
  obtain ⟨hf, hrec⟩ := rebuild_trace _ _ _ _ _ hr
  exact ⟨⟨s', by simpa [initial] using hf, c'⟩, hrec [] rfl⟩

/-- The steps of the recovery do the same with the calls of events as with the events. -/
theorem foldlM_filter (events : List Event) (state : Recovery.State) :
    (events.filter Event.isCall).foldlM step state = events.foldlM step state := by
  induction events generalizing state with
  | nil => rfl
  | cons event events ih =>
    cases event <;> simp [List.filter, Event.isCall, step, ih]

/-- The calls of a script's recording rebuild the script. -/
theorem recover_record {version : Version} {commands : List Tree.Command}
    (h : Script version commands) :
    recover version ((record commands).filter Event.isCall) = some commands := by
  obtain ⟨⟨s', hf, c'⟩, -⟩ := parse_rebuilds h (Nat.lt_succ_self (10 * sizeOf commands))
  rw [record_eq_trace h (Nat.lt_succ_self _), recover, foldlM_filter, hf]
  simp [c']

/-- The traversal of a script takes what a parser receives for it, each item arriving and then
processed. -/
theorem record_items {version : Version} {commands : List Tree.Command}
    (h : Script version commands) :
    (record commands).filterMap Event.arrived = received commands ∧
      (record commands).filterMap Event.processed = received commands := by
  obtain ⟨-, hok⟩ := parse_rebuilds h (Nat.lt_succ_self (10 * sizeOf commands))
  have := trace_items _ _ [] () [] hok
  rw [record_eq_trace h (Nat.lt_succ_self _)]
  simpa [calls] using this

end BSmtLib.SpecChecks.Parser
