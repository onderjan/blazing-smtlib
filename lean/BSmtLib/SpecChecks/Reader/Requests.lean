import BSmtLibSpec.Reader
import BSmtLibSpec.Grammar.Properties
import BSmtLib.SpecChecks.Parser.Bridge

/-!
# What the traversal asks of its producer

The requests that the traversal of commands makes of its producer after the item at a position
of what a parser takes for them (`requestsAt`): a switch of the version or the discarding, after
the `)` of a version declaration or of `exit`, and nothing anywhere else
(`requestsAfterLast_record`). Where it has asked for the discarding before an item, it asked for
it after the item before that one (`discard_record`). Folding the switches over the positions gives the version in force
at each position (`foldVersion_requestsAt`).

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Reader

open BSmtLibSpec BSmtLibSpec.Lexicon BSmtLibSpec.Grammar BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLibSpec.Lexicon.Properties
open BSmtLibSpec.Regex (Chars chars)
open BSmtLibSpec.Reader BSmtLibSpec.Parser.Traversal BSmtLib.SpecChecks.Parser

/-- Whether the command is `exit`. -/
def exitFlag : Tree.Command → Bool
  | .exit => true
  | _ => false

/-- The requests of the traversal after the item at position `count` (from one) of what a parser
takes for the commands: the version declared and whether the rest is discarded, after the `)`
of a command, and nothing elsewhere. -/
def requestsAt : List Tree.Command → Nat → Option Version × Bool
  | [], _ => (none, false)
  | first :: rest, count =>
    if count < first.tokens.length then (none, false)
    else if count = first.tokens.length then (first.declaredVersion, exitFlag first)
    else requestsAt rest (count - first.tokens.length)

/-- The version in force after `count` items, starting from `start`, when the switch after the
item at position `j` (from one) is `switch j`. -/
def foldVersion (start : Version) (switch : Nat → Option Version) : Nat → Version
  | 0 => start
  | count + 1 => (switch (count + 1)).getD (foldVersion start switch count)

/-! ## Lists of events -/

/-- The event is no request of the producer. -/
def notProducer : Event → Bool
  | .producerSwitch _ | .producerDiscard => false
  | _ => true

/-- The number of arrivals among the events. -/
abbrev arrivals (events : List Event) : Nat := (events.filterMap Event.arrived).length

/-- The events begin with an item arriving and then processed. -/
def Leads (events : List Event) : Prop :=
  ∃ item rest, events = .arrive item :: .process item :: rest

theorem eventsBefore_other {event : Event} (h : event.arrived = none) (count : Nat)
    (rest : List Event) : eventsBefore count (event :: rest) = event :: eventsBefore count rest := by
  cases event with
  | arrive => cases h
  | _ => cases count <;> rfl

theorem eventsBefore_append_lt : ∀ (first rest : List Event) (count : Nat),
    count < arrivals first → eventsBefore count (first ++ rest) = eventsBefore count first
  | [], _, _, h => by simp [arrivals] at h
  | event :: first, rest, count, h => by
    cases event with
    | arrive item =>
      cases count with
      | zero => rfl
      | succ count =>
        have h' : count < arrivals first := by simpa [arrivals, List.filterMap_cons, Event.arrived] using h
        simp only [List.cons_append, eventsBefore]
        rw [eventsBefore_append_lt first rest count h']
    | _ =>
      have h' : count < arrivals first := by simpa [arrivals, List.filterMap_cons, Event.arrived] using h
      rw [List.cons_append, eventsBefore_other rfl, eventsBefore_other rfl,
        eventsBefore_append_lt first rest count h']

theorem eventsBefore_append_ge : ∀ (first rest : List Event) (count : Nat),
    arrivals first ≤ count →
      eventsBefore count (first ++ rest) = first ++ eventsBefore (count - arrivals first) rest
  | [], _, _, _ => by simp [arrivals]
  | event :: first, rest, count, h => by
    cases event with
    | arrive item =>
      have he : arrivals (.arrive item :: first) = arrivals first + 1 := by
        simp [arrivals, Event.arrived]
      cases count with
      | zero => simp [he] at h
      | succ count =>
        have h' : arrivals first ≤ count := by omega
        simp only [List.cons_append, eventsBefore]
        rw [eventsBefore_append_ge first rest count h', he]
        simp
    | _ =>
      have h' : arrivals first ≤ count := by simpa [arrivals, List.filterMap_cons, Event.arrived] using h
      have he : ∀ e : Event, e.arrived = none → arrivals (e :: first) = arrivals first := by
        intro e he; simp [arrivals, he]
      rw [List.cons_append, eventsBefore_other rfl, he _ rfl,
        eventsBefore_append_ge first rest count h', List.cons_append]

theorem mem_eventsBefore : ∀ (count : Nat) (events : List Event) (event : Event),
    event ∈ eventsBefore count events → event ∈ events
  | _, [], _, h => by simp [eventsBefore] at h
  | count, head :: events, event, h => by
    cases head with
    | arrive item =>
      cases count with
      | zero => simp [eventsBefore] at h
      | succ count =>
        simp only [eventsBefore] at h
        rcases List.mem_cons.mp h with h | h
        · exact h ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_eventsBefore count events event h)
    | _ =>
      rw [eventsBefore_other rfl] at h
      rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_eventsBefore count events event h)

theorem eventsBefore_leads {events : List Event} (h : Leads events) {count : Nat}
    (hc : 1 ≤ count) : ∃ event ∈ eventsBefore count events, event.processed.isSome := by
  obtain ⟨item, rest, rfl⟩ := h
  obtain ⟨count, rfl⟩ : ∃ k, count = k + 1 := ⟨count - 1, by omega⟩
  refine ⟨.process item, ?_, rfl⟩
  simp [eventsBefore]

theorem eventsBefore_zero_leads {events : List Event} (h : Leads events) :
    eventsBefore 0 events = [] := by
  obtain ⟨item, rest, rfl⟩ := h
  rfl

theorem foldr_takeWhile_quiet {α β : Type} (f : α → β → β) (init : β) (p : α → Bool) :
    ∀ (events : List α), (∀ event ∈ events, ∀ r, f event r = r) →
      (events.takeWhile p).foldr f init = init
  | [], _ => rfl
  | event :: events, h => by
    simp only [List.takeWhile_cons]
    split
    · rw [List.foldr_cons, foldr_takeWhile_quiet f init p events
        (fun e he => h e (List.mem_cons_of_mem _ he)), h event List.mem_cons_self]
    · rfl

theorem foldr_takeWhile_append {α β : Type} (f : α → β → β) (init : β) (p : α → Bool)
    (later : List α) (h : ∀ event ∈ later, ∀ r, f event r = r) :
    ∀ (events : List α),
      ((events ++ later).takeWhile p).foldr f init = (events.takeWhile p).foldr f init
  | [] => by simp [foldr_takeWhile_quiet f init p later h]
  | event :: events => by
    simp only [List.cons_append, List.takeWhile_cons]
    split
    · simp only [List.foldr_cons, foldr_takeWhile_append f init p later h events]
    · rfl

theorem takeWhile_append_stop {α : Type} (p : α → Bool) (later : List α) :
    ∀ (events : List α), (∃ event ∈ events, p event = false) →
      (events ++ later).takeWhile p = events.takeWhile p
  | [], ⟨_, h, _⟩ => by simp at h
  | event :: events, ⟨e, he, hp⟩ => by
    simp only [List.cons_append, List.takeWhile_cons]
    split
    · rename_i hpe
      rcases List.mem_cons.mp he with rfl | he
      · simp [hp] at hpe
      · rw [takeWhile_append_stop p later events ⟨e, he, hp⟩]
    · rfl

/-- Events with no request of the producer before others leave their requests. -/
theorem requestsAfterLast_quiet_append {first : List Event}
    (h : ∀ event ∈ first, notProducer event = true) (rest : List Event) :
    requestsAfterLast (first ++ rest) = requestsAfterLast rest := by
  simp only [requestsAfterLast, List.reverse_append]
  refine foldr_takeWhile_append _ _ _ _ (fun event he r => ?_) _
  have hq := h event (List.mem_reverse.mp he)
  cases event <;> first | rfl | simp [notProducer] at hq

theorem requestsAfterLast_quiet {events : List Event}
    (h : ∀ event ∈ events, notProducer event = true) :
    requestsAfterLast events = (none, false) := by
  have := requestsAfterLast_quiet_append h []
  rw [List.append_nil] at this
  rw [this]
  rfl

/-- After a processing, the events before it make no difference. -/
theorem requestsAfterLast_append_processed (first : List Event) {rest : List Event}
    (h : ∃ event ∈ rest, event.processed.isSome) :
    requestsAfterLast (first ++ rest) = requestsAfterLast rest := by
  obtain ⟨event, he, hs⟩ := h
  simp only [requestsAfterLast, List.reverse_append]
  rw [takeWhile_append_stop _ _ _ ⟨event, List.mem_reverse.mpr he, by
    cases hp : event.processed <;> simp_all⟩]

/-! ## A command in a recording run -/

/-- A producer that never refuses and writes nothing down. -/
def silentProducer : Producer Recording := ⟨fun _ => pure (), pure ()⟩

theorem silent_switch_run (declarations : Nat) (version : Version) (state : List Event) :
    (switchVersion (ε := Empty) recordingHandler silentProducer VersionPolicy.unrestricted
        declarations version).run.run state =
      (.ok (), .handlerSwitch version :: state) := by
  simp only [switchVersion, unrestricted_check]
  rfl

theorem silent_discard_run (state : List Event) :
    (ExceptT.lift silentProducer.discardRest : Run Recording Empty Unit).run.run state =
      (.ok (), state) := rfl

/-- A program run with the silent producer writes down its trace without the producer's
requests. -/
theorem silent_state {α : Type} (p : Program Recorded α) :
    ∀ (items : List Received) (state : List Event),
      ((Program.run recordingPoints recordingHandler silentProducer VersionPolicy.unrestricted
          p items).run.run state).2 =
        ((trace p items (Parser.calls state)).filter notProducer).reverse ++ state := by
  induction p with
  | done => intro items state; rfl
  | receive atArrival next ih =>
    intro items state
    cases items with
    | nil => cases atArrival <;> rfl
    | cons item items =>
      rw [Program.run, bind_run (receive_run item atArrival state), ih]
      cases atArrival <;> simp [trace, Parser.calls, Event.isCall, List.countP_cons, notProducer, List.filter_cons]
  | call request next ih =>
    intro items state
    rw [Program.run, bind_run (call_run request state), ih]
    simp [trace, Parser.calls, Event.isCall, List.countP_cons, notProducer, List.filter_cons]
  | setVersion version next ih =>
    intro items state
    rw [Program.run, bind_run (setVersion_run version state), ih]
    simp [trace, Parser.calls, Event.isCall, List.countP_cons, notProducer, List.filter_cons]
  | discard next ih =>
    intro items state
    rw [Program.run, bind_run (silent_discard_run state), ih]
    simp [trace, notProducer]
  | switch declarations version next ih =>
    intro items state
    rw [Program.run, bind_run (silent_switch_run declarations version state), ih]
    simp [trace, Parser.calls, Event.isCall, List.countP_cons, notProducer, List.filter_cons]
  | stuck => intro items state; rfl

/-- The recording run of a valid command succeeds, writing down events that request nothing of
the producer, take the command's tokens and begin with its `(` arriving and processed. -/
theorem command_events {version : Version} {command : Tree.Command} (hv : command.Valid version)
    (state : List Event) :
    ∃ events, (Traversal.command (ε := Empty) recordingPoints recordingHandler command).run.run
        state = (.ok (), events.reverse ++ state) ∧
      (∀ event ∈ events, notProducer event = true) ∧
      arrivals events = command.tokens.length ∧ Leads events := by
  have hn : 10 * sizeOf command < 10 * sizeOf command + 1 := Nat.lt_succ_self _
  let events := trace (commandFirst (10 * sizeOf command + 1)) (items command.tokens)
    (Parser.calls state)
  have hRec := run_command (points := recordingPoints) (handler := recordingHandler)
    (producer := recordingProducer) (policy := VersionPolicy.unrestricted) version command [] hv hn
  have hSil := run_command (points := recordingPoints) (handler := recordingHandler)
    (producer := silentProducer) (policy := VersionPolicy.unrestricted) version command [] hv hn
  have hReb := run_command (points := rebuildPoints) (handler := rebuildHandler)
    (producer := rebuildProducer) (policy := VersionPolicy.unrestricted) version command [] hv hn
  rw [List.append_nil] at hRec hSil hReb
  let start : Recovery.State := ⟨version, List.replicate (Parser.calls state) .none, .none, []⟩
  obtain ⟨s', hs', -⟩ := built_command command start rfl hv
  have hr : (runRebuild (commandFirst (10 * sizeOf command + 1)) (items command.tokens)).run.run
      start = (.ok (afterOf command, []), s') := by
    simp only [runRebuild, hReb]
    exact yields_bind hs' (yields_pure _ _)
  have hok := (rebuild_trace _ _ _ _ _ hr).2 state (by simp [start])
  have hst := runRecording_state (commandFirst (10 * sizeOf command + 1)) (items command.tokens)
    state
  have hsil := silent_state (commandFirst (10 * sizeOf command + 1)) (items command.tokens) state
  have hrun : (runRecording (commandFirst (10 * sizeOf command + 1)) (items command.tokens)).run.run
      state = (.ok (afterOf command, []), events.reverse ++ state) := Prod.ext hok hst
  refine ⟨events, ?_, ?_, ?_, ?_⟩
  · simp only [runRecording, hRec] at hrun
    rw [recording_bind_run] at hrun
    revert hrun
    rcases (Traversal.command (ε := Empty) recordingPoints recordingHandler command).run.run state
      with ⟨result, after⟩
    cases result with
    | error e => intro h; cases h
    | ok u => intro h; cases u; cases h; rfl
  · have he : events.filter notProducer = events := by
      simp only [runRecording] at hst
      rw [hRec, ← hSil, hsil] at hst
      exact List.reverse_inj.mp (List.append_cancel_right hst)
    intro event hm
    exact List.filter_eq_self.mp he event hm
  · have := (trace_items _ _ _ _ _ hok).1
    simp only [List.append_nil] at this
    simp only [arrivals]
    rw [this]
    simp
  · obtain ⟨inner, hc⟩ := command_tokens_open command
    simp only [events, hc]
    exact ⟨_, _, rfl⟩

/-! ## The commands in a recording run -/

/-- The traversal of the commands in a recording run. -/
abbrev recordCommands (declarations : Nat) (commands : List Tree.Command) :
    Run Recording Empty Unit :=
  Traversal.commands recordingPoints recordingHandler recordingProducer
    VersionPolicy.unrestricted declarations commands

theorem recordCommands_none {command : Tree.Command} (hne : command ≠ .exit)
    (hd : command.declaredVersion = none) (declarations : Nat) (commands : List Tree.Command) :
    recordCommands declarations (command :: commands) =
      (Traversal.command recordingPoints recordingHandler command >>= fun _ =>
        if command.namesNoVersion then throw (.syntax .unsupportedVersion)
        else recordCommands declarations commands) := by
  cases command <;> first | exact absurd rfl hne | simp [Traversal.commands, hd]

theorem recordCommands_some {command : Tree.Command} (hne : command ≠ .exit) {version : Version}
    (hd : command.declaredVersion = some version) (declarations : Nat)
    (commands : List Tree.Command) :
    recordCommands declarations (command :: commands) =
      (Traversal.command recordingPoints recordingHandler command >>= fun _ =>
        switchVersion recordingHandler recordingProducer VersionPolicy.unrestricted declarations
          version >>= fun _ => recordCommands (declarations + 1) commands) := by
  cases command <;> first | exact absurd rfl hne | simp [Traversal.commands, hd]

theorem exitFlag_of_ne {command : Tree.Command} (hne : command ≠ .exit) :
    exitFlag command = false := by
  cases command <;> first | exact absurd rfl hne | rfl

/-- A declaration of a version that is not supported declares none and is rejected. -/
theorem refused_facts {version : Version} {command : Tree.Command}
    (h : command.modeAfter version = none) :
    command ≠ .exit ∧ command.declaredVersion = none ∧ command.namesNoVersion = true := by
  cases command with
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    simp only [Tree.Command.modeAfter] at h
    by_cases hk : keyword = chars "smt-lib-version"
    · simp only [hk, ite_true] at h
      refine ⟨by simp, ?_, ?_⟩
      · rcases value with _ | ((_ | decimal | _ | _ | _) | _ | _) <;>
          simp_all [Tree.Command.declaredVersion]
      · rcases value with _ | ((_ | decimal | _ | _ | _) | _ | _) <;>
          simp_all [Tree.Command.namesNoVersion]
    · simp [hk] at h
  | _ => simp [Tree.Command.modeAfter] at h

/-- The requests after the items of a command, then of events with neither arrivals nor
processings, then of commands that follow. -/
theorem requests_step {events between later : List Event}
    (hq : ∀ event ∈ events, notProducer event = true) (hl : Leads later)
    (hb : ∀ event ∈ between, event.arrived = none ∧ event.processed = none)
    (later' : Nat → Option Version × Bool)
    (hr : ∀ count, 1 ≤ count → requestsAfterLast (eventsBefore count later) = later' count)
    (count : Nat) :
    requestsAfterLast (eventsBefore count (events ++ between ++ later)) =
      if count < arrivals events then (none, false)
      else if count = arrivals events then requestsAfterLast between
      else later' (count - arrivals events) := by
  have hzero : arrivals between = 0 := by
    simp only [arrivals, List.length_eq_zero_iff, List.filterMap_eq_nil_iff]
    intro event he
    simp [(hb event he).1]
  rw [List.append_assoc]
  split
  · rename_i hlt
    rw [eventsBefore_append_lt _ _ _ hlt]
    exact requestsAfterLast_quiet fun event he => hq event (mem_eventsBefore _ _ _ he)
  · rename_i hlt
    rw [eventsBefore_append_ge _ _ _ (by omega),
      eventsBefore_append_ge _ _ _ (by omega), hzero, Nat.sub_zero]
    split
    · rename_i heq
      rw [heq, Nat.sub_self, eventsBefore_zero_leads hl, List.append_nil,
        requestsAfterLast_quiet_append hq]
    · rename_i hne
      rw [← List.append_assoc, requestsAfterLast_append_processed _
        (eventsBefore_leads hl (by omega)), hr _ (by omega)]

theorem not_discard_of_quiet {events : List Event}
    (hq : ∀ event ∈ events, notProducer event = true) : .producerDiscard ∉ events :=
  fun h => by simpa [notProducer] using hq _ h

/-- Where the events of a command, then events with no arrivals and no discarding, then those of
the commands that follow have asked for the discarding before an item, the requests after it are
those of the commands that follow. -/
theorem discard_step {events between later : List Event} {first : Tree.Command}
    {rest : List Tree.Command} {items : List Traversal.Received}
    (hq : ∀ event ∈ events, notProducer event = true) (harr : arrivals events = first.tokens.length)
    (hl : Leads later) (hb : ∀ event ∈ between, event.arrived = none ∧ event ≠ .producerDiscard)
    (hlater : ∀ count, count < items.length → .producerDiscard ∈ eventsBefore count later →
      (requestsAt rest count).2 = true) :
    ∀ count, count < (first.tokens.map Traversal.Received.token ++ items).length →
      .producerDiscard ∈ eventsBefore count (events ++ between ++ later) →
      (requestsAt (first :: rest) count).2 = true := by
  intro count hc hm
  have hzero : arrivals between = 0 := by
    simp only [arrivals, List.length_eq_zero_iff, List.filterMap_eq_nil_iff]
    intro event he
    simp [(hb event he).1]
  rw [List.append_assoc] at hm
  by_cases hlt : count < arrivals events
  · rw [eventsBefore_append_lt _ _ _ hlt] at hm
    exact absurd (mem_eventsBefore _ _ _ hm) (not_discard_of_quiet hq)
  · rw [eventsBefore_append_ge _ _ _ (by omega), eventsBefore_append_ge _ _ _ (by omega), hzero,
      Nat.sub_zero] at hm
    simp only [List.mem_append] at hm
    rcases hm with hm | hm | hm
    · exact absurd hm (not_discard_of_quiet hq)
    · exact absurd rfl (hb _ hm).2
    · by_cases heq : count = arrivals events
      · rw [heq, Nat.sub_self, eventsBefore_zero_leads hl] at hm
        simp at hm
      · have h' := hlater (count - arrivals events) (by simp at hc; omega) hm
        rw [harr] at heq hlt h'
        simp [requestsAt, hlt, heq, h']

/-- The events of the traversal of what a parser takes for commands, from any state: they begin
with an item arriving and processed, their requests are those of `requestsAt`, and where they
have asked for the discarding before an item, `requestsAt` discards after it. -/
theorem commands_events {version : Version} {commands : List Tree.Command}
    {taken : List Traversal.Received} {ending : Ending} (h : Takes version commands taken ending) :
    ∀ (declarations : Nat) (state : List Event), ∃ events,
      ((recordCommands declarations commands).run.run state).2 = events.reverse ++ state ∧
      Leads events ∧
      (∀ count, 1 ≤ count →
        requestsAfterLast (eventsBefore count events) = requestsAt commands count) ∧
      ∀ count, count < taken.length → .producerDiscard ∈ eventsBefore count events →
        (requestsAt commands count).2 = true := by
  induction h with
  | done =>
    intro declarations state
    refine ⟨[.arrive .endOfInput, .process .endOfInput], rfl, ⟨_, _, rfl⟩, ?_, ?_⟩
    · intro count hc
      obtain ⟨count, rfl⟩ : ∃ k, count = k + 1 := ⟨count - 1, by omega⟩
      simp [eventsBefore, requestsAt]
      rfl
    · intro count _ hm
      have := mem_eventsBefore _ _ _ hm
      simp at this
  | @command version nextVersion rest items ending first hv hm _ ih =>
    intro declarations state
    have hne : first ≠ .exit := by
      rintro rfl
      simp [Tree.Command.modeAfter] at hm
    obtain ⟨events, hrun, hq, harr, hl⟩ := command_events hv state
    have hreq : ∀ count, requestsAt (first :: rest) count =
        if count < arrivals events then (none, false)
        else if count = arrivals events then (first.declaredVersion, exitFlag first)
        else requestsAt rest (count - arrivals events) := by
      intro count
      rw [harr]
      rfl
    cases hd : first.declaredVersion with
    | none =>
      obtain ⟨later, hlater, hll, hlr, hld⟩ := ih declarations (events.reverse ++ state)
      refine ⟨events ++ [] ++ later, ?_, ?_, ?_, discard_step hq harr hll (by simp) hld⟩
      · rw [recordCommands_none hne hd, bind_run hrun, namesNoVersion_eq_false hm]
        simp [hlater]
      · obtain ⟨item, tail, he⟩ := hl
        exact ⟨item, tail ++ later, by simp [he]⟩
      · intro count hc
        rw [requests_step hq hll (by simp) _ hlr count, hreq, hd, exitFlag_of_ne hne]
        rfl
    | some declared =>
      obtain ⟨later, hlater, hll, hlr, hld⟩ := ih (declarations + 1)
        (.handlerSwitch declared :: .producerSwitch declared :: (events.reverse ++ state))
      refine ⟨events ++ [.producerSwitch declared, .handlerSwitch declared] ++ later, ?_, ?_, ?_,
        discard_step hq harr hll (by simp [Event.arrived]) hld⟩
      · rw [recordCommands_some hne hd, bind_run hrun,
          bind_run (switch_run declarations declared _), hlater]
        simp
      · obtain ⟨item, tail, he⟩ := hl
        exact ⟨item, tail ++ [.producerSwitch declared, .handlerSwitch declared] ++ later, by simp [he]⟩
      · intro count hc
        rw [requests_step hq hll (by simp [Event.arrived, Event.processed]) _ hlr count, hreq,
          hd, exitFlag_of_ne hne]
        rfl
  | @stop version last hv hm =>
    intro declarations state
    obtain rfl := modeAfter_unparsed hm
    obtain ⟨events, hrun, hq, harr, hl⟩ := command_events hv state
    refine ⟨events ++ [.producerDiscard] ++ [.arrive .endOfInput, .process .endOfInput], ?_, ?_, ?_,
      ?_⟩
    · simp only [recordCommands, Traversal.commands]
      rw [bind_run hrun, bind_run (discard_run _)]
      simp
      rfl
    · obtain ⟨item, tail, he⟩ := hl
      exact ⟨item, tail ++ [.producerDiscard] ++ [.arrive .endOfInput, .process .endOfInput],
        by simp [he]⟩
    · intro count hc
      rw [requests_step hq ⟨_, _, rfl⟩ (by simp [Event.arrived, Event.processed])
        (fun _ => (none, false)) _ count]
      · rw [harr]
        rfl
      · intro k hk
        obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp [eventsBefore]
        rfl
    · intro count hc hm
      by_cases hlt : count < arrivals events
      · rw [List.append_assoc, eventsBefore_append_lt _ _ _ hlt] at hm
        exact absurd (mem_eventsBefore _ _ _ hm) (not_discard_of_quiet hq)
      · obtain rfl : count = Tree.Command.exit.tokens.length := by simp at hc; omega
        simp [requestsAt, exitFlag]
  | @refused version last hv hm =>
    intro declarations state
    obtain ⟨hne, hd, hn⟩ := refused_facts hm
    obtain ⟨events, hrun, hq, _, hl⟩ := command_events hv state
    refine ⟨events, ?_, hl, ?_,
      fun _ _ hm => absurd (mem_eventsBefore _ _ _ hm) (not_discard_of_quiet hq)⟩
    · rw [recordCommands_none hne hd, bind_run hrun, hn]
      rfl
    · intro count hc
      rw [requestsAfterLast_quiet fun event he => hq event (mem_eventsBefore _ _ _ he)]
      simp only [requestsAt]
      split
      · rfl
      · split
        · rw [hd, exitFlag_of_ne hne]
        · rfl

/-- The events of a recording run: the switch to the version, then those of `commands_events`. -/
theorem record_events {version : Version} {commands : List Tree.Command}
    {taken : List Traversal.Received} {ending : Ending} (h : Takes version commands taken ending) :
    ∃ events, record version commands = .handlerSwitch version :: events ∧ Leads events ∧
      (∀ count, 1 ≤ count →
        requestsAfterLast (eventsBefore count events) = requestsAt commands count) ∧
      ∀ count, count < taken.length → .producerDiscard ∈ eventsBefore count events →
        (requestsAt commands count).2 = true := by
  obtain ⟨events, hrun, hl, hreq, hd⟩ := commands_events h 0 [.handlerSwitch version]
  have hscript : (script (ε := Empty) recordingPoints recordingHandler recordingProducer
      VersionPolicy.unrestricted version commands).run.run [] =
        (recordCommands 0 commands).run.run [.handlerSwitch version] :=
    bind_run (setVersion_run version [])
  have hrec : record version commands = .handlerSwitch version :: events := by
    simp only [record, Id.run]
    rw [hscript, hrun]
    simp
  exact ⟨events, hrec, hl, hreq, hd⟩

/-- The requests of a recording run after the item at a position are those of `requestsAt`. -/
theorem requestsAfterLast_record {version : Version} {commands : List Tree.Command}
    {taken : List Traversal.Received} {ending : Ending} (h : Takes version commands taken ending)
    {count : Nat} (h₁ : 1 ≤ count) :
    requestsAfterLast (eventsBefore count (record version commands)) =
      requestsAt commands count := by
  obtain ⟨events, hrec, -, hreq, -⟩ := record_events h
  rw [hrec, eventsBefore_other rfl, ← List.singleton_append,
    requestsAfterLast_quiet_append (by simp [notProducer]), hreq count h₁]

/-- Where a recording run has asked for the discarding before an item of what a parser takes,
the item is not the first, and `requestsAt` discards after the item before it. -/
theorem discard_record {version : Version} {commands : List Tree.Command}
    {taken : List Traversal.Received} {ending : Ending} (h : Takes version commands taken ending)
    {count : Nat} (hc : count < taken.length)
    (hm : .producerDiscard ∈ eventsBefore count (record version commands)) :
    1 ≤ count ∧ (requestsAt commands count).2 = true := by
  obtain ⟨events, hrec, hl, -, hd⟩ := record_events h
  rw [hrec, eventsBefore_other rfl] at hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm
  · refine ⟨?_, hd count hc hm⟩
    rcases Nat.eq_zero_or_pos count with rfl | hpos
    · rw [eventsBefore_zero_leads hl] at hm
      simp at hm
    · exact hpos

/-! ## The version in force -/

theorem foldVersion_quiet (start : Version) (switch : Nat → Option Version) :
    ∀ count, (∀ j, 1 ≤ j → j ≤ count → switch j = none) → foldVersion start switch count = start
  | 0, _ => rfl
  | count + 1, h => by
    simp only [foldVersion, h (count + 1) (by omega) (Nat.le_refl _), Option.getD_none]
    exact foldVersion_quiet start switch count fun j h₁ h₂ => h j h₁ (by omega)

theorem foldVersion_shift (start : Version) (switch : Nat → Option Version) (shift : Nat) :
    ∀ count, foldVersion start switch (shift + count) =
      foldVersion (foldVersion start switch shift) (fun j => switch (shift + j)) count
  | 0 => rfl
  | count + 1 => by
    simp only [foldVersion, ← foldVersion_shift start switch shift count]
    rfl

theorem foldVersion_congr (start : Version) {switch switch' : Nat → Option Version}
    (h : ∀ j, 1 ≤ j → switch j = switch' j) :
    ∀ count, foldVersion start switch count = foldVersion start switch' count
  | 0 => rfl
  | count + 1 => by
    simp only [foldVersion, h (count + 1) (by omega), foldVersion_congr start h count]

/-- Folding the switches of `requestsAt` gives the version in force. -/
theorem foldVersion_requestsAt (version : Version) (commands : List Tree.Command) (count : Nat) :
    foldVersion version (fun j => (requestsAt commands j).1) count =
      versionAt version commands count := by
  induction commands generalizing version count with
  | nil =>
    exact foldVersion_quiet _ _ _ fun _ _ _ => rfl
  | cons first rest ih =>
    obtain ⟨inner, hc⟩ := command_tokens_open first
    have hpos : 1 ≤ first.tokens.length := by simp [hc]
    have hbefore : ∀ j, j < first.tokens.length → (requestsAt (first :: rest) j).1 = none := by
      intro j hj
      simp [requestsAt, hj]
    simp only [versionAt]
    split
    · rename_i hlt
      exact foldVersion_quiet _ _ _ fun j _ hj => hbefore j (by omega)
    · rename_i hge
      obtain ⟨k, rfl⟩ : ∃ k, count = first.tokens.length + k :=
        ⟨count - first.tokens.length, by omega⟩
      rw [foldVersion_shift, Nat.add_sub_cancel_left, ← ih]
      have hat : foldVersion version (fun j => (requestsAt (first :: rest) j).1)
          first.tokens.length = first.declaredVersion.getD version := by
        obtain ⟨n, hn⟩ : ∃ n, first.tokens.length = n + 1 := ⟨_, (Nat.sub_add_cancel hpos).symm⟩
        rw [hn, foldVersion, foldVersion_quiet _ _ n fun j _ hj => hbefore j (by omega)]
        simp [requestsAt, hn]
      rw [hat]
      apply foldVersion_congr
      intro j hj
      have hj' : ¬ first.tokens.length + j < first.tokens.length := by omega
      have hj'' : j ≠ 0 := by omega
      simp [requestsAt, hj', hj'']

end BSmtLib.SpecChecks.Reader
