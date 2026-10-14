module

public import BSmtLib.Facts.Proofs.Reader.Consumer

@[expose] public section

/-!
# Where the traversal asks its producer, along what a parser takes

`requests_record` in `Facts.Proofs.Parser.Trace` states what the traversal of a script asks of its
producer after each item. Here the same is stated for what a parser takes for any commands
(`Takes`), a declaration that names no supported version at their end included
(`requests_takes_record`): the traversal is followed command by command, as `Traversal.commands` is
written, and each command's recording run is the trace of the reader of the command
(`command_state`), which succeeds (`command_ok`) and asks nothing of the producer.

So the script consumer, on tokens that stand for a start of what a parser takes, asks for what
`requestsAt` says (`requests_takes_prefix`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Requests

open BSmtLibSpec BSmtLibSpec.Grammar BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Regex (chars)
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Facts.Proofs.Parser.Cut (isArrival eventsBefore_append)
open BSmtLib.Facts.Parser.Adapters.Run (isProcessing afterLastProcess switchOf discardOf)
open BSmtLib.Facts.Proofs.Parser.Trace (command_trace_quiet requestEvents
    afterLastProcess_append_proc eventsBefore_trace_proc eventsBefore_append_left
        eventsBefore_sublist requestsAt switchIn discardIn switchOf_eq_switchIn
            discardOf_eq_discardIn requests_split commandFirst_arrivals switchOf_handlerSwitch
                requests_record)
open BSmtLib.Facts.Proofs.Reader.Consumer BSmtLib.Facts.Reader.Adapters
open BSmtLibSpec.Facts.Proofs.Parser BSmtLibSpec.Facts.Proofs.Parser.Calls
open BSmtLibSpec.Facts.Proofs.Parser.Rebuild BSmtLibSpec.Facts.Proofs.Parser.Recording
open BSmtLibSpec.Facts.Proofs.Parser.Simulation

open BSmtLib.Facts.Parser.Adapters.Run.Rejection (libraryParser)
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection (rcv)

/-! ## A command's recording run -/

/-- The recording run of a valid command's traversal writes down the trace of the reader of the
command. -/
theorem command_state {version : Lexicon.Version} {command : Tree.Command}
    (hv : command.Valid version) (rest : List Received) {n : Nat}
    (hn : 10 * sizeOf command < n) (state : List Event) :
    ((Traversal.command recordingPoints recordingHandler command).run.run state).2 =
      (trace (commandFirst n) (items command.tokens ++ rest) (calls state)).reverse ++
        state := by
  have h₁ := run_command (points := recordingPoints) (handler := recordingHandler)
    (producer := recordingProducer) (policy := VersionPolicy.unrestricted) version command
    rest hv hn
  have hs := runRecording_state (commandFirst n) (items command.tokens ++ rest) state
  simp only [runRecording] at hs
  rw [h₁, recording_bind_pure_state] at hs
  exact hs

/-- The recording run of a valid command's traversal succeeds, from every state. -/
theorem command_ok {version : Lexicon.Version} {command : Tree.Command}
    (hv : command.Valid version) (state : List Event) :
    ((Traversal.command recordingPoints recordingHandler command).run.run state).1 =
      .ok () := by
  let s : Facts.Proofs.Parser.Recovery.State := ⟨version, List.replicate
      (calls state) .none, .none, []⟩
  obtain ⟨s', hy, -⟩ := built_command command s rfl hv
  have hr := run_command (points := rebuildPoints) (handler := rebuildHandler)
    (producer := rebuildProducer) (policy := VersionPolicy.unrestricted) version command []
    (n := 10 * sizeOf command + 1) hv (by omega)
  have hrun : (runRebuild (commandFirst (10 * sizeOf command + 1))
      (items command.tokens ++ [])).run.run s = (.ok (afterOf command, []), s') := by
    simp only [runRebuild]
    rw [hr]
    exact yields_bind hy (yields_pure _ _)
  have hok := (rebuild_trace _ _ _ _ _ hrun).2 state (by simp [s])
  have h₁ := run_command (points := recordingPoints) (handler := recordingHandler)
    (producer := recordingProducer) (policy := VersionPolicy.unrestricted) version command
    [] (n := 10 * sizeOf command + 1) hv (by omega)
  simp only [runRecording] at hok
  rw [h₁, recording_bind_run] at hok
  revert hok
  rcases (Traversal.command recordingPoints recordingHandler command).run.run state with ⟨r, s''⟩
  rcases r with e | ⟨⟩
  · intro h; cases h
  · intro _; rfl

/-- The recording run of a valid command's traversal: its trace, and success. -/
theorem command_run {version : Lexicon.Version} {command : Tree.Command}
    (hv : command.Valid version) (rest : List Received) {n : Nat}
    (hn : 10 * sizeOf command < n) (state : List Event) :
    (Traversal.command recordingPoints recordingHandler command).run.run state =
      (.ok (), (trace (commandFirst n) (items command.tokens ++ rest)
        (calls state)).reverse ++ state) :=
  Prod.ext (command_ok hv state) (command_state hv rest hn state)

/-- The reader of a valid command succeeds in a recording run, from every state. -/
theorem commandFirst_ok {version : Lexicon.Version} {command : Tree.Command}
    (hv : command.Valid version) (rest : List Received) {n : Nat}
    (hn : 10 * sizeOf command < n) (state : List Event) :
    ∃ state', (runRecording (commandFirst n) (items command.tokens ++ rest)).run.run state =
      (.ok (afterOf command, rest), state') := by
  have h₁ := run_command (points := recordingPoints) (handler := recordingHandler)
    (producer := recordingProducer) (policy := VersionPolicy.unrestricted) version command
    rest hv hn
  simp only [runRecording]
  rw [h₁, recording_bind_run, command_run hv rest hn state]
  exact ⟨_, rfl⟩

/-- The trace of the reader of a command starts with the arrival of the command's `(`. -/
theorem commandFirst_trace_head (command : Tree.Command) (rest : List Received)
    (n count : Nat) :
    eventsBefore 0 (trace (commandFirst n) (items command.tokens ++ rest) count) = [] := by
  obtain ⟨inner, h⟩ := command_tokens_open command
  rw [h]
  rfl

/-- Before the arrival of any item after the first, the events of a part that has processed an
item, followed by more, have processed one. -/
theorem proc_append {X : List Event} (Y : List Event)
    (hX : ∀ j, ∃ e ∈ eventsBefore (j + 1) X, isProcessing e = true) (j : Nat) :
    ∃ e ∈ eventsBefore (j + 1) (X ++ Y), isProcessing e = true := by
  by_cases hj : j + 1 < X.countP isArrival
  · rw [eventsBefore_append_left _ hj]
    exact hX j
  · obtain ⟨e, he, hp⟩ := hX j
    refine ⟨e, ?_, hp⟩
    rw [show j + 1 = X.countP isArrival + (j + 1 - X.countP isArrival) by omega,
      eventsBefore_append]
    exact List.mem_append_left _ ((eventsBefore_sublist _ X).subset he)

theorem tokens_length_pos (command : Tree.Command) : 0 < command.tokens.length :=
  Nat.pos_of_ne_zero (Parser.Rejection.Unique.tokens_ne_nil command)

theorem eventsBefore_zero_append {X : List Event} (Y : List Event) (h : eventsBefore 0 X = [])
    (hpos : 0 < X.countP isArrival) : eventsBefore 0 (X ++ Y) = [] := by
  rw [eventsBefore_append_left _ hpos, h]

theorem trace_proc {α : Type} (p : Program Recorded α) (items : List Received) (count : Nat)
    (h : 0 < (trace p items count).countP isArrival) (j : Nat) :
    ∃ e ∈ eventsBefore (j + 1) (trace p items count), isProcessing e = true :=
  eventsBefore_trace_proc p items count j h

/-- A recording run that ends with a call that returns nothing, where it succeeds, writes that
call down last. -/
theorem call_last {α : Type} (first : Run Recording Empty α) (f : α → Call Recorded .nothing)
    (state : List Event)
    (h : ((first >>= fun a => Traversal.call recordingHandler (f a)).run.run state).1 = .ok ()) :
    ∃ a rest, ((first >>= fun a => Traversal.call recordingHandler (f a)).run.run state).2 =
      .call .nothing (f a) :: rest := by
  rw [recording_bind_run] at h ⊢
  revert h
  rcases first.run.run state with ⟨r, s⟩
  rcases r with e | a
  · intro h; cases h
  · intro _
    exact ⟨a, s, rfl⟩


/-- The recording run of a valid `set-info` ends with its call. -/
theorem setInfo_run {version : Lexicon.Version} {info : Tree.Attribute}
    (hv : (Tree.Command.setInfo info).Valid version) (state : List Event) :
    ∃ handled rest, ((Traversal.command recordingPoints recordingHandler
        (.setInfo info)).run.run state).2 =
      .call .nothing (.commandSetInfo handled) :: rest := by
  obtain ⟨keyword, value⟩ := info
  have hok := command_ok hv state
  have e : Traversal.command recordingPoints recordingHandler (.setInfo ⟨keyword, value⟩) =
      ((opening recordingPoints "set-info" >>=
        fun _ => take recordingPoints (.keyword keyword)) >>= fun _ =>
        attributeThen recordingPoints recordingHandler keyword .parenClose value) >>=
        fun handled => call recordingHandler (.commandSetInfo handled) := by
    simp only [Traversal.command, bind_assoc]
    rfl
  rw [e] at hok ⊢
  exact call_last _ _ _ hok

theorem getLast?_of_reverse_append {X s r : List Event} {a : Event} (hne : X ≠ [])
    (h : X.reverse ++ s = a :: r) : X.getLast? = some a := by
  rw [← List.head?_reverse]
  cases hX : X.reverse with
  | nil => simp at hX; exact absurd hX hne
  | cons b X' =>
    rw [hX] at h
    simp only [List.cons_append, List.cons.injEq] at h
    simp [h.1]

/-! ## Along what a parser takes -/

/-- The events of the traversal of commands that a parser takes, from any state and any number
of declarations before: they start with an arrival, have processed an item before the second
arrival, and after each item ask the producer for what `requestsAt` says. -/
theorem requests_takes_trace {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes version commands taken ending) :
    ∀ (declarations : Nat) (state : List Event), ∃ events : List Event,
      ((Traversal.commands recordingPoints recordingHandler recordingProducer
          VersionPolicy.unrestricted declarations commands).run.run state).2 =
          events.reverse ++ state ∧
        eventsBefore 0 events = [] ∧ events.countP isArrival = taken.length ∧
        (ending ≠ .finished →
          ∃ handled, events.getLast? = some (.call .nothing (.commandSetInfo handled))) ∧
        (∀ j, ∃ e ∈ eventsBefore (j + 1) events, isProcessing e = true) ∧
        ∀ k < taken.length,
          switchOf (eventsBefore (k + 1) events) = (requestsAt commands k).1 ∧
            discardOf (eventsBefore (k + 1) events) = (requestsAt commands k).2 := by
  induction htakes with
  | done =>
    intro declarations state
    refine ⟨[.arrive .endOfInput, .process .endOfInput], rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro h; exact absurd rfl h
    · intro j
      exact ⟨.process .endOfInput, by simp [eventsBefore], rfl⟩
    · intro k hk
      simp only [List.length_singleton] at hk
      obtain rfl : k = 0 := by omega
      simp [eventsBefore, switchOf, discardOf, afterLastProcess, isProcessing, requestsAt]
  | @stop v last hv hm =>
    obtain rfl := Parser.Script.modeAfter_unparsed hm
    intro declarations state
    let n := 10 * sizeOf Tree.Command.exit + 1
    let T := trace (commandFirst n) (items Tree.Command.exit.tokens ++ [.endOfInput])
      (calls state)
    refine ⟨T ++ [.producerDiscard] ++ [.arrive .endOfInput, .process .endOfInput],
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Traversal.commands]
      rw [recording_bind_run, command_run hv [.endOfInput] (n := n) (by omega) state]
      simp only [recording_bind_run, discard_run]
      rw [show (Traversal.receive recordingPoints Received.endOfInput : Run Recording Empty Unit) =
        Traversal.receive recordingPoints .endOfInput
          (Facts.Proofs.Parser.Program.arrival recordingHandler none) from rfl,
        receive_run]
      simp [T]
    · rw [List.append_assoc]
      obtain ⟨_, hok⟩ := commandFirst_ok hv [.endOfInput] (n := n) (by omega) state
      have harr := commandFirst_arrivals hv [.endOfInput] (n := n) (by omega) hok
      exact eventsBefore_zero_append _ (commandFirst_trace_head _ _ _ _)
        (by rw [harr]; decide)
    · obtain ⟨_, hok⟩ := commandFirst_ok hv [.endOfInput] (n := n) (by omega) state
      have harr := commandFirst_arrivals hv [.endOfInput] (n := n) (by omega) hok
      simp only [List.countP_append, T, harr]
      rfl
    · intro h; exact absurd rfl h
    · rw [List.append_assoc]
      obtain ⟨_, hok⟩ := commandFirst_ok hv [.endOfInput] (n := n) (by omega) state
      have harr := commandFirst_arrivals hv [.endOfInput] (n := n) (by omega) hok
      exact proc_append _ (trace_proc _ _ _ (by rw [harr]; decide))
    · obtain ⟨_, hok⟩ := commandFirst_ok hv [.endOfInput] (n := n) (by omega) state
      have harr := commandFirst_arrivals hv [.endOfInput] (n := n) (by omega) hok
      have hq := command_trace_quiet hv [.endOfInput] (n := n) (by omega) (calls state)
      intro k hk
      have hsplit := requests_split (R := [.producerDiscard])
        (U := [.arrive .endOfInput, .process .endOfInput]) hq harr
        (by intro e he; simp at he; subst he; simp [isProcessing, isArrival])
        rfl k
      simp only [List.length_append, List.length_map, List.length_singleton] at hk
      by_cases h1 : k + 1 < Tree.Command.exit.tokens.length
      · obtain ⟨e1, e2⟩ := hsplit.1 h1
        rw [e1, e2]; simp [requestsAt, h1]
      · by_cases h2 : k + 1 = Tree.Command.exit.tokens.length
        · obtain ⟨e1, e2⟩ := hsplit.2.1 h2
          rw [e1, e2]; simp [requestsAt, h2, switchIn, discardIn, Tree.Command.declaredVersion]
        · have h3 : k = Tree.Command.exit.tokens.length := by omega
          rw [hsplit.2.2 (by omega), h3]
          simp [requestsAt, eventsBefore, switchOf, discardOf, afterLastProcess, isProcessing]
  | @refused v last hv hm =>
    intro declarations state
    let n := 10 * sizeOf last + 1
    let T := trace (commandFirst n) (items last.tokens ++ []) (calls state)
    have hrun := command_run hv [] (n := n) (by omega) state
    refine ⟨T, ?_, commandFirst_trace_head _ _ _ _, ?_, ?_, ?_, ?_⟩
    · rw [Parser.Refused.commands_refused _ _ _ hm, recording_bind_run, hrun]
      rfl
    · obtain ⟨_, hok⟩ := commandFirst_ok hv [] (n := n) (by omega) state
      have harr := commandFirst_arrivals hv [] (n := n) (by omega) hok
      simpa [T] using harr
    · intro _
      obtain ⟨info, rfl⟩ : ∃ info, last = .setInfo info := by
        cases last <;> first | exact ⟨_, rfl⟩ | simp [Tree.Command.modeAfter] at hm
      obtain ⟨handled, rest, hlast⟩ := setInfo_run hv state
      rw [hrun] at hlast
      obtain ⟨_, hok⟩ := commandFirst_ok hv [] (n := n) (by omega) state
      have harr := commandFirst_arrivals hv [] (n := n) (by omega) hok
      have hne : T ≠ [] := by
        intro h
        have := tokens_length_pos (.setInfo info)
        simp only [T] at h
        rw [h] at harr
        simp at harr
        omega
      exact ⟨handled, getLast?_of_reverse_append hne hlast⟩
    · obtain ⟨_, hok⟩ := commandFirst_ok hv [] (n := n) (by omega) state
      have harr := commandFirst_arrivals hv [] (n := n) (by omega) hok
      exact trace_proc _ _ _ (by rw [harr]; exact tokens_length_pos last)
    · obtain ⟨_, hok⟩ := commandFirst_ok hv [] (n := n) (by omega) state
      have harr := commandFirst_arrivals hv [] (n := n) (by omega) hok
      have hq := command_trace_quiet hv [] (n := n) (by omega) (calls state)
      intro k hk
      have hsplit := requests_split (R := []) (U := []) hq harr (by simp) rfl k
      simp only [T, List.append_nil] at hsplit ⊢
      simp only [List.length_map] at hk
      have hd : last.declaredVersion = none := by
        cases last with
        | setInfo info =>
          obtain ⟨keyword, value⟩ := info
          simp only [Tree.Command.modeAfter] at hm
          by_cases hk : keyword = chars "smt-lib-version"
          · subst hk
            rcases value with _ | ⟨⟨_ | decimal | _ | _ | _⟩ | _ | _⟩ <;>
              simp_all [Tree.Command.declaredVersion]
          · simp [hk] at hm
        | _ => simp [Tree.Command.modeAfter] at hm
      have hne : last ≠ .exit := by rintro rfl; simp [Tree.Command.modeAfter] at hm
      by_cases h1 : k + 1 < last.tokens.length
      · obtain ⟨e1, e2⟩ := hsplit.1 h1
        rw [e1, e2]; simp [requestsAt, h1]
      · have h2 : k + 1 = last.tokens.length := by omega
        obtain ⟨e1, e2⟩ := hsplit.2.1 h2
        rw [e1, e2]
        simp only [requestsAt, h2, Nat.lt_irrefl, ↓reduceIte, hd]
        cases last <;> first | exact absurd rfl hne | simp [switchIn, discardIn]
  | @command v next rest items ending c hv hm _ ih =>
    intro declarations state
    obtain ⟨hexit, -⟩ := Parser.Script.modeAfter_read hm
    let n := 10 * sizeOf c + 1
    let T := trace (commandFirst n) (Facts.Proofs.Parser.Simulation.items c.tokens ++ items)
      (calls state)
    have hrun := command_run hv items (n := n) (by omega) state
    obtain ⟨_, hok⟩ := commandFirst_ok hv items (n := n) (by omega) state
    have harr := commandFirst_arrivals hv items (n := n) (by omega) hok
    have hq := command_trace_quiet hv items (n := n) (by omega) (calls state)
    have hTproc := trace_proc (commandFirst n) (Facts.Proofs.Parser.Simulation.items c.tokens ++
        items)
      (calls state) (by rw [harr]; exact tokens_length_pos c)
    have hR : ∀ e ∈ requestEvents c, isProcessing e = false ∧ isArrival e = false := by
      intro e he
      unfold requestEvents at he
      split at he
      · simp at he
      · simp at he; rcases he with rfl | rfl <;> simp [isProcessing, isArrival]
    -- the run of the rest, from the state after the command and the producer's events
    have hrest : ∃ U : List Event, eventsBefore 0 U = [] ∧ U.countP isArrival = items.length ∧
        (ending ≠ .finished →
          ∃ handled, U.getLast? = some (.call .nothing (.commandSetInfo handled))) ∧
        (∀ j, ∃ e ∈ eventsBefore (j + 1) U, isProcessing e = true) ∧
        (∀ k < items.length,
          switchOf (eventsBefore (k + 1) U) = (requestsAt rest k).1 ∧
            discardOf (eventsBefore (k + 1) U) = (requestsAt rest k).2) ∧
        ((Traversal.commands recordingPoints recordingHandler recordingProducer
          VersionPolicy.unrestricted declarations (c :: rest)).run.run state).2 =
          (T ++ requestEvents c ++ U).reverse ++ state := by
      rw [Parser.Script.commands_cons _ _ _ hexit (Parser.Script.namesNoVersion_of_read hm),
        recording_bind_run, hrun]
      simp only
      cases hd : c.declaredVersion with
      | none =>
        obtain ⟨U, hUs, hU, hUa, hUl, hUp, hUr⟩ := ih declarations (T.reverse ++ state)
        refine ⟨U, hU, hUa, hUl, hUp, hUr, ?_⟩
        rw [hUs]
        simp [requestEvents, hd, T]
      | some declared =>
        simp only
        rw [recording_bind_run, switch_run]
        simp only
        obtain ⟨U, hUs, hU, hUa, hUl, hUp, hUr⟩ := ih (declarations + 1)
          (.handlerSwitch declared :: .producerSwitch declared :: (T.reverse ++ state))
        refine ⟨U, hU, hUa, hUl, hUp, hUr, ?_⟩
        rw [hUs]
        simp [requestEvents, hd, T]
    obtain ⟨U, hU, hUa, hUl, hUp, hUr, hUs⟩ := hrest
    refine ⟨T ++ requestEvents c ++ U, hUs, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.append_assoc]
      exact eventsBefore_zero_append _ (commandFirst_trace_head _ _ _ _)
        (by rw [harr]; exact tokens_length_pos c)
    · have hreq : (requestEvents c).countP isArrival = 0 := by
        unfold requestEvents; split <;> rfl
      simp only [List.countP_append, T, harr, hreq, hUa, List.length_append, List.length_map]
      omega
    · intro hne
      obtain ⟨handled, hl⟩ := hUl hne
      exact ⟨handled, by rw [List.getLast?_append, hl]; rfl⟩
    · rw [List.append_assoc]
      exact proc_append _ hTproc
    · intro k hk
      have hsplit := requests_split hq harr hR hU k
      rw [List.length_append, List.length_map] at hk
      by_cases h1 : k + 1 < c.tokens.length
      · obtain ⟨e1, e2⟩ := hsplit.1 h1
        rw [e1, e2]; simp [requestsAt, h1]
      · by_cases h2 : k + 1 = c.tokens.length
        · obtain ⟨e1, e2⟩ := hsplit.2.1 h2
          rw [e1, e2]
          simp only [requestsAt, h2, Nat.lt_irrefl, ↓reduceIte]
          unfold requestEvents
          cases c.declaredVersion <;> cases c <;>
            first | exact absurd rfl hexit | simp [switchIn, discardIn]
        · rw [hsplit.2.2 (by omega)]
          have hk' : k + 1 - c.tokens.length = (k - c.tokens.length) + 1 := by omega
          rw [hk', switchOf_eq_switchIn, discardOf_eq_discardIn,
            afterLastProcess_append_proc (hUp _), ← switchOf_eq_switchIn,
            ← discardOf_eq_discardIn]
          simp only [requestsAt, h1, h2, ite_false]
          exact hUr _ (by omega)

/-- The traversal of commands that a parser takes, recorded: what `requests_takes_trace` states,
for the events of `record`, which begin with the handler's switch to the version read from. -/
theorem record_takes {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes version commands taken ending) :
    (record version commands).countP isArrival = taken.length ∧
      (ending ≠ .finished →
        ∃ handled, (record version commands).getLast? =
          some (.call .nothing (.commandSetInfo handled))) ∧
      ∀ k < taken.length,
        switchOf (eventsBefore (k + 1) (record version commands)) = (requestsAt commands k).1 ∧
          discardOf (eventsBefore (k + 1) (record version commands)) =
            (requestsAt commands k).2 := by
  obtain ⟨events, hs, -, ha, hl, -, hr⟩ :=
    requests_takes_trace htakes 0 [.handlerSwitch version]
  have hrec : record version commands = .handlerSwitch version :: events := by
    simp only [record, Id.run, Traversal.script]
    rw [recording_bind_run, setVersion_run]
    erw [hs]
    simp
  rw [hrec]
  refine ⟨by simpa [List.countP_cons, isArrival] using ha, fun hne => ?_, fun k hk => ?_⟩
  · obtain ⟨handled, hlast⟩ := hl hne
    refine ⟨handled, ?_⟩
    rw [List.getLast?_cons, hlast]
    rfl
  · have hcons : eventsBefore (k + 1) (.handlerSwitch version :: events) =
        .handlerSwitch version :: eventsBefore (k + 1) events := rfl
    rw [hcons, (switchOf_handlerSwitch _ _).1, (switchOf_handlerSwitch _ _).2]
    exact hr k hk

/-- At every item of what a parser takes for commands, the traversal of the commands asks the
producer for what `requestsAt` says, after the item's processing and before the next item's
arrival. -/
theorem requests_takes_record {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes version commands taken ending)
    (k : Nat) (hk : k < taken.length) :
    switchOf (eventsBefore (k + 1) (record version commands)) = (requestsAt commands k).1 ∧
      discardOf (eventsBefore (k + 1) (record version commands)) = (requestsAt commands k).2 :=
  (record_takes htakes).2.2 k hk

/-- The consumer's requests on tokens that stand for a start of what a parser takes: those of
`requestsAt` at the last token. -/
theorem requests_takes_prefix {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes version commands taken ending)
    {handed : List Lexer.Handed}
    (hst : handed.map (rcv ∘ itemOf) = taken.take handed.length)
    (hpos : 0 < handed.length) (hlen : handed.length ≤ taken.length) :
    (scriptConsumer version).switchTo handed = (requestsAt commands (handed.length - 1)).1 ∧
      (scriptConsumer version).discards handed = (requestsAt commands (handed.length - 1)).2 := by
  simp only [scriptConsumer, parse_takes htakes hst hlen]
  have := requests_takes_record htakes (handed.length - 1) (by omega)
  rw [show handed.length - 1 + 1 = handed.length by omega] at this
  exact this

end BSmtLib.Facts.Proofs.Reader.Requests
