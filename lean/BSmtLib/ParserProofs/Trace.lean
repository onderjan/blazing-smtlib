import BSmtLib.SpecChecks.Parser.Calls
import BSmtLib.ParserProofs.Cut

/-!
# Where the traversal of a script asks its producer

In the recording run of a script (`Spec.Parser.record`), the producer's events, a switch of the
version and the discarding, come right after a command: the switch after a version declaration,
the discarding after `exit`. Nothing a command does itself is the producer's: the traversal of a
command is not given the producer. That is shown without going through the commands one by one:
the reader of a command (`SpecChecks.Parser.commandFirst`) makes the traversal's calls with every
producer (`SpecChecks.Parser.run_command`), so its runs with the recording producer and with a
producer that writes nothing down are the same, and so its trace has no producer's event.

`requests_at` states what the producer is asked for after each item of what a parser receives
for a script, as the events after the item's processing and before the next item's arrival.
-/

namespace BSmtLib.ParserProofs

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal
open BSmtLib.SpecChecks.Parser

/-! ## The producer's events -/

/-- Whether the event is the producer's. -/
def isProducer : Event → Bool
  | .producerSwitch _ | .producerDiscard => true
  | _ => false

/-- The producer of a recording run that writes nothing down and never refuses. -/
def silentProducer : Producer Recording where
  setVersion _ := pure ()
  discardRest := pure ()

theorem silent_discard_run (state : List Event) :
    (ExceptT.lift silentProducer.discardRest : Run Recording Empty Unit).run.run state =
      (.ok (), state) := rfl

theorem silent_switch_run (declarations : Nat) (version : Lexicon.Version) (state : List Event) :
    (switchVersion recordingHandler silentProducer VersionPolicy.unrestricted declarations
        version).run.run state =
      (.ok (), .handlerSwitch version :: state) := by
  simp only [switchVersion, unrestricted_check]
  rfl

/-- A program run with the silent producer writes down its trace without the producer's
events. -/
theorem runSilent_state {α : Type} (p : Program Recorded α) :
    ∀ (items : List Received) (state : List Event),
      ((Program.run recordingPoints recordingHandler silentProducer VersionPolicy.unrestricted p
          items).run.run state).2 =
        ((trace p items (calls state)).filter fun e => !isProducer e).reverse ++ state := by
  induction p with
  | done => intro items state; rfl
  | receive atArrival next ih =>
    intro items state
    cases items with
    | nil => cases atArrival <;> rfl
    | cons item items =>
      rw [Program.run, bind_run (receive_run item atArrival state), ih]
      cases atArrival <;> simp [trace, calls, Event.isCall, List.countP_cons, isProducer]
  | call request next ih =>
    intro items state
    rw [Program.run, bind_run (call_run request state), ih]
    simp [trace, calls, Event.isCall, List.countP_cons, isProducer]
  | setVersion version next ih =>
    intro items state
    rw [Program.run, bind_run (setVersion_run version state), ih]
    simp [trace, calls, Event.isCall, List.countP_cons, isProducer]
  | discard next ih =>
    intro items state
    rw [Program.run, bind_run (silent_discard_run state), ih]
    simp [trace, calls, isProducer]
  | switch declarations version next ih =>
    intro items state
    rw [Program.run, bind_run (silent_switch_run declarations version state), ih]
    simp [trace, calls, Event.isCall, List.countP_cons, isProducer]
  | stuck => intro items state; rfl

/-- A state with the given number of calls. -/
def callsState (count : Nat) : List Event := List.replicate count (.call .nothing .commandCheckSat)

theorem calls_callsState (count : Nat) : calls (callsState count) = count := by
  simp [callsState, calls, List.countP_replicate, Event.isCall]

/-- The reader of a valid command writes down no producer's event. -/
theorem command_trace_quiet {version : Lexicon.Version} {command : Tree.Command}
    (hv : command.Valid version) (rest : List Received) {n : Nat}
    (hn : 10 * sizeOf command < n) (count : Nat) :
    ∀ e ∈ trace (commandFirst n) (items command.tokens ++ rest) count, isProducer e = false
    := by
  have h₁ := run_command (points := recordingPoints) (handler := recordingHandler)
    (producer := recordingProducer) (policy := VersionPolicy.unrestricted) version command
    rest hv hn
  have h₂ := run_command (points := recordingPoints) (handler := recordingHandler)
    (producer := silentProducer) (policy := VersionPolicy.unrestricted) version command
    rest hv hn
  rw [← h₂] at h₁
  have hs₁ := runRecording_state (commandFirst n) (items command.tokens ++ rest)
    (callsState count)
  have hs₂ := runSilent_state (commandFirst n) (items command.tokens ++ rest)
    (callsState count)
  simp only [runRecording] at hs₁
  rw [h₁, hs₂, calls_callsState] at hs₁
  have heq := List.append_cancel_right hs₁
  rw [List.reverse_inj] at heq
  intro e he
  have := List.mem_filter.mp (heq ▸ he)
  simpa using this.2

theorem recording_bind_ok_inv {α β : Type} {x : Run Recording Empty α}
    {f : α → Run Recording Empty β} {s s'' : List Event} {r : β}
    (h : (x >>= f).run.run s = (.ok r, s'')) :
    ∃ a s', x.run.run s = (.ok a, s') ∧ (f a).run.run s' = (.ok r, s'') := by
  rw [recording_bind_run] at h
  revert h
  rcases x.run.run s with ⟨e, s'⟩
  cases e with
  | error e => intro h; cases h
  | ok a => intro h; exact ⟨a, s', rfl, h⟩

/-- The reader of a valid command, where its recording run succeeds, ends as the command does,
with what follows the command left. -/
theorem commandFirst_result {version : Lexicon.Version} {command : Tree.Command}
    (hv : command.Valid version) (rest : List Received) {n : Nat}
    (hn : 10 * sizeOf command < n) {state state' : List Event} {r : After × List Received}
    (h : (runRecording (commandFirst n) (items command.tokens ++ rest)).run.run state =
      (.ok r, state')) :
    r = (afterOf command, rest) := by
  have h₁ := run_command (points := recordingPoints) (handler := recordingHandler)
    (producer := recordingProducer) (policy := VersionPolicy.unrestricted) version command
    rest hv hn
  simp only [runRecording] at h
  rw [h₁] at h
  obtain ⟨a, s', -, hp⟩ := recording_bind_ok_inv h
  cases hp
  rfl

/-! ## Traces of programs that go on -/

/-- The trace of a program and then the program its result chooses, where the first one's
recording run succeeds: the first's trace, then the second's on what the first left. -/
theorem trace_bind {α β : Type} (p : Program Recorded α) (f : α → Program Recorded β) :
    ∀ (items : List Received) (state : List Event) (a : α) (rest : List Received)
      (state' : List Event),
      (runRecording p items).run.run state = (.ok (a, rest), state') →
      trace (p >>= f) items (calls state) =
        trace p items (calls state) ++ trace (f a) rest (calls state') := by
  simp only [runRecording]
  induction p with
  | done result =>
    intro items state a rest state' h
    simp only [Program.run_done] at h
    cases h
    rfl
  | receive atArrival next ih =>
    intro items state a rest state' h
    cases items with
    | nil => cases atArrival <;> cases h
    | cons item items =>
      rw [Program.run, bind_run (receive_run item atArrival state)] at h
      have := ih item items _ a rest state' h
      cases atArrival
      · simp only [trace]
        simp only [calls, List.countP_cons, Event.isCall, Bool.false_eq_true, ite_false,
          Nat.add_zero, List.cons_append, List.nil_append] at this
        exact congrArg _ (congrArg _ this)
      · simp only [trace, List.cons_append]
        simp only [calls, List.countP_cons, Event.isCall, ite_true, Bool.false_eq_true,
          ite_false, Nat.add_zero, List.cons_append, List.nil_append] at this
        exact congrArg _ (congrArg _ (congrArg _ this))
  | call request next ih =>
    intro items state a rest state' h
    rw [Program.run, bind_run (call_run request state)] at h
    have := ih _ items _ a rest state' h
    simp only [trace, List.cons_append]
    simp only [calls, List.countP_cons, Event.isCall, ite_true] at this
    exact congrArg _ this
  | setVersion version next ih =>
    intro items state a rest state' h
    rw [Program.run, bind_run (setVersion_run version state)] at h
    have := ih items _ a rest state' h
    simp only [trace, List.cons_append]
    simp only [calls, List.countP_cons, Event.isCall, ite_true] at this
    exact congrArg _ this
  | discard next ih =>
    intro items state a rest state' h
    rw [Program.run, bind_run (discard_run state)] at h
    have := ih items _ a rest state' h
    simp only [trace, List.cons_append]
    simp only [calls, List.countP_cons, Event.isCall, Bool.false_eq_true, ite_false,
      Nat.add_zero] at this
    exact congrArg _ this
  | switch declarations version next ih =>
    intro items state a rest state' h
    rw [Program.run, bind_run (switch_run declarations version state)] at h
    have := ih items _ a rest state' h
    simp only [trace, List.cons_append]
    simp only [calls, List.countP_cons, Event.isCall, ite_true, Bool.false_eq_true,
      ite_false, Nat.add_zero] at this
    exact congrArg _ (congrArg _ this)
  | stuck =>
    intro items state a rest state' h
    cases h

/-! ## The trace of a script, command by command -/

/-- How the reader of a script goes on after a command, given the reader of the commands after
it and the number of version declarations before it. -/
def afterCommand (rec : Nat → Program Recorded Unit) (declarations : Nat) :
    After → Program Recorded Unit
  | .exit => .discard endAfterExit
  | .continue none => rec declarations
  | .continue (some version) => .switch declarations version (rec (declarations + 1))

theorem commandsStep_eq (rec : Nat → Program Recorded Unit) (n : Nat)
    (declarations : Nat) (command : Tree.Command) (rest : List Received) :
    ∃ f g, commandsStep rec n declarations = .receive none f ∧
      (commandFirst n >>= afterCommand rec declarations) = .receive none g ∧
      f (.token .parenOpen) = g (.token .parenOpen) ∧
      items command.tokens ++ rest = .token .parenOpen :: (items command.tokens ++ rest).tail := by
  obtain ⟨inner, hc⟩ := command_tokens_open command
  refine ⟨_, _, rfl, rfl, ?_, by rw [hc]; rfl⟩
  show (commandAfterOpen n).bind _ = ((commandAfterOpen n).bind _)
  congr 1

theorem trace_receive_eq {α : Type} {atArrival : Option (Call Recorded .nothing)}
    {f g : Received → Program Recorded α}
    {item : Received} (h : f item = g item) (items : List Received) (count : Nat) :
    trace (.receive atArrival f) (item :: items) count =
      trace (.receive atArrival g) (item :: items) count := by
  cases atArrival <;> simp [trace, h]

theorem run_receive_eq {α : Type} {atArrival : Option (Call Recorded .nothing)}
    {f g : Received → Program Recorded α}
    {item : Received} (h : f item = g item) (items : List Received) :
    runRecording (.receive atArrival f) (item :: items) =
      runRecording (.receive atArrival g) (item :: items) := by
  simp only [runRecording, Program.run, h]

/-- The producer's events, and the handler's switch, right after a command of a script. -/
def requestEvents (command : Tree.Command) : List Event :=
  match command.declaredVersion with
  | none => []
  | some version => [.producerSwitch version, .handlerSwitch version]

/-- The number of version declarations after a command. -/
def declarationsAfter (command : Tree.Command) (declarations : Nat) : Nat :=
  match command.declaredVersion with
  | none => declarations
  | some _ => declarations + 1

/-- The trace of a script's commands, at a command after which the script goes on: the command's
reader, the producer's events after it, then the rest; with the run of the rest succeeding where
the whole run does. -/
theorem trace_commandsFrom_cons {version next : Lexicon.Version} {command : Tree.Command}
    {commands : List Tree.Command} (hv : command.Valid version)
    (hm : command.modeAfter version = some (.read next)) (declarations : Nat)
    {n : Nat} (hn : 10 * sizeOf command < n) (state : List Event) {r : Unit × List Received}
    {final : List Event}
    (hrun : (runRecording (commandsFrom (n + 1) declarations) (received (command :: commands))
      ).run.run state = (.ok r, final)) :
    trace (commandsFrom (n + 1) declarations) (received (command :: commands)) (calls state)
        = trace (commandFirst n) (items command.tokens ++ received commands) (calls state) ++
          requestEvents command ++
          trace (commandsFrom n (declarationsAfter command declarations)) (received commands)
            (calls ((requestEvents command).reverse ++ (trace (commandFirst n)
              (items command.tokens ++ received commands) (calls state)).reverse ++ state)) ∧
      (runRecording (commandsFrom n (declarationsAfter command declarations))
        (received commands)).run.run ((requestEvents command).reverse ++ (trace
          (commandFirst n) (items command.tokens ++ received commands)
          (calls state)).reverse ++ state) = (.ok r, final) := by
  have hne : command ≠ .exit := (ParserProofs.modeAfter_read hm).1
  obtain ⟨f, g, hf, hg, hfg, hitems⟩ := commandsStep_eq (commandsFrom n) n declarations
    command (received commands)
  rw [received_cons hne] at hrun ⊢
  simp only [commandsFrom] at hrun ⊢
  rw [hf, hitems, run_receive_eq hfg, ← hg, ← hitems] at hrun
  rw [hf, hitems, trace_receive_eq hfg, ← hg, ← hitems]
  simp only [runRecording] at hrun
  rw [Program.run_bind] at hrun
  obtain ⟨⟨a, rest⟩, s₁, h₁, h₂⟩ := recording_bind_ok_inv hrun
  have hres := commandFirst_result hv (received commands) hn
    (by simpa [runRecording] using h₁)
  cases hres
  have hs₁ := runRecording_state (commandFirst n) (items command.tokens ++ received commands)
    state
  simp only [runRecording] at hs₁
  rw [h₁] at hs₁
  simp only at hs₁
  subst hs₁
  rw [trace_bind _ _ _ state _ _ _ (by simpa [runRecording] using h₁)]
  have ha : afterOf command = .continue command.declaredVersion := by
    cases command <;> first | exact absurd rfl hne | rfl
  rw [ha] at h₂
  simp only [ha]
  cases hd : command.declaredVersion with
  | none =>
    simp only [hd, afterCommand, requestEvents, declarationsAfter, List.append_nil,
      List.reverse_nil, List.nil_append] at h₂ ⊢
    exact ⟨trivial, h₂⟩
  | some v =>
    simp only [hd, afterCommand, requestEvents, declarationsAfter] at h₂ ⊢
    simp only [Program.run] at h₂
    rw [bind_run (switch_run declarations v _)] at h₂
    refine ⟨?_, by simpa [runRecording] using h₂⟩
    simp [trace, calls, Event.isCall, List.countP_cons]

/-- The trace of a script that is `exit`: its reader, the discarding, then the end of the
input. -/
theorem trace_commandsFrom_exit {version : Lexicon.Version} (hv : Tree.Command.exit.Valid version)
    (declarations : Nat) {n : Nat} (hn : 10 * sizeOf Tree.Command.exit < n)
    (state : List Event) {r : Unit × List Received} {final : List Event}
    (hrun : (runRecording (commandsFrom (n + 1) declarations) (received [.exit])
      ).run.run state = (.ok r, final)) :
    trace (commandsFrom (n + 1) declarations) (received [.exit]) (calls state) =
      trace (commandFirst n) (items Tree.Command.exit.tokens ++ [.endOfInput])
          (calls state) ++
        [.producerDiscard, .arrive .endOfInput, .process .endOfInput] := by
  obtain ⟨f, g, hf, hg, hfg, hitems⟩ := commandsStep_eq (commandsFrom n) n declarations
    .exit [.endOfInput]
  have hrec : received [.exit] = items Tree.Command.exit.tokens ++ [.endOfInput] := rfl
  rw [hrec] at hrun ⊢
  simp only [commandsFrom] at hrun ⊢
  rw [hf, hitems, run_receive_eq hfg, ← hg, ← hitems] at hrun
  rw [hf, hitems, trace_receive_eq hfg, ← hg, ← hitems]
  simp only [runRecording] at hrun
  rw [Program.run_bind] at hrun
  obtain ⟨⟨a, rest⟩, s₁, h₁, -⟩ := recording_bind_ok_inv hrun
  have hres := commandFirst_result hv [.endOfInput] hn (by simpa [runRecording] using h₁)
  cases hres
  rw [trace_bind _ _ _ state _ _ _ (by simpa [runRecording] using h₁)]
  simp [afterOf, afterCommand, trace, endAfterExit]

/-- The trace of a script with no command: the end of the input. -/
theorem trace_commandsFrom_nil (declarations n : Nat) (count : Nat) :
    trace (commandsFrom (n + 1) declarations) (received []) count =
      [.arrive .endOfInput, .process .endOfInput] := rfl

/-! ## The events after an item's processing -/

theorem takeWhile_append_of_not {α : Type} {p : α → Bool} {l₁ : List α} (l₂ : List α)
    (h : ∃ x ∈ l₁, p x = false) : (l₁ ++ l₂).takeWhile p = l₁.takeWhile p := by
  induction l₁ with
  | nil => simp at h
  | cons a l₁ ih =>
    by_cases ha : p a = true
    · have h' : ∃ x ∈ l₁, p x = false := by
        obtain ⟨x, hx, hpx⟩ := h
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [ha] at hpx; cases hpx
        · exact ⟨x, hx, hpx⟩
      simp [ha, ih h']
    · simp [ha]

theorem takeWhile_append_of_all {α : Type} {p : α → Bool} {l₁ : List α} (l₂ : List α)
    (h : ∀ x ∈ l₁, p x = true) : (l₁ ++ l₂).takeWhile p = l₁ ++ l₂.takeWhile p := by
  induction l₁ with
  | nil => rfl
  | cons a l₁ ih =>
    simp [h a (by simp), ih fun x hx => h x (by simp [hx])]

theorem afterLastProcess_append_proc {X Y : List Event} (h : ∃ e ∈ Y, isProcessing e = true) :
    afterLastProcess (X ++ Y) = afterLastProcess Y := by
  unfold afterLastProcess
  rw [List.reverse_append, takeWhile_append_of_not]
  obtain ⟨e, he, hp⟩ := h
  exact ⟨e, List.mem_reverse.mpr he, by simp [hp]⟩

theorem afterLastProcess_append_noproc {X Y : List Event} (h : ∀ e ∈ Y, isProcessing e = false) :
    afterLastProcess (X ++ Y) = afterLastProcess X ++ Y := by
  unfold afterLastProcess
  rw [List.reverse_append, takeWhile_append_of_all _ (fun e he => by
    simp [h e (List.mem_reverse.mp he)])]
  simp

theorem afterLastProcess_suffix (X : List Event) : afterLastProcess X <:+ X := by
  unfold afterLastProcess
  have := List.takeWhile_prefix (fun e => !isProcessing e) (l := X.reverse)
  obtain ⟨t, ht⟩ := this
  refine ⟨t.reverse, ?_⟩
  have := congrArg List.reverse ht
  simpa using this

theorem switchOf_none_of {X : List Event} (h : ∀ e ∈ afterLastProcess X, isProducer e = false) :
    switchOf X = none := by
  unfold switchOf
  rw [List.findSome?_eq_none_iff]
  intro e he
  have := h e he
  cases e <;> simp_all [isProducer]

theorem discardOf_false_of {X : List Event} (h : ∀ e ∈ afterLastProcess X, isProducer e = false) :
    discardOf X = false := by
  unfold discardOf
  rw [List.any_eq_false]
  intro e he
  have := h e he
  cases e <;> simp_all [isProducer]

/-- Before the arrival of any item after the first, a trace with an arrival has processed an
item: a receipt writes down the arrival and then the processing. -/
theorem eventsBefore_trace_proc {α : Type} (p : Program Recorded α) :
    ∀ (items : List Received) (count k : Nat),
      0 < (trace p items count).countP isArrival →
      ∃ e ∈ eventsBefore (k + 1) (trace p items count), isProcessing e = true := by
  induction p with
  | done => intro items count k h; simp [trace] at h
  | receive atArrival next ih =>
    intro items count k h
    cases items with
    | nil => cases atArrival <;> simp [trace] at h
    | cons item items =>
      cases atArrival
      · cases k <;> simp [trace, eventsBefore, isProcessing]
      · cases k <;> simp [trace, eventsBefore, isProcessing]
  | call request next ih =>
    intro items count k h
    simp only [trace, List.countP_cons, isArrival, Bool.false_eq_true, ite_false,
      Nat.add_zero] at h
    obtain ⟨e, he, hp⟩ := ih _ items _ k h
    exact ⟨e, by simp [trace, eventsBefore, he], hp⟩
  | setVersion version next ih =>
    intro items count k h
    simp only [trace, List.countP_cons, isArrival, Bool.false_eq_true, ite_false,
      Nat.add_zero] at h
    obtain ⟨e, he, hp⟩ := ih items _ k h
    exact ⟨e, by simp [trace, eventsBefore, he], hp⟩
  | discard next ih =>
    intro items count k h
    simp only [trace, List.countP_cons, isArrival, Bool.false_eq_true, ite_false,
      Nat.add_zero] at h
    obtain ⟨e, he, hp⟩ := ih items _ k h
    exact ⟨e, by simp [trace, eventsBefore, he], hp⟩
  | switch declarations version next ih =>
    intro items count k h
    simp only [trace, List.countP_cons, isArrival, Bool.false_eq_true, ite_false,
      Nat.add_zero] at h
    obtain ⟨e, he, hp⟩ := ih items _ k h
    exact ⟨e, by simp [trace, eventsBefore, he], hp⟩
  | stuck => intro items count k h; simp [trace] at h

theorem eventsBefore_append_left {X : List Event} (Y : List Event) {k : Nat}
    (h : k < X.countP isArrival) : eventsBefore k (X ++ Y) = eventsBefore k X := by
  induction X generalizing k with
  | nil => simp at h
  | cons e X ih =>
    cases e with
    | arrive item =>
      cases k with
      | zero => rfl
      | succ k =>
        simp only [List.countP_cons, isArrival, ite_true] at h
        simp [eventsBefore, ih (k := k) (by omega)]
    | _ =>
      simp only [List.countP_cons, isArrival, Bool.false_eq_true, ite_false, Nat.add_zero] at h
      cases k <;> simp [eventsBefore, ih h]

theorem eventsBefore_sublist (k : Nat) (X : List Event) : (eventsBefore k X).Sublist X := by
  induction X generalizing k with
  | nil => cases k <;> simp [eventsBefore]
  | cons e X ih =>
    cases e with
    | arrive item =>
      cases k with
      | zero => simp [eventsBefore]
      | succ k => simpa [eventsBefore] using (ih k).cons_cons (.arrive item)
    | _ => cases k <;> simp [eventsBefore, (ih _).cons_cons]

/-! ## What the producer is asked for after each item -/

/-- What the producer is asked for after the item at the position, among what a parser receives
for the commands: after the `)` of a version declaration, a switch to its version; after the `)`
of `exit`, discarding; after any other item, nothing. -/
def requestsAt : List Tree.Command → Nat → Option Lexicon.Version × Bool
  | [], _ => (none, false)
  | command :: commands, k =>
    if k + 1 < command.tokens.length then (none, false)
    else if k + 1 = command.tokens.length then
      (command.declaredVersion, match command with | .exit => true | _ => false)
    else requestsAt commands (k - command.tokens.length)

theorem countP_arrival (l : List Event) :
    l.countP isArrival = (l.filterMap Event.arrived).length := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    cases e <;> simp only [List.countP_cons, isArrival, Event.arrived, List.filterMap_cons, ih,
      ite_true, Bool.false_eq_true, ite_false, Nat.add_zero, List.length_cons]

/-- The producer's switch and discarding among events. -/
def switchIn (events : List Event) : Option Lexicon.Version :=
  events.findSome? fun
    | .producerSwitch version => some version
    | _ => none

def discardIn (events : List Event) : Bool :=
  events.any fun
    | .producerDiscard => true
    | _ => false

theorem switchOf_eq_switchIn (X : List Event) : switchOf X = switchIn (afterLastProcess X) := rfl

theorem discardOf_eq_discardIn (X : List Event) : discardOf X = discardIn (afterLastProcess X) :=
  rfl

theorem switchIn_append_quiet {X Y : List Event} (h : ∀ e ∈ X, isProducer e = false) :
    switchIn (X ++ Y) = switchIn Y := by
  unfold switchIn
  rw [List.findSome?_append, (List.findSome?_eq_none_iff).mpr fun e he => by
    have := h e he; cases e <;> simp_all [isProducer]]
  rfl

theorem discardIn_append_quiet {X Y : List Event} (h : ∀ e ∈ X, isProducer e = false) :
    discardIn (X ++ Y) = discardIn Y := by
  unfold discardIn
  rw [List.any_append, (List.any_eq_false).mpr fun e he => by
    have := h e he; cases e <;> simp_all [isProducer]]
  simp

/-- At an item of a part of a trace whose events are no producer's, followed by events that are
neither arrivals nor processings and then by more: before the part's last item, nothing is
asked; at its last item, what the events after it ask; after it, as in the more. -/
theorem requests_split {T R U : List Event} {m : Nat} (hT : ∀ e ∈ T, isProducer e = false)
    (hm : T.countP isArrival = m)
    (hR : ∀ e ∈ R, isProcessing e = false ∧ isArrival e = false) (hU : eventsBefore 0 U = [])
    (k : Nat) :
    (k + 1 < m → switchOf (eventsBefore (k + 1) (T ++ R ++ U)) = none ∧
      discardOf (eventsBefore (k + 1) (T ++ R ++ U)) = false) ∧
    (k + 1 = m → switchOf (eventsBefore (k + 1) (T ++ R ++ U)) = switchIn R ∧
      discardOf (eventsBefore (k + 1) (T ++ R ++ U)) = discardIn R) ∧
    (m ≤ k → eventsBefore (k + 1) (T ++ R ++ U) = T ++ R ++ eventsBefore (k + 1 - m) U) := by
  have hRarr : R.countP isArrival = 0 := by
    rw [List.countP_eq_zero]
    intro e he
    simp [(hR e he).2]
  have hsplit : ∀ j, eventsBefore (m + j) (T ++ R ++ U) = T ++ R ++ eventsBefore j U := by
    intro j
    have := eventsBefore_append (T ++ R) U j
    rw [List.countP_append, hRarr, hm, Nat.add_zero] at this
    rw [List.append_assoc] at this ⊢
    exact this
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_⟩
  · rw [List.append_assoc, eventsBefore_append_left _ (by omega)]
    have hq : ∀ e ∈ afterLastProcess (eventsBefore (k + 1) T), isProducer e = false :=
      fun e he => hT e ((eventsBefore_sublist _ T).subset
        ((afterLastProcess_suffix _).subset he))
    exact ⟨switchOf_none_of hq, discardOf_false_of hq⟩
  · rw [hk, ← Nat.add_zero m, hsplit, hU, List.append_nil, switchOf_eq_switchIn,
      discardOf_eq_discardIn, afterLastProcess_append_noproc (fun e he => (hR e he).1)]
    have hq : ∀ e ∈ afterLastProcess T, isProducer e = false :=
      fun e he => hT e ((afterLastProcess_suffix _).subset he)
    exact ⟨switchIn_append_quiet hq, discardIn_append_quiet hq⟩
  · rw [show k + 1 = m + (k + 1 - m) by omega, hsplit]
    congr 2
    omega

/-- The reader of a valid command, where its recording run succeeds, receives the command's
tokens. -/
theorem commandFirst_arrivals {version : Lexicon.Version} {command : Tree.Command}
    (hv : command.Valid version) (rest : List Received) {n : Nat}
    (hn : 10 * sizeOf command < n) {state state' : List Event} {r : After × List Received}
    (h : (runRecording (commandFirst n) (items command.tokens ++ rest)).run.run state =
      (.ok r, state')) :
    (trace (commandFirst n) (items command.tokens ++ rest) (calls state)).countP isArrival
      = command.tokens.length := by
  have hr := commandFirst_result hv rest hn h
  subst hr
  have := (trace_items _ _ state _ _ (by rw [h])).1
  rw [countP_arrival]
  have hl := congrArg List.length this
  simp only [List.length_append, List.length_map] at hl
  omega

theorem afterLastProcess_append_trace {α : Type} (X : List Event) (p : Program Recorded α)
    (items : List Received) (count k : Nat) (h : 0 < (trace p items count).countP isArrival) :
    afterLastProcess (X ++ eventsBefore (k + 1) (trace p items count)) =
      afterLastProcess (eventsBefore (k + 1) (trace p items count)) :=
  afterLastProcess_append_proc (eventsBefore_trace_proc p items count k h)

/-- At every item of what a parser receives for a script, the reader of the script asks the
producer for what `requestsAt` says, after the item's processing and before the next item's
arrival. -/
theorem requests_trace : ∀ (commands : List Tree.Command) (version : Lexicon.Version)
    (declarations : Nat) {n : Nat} (state : List Event)
    {r : Unit × List Received} {final : List Event}, Script version commands →
    10 * sizeOf commands < n →
    (runRecording (commandsFrom n declarations) (received commands)).run.run state =
      (.ok r, final) →
    ∀ k < (received commands).length,
      switchOf (eventsBefore (k + 1) (trace (commandsFrom n declarations)
          (received commands) (calls state))) = (requestsAt commands k).1 ∧
        discardOf (eventsBefore (k + 1) (trace (commandsFrom n declarations)
          (received commands) (calls state))) = (requestsAt commands k).2
  | [], _, declarations, n + 1, state, _, _, _, _, _ => by
    intro k hk
    simp only [received, List.length_singleton] at hk
    obtain rfl : k = 0 := by omega
    rw [trace_commandsFrom_nil]
    simp [eventsBefore, switchOf, discardOf, afterLastProcess, isProcessing, requestsAt]
  | command :: commands, version, declarations, n + 1, state, r, final, hs, hn, hrun => by
    intro k hk
    simp only [List.cons.sizeOf_spec] at hn
    cases hs with
    | stop hv hm =>
      obtain rfl := ParserProofs.modeAfter_unparsed hm
      rw [trace_commandsFrom_exit hv declarations (n := n) (by omega) state hrun]
      -- the reader of `exit` succeeds
      obtain ⟨f, g, hf, hg, hfg, hitems⟩ := commandsStep_eq (commandsFrom n) n declarations
        .exit [.endOfInput]
      have hrun' := hrun
      have hrec : received [.exit] = items Tree.Command.exit.tokens ++ [.endOfInput] := rfl
      rw [hrec] at hrun'
      simp only [commandsFrom] at hrun'
      rw [hf, hitems, run_receive_eq hfg, ← hg, ← hitems] at hrun'
      simp only [runRecording] at hrun'
      rw [Program.run_bind] at hrun'
      obtain ⟨_, s₁, h₁, -⟩ := recording_bind_ok_inv hrun'
      have harr := commandFirst_arrivals hv [.endOfInput] (n := n) (by omega)
        (by simpa [runRecording] using h₁)
      have hq := command_trace_quiet hv [.endOfInput] (n := n) (by omega) (calls state)
      have hsplit := requests_split (R := [.producerDiscard])
        (U := [.arrive .endOfInput, .process .endOfInput]) hq harr
        (by intro e he; simp at he; subst he; simp [isProcessing, isArrival])
        rfl k
      have hlen : (received [Tree.Command.exit]).length = Tree.Command.exit.tokens.length + 1 :=
        by simp [received]
      rw [hlen] at hk
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hsplit
      by_cases h1 : k + 1 < Tree.Command.exit.tokens.length
      · obtain ⟨e1, e2⟩ := hsplit.1 h1
        rw [e1, e2]; simp [requestsAt, h1]
      · by_cases h2 : k + 1 = Tree.Command.exit.tokens.length
        · obtain ⟨e1, e2⟩ := hsplit.2.1 h2
          rw [e1, e2]; simp [requestsAt, h2, switchIn, discardIn, Tree.Command.declaredVersion]
        · have h3 : k = Tree.Command.exit.tokens.length := by omega
          rw [hsplit.2.2 (by omega), h3]
          simp [requestsAt, eventsBefore, switchOf, discardOf, afterLastProcess, isProcessing]
    | command hv hm hrest =>
      rename_i next
      have hne : command ≠ .exit := (ParserProofs.modeAfter_read hm).1
      obtain ⟨htrace, hrun₂⟩ := trace_commandsFrom_cons hv hm declarations (n := n)
        (by omega) state hrun
      rw [htrace]
      -- the reader of the command succeeds
      obtain ⟨f, g, hf, hg, hfg, hitems⟩ := commandsStep_eq (commandsFrom n) n declarations
        command (received commands)
      have hrun' := hrun
      rw [received_cons hne] at hrun'
      simp only [commandsFrom] at hrun'
      rw [hf, hitems, run_receive_eq hfg, ← hg, ← hitems] at hrun'
      simp only [runRecording] at hrun'
      rw [Program.run_bind] at hrun'
      obtain ⟨_, s₁, h₁, -⟩ := recording_bind_ok_inv hrun'
      have harr := commandFirst_arrivals hv (received commands) (n := n) (by omega)
        (by simpa [runRecording] using h₁)
      have hq := command_trace_quiet hv (received commands) (n := n) (by omega) (calls state)
      have hU : ∀ (st : List Event),
          eventsBefore 0 (trace (commandsFrom n (declarationsAfter command declarations))
            (received commands) (calls st)) = [] := by
        intro st
        cases n with
        | zero => omega
        | succ n' =>
          cases commands with
          | nil => simp [trace_commandsFrom_nil, eventsBefore]
          | cons c cs =>
            obtain ⟨f', g', hf', -, -, -⟩ := commandsStep_eq (commandsFrom n') n'
              (declarationsAfter command declarations) c (received cs)
            cases c <;> simp [commandsFrom, hf', received, trace, eventsBefore,
              Tree.Command.tokens, commandTokens, paren]
      have hR : ∀ e ∈ requestEvents command, isProcessing e = false ∧ isArrival e = false := by
        intro e he
        unfold requestEvents at he
        split at he
        · simp at he
        · simp at he; rcases he with rfl | rfl <;> simp [isProcessing, isArrival]
      have hsplit := requests_split hq harr hR (hU ((requestEvents command).reverse ++
        (trace (commandFirst n) (items command.tokens ++ received commands)
          (calls state)).reverse ++ state)) k
      rw [List.append_assoc] at hsplit
      rw [received_cons hne, List.length_append, List.length_map] at hk
      by_cases h1 : k + 1 < command.tokens.length
      · obtain ⟨e1, e2⟩ := hsplit.1 h1
        rw [List.append_assoc, e1, e2]; simp [requestsAt, h1]
      · by_cases h2 : k + 1 = command.tokens.length
        · obtain ⟨e1, e2⟩ := hsplit.2.1 h2
          rw [List.append_assoc, e1, e2]
          simp only [requestsAt, h2, Nat.lt_irrefl, ↓reduceIte]
          unfold requestEvents
          cases command.declaredVersion <;> simp [switchIn, discardIn]
        · rw [List.append_assoc, hsplit.2.2 (by omega)]
          have hk' : k + 1 - command.tokens.length = (k - command.tokens.length) + 1 := by omega
          rw [hk', switchOf_eq_switchIn, discardOf_eq_discardIn,
            afterLastProcess_append_trace _ _ _ _ _ (by
              cases n with
              | zero => omega
              | succ n' =>
                cases commands with
                | nil => simp [trace_commandsFrom_nil, isArrival]
                | cons c cs =>
                  obtain ⟨f', g', hf', -, -, -⟩ := commandsStep_eq (commandsFrom n') n'
                    (declarationsAfter command declarations) c (received cs)
                  cases c <;> simp [commandsFrom, hf', received, trace, isArrival,
                    Tree.Command.tokens, commandTokens, paren, items]),
            ← switchOf_eq_switchIn, ← discardOf_eq_discardIn]
          have ih := requests_trace commands next (declarationsAfter command declarations)
            _ hrest (by omega) hrun₂ (k - command.tokens.length)
            (by omega)
          simp only [requestsAt, h1, h2, ite_false]
          exact ih

/-- The events after the last processing, with an event before them that is no processing: the
same events, or that event and then them. -/
theorem afterLastProcess_cons_quiet {e : Event} (he : isProcessing e = false) (X : List Event) :
    afterLastProcess (e :: X) = afterLastProcess X ∨
      afterLastProcess (e :: X) = e :: afterLastProcess X := by
  by_cases hX : ∃ x ∈ X, isProcessing x = true
  · left
    exact afterLastProcess_append_proc (X := [e]) hX
  · right
    have hall : ∀ x ∈ X, isProcessing x = false := fun x hx => by
      cases h : isProcessing x
      · rfl
      · exact absurd ⟨x, hx, h⟩ hX
    have h₁ := afterLastProcess_append_noproc (X := [e]) hall
    have h₂ := afterLastProcess_append_noproc (X := []) hall
    simp only [List.singleton_append, List.nil_append] at h₁ h₂
    rw [h₁, h₂]
    simp [afterLastProcess, he]
/-- The handler's switch of the version before the events changes nothing the producer is asked
for after the last processing. -/
theorem switchOf_handlerSwitch (version : Lexicon.Version) (X : List Event) :
    switchOf (.handlerSwitch version :: X) = switchOf X ∧
      discardOf (.handlerSwitch version :: X) = discardOf X := by
  rw [switchOf_eq_switchIn, discardOf_eq_discardIn, switchOf_eq_switchIn,
    discardOf_eq_discardIn]
  rcases afterLastProcess_cons_quiet (e := .handlerSwitch version) rfl X with he | he <;>
    rw [he]
  · exact ⟨rfl, rfl⟩
  · exact ⟨switchIn_append_quiet (X := [.handlerSwitch version]) (by simp [isProducer]),
      discardIn_append_quiet (X := [.handlerSwitch version]) (by simp [isProducer])⟩


/-- At every item of what a parser receives for a script, the traversal of the script asks the
producer for what `requestsAt` says, after the item's processing and before the next item's
arrival. -/
theorem requests_record {version : Lexicon.Version} {commands : List Tree.Command}
    (h : Script version commands) (k : Nat) (hk : k < (received commands).length) :
    switchOf (eventsBefore (k + 1) (record version commands)) = (requestsAt commands k).1 ∧
      discardOf (eventsBefore (k + 1) (record version commands)) =
        (requestsAt commands k).2 := by
  have hn : 10 * sizeOf commands < 10 * sizeOf commands + 1 := Nat.lt_succ_self _
  rw [record_eq_trace h hn]
  obtain ⟨-, hok⟩ := parse_rebuilds h hn
  have hrun₀ : (runRecording (parseScript (10 * sizeOf commands + 1) version)
      (received commands)).run.run [] =
      (runRecording (commandsFrom (10 * sizeOf commands + 1) 0) (received commands)).run.run
        [.handlerSwitch version] := by
    simp only [runRecording, parseScript, Program.run]
    exact bind_run (setVersion_run version [])
  rw [hrun₀] at hok
  rcases hrun : (runRecording (commandsFrom (10 * sizeOf commands + 1) 0)
    (received commands)).run.run [.handlerSwitch version] with ⟨res, final⟩
  rw [hrun] at hok
  simp only at hok
  subst hok
  have ht := requests_trace commands version 0 [.handlerSwitch version] h hn hrun k hk
  have hcalls : calls [.handlerSwitch version] = 1 := rfl
  rw [hcalls] at ht
  have htrace : trace (parseScript (10 * sizeOf commands + 1) version) (received commands) 0 =
      .handlerSwitch version :: trace (commandsFrom (10 * sizeOf commands + 1) 0)
        (received commands) 1 := rfl
  rw [htrace]
  have hcons : ∀ X : List Event, eventsBefore (k + 1) (.handlerSwitch version :: X) =
      .handlerSwitch version :: eventsBefore (k + 1) X := fun X => rfl
  rw [hcons, switchOf_eq_switchIn, discardOf_eq_discardIn]
  have hq : ∀ Y : List Event, switchIn (.handlerSwitch version :: Y) = switchIn Y ∧
      discardIn (.handlerSwitch version :: Y) = discardIn Y := fun Y =>
    ⟨switchIn_append_quiet (X := [.handlerSwitch version]) (by simp [isProducer]),
      discardIn_append_quiet (X := [.handlerSwitch version]) (by simp [isProducer])⟩
  rcases afterLastProcess_cons_quiet (e := .handlerSwitch version) rfl
    (eventsBefore (k + 1) _) with he | he <;>
    rw [he] <;> first | exact ht | (rw [(hq _).1, (hq _).2]; exact ht)

end BSmtLib.ParserProofs
