import BSmtLib.SpecChecks.Parser.Placement

/-!
# Every handler's run is placed as the recording's

A cut run (`cutRun`) is the traversal of a script with any handler, points and producer,
stopped when a given item arrives: its points count the items that arrive and stop the run at
the arrival of the item at the given position, so nothing after it happens; a processing-cut run
(`processingCutRun`) stops before the processing of that item instead, after the calls due at its
arrival but without passing the arrival itself on. The cut runs of two
valid scripts are equal when what a parser receives for them agrees before that item
(`cutRun_eq`), and so when their recordings agree before that item (`cutRun_eq_of_record`); and
likewise for processing-cut runs (`processingCutRun_eq`, `processingCutRun_eq_of_record`).

The proof: the traversal is `parseScript` run on the items (`Parser.Simulation`), and a program
run with the counting points does before the cut only what the items before the cut tell it.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Parser

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal

/-- The monad of a cut run: the handler's monad, with the number of items arrived so far and a
stop. -/
abbrev Cut (m : Type → Type) := StateT Nat (ExceptT Unit m)

section

variable {m : Type → Type} [Monad m] {ε : Type} {values : Values}

/-- Points that count the items that arrive, and stop at the arrival of the item at position
`count`, before the points it stands in for see it. -/
def cutPoints (points : Points m) (count : Nat) : Points (Cut m) where
  arrive received := do
    let arrived ← get
    if arrived = count then throw ()
    else
      set (arrived + 1)
      monadLift (points.arrive received)
  process received := monadLift (points.process received)

/-- The handler in the monad of a cut run. -/
def cutHandler (handler : Handler m ε values) : Handler (Cut m) ε values where
  call request := ExceptT.mk (monadLift (handler.call request).run)
  setVersion version := monadLift (handler.setVersion version)

/-- The producer in the monad of a cut run. -/
def cutProducer (producer : Producer m) : Producer (Cut m) where
  setVersion version := ExceptT.mk (monadLift (producer.setVersion version).run)
  discardRest := monadLift producer.discardRest

/--
The traversal of the script with the handler, points, producer and policy, stopped at the
arrival of the item at position `count` of what a parser receives: what it has done before
that item arrives. It ends with the stop, `.error ()`, if the item arrives, and otherwise with
the traversal's result and the number of items that arrived.
-/
def cutRun (points : Points m) (handler : Handler m ε values)
    (producer : Producer m) (policy : VersionPolicy)
    (count : Nat) (version : Version) (commands : List Tree.Command) :
    m (Except Unit (Except (Cause ε) Unit × Nat)) :=
  (((script (cutPoints points count) (cutHandler handler) (cutProducer producer) policy
    version commands).run).run 0).run

end
/-! ## Runs that do not count -/

section

variable {m : Type → Type} [Monad m] [LawfulMonad m] {ε : Type} {values : Values}

/-- A run of the cut monad from a number of arrived items, down to the handler's monad. -/
def R {β : Type} (x : Run (Cut m) ε β) (k : Nat) : m (Except Unit (Except (Cause ε) β × Nat)) :=
  ((x.run).run k).run

omit [LawfulMonad m] in
theorem R_bind {β γ : Type} (x : Run (Cut m) ε β) (f : β → Run (Cut m) ε γ) (k : Nat) :
    R (x >>= f) k = R x k >>= fun r => match r with
      | .error () => pure (.error ())
      | .ok (.error e, k') => pure (.ok (.error e, k'))
      | .ok (.ok a, k') => R (f a) k' := by
  simp only [R, ExceptT.run_bind, StateT.run_bind]
  congr 1
  funext r
  rcases r with ⟨⟩ | ⟨_ | a, k'⟩ <;> simp []

/-- The run does not look at or change the number of arrived items. -/
def NoCount {β : Type} (x : Run (Cut m) ε β) : Prop :=
  ∃ y : m (Except Unit (Except (Cause ε) β)), ∀ k, R x k = (Except.map (·, k)) <$> y

theorem congr_noCount {β γ : Type} {x : Run (Cut m) ε β} (hx : NoCount x)
    {f g : β → Run (Cut m) ε γ} {k : Nat} (h : ∀ a, R (f a) k = R (g a) k) :
    R (x >>= f) k = R (x >>= g) k := by
  obtain ⟨y, hy⟩ := hx
  rw [R_bind, R_bind, hy]
  simp only [bind_map_left]
  congr 1
  funext r
  rcases r with ⟨⟩ | (_ | a) <;> simp [Except.map, h]

theorem noCount_lift {β : Type} (z : m β) :
    NoCount (ExceptT.lift (monadLift z : Cut m β) : Run (Cut m) ε β) :=
  ⟨(fun a => .ok (.ok a)) <$> z, fun k => by simp [R, Except.map]⟩

theorem noCount_pure {β : Type} (a : β) : NoCount (pure a : Run (Cut m) ε β) :=
  ⟨pure (.ok (.ok a)), fun k => by simp [R, Except.map]⟩

theorem noCount_call (handler : Handler m ε values) {returns : Returns}
    (request : Call values returns) :
    NoCount (Traversal.call (cutHandler handler) request) :=
  ⟨(fun e => .ok (e.mapError Cause.handler)) <$> (handler.call request).run, fun k => by
    simp [R, Traversal.call, cutHandler, ExceptT.adapt, Except.map, ExceptT.run_mk, StateT.run_map,
      ExceptT.run_map]
    simp only [ExceptT.mk, StateT.run_monadLift]
    simp [Except.map]
    done⟩

theorem noCount_bind {β γ : Type} {x : Run (Cut m) ε β} {f : β → Run (Cut m) ε γ}
    (hx : NoCount x) (hf : ∀ a, NoCount (f a)) : NoCount (x >>= f) := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨y >>= fun r => match r with
    | .error () => pure (.error ())
    | .ok (.error e) => pure (.ok (.error e))
    | .ok (.ok a) => Classical.choose (hf a), fun k => ?_⟩
  rw [R_bind, hy]
  simp only [bind_map_left, map_bind]
  congr 1
  funext r
  rcases r with ⟨⟩ | (_ | a) <;> simp [Except.map, Classical.choose_spec (hf _) k]

theorem noCount_throw {β : Type} (e : Cause ε) : NoCount (throw e : Run (Cut m) ε β) :=
  ⟨pure (.ok (.error e)), fun k => by simp [R, Except.map]⟩

theorem noCount_adaptSwitch (producer : Producer m)
    (version : Version) :
    NoCount (ExceptT.adapt (fun _ => Cause.syntax .unsupportedVersion)
      ((cutProducer producer).setVersion version) : Run (Cut m) ε Unit) := by
  refine ⟨(fun e => .ok (e.mapError fun _ => Cause.syntax .unsupportedVersion)) <$>
    (producer.setVersion version).run, fun k => ?_⟩
  simp [R, cutProducer, ExceptT.adapt, Except.map]
  simp only [ExceptT.mk, StateT.run_monadLift]
  simp [Except.map]

theorem noCount_switch (handler : Handler m ε values)
    (producer : Producer m) (policy : VersionPolicy)
    (declarations : Nat) (version : Version) :
    NoCount (switchVersion (cutHandler handler) (cutProducer producer) policy declarations
      version) := by
  simp only [switchVersion]
  split
  · exact noCount_bind (noCount_throw _) fun _ =>
      noCount_bind (noCount_adaptSwitch producer version) fun _ => noCount_lift _
  · exact noCount_bind (noCount_adaptSwitch producer version) fun _ => noCount_lift _

theorem noCount_arrival (handler : Handler m ε values)
    (atArrival : Option (Call values .nothing)) :
    NoCount (Program.arrival (cutHandler handler) atArrival) := by
  cases atArrival with
  | none => exact noCount_pure ()
  | some request => exact noCount_call handler request

/-- Taking an item without counting it. -/
def receivePlain (points : Points m) (item : Received) (atArrival : Run (Cut m) ε Unit) :
    Run (Cut m) ε Unit := do
  ExceptT.lift (monadLift (points.arrive item) : Cut m Unit)
  atArrival
  ExceptT.lift (monadLift (points.process item) : Cut m Unit)

theorem noCount_receivePlain (points : Points m) (item : Received)
    {atArrival : Run (Cut m) ε Unit} (ha : NoCount atArrival) :
    NoCount (receivePlain points item atArrival) :=
  noCount_bind (noCount_lift _) fun _ => noCount_bind ha fun _ => noCount_lift _

theorem R_arrive_stop (points : Points m) (count : Nat) (item : Received) :
    R (ExceptT.lift ((cutPoints points count).arrive item) : Run (Cut m) ε Unit) count =
      pure (.error ()) := by
  simp [R, cutPoints]
  simp [throw, throwThe, MonadExceptOf.throw, Except.map, ExceptT.mk]
  exact map_pure _ _

theorem R_arrive_go (points : Points m) (count : Nat) (item : Received) {k : Nat}
    (hk : k ≠ count) :
    R (ExceptT.lift ((cutPoints points count).arrive item) : Run (Cut m) ε Unit) k =
      R (ExceptT.lift (monadLift (points.arrive item) : Cut m Unit)) (k + 1) := by
  simp [R, cutPoints, hk]

/-- At the item at position `count`, a cut run stops. -/
theorem R_receive_stop {β : Type} (points : Points m) (count : Nat) (item : Received)
    (atArrival : Run (Cut m) ε Unit) (f : Unit → Run (Cut m) ε β) :
    R (Traversal.receive (cutPoints points count) item atArrival >>= f) count =
      pure (.error ()) := by
  simp only [Traversal.receive, bind_assoc]
  rw [R_bind]
  rw [R_arrive_stop]
  simp

/-- Before the item at position `count`, a cut run counts the item and goes on. -/
theorem R_receive_go {β : Type} (points : Points m) (count : Nat) (item : Received)
    (atArrival : Run (Cut m) ε Unit) (f : Unit → Run (Cut m) ε β) {k : Nat} (hk : k ≠ count) :
    R (Traversal.receive (cutPoints points count) item atArrival >>= f) k =
      R (receivePlain points item atArrival >>= f) (k + 1) := by
  simp only [Traversal.receive, receivePlain, bind_assoc]
  rw [R_bind, R_bind]
  rw [R_arrive_go points count item hk]
  rfl

/-! ## Programs and scripts -/

variable (points : Points m) (handler : Handler m ε values)
variable (producer : Producer m) (policy : VersionPolicy)
variable (count : Nat)

/-- A program run with the counting points. -/
abbrev runCut {α : Type} (p : Program values α) (items : List Received) :
    Run (Cut m) ε (α × List Received) :=
  Program.run (cutPoints points count) (cutHandler handler) (cutProducer producer) policy p
    items

/-- A program run with the counting points does before the cut what the items before the cut
tell it. -/
theorem cut_program {α : Type} (p : Program values α) :
    ∀ (items items' : List Received) (k : Nat), k ≤ count →
      items.take (count - k) = items'.take (count - k) → count - k < items.length →
      count - k < items'.length →
      R (Prod.fst <$> runCut points handler producer policy count p items) k =
        R (Prod.fst <$> runCut points handler producer policy count p items') k := by
  induction p with
  | done a => intros; simp [runCut, Program.run]
  | receive atArrival next ih =>
    intro items items' k hk ht hl hl'
    cases items with
    | nil => simp at hl
    | cons x s =>
      cases items' with
      | nil => simp at hl'
      | cons x' s' =>
        simp only [runCut, Program.run, map_bind]
        by_cases hc : k = count
        · subst hc
          rw [R_receive_stop, R_receive_stop]
        · rw [R_receive_go points count x _ _ hc, R_receive_go points count x' _ _ hc]
          have hpos : count - k = (count - (k + 1)) + 1 := by omega
          rw [hpos] at ht
          obtain ⟨rfl, ht'⟩ := take_cons_succ ht
          refine congr_noCount (noCount_receivePlain points x (noCount_arrival handler atArrival))
            fun _ => ?_
          exact ih x s s' (k + 1) (by omega) ht' (by simp at hl; omega) (by simp at hl'; omega)
  | call request next ih =>
    intro items items' k hk ht hl hl'
    simp only [runCut, Program.run, map_bind]
    exact congr_noCount (noCount_call handler request) fun v => ih v items items' k hk ht hl hl'
  | setVersion version next ih =>
    intro items items' k hk ht hl hl'
    simp only [runCut, Program.run, map_bind]
    exact congr_noCount (noCount_lift _) fun _ => ih items items' k hk ht hl hl'
  | discard next ih =>
    intro items items' k hk ht hl hl'
    simp only [runCut, Program.run, map_bind]
    exact congr_noCount (noCount_lift _) fun _ => ih items items' k hk ht hl hl'
  | switch declarations version next ih =>
    intro items items' k hk ht hl hl'
    simp only [runCut, Program.run, map_bind]
    exact congr_noCount (noCount_switch handler producer policy declarations version)
      fun _ => ih items items' k hk ht hl hl'
  | stuck => intros; rfl

/-- The cut run of a script is `parseScript` run with the counting points on what a parser
receives for it. -/
theorem cutRun_eq_parse {version : Version} {commands : List Tree.Command}
    (h : Script version commands) {n : Nat} (hn : 10 * sizeOf commands < n) :
    cutRun points handler producer policy count version commands =
      R (Prod.fst <$> runCut points handler producer policy count (parseScript n version)
        (received commands)) 0 := by
  have hm := run_script (points := cutPoints points count) (handler := cutHandler handler)
    (producer := cutProducer producer) (policy := policy) version commands [] h hn
  rw [List.append_nil] at hm
  simp only [runCut, hm, map_bind, map_pure]
  rw [show (fun _ : Unit => (pure () : Run (Cut m) ε Unit)) = pure from
    funext fun u => by cases u; rfl, bind_pure]
  rfl

/-- The cut runs of two valid scripts from the same version are equal when what a parser
receives for them agrees before the cut. -/
theorem cutRun_eq {version : Version} {commands commands' : List Tree.Command}
    (h : Script version commands) (h' : Script version commands')
    (ht : (received commands).take count = (received commands').take count) :
    cutRun points handler producer policy count version commands =
      cutRun points handler producer policy count version commands' := by
  let n := 10 * (sizeOf commands + sizeOf commands') + 1
  rw [cutRun_eq_parse points handler producer policy count h (n := n) (by omega),
    cutRun_eq_parse points handler producer policy count h' (n := n) (by omega)]
  by_cases hl : count < (received commands).length
  · have hl' := (received_length h h' ht).mp hl
    exact cut_program points handler producer policy count _ _ _ 0 (Nat.zero_le _)
      (by simpa using ht) (by simpa using hl) (by simpa using hl')
  · have hp : received commands' = received commands ++ (received commands').drop count := by
      rw [← List.take_of_length_le (Nat.le_of_not_lt hl), ht, List.take_append_drop]
    have := received_not_prefix h' h hp
    rw [this, List.append_nil] at hp
    rw [hp]

/-- The arrivals before the item at position `count` are the first `count` items that arrive. -/
theorem arrived_eventsBefore : ∀ (k : Nat) (events : List Event),
    (eventsBefore k events).filterMap Event.arrived =
      (events.filterMap Event.arrived).take k
  | _, [] => by simp [eventsBefore]
  | 0, event :: events => by
    have ih := arrived_eventsBefore 0 events
    cases event <;> simp only [eventsBefore, List.filterMap_cons, Event.arrived, ih,
      List.take_zero, List.filterMap_nil]
  | k + 1, event :: events => by
    have ih₀ := arrived_eventsBefore (k + 1) events
    have ih₁ := arrived_eventsBefore k events
    cases event <;> simp only [eventsBefore, List.filterMap_cons, Event.arrived, ih₀, ih₁,
      List.take_succ_cons]

/-- The processings before that of the item at position `count` are the first `count` items
processed. -/
theorem processed_eventsBeforeProcessing : ∀ (k : Nat) (events : List Event),
    (eventsBeforeProcessing k events).filterMap Event.processed =
      (events.filterMap Event.processed).take k
  | _, [] => by simp [eventsBeforeProcessing]
  | 0, event :: events => by
    have ih := processed_eventsBeforeProcessing 0 events
    cases event <;> simp only [eventsBeforeProcessing, List.filterMap_cons, Event.processed, ih,
      List.take_zero, List.filterMap_nil]
  | k + 1, event :: events => by
    have ih₀ := processed_eventsBeforeProcessing (k + 1) events
    have ih₁ := processed_eventsBeforeProcessing k events
    cases event <;> simp only [eventsBeforeProcessing, List.filterMap_cons, Event.processed,
      ih₀, ih₁, List.take_succ_cons]

/-- A recording begins with the handler's switch to the version the script is read from. -/
theorem record_head {version : Version} {commands : List Tree.Command}
    (h : Script version commands) :
    ∃ rest, record version commands = .handlerSwitch version :: rest :=
  ⟨_, record_eq_trace h (Nat.lt_succ_self _)⟩

/-- Two recordings that agree before an item are of scripts from the same version. -/
theorem version_eq_of_record {version version' : Version}
    {commands commands' : List Tree.Command} (h : Script version commands)
    (h' : Script version' commands')
    (he : eventsBefore count (record version commands) =
      eventsBefore count (record version' commands')) : version = version' := by
  obtain ⟨r, hr⟩ := record_head h
  obtain ⟨r', hr'⟩ := record_head h'
  rw [hr, hr'] at he
  cases count <;> simp only [eventsBefore, List.cons.injEq, Event.handlerSwitch.injEq] at he <;>
    exact he.1

/-- The cut runs of two valid scripts are equal when their recordings agree before the cut. -/
theorem cutRun_eq_of_record {version version' : Version}
    {commands commands' : List Tree.Command} (h : Script version commands)
    (h' : Script version' commands')
    (he : eventsBefore count (record version commands) =
      eventsBefore count (record version' commands')) :
    cutRun points handler producer policy count version commands =
      cutRun points handler producer policy count version' commands' := by
  obtain rfl := version_eq_of_record count h h' he
  refine cutRun_eq points handler producer policy count h h' ?_
  have := congrArg (List.filterMap Event.arrived) he
  rwa [arrived_eventsBefore, arrived_eventsBefore, (record_items h).1, (record_items h').1]
    at this

end

/-! ## Stopping before the processing of an item -/

section

variable {m : Type → Type} [Monad m] {ε : Type} {values : Values}

/-- Points that count the items that arrive and stop before the processing of the item at
position `count`; the arrival of that item is not passed on, only the calls due at it are made.
-/
def processingCutPoints (points : Points m) (count : Nat) : Points (Cut m) where
  arrive received := do
    let arrived ← get
    set (arrived + 1)
    if arrived = count then pure () else monadLift (points.arrive received)
  process received := do
    let arrived ← get
    if arrived = count + 1 then throw () else monadLift (points.process received)

/--
The traversal of the script with the handler, points, producer and policy, stopped before
the processing of the item at position `count`: what it has done when it rejects that item,
without the item's own arrival.
-/
def processingCutRun (points : Points m) (handler : Handler m ε values)
    (producer : Producer m) (policy : VersionPolicy)
    (count : Nat) (version : Version) (commands : List Tree.Command) :
    m (Except Unit (Except (Cause ε) Unit × Nat)) :=
  (((script (processingCutPoints points count) (cutHandler handler) (cutProducer producer)
    policy version commands).run).run 0).run

end

section

variable {m : Type → Type} [Monad m] [LawfulMonad m] {ε : Type} {values : Values}

theorem R_arrive_processing (points : Points m) (count : Nat) (item : Received) (k : Nat)
    {β : Type} (f : Unit → Run (Cut m) ε β) :
    R (ExceptT.lift ((processingCutPoints points count).arrive item) >>= f) k =
      if k = count then R (f ()) (k + 1)
      else R (ExceptT.lift (monadLift (points.arrive item) : Cut m Unit) >>= f) (k + 1) := by
  by_cases hk : k = count
  · subst hk
    simp only [↓reduceIte]
    rw [R_bind]
    simp [R, processingCutPoints]
  · simp only [hk, ↓reduceIte]
    rw [R_bind, R_bind]
    simp [R, processingCutPoints, hk]

theorem R_process_stop (points : Points m) (count : Nat) (item : Received)
    {β : Type} (f : Unit → Run (Cut m) ε β) :
    R (ExceptT.lift ((processingCutPoints points count).process item) >>= f) (count + 1) =
      pure (.error ()) := by
  rw [R_bind]
  have : R (ExceptT.lift ((processingCutPoints points count).process item) :
      Run (Cut m) ε Unit) (count + 1) = pure (.error ()) := by
    simp [R, processingCutPoints]
    simp [throw, throwThe, MonadExceptOf.throw, Except.map, ExceptT.mk]
    exact map_pure _ _
  rw [this]
  simp

theorem R_process_go (points : Points m) (count : Nat) (item : Received) {k : Nat}
    (hk : k ≠ count + 1) {β : Type} (f : Unit → Run (Cut m) ε β) :
    R (ExceptT.lift ((processingCutPoints points count).process item) >>= f) k =
      R (ExceptT.lift (monadLift (points.process item) : Cut m Unit) >>= f) k := by
  rw [R_bind, R_bind]
  simp [R, processingCutPoints, hk]

theorem R_receive_stop_processing {β : Type} (points : Points m) (count : Nat) (item : Received)
    {atArrival : Run (Cut m) ε Unit} (ha : NoCount atArrival) (f : Unit → Run (Cut m) ε β) :
    R (Traversal.receive (processingCutPoints points count) item atArrival >>= f) count =
      R (atArrival >>= fun _ =>
        (ExceptT.lift (throw () : Cut m β) : Run (Cut m) ε β)) (count + 1) := by
  simp only [Traversal.receive, bind_assoc]
  simp only [R_arrive_processing, ↓reduceIte]
  refine congr_noCount ha fun _ => ?_
  rw [R_process_stop]
  simp [R, throw, throwThe, MonadExceptOf.throw, ExceptT.mk]
  show _ = _ <$> (pure (Except.error ()) : m _)
  rw [map_pure]
  rfl

theorem R_receive_go_processing {β : Type} (points : Points m) (count : Nat) (item : Received)
    {atArrival : Run (Cut m) ε Unit} (ha : NoCount atArrival) (f : Unit → Run (Cut m) ε β)
    {k : Nat} (hk : k ≠ count) :
    R (Traversal.receive (processingCutPoints points count) item atArrival >>= f) k =
      R (receivePlain points item atArrival >>= f) (k + 1) := by
  simp only [Traversal.receive, receivePlain, bind_assoc]
  simp only [R_arrive_processing, hk, ↓reduceIte]
  refine congr_noCount (noCount_lift _) fun _ => congr_noCount ha fun _ => ?_
  exact R_process_go points count item (by omega) f

variable (points : Points m) (handler : Handler m ε values)
variable (producer : Producer m) (policy : VersionPolicy)
variable (count : Nat)

/-- A program run with the points that stop before processing. -/
abbrev runProcessingCut {α : Type} (p : Program values α) (items : List Received) :
    Run (Cut m) ε (α × List Received) :=
  Program.run (processingCutPoints points count) (cutHandler handler) (cutProducer producer)
    policy p items

theorem processingCut_program {α : Type} (p : Program values α) :
    ∀ (items items' : List Received) (k : Nat), k ≤ count →
      items.take (count - k) = items'.take (count - k) → count - k < items.length →
      count - k < items'.length →
      R (Prod.fst <$> runProcessingCut points handler producer policy count p items) k =
        R (Prod.fst <$> runProcessingCut points handler producer policy count p items')
          k := by
  induction p with
  | done a => intros; simp [runProcessingCut, Program.run]
  | receive atArrival next ih =>
    intro items items' k hk ht hl hl'
    cases items with
    | nil => simp at hl
    | cons x s =>
      cases items' with
      | nil => simp at hl'
      | cons x' s' =>
        simp only [runProcessingCut, Program.run, map_bind]
        have ha := noCount_arrival handler atArrival
        by_cases hc : k = count
        · subst hc
          rw [R_receive_stop_processing points k x ha,
            R_receive_stop_processing points k x' ha]
        · rw [R_receive_go_processing points count x ha _ hc,
            R_receive_go_processing points count x' ha _ hc]
          have hpos : count - k = (count - (k + 1)) + 1 := by omega
          rw [hpos] at ht
          obtain ⟨rfl, ht'⟩ := take_cons_succ ht
          refine congr_noCount (noCount_receivePlain points x ha) fun _ => ?_
          exact ih x s s' (k + 1) (by omega) ht' (by simp at hl; omega) (by simp at hl'; omega)
  | call request next ih =>
    intro items items' k hk ht hl hl'
    simp only [runProcessingCut, Program.run, map_bind]
    exact congr_noCount (noCount_call handler request) fun v => ih v items items' k hk ht hl hl'
  | setVersion version next ih =>
    intro items items' k hk ht hl hl'
    simp only [runProcessingCut, Program.run, map_bind]
    exact congr_noCount (noCount_lift _) fun _ => ih items items' k hk ht hl hl'
  | discard next ih =>
    intro items items' k hk ht hl hl'
    simp only [runProcessingCut, Program.run, map_bind]
    exact congr_noCount (noCount_lift _) fun _ => ih items items' k hk ht hl hl'
  | switch declarations version next ih =>
    intro items items' k hk ht hl hl'
    simp only [runProcessingCut, Program.run, map_bind]
    exact congr_noCount (noCount_switch handler producer policy declarations version)
      fun _ => ih items items' k hk ht hl hl'
  | stuck => intros; rfl

theorem processingCutRun_eq_parse {version : Version} {commands : List Tree.Command}
    (h : Script version commands) {n : Nat} (hn : 10 * sizeOf commands < n) :
    processingCutRun points handler producer policy count version commands =
      R (Prod.fst <$> runProcessingCut points handler producer policy count
        (parseScript n version) (received commands)) 0 := by
  have hm := run_script (points := processingCutPoints points count)
    (handler := cutHandler handler) (producer := cutProducer producer)
    (policy := policy) version commands [] h hn
  rw [List.append_nil] at hm
  simp only [runProcessingCut, hm, map_bind, map_pure]
  rw [show (fun _ : Unit => (pure () : Run (Cut m) ε Unit)) = pure from
    funext fun u => by cases u; rfl, bind_pure]
  rfl

/-- The processing-cut runs of two valid scripts from the same version are equal when what a
parser receives for them agrees before the cut. -/
theorem processingCutRun_eq {version : Version}
    {commands commands' : List Tree.Command} (h : Script version commands)
    (h' : Script version commands')
    (ht : (received commands).take count = (received commands').take count) :
    processingCutRun points handler producer policy count version commands =
      processingCutRun points handler producer policy count version commands' := by
  let n := 10 * (sizeOf commands + sizeOf commands') + 1
  rw [processingCutRun_eq_parse points handler producer policy count h (n := n)
      (by omega),
    processingCutRun_eq_parse points handler producer policy count h' (n := n)
      (by omega)]
  by_cases hl : count < (received commands).length
  · have hl' := (received_length h h' ht).mp hl
    exact processingCut_program points handler producer policy count _ _ _ 0
      (Nat.zero_le _) (by simpa using ht) (by simpa using hl) (by simpa using hl')
  · have hp : received commands' = received commands ++ (received commands').drop count := by
      rw [← List.take_of_length_le (Nat.le_of_not_lt hl), ht, List.take_append_drop]
    have := received_not_prefix h' h hp
    rw [this, List.append_nil] at hp
    rw [hp]

/-- The processing-cut runs of two valid scripts are equal when their recordings agree before
the processing of the item at the cut. -/
theorem processingCutRun_eq_of_record {version version' : Version}
    {commands commands' : List Tree.Command} (h : Script version commands)
    (h' : Script version' commands')
    (he : eventsBeforeProcessing count (record version commands) =
      eventsBeforeProcessing count (record version' commands')) :
    processingCutRun points handler producer policy count version commands =
      processingCutRun points handler producer policy count version' commands' := by
  have hv : version = version' := by
    obtain ⟨r, hr⟩ := record_head h
    obtain ⟨r', hr'⟩ := record_head h'
    rw [hr, hr'] at he
    cases count <;>
      simp only [eventsBeforeProcessing, List.cons.injEq, Event.handlerSwitch.injEq] at he <;>
      exact he.1
  obtain rfl := hv
  refine processingCutRun_eq points handler producer policy count h h' ?_
  have := congrArg (List.filterMap Event.processed) he
  rwa [processed_eventsBeforeProcessing, processed_eventsBeforeProcessing,
    (record_items h).2, (record_items h').2] at this

end

end BSmtLib.SpecChecks.Parser
