import BSmtLib.EndToEnd.Param.EraseSteps
import BSmtLib.EndToEnd.Consumer
import BSmtLib.Parser.Adapter
import BSmtLib.Proofs.Adapters

/-!
# The parse adapter's token against the recording run's

The parse adapter (`Parser.ParseAdapter`) has the parser take a token as the recording run of
the parser's driver does (`ParserProofs.recAfter`), without the token points and with the
producer's actions done on its cursor: its handler's log is the recording log with the events
that are not calls left out (`Erasing`), its parser goes on in the same state, and it acts on its
cursor as the recording log says the run asked its producer to (`takeOne_rec`).
-/

namespace BSmtLib.EndToEnd.Param

open BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal
open BSmtLib.ParserProofs
open BSmtLib.Parser
open BSmtLib.Proofs.Adapter (toVersion)

/-- The cursor after the requests: the switch of the version, then discarding. -/
def applyRequests {b : BatchTag} (cursor : BatchCursor b) (switch : Option Spec.Lexicon.Version)
    (discard : Bool) : BatchCursor b :=
  let switched := match switch with
    | none => cursor
    | some version =>
      match cursor.setVersion (toVersion version) with
      | .ok next => next
      | .error _ => cursor
  if discard then switched.discardRest else switched

/-- What the parse adapter does with a token, by what the recording run does with it: fails, or
finishes, or goes on, acting on the cursor as the run asked its producer after the token's
processing, a failed parser going on from its reset; the log is the run's with the events that
are not calls left out. -/
def paOf {b : BatchTag} (parser : ScriptParser (List Event)) (next : BatchCursor b) :
    Except (ParseErrorCause Unit) ((Version × ScriptParser (List Event)) ⊕ Unit) × List Event →
      (ParseAdapter.After (ScriptParser (List Event)) Unit Unit × BatchCursor b) × List Event
  | (.error e, log) =>
    ((.stop (.error e) (Parse.reset parser),
      applyRequests next (ParserProofs.switchOf log.reverse) (ParserProofs.discardOf log.reverse)),
      calls log)
  | (.ok (.inr ()), log) =>
    ((.stop (.ok (.break ())) (Parse.reset parser),
      applyRequests next (ParserProofs.switchOf log.reverse) (ParserProofs.discardOf log.reverse)),
      calls log)
  | (.ok (.inl (_, parser')), log) =>
    if (ParserProofs.switchOf log.reverse).isSome || ParserProofs.discardOf log.reverse then
      ((.stop (.ok .continue) parser',
        applyRequests next (ParserProofs.switchOf log.reverse) (ParserProofs.discardOf log.reverse)),
        calls log)
    else ((.goOn parser', next), calls log)

theorem calls_append_calls {added : List Event} (h : ∀ e ∈ added, e.isCall = true)
    (events : List Event) : calls (added ++ events) = added ++ calls events := by
  simp only [calls, List.filter_append]
  rw [List.filter_eq_self.mpr h]

theorem calls_cons_point {event : Event} (h : event.isCall = false) (events : List Event) :
    calls (event :: events) = calls events :=
  List.filter_cons_of_neg (by simp [h])

theorem calls_arrivalCalls (parser : ScriptParser (List Event)) (item : Input)
    (events : List Event) :
    calls (arrivalCalls parser item ++ events) = arrivalCalls parser item ++ calls events := by
  apply calls_append_calls
  intro e he
  unfold arrivalCalls at he
  split at he
  · simp at he
  · split at he
    · split at he
      · split at he
        · simp at he; subst he; rfl
        · simp at he
      · simp at he
    · simp at he

theorem toVersion_version (version : Version) : toVersion (Bridge.version version) = version := by
  cases version <;> rfl

/-- The events after the last processing, when the log ends with events that are no processing
after a processing. -/
theorem afterLastProcess_shape (pre : List Event) (received : Received) (rest : List Event)
    (h : ∀ e ∈ pre, isProcessing e = false) :
    ParserProofs.afterLastProcess ((pre ++ .process received :: rest).reverse) = pre.reverse := by
  unfold ParserProofs.afterLastProcess
  rw [List.reverse_reverse, List.takeWhile_append_of_pos (by simpa using h)]
  simp [isProcessing]

theorem isProcessing_of_isCall {e : Event} (h : e.isCall = true) : isProcessing e = false := by
  cases e <;> first | rfl | exact absurd h (by simp [Event.isCall])

theorem findSome_calls {α : Type} {f : Event → Option α} (hf : ∀ e, e.isCall = true → f e = none)
    {l : List Event} (h : ∀ e ∈ l, e.isCall = true) : l.findSome? f = none := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.findSome?_cons, hf e (h e (by simp))]
    exact ih fun e he => h e (by simp [he])

theorem any_calls {f : Event → Bool} (hf : ∀ e, e.isCall = true → f e = false)
    {l : List Event} (h : ∀ e ∈ l, e.isCall = true) : l.any f = false := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.any_cons, hf e (h e (by simp)), Bool.false_or]
    exact ih fun e he => h e (by simp [he])

/-- The recording run's processing of a token, from the log before it: its arrival, the calls
due at it and its processing written. -/
theorem recAfter_eq (version : Version) (parser : ScriptParser (List Event)) {item : Input}
    {received : Received} (hr : Bridge.received item = some received) (events : List Event) :
    (recAfter version parser item).run.run events =
      (afterProcessing recordingProducer version parser item).run.run
        (.process received :: (arrivalCalls parser item ++ .arrive received :: events)) := by
  have h₁ : ((ExceptT.lift (arriveAt recordingPoints item) : RPM Unit).run.run events) =
      (.ok (), .arrive received :: events) := by
    simp [arriveAt, hr, recordingPoints, emit]; rfl
  have h₂ := arrive_run parser item (.arrive received :: events)
  have h₃ : ((ExceptT.lift (processAt recordingPoints item) : RPM Unit).run.run
      (arrivalCalls parser item ++ .arrive received :: events)) =
      (.ok (), .process received :: (arrivalCalls parser item ++ .arrive received :: events)) := by
    simp [processAt, hr, recordingPoints, emit]; rfl
  show ((afterToken recordingPoints recordingProducer version parser item).run.run events) = _
  unfold afterToken
  rw [run_bind_ok h₁, run_bind_ok h₂, run_bind_ok h₃]

theorem requests_none {added : List Event} (h : ∀ e ∈ added, e.isCall = true) (received : Received)
    (rest : List Event) :
    ParserProofs.switchOf ((added ++ .process received :: rest).reverse) = none ∧
      ParserProofs.discardOf ((added ++ .process received :: rest).reverse) = false := by
  unfold ParserProofs.switchOf ParserProofs.discardOf
  rw [afterLastProcess_shape added received rest (fun e he => isProcessing_of_isCall (h e he))]
  have h' : ∀ e ∈ added.reverse, e.isCall = true := fun e he => h e (List.mem_reverse.mp he)
  exact ⟨findSome_calls (fun e he => by
      cases e <;> first | rfl | exact absurd he (by simp [Event.isCall])) h',
    any_calls (fun e he => by
      cases e <;> first | rfl | exact absurd he (by simp [Event.isCall])) h'⟩

theorem requests_switch {added added' : List Event} (h : ∀ e ∈ added, e.isCall = true)
    (h' : ∀ e ∈ added', e.isCall = true) (version : Spec.Lexicon.Version) (received : Received)
    (rest : List Event) :
    ParserProofs.switchOf
          ((added' ++ .producerSwitch version :: (added ++ .process received :: rest)).reverse) =
        some version ∧
      ParserProofs.discardOf
          ((added' ++ .producerSwitch version :: (added ++ .process received :: rest)).reverse) =
        false := by
  unfold ParserProofs.switchOf ParserProofs.discardOf
  rw [show added' ++ .producerSwitch version :: (added ++ .process received :: rest) =
      (added' ++ .producerSwitch version :: added) ++ .process received :: rest by simp,
    afterLastProcess_shape _ received rest (fun e he => by
      simp only [List.mem_append, List.mem_cons] at he
      rcases he with he | he | he
      · exact isProcessing_of_isCall (h' e he)
      · subst he; rfl
      · exact isProcessing_of_isCall (h e he))]
  have hr : ∀ e ∈ added.reverse, e.isCall = true := fun e he => h e (List.mem_reverse.mp he)
  have hr' : ∀ e ∈ added'.reverse, e.isCall = true := fun e he => h' e (List.mem_reverse.mp he)
  simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append,
    List.findSome?_append, List.any_append, List.findSome?_cons, List.any_cons]
  rw [findSome_calls ?a hr, any_calls ?b hr, any_calls ?c hr']
  · simp
  all_goals intro e he; cases e <;> simp_all [Event.isCall]

theorem requests_discard {added added' : List Event} (h : ∀ e ∈ added, e.isCall = true)
    (h' : ∀ e ∈ added', e.isCall = true) (received : Received) (rest : List Event) :
    ParserProofs.switchOf
          ((added' ++ .producerDiscard :: (added ++ .process received :: rest)).reverse) =
        none ∧
      ParserProofs.discardOf
          ((added' ++ .producerDiscard :: (added ++ .process received :: rest)).reverse) =
        true := by
  unfold ParserProofs.switchOf ParserProofs.discardOf
  rw [show added' ++ .producerDiscard :: (added ++ .process received :: rest) =
      (added' ++ .producerDiscard :: added) ++ .process received :: rest by simp,
    afterLastProcess_shape _ received rest (fun e he => by
      simp only [List.mem_append, List.mem_cons] at he
      rcases he with he | he | he
      · exact isProcessing_of_isCall (h' e he)
      · subst he; rfl
      · exact isProcessing_of_isCall (h e he))]
  have hr : ∀ e ∈ added.reverse, e.isCall = true := fun e he => h e (List.mem_reverse.mp he)
  have hr' : ∀ e ∈ added'.reverse, e.isCall = true := fun e he => h' e (List.mem_reverse.mp he)
  simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append,
    List.findSome?_append, List.any_append, List.findSome?_cons, List.any_cons]
  rw [findSome_calls ?a hr, findSome_calls ?b hr', any_calls ?c hr]
  · simp
  all_goals intro e he; cases e <;> simp_all [Event.isCall]

theorem id_bind_eq {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

theorem run_bind_error {α β : Type} {x : RPM α} {f : α → RPM β} {events events' : List Event}
    {e : ParseErrorCause Unit} (h : (x.run.run events) = (.error e, events')) :
    ((x >>= f).run.run events) = (.error e, events') := by
  simp only [ExceptT.run_bind, StateT.run_bind]
  rw [h]
  rfl

theorem takeOne_rec {b : BatchTag} (parser : ScriptParser (List Event))
    (cursor next : BatchCursor b) (token : Token b) (consumed : next.Consumed cursor)
    (events : List Event) {received : Received}
    (hr : Bridge.received (Input.ofSyntax (next.syntax token)) = some received) :
    let r := (ParseAdapter.takeOne (H := List Event) (m := Id) (P := ScriptParser (List Event))
      parser cursor token next consumed).run (calls events)
    ((r.1.1, r.1.2.val), r.2) =
      paOf parser next ((recAfter next.version parser (Input.ofSyntax (next.syntax token))).run.run
        events) := by
  intro r
  have hitem' : Input.ofSyntax (Produce.syntax next token) =
      Input.ofSyntax (next.syntax token) := rfl
  generalize hitem : Input.ofSyntax (next.syntax token) = item at hr ⊢
  rw [recAfter_eq _ _ hr]
  have hY : calls (.process received :: (arrivalCalls parser item ++ .arrive received :: events)) =
      arrivalCalls parser item ++ calls events := by
    rw [calls_cons_point rfl, calls_arrivalCalls, calls_cons_point rfl]
  have hE := scriptStep_erasing next.version parser item
  have hstep :=
    hE.erase (.process received :: (arrivalCalls parser item ++ .arrive received :: events))
  obtain ⟨added, hlog, hcalls⟩ :=
    hE.adds (.process received :: (arrivalCalls parser item ++ .arrive received :: events))
  have hpost :=
    hE.post (.process received :: (arrivalCalls parser item ++ .arrive received :: events))
  rw [hY] at hstep
  rcases hS : (Parse.step (H := List Event) next.version parser item).run.run
    (.process received :: (arrivalCalls parser item ++ .arrive received :: events)) with ⟨res, log⟩
  rw [hS] at hstep hlog hpost
  simp only at hstep hlog hpost
  have hX : ((Parse.arrive (H := List Event) parser item >>= fun _ =>
      Parse.step (Produce.version next) parser item : RPM _).run.run (calls events)) =
        (res, calls log) := by
    rw [run_bind_ok (arrive_run parser item (calls events))]
    exact hstep
  simp only [r, ParseAdapter.takeOne, StateT.run_bind]
  try rw [hitem']
  rw [hitem, hX]
  unfold afterProcessing
  rcases res with e | flow
  · rw [run_bind_error hS]
    subst hlog
    obtain ⟨hsw, hdi⟩ := requests_none hcalls received
      (arrivalCalls parser item ++ .arrive received :: events)
    show _ = paOf parser next (.error e, _)
    simp only [paOf, hsw, hdi]
    rfl
  · rw [run_bind_ok hS]
    subst hlog
    cases flow with
    | more p =>
      obtain ⟨hsw, hdi⟩ := requests_none hcalls received
        (arrivalCalls parser item ++ .arrive received :: events)
      show _ = paOf parser next (.ok (.inl (next.version, p)), _)
      simp only [paOf, hsw, hdi, Option.isSome_none, Bool.or_false, Bool.false_eq_true, ite_false]
      rfl
    | done result =>
      obtain ⟨hsw, hdi⟩ := requests_none hcalls received
        (arrivalCalls parser item ++ .arrive received :: events)
      show _ = paOf parser next (.ok (.inr ()), _)
      simp only [paOf, hsw, hdi]
      rfl
    | switchVersion declared resume =>
      have hres : Erases resume := hpost (.switchVersion declared resume) rfl
      have hset : ((ExceptT.lift (recordingProducer.setVersion (Bridge.version declared)).run :
          RPM (Except Traversal.VersionRefused Unit)).run.run
          (added ++ .process received ::
            (arrivalCalls parser item ++ .arrive received :: events))) =
          (.ok (.ok ()), .producerSwitch (Bridge.version declared) ::
            (added ++ .process received ::
              (arrivalCalls parser item ++ .arrive received :: events))) :=
            rfl
      rw [run_bind_ok hset]
      dsimp only
      have herase := hres.erase (.producerSwitch (Bridge.version declared) ::
        (added ++ .process received :: (arrivalCalls parser item ++ .arrive received :: events)))
      obtain ⟨added', hlog', hcalls'⟩ := hres.adds (.producerSwitch (Bridge.version declared) ::
        (added ++ .process received :: (arrivalCalls parser item ++ .arrive received :: events)))
      rw [calls_cons_point rfl] at herase
      rcases hR : resume.run.run (.producerSwitch (Bridge.version declared) ::
        (added ++ .process received ::
          (arrivalCalls parser item ++ .arrive received :: events))) with
        ⟨res₂, log₂⟩
      rw [hR] at herase hlog'
      simp only at herase hlog'
      subst hlog'
      obtain ⟨hsw, hdi⟩ := requests_switch hcalls hcalls' (Bridge.version declared) received
        (arrivalCalls parser item ++ .arrive received :: events)
      simp only [id_bind_eq]
      try dsimp only
      split
      · rename_i heq
        simp [Produce.setVersion, BatchCursor.setVersion] at heq
      · rename_i switched heq
        have heq' : next.setVersion declared = .ok switched := heq
        have happly : applyRequests next (some (Bridge.version declared)) false = switched := by
          simp only [applyRequests, toVersion_version, heq', Bool.false_eq_true, ite_false]
        simp only [StateT.run_bind]
        rw [herase]
        simp only [id_bind_eq]
        rcases res₂ with e | step
        · rw [run_bind_error hR]
          show _ = paOf parser next (.error e, _)
          simp only [paOf, hsw, hdi, happly]
          rfl
        · rw [run_bind_ok hR]
          cases step with
          | more p =>
            show _ = paOf parser next (.ok (.inl (declared, p)), _)
            simp only [paOf, hsw, hdi, Option.isSome_some, Bool.true_or, ite_true, happly]
            rfl
          | done result =>
            show _ = paOf parser next (.ok (.inr ()), _)
            simp only [paOf, hsw, hdi, happly]
            rfl
    | discardRest resume =>
      have hres : Erases resume := hpost (.discardRest resume) rfl
      have hdisc : ((ExceptT.lift recordingProducer.discardRest : RPM Unit).run.run
          (added ++ .process received ::
            (arrivalCalls parser item ++ .arrive received :: events))) =
          (.ok (), .producerDiscard ::
            (added ++ .process received ::
              (arrivalCalls parser item ++ .arrive received :: events))) :=
            rfl
      rw [run_bind_ok hdisc]
      have herase := hres.erase (.producerDiscard ::
        (added ++ .process received :: (arrivalCalls parser item ++ .arrive received :: events)))
      obtain ⟨added', hlog', hcalls'⟩ := hres.adds (.producerDiscard ::
        (added ++ .process received :: (arrivalCalls parser item ++ .arrive received :: events)))
      rw [calls_cons_point rfl] at herase
      rcases hR : resume.run.run (.producerDiscard ::
        (added ++ .process received ::
          (arrivalCalls parser item ++ .arrive received :: events))) with
        ⟨res₂, log₂⟩
      rw [hR] at herase hlog'
      simp only at herase hlog'
      subst hlog'
      obtain ⟨hsw, hdi⟩ := requests_discard hcalls hcalls' received
        (arrivalCalls parser item ++ .arrive received :: events)
      have happly : applyRequests next none true = next.discardRest := rfl
      simp only [id_bind_eq]
      try dsimp only
      simp only [StateT.run_bind]
      rw [herase]
      simp only [id_bind_eq]
      rcases res₂ with e | step
      · rw [run_bind_error hR]
        show _ = paOf parser next (.error e, _)
        simp only [paOf, hsw, hdi, happly]
        rfl
      · rw [run_bind_ok hR]
        cases step with
        | more p =>
          show _ = paOf parser next (.ok (.inl (next.version, p)), _)
          simp only [paOf, hsw, hdi, Option.isSome_none, Bool.false_or, ite_true, happly]
          rfl
        | done result =>
          show _ = paOf parser next (.ok (.inr ()), _)
          simp only [paOf, hsw, hdi, happly]
          rfl

/-- The version the recording run goes on in after a token: the one it asked its producer to
switch to after the token's processing, if it did, else the one it was in. -/
theorem recAfter_version (version : Version) (parser : ScriptParser (List Event)) {item : Input}
    {received : Received} (hr : Bridge.received item = some received) (events : List Event)
    {version' : Version} {parser' : ScriptParser (List Event)} {log : List Event}
    (h : (recAfter version parser item).run.run events = (.ok (.inl (version', parser')), log)) :
    version' = match ParserProofs.switchOf log.reverse with
      | some switched => toVersion switched
      | none => version := by
  rw [recAfter_eq _ _ hr] at h
  have hE := scriptStep_erasing version parser item
  obtain ⟨added, hlog, hcalls⟩ :=
    hE.adds (.process received :: (arrivalCalls parser item ++ .arrive received :: events))
  have hpost :=
    hE.post (.process received :: (arrivalCalls parser item ++ .arrive received :: events))
  rcases hS : (Parse.step (H := List Event) version parser item).run.run
    (.process received :: (arrivalCalls parser item ++ .arrive received :: events)) with ⟨res, log₀⟩
  rw [hS] at hlog hpost
  simp only at hlog hpost
  subst hlog
  unfold afterProcessing at h
  rcases res with e | flow
  · rw [run_bind_error hS] at h
    cases h
  · rw [run_bind_ok hS] at h
    cases flow with
    | more p =>
      obtain ⟨hsw, -⟩ := requests_none hcalls received
        (arrivalCalls parser item ++ .arrive received :: events)
      cases h
      rw [hsw]
    | done result => cases h
    | switchVersion declared resume =>
      have hres : Erases resume := hpost (.switchVersion declared resume) rfl
      have hset : ((ExceptT.lift (recordingProducer.setVersion (Bridge.version declared)).run :
          RPM (Except Traversal.VersionRefused Unit)).run.run
          (added ++ .process received ::
            (arrivalCalls parser item ++ .arrive received :: events))) =
          (.ok (.ok ()), .producerSwitch (Bridge.version declared) ::
            (added ++ .process received ::
              (arrivalCalls parser item ++ .arrive received :: events))) :=
            rfl
      rw [run_bind_ok hset] at h
      obtain ⟨added', hlog', hcalls'⟩ := hres.adds (.producerSwitch (Bridge.version declared) ::
        (added ++ .process received :: (arrivalCalls parser item ++ .arrive received :: events)))
      rcases hR : resume.run.run (.producerSwitch (Bridge.version declared) ::
        (added ++ .process received ::
          (arrivalCalls parser item ++ .arrive received :: events))) with
        ⟨res₂, log₂⟩
      rw [hR] at hlog'
      simp only at hlog'
      subst hlog'
      obtain ⟨hsw, -⟩ := requests_switch hcalls hcalls' (Bridge.version declared) received
        (arrivalCalls parser item ++ .arrive received :: events)
      rcases res₂ with e | step
      · simp only [run_bind_error hR] at h
        cases h
      · simp only [run_bind_ok hR] at h
        cases step with
        | more p =>
          cases h
          rw [hsw]
          exact (toVersion_version _).symm
        | done r => cases h
    | discardRest resume =>
      have hres : Erases resume := hpost (.discardRest resume) rfl
      have hdisc : ((ExceptT.lift recordingProducer.discardRest : RPM Unit).run.run
          (added ++ .process received ::
            (arrivalCalls parser item ++ .arrive received :: events))) =
          (.ok (), .producerDiscard ::
            (added ++ .process received ::
              (arrivalCalls parser item ++ .arrive received :: events))) :=
            rfl
      rw [run_bind_ok hdisc] at h
      obtain ⟨added', hlog', hcalls'⟩ := hres.adds (.producerDiscard ::
        (added ++ .process received :: (arrivalCalls parser item ++ .arrive received :: events)))
      rcases hR : resume.run.run (.producerDiscard ::
        (added ++ .process received ::
          (arrivalCalls parser item ++ .arrive received :: events))) with
        ⟨res₂, log₂⟩
      rw [hR] at hlog'
      simp only at hlog'
      subst hlog'
      obtain ⟨hsw, -⟩ := requests_discard hcalls hcalls' received
        (arrivalCalls parser item ++ .arrive received :: events)
      rcases res₂ with e | step
      · simp only [run_bind_error hR] at h
        cases h
      · simp only [run_bind_ok hR] at h
        cases step with
        | more p =>
          cases h
          rw [hsw]
        | done r => cases h

/-! ## The adapter's loop over a cursor -/

/-- The parse adapter's loop over the tokens of a cursor, from the parser: each token taken in
turn, until the cursor has none or the handover stops. -/
def paLoop {b : BatchTag} (parser : ScriptParser (List Event)) (cursor : BatchCursor b) :
    StateT (List Event) Id
      (Except (ParseErrorCause Unit) (ControlFlow Unit) × ScriptParser (List Event) ×
        BatchCursor b) :=
  if h : cursor.HasNext then
    match cursor.next h with
    | (token, ⟨next, consumed⟩) => do
      match ← ParseAdapter.takeOne (H := List Event) (m := Id) parser cursor token next
          consumed with
      | (.goOn parser', ⟨later, _taken⟩) => paLoop parser' later
      | (.stop answer parser', ⟨later, _⟩) => return (answer, parser', later)
  else return (.ok .continue, parser, cursor)
termination_by cursor.remaining
decreasing_by exact BatchCursor.Consumed.remaining_lt _taken

theorem next?_hasNext {b : BatchTag} (cursor : BatchCursor b) (h : cursor.HasNext) :
    Produce.next? cursor = some (cursor.next h) := by
  show BatchCursor.next? cursor = _
  unfold BatchCursor.next?
  rw [dite_eq_left_of_eq_true (eq_true h)]

theorem next?_not {b : BatchTag} (cursor : BatchCursor b) (h : ¬ cursor.HasNext) :
    Produce.next? cursor = none := by
  show BatchCursor.next? cursor = _
  unfold BatchCursor.next?
  rw [dite_eq_right_of_eq_false (eq_false h)]

/-- The adapter's loop over the rest of its producer is `paLoop`. -/
theorem rest_eq {b : BatchTag} (origin : BatchCursor b) :
    ∀ (n : Nat) (parser : ScriptParser (List Event)) (cursor : BatchCursor b)
      (consumed : Produce.Consumed cursor origin) (handler : List Event), cursor.remaining < n →
      let r := (ParseAdapter.rest (H := List Event) (m := Id) origin parser cursor consumed).run
        handler
      ((r.1.1, r.1.2.1, r.1.2.2.val), r.2) = (paLoop parser cursor).run handler
  | 0, _, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, parser, cursor, consumed, handler, hn => by
    intro r
    simp only [r]
    rw [ParseAdapter.rest, paLoop]
    by_cases h : cursor.HasNext
    · rw [next?_hasNext cursor h, dite_eq_left_of_eq_true (eq_true h)]
      simp only [StateT.run_bind]
      generalize (ParseAdapter.takeOne (H := List Event) (m := Id) parser cursor (cursor.next h).1
        (cursor.next h).2.val (cursor.next h).2.property).run handler = t
      obtain ⟨⟨after, ⟨later, taken⟩⟩, handler'⟩ := t
      cases after with
      | goOn parser' =>
        exact rest_eq origin n parser' later _ handler'
          (Nat.lt_of_lt_of_le (BatchCursor.Consumed.remaining_lt taken) (Nat.le_of_lt_succ hn))
      | stop answer parser' => rfl
    · rw [next?_not cursor h, dite_eq_right_of_eq_false (eq_false h)]
      rfl

theorem first_eq {b : BatchTag} (cursor : BatchCursor b) (h : cursor.HasNext) :
    ParseAdapter.first cursor h = cursor.next h := by
  unfold ParseAdapter.first
  split
  · rename_i first hfirst
    rw [next?_hasNext cursor h] at hfirst
    exact (Option.some.inj hfirst).symm
  · rename_i hnone
    rw [next?_hasNext cursor h] at hnone
    cases hnone

/-- The log the adapter's handler holds when its loop over a cursor in the version begins: the
switch to the version first, unless the handler was told the version of the input already. -/
def startLog (adapter : RecAdapter) (version : Version) : List Event :=
  if adapter.versionSet then adapter.handler
  else .handlerSwitch (Bridge.version version) :: adapter.handler

/-- A call of the adapter is its loop over the cursor, from its parser and its handler's log with
the switch to the cursor's version first, unless the handler was told the version already;
afterwards the handler is told the version again only after the parser broke. -/
theorem consume_eq {b : BatchTag} (cursor : BatchCursor b) (h : cursor.HasNext)
    (adapter : RecAdapter) :
    let q := (ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run adapter
    let r := (paLoop adapter.parser cursor).run (startLog adapter cursor.version)
    (q.1.1, q.1.2.val, q.2) = (r.1.1, r.1.2.2,
      { handler := r.2, parser := r.1.2.1,
        versionSet := ParseAdapter.versionSetAfter r.1.1 }) := by
  intro q r
  simp only [q, r]
  rw [paLoop, dite_eq_left_of_eq_true (eq_true h)]
  simp only [ConsumeFrom.consume]
  have hf := first_eq cursor h
  generalize ParseAdapter.first cursor h = pr at hf ⊢
  subst hf
  have hstart : ((show StateT (List Event) Id Unit from
      if adapter.versionSet then pure ()
      else Handler.setVersion (Produce.version cursor)).run adapter.handler) =
      ((), startLog adapter cursor.version) := by
    unfold startLog
    cases adapter.versionSet <;> rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, liftM, monadLift,
    MonadLift.monadLift, StateT.run_lift, bind_pure_comp]
  rw [hstart]
  simp only [id_bind_eq]
  generalize (ParseAdapter.takeOne (H := List Event) (m := Id) adapter.parser cursor
    (cursor.next h).1 (cursor.next h).2.val (cursor.next h).2.property).run
      (startLog adapter cursor.version) = t
  obtain ⟨⟨after, ⟨later, taken⟩⟩, handler'⟩ := t
  cases after with
  | stop answer parser' => rfl
  | goOn parser' =>
    have := rest_eq cursor (later.remaining + 1) parser' later taken handler' (Nat.lt_succ_self _)
    simp only at this
    exact congrArg (fun x : (Except (ParseErrorCause Unit) (ControlFlow Unit) ×
      ScriptParser (List Event) × BatchCursor b) × List Event =>
        (x.1.1, x.1.2.2, (ParseAdapter.mk x.2 x.1.2.1
          (ParseAdapter.versionSetAfter x.1.1) : RecAdapter))) this

end BSmtLib.EndToEnd.Param
