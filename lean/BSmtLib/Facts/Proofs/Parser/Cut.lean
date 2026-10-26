module

public import BSmtLib.Facts.Proofs.Parser.QuietSteps
public import BSmtLib.Facts.Proofs.Parser.Script
import all BSmtLib.Parser
import all BSmtLib.Parser.Command
import all BSmtLib.Parser.Command.Internal.Function
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# What the parser has done before an item

The placement of the calls among the items (`BSmtLibSpec.Parser.Properties.PlacementDetermined`) for
the library's parser: in a recording run, what the script parser has done before an item arrives,
and before it is processed, is what the traversal of any valid script that agrees with the input
up to that item has done (`placement_arrival`, `placement_processing`); and where its input
stops, it has done what the traversal does before the next item arrives (`placement_prefix`).

The parser's run takes the items one by one (`driveParse_cons`); each item adds its arrival, the
calls due at its arrival, its processing and silent events (`afterToken_shape`), so the cut
functions of the specification formalism (`BSmtLibSpec`) pass over the items before the cut alike in
two runs that share them.
-/

namespace BSmtLib.Facts.Proofs.Parser.Cut

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Version (VersionPosture)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.QuietSteps BSmtLib.Facts.Proofs.Parser.Recording
open BSmtLib.Facts.Proofs.Parser.Script

/-! ## One item at a time -/

theorem bind_ext {m : Type → Type} [Monad m] {α β : Type} {x : m α} {f g : α → m β}
    (h : ∀ a, f a = g a) : x >>= f = x >>= g := by
  rw [funext h]

section

variable {H P R : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
variable [Parser.Internal.ParseByToken P H m (Handler.Error H) R]
variable (points : Points (StateT H m)) (producer : Producer (StateT H m))

/-- What the driver does with an item after its processing: the parser's step and what the step
asks of the producer; then whether the parser goes on, in which version and state, or
finished. -/
def afterProcessing (version : Version) (parser : P) (token : Parser.Internal.Input) :
    PM H ((Version × P) ⊕ R) := do
  match ← Parser.Internal.ParseByToken.step version parser token with
  | .more parser => pure (.inl (version, parser))
  | .done result => pure (.inr result)
  | .switchVersion declared resume =>
    match ← ExceptT.lift (producer.setVersion (Bridge.version declared)).run with
    | .error _ => throw (.version .unsupported)
    | .ok () =>
      match ← resume with
      | .more parser => pure (.inl (declared, parser))
      | .done result => pure (.inr result)
  | .discardRest resume => do
    ExceptT.lift producer.discardRest
    match ← resume with
    | .more parser => pure (.inl (version, parser))
    | .done result => pure (.inr result)

/-- What the driver does with one item: its arrival, the parser's calls due at it, its
processing, then as `afterProcessing`. -/
def afterToken (version : Version) (parser : P) (token : Parser.Internal.Input) :
    PM H ((Version × P) ⊕ R) := do
  ExceptT.lift (arriveAt points token)
  Parser.Internal.ParseByToken.arrive parser token
  ExceptT.lift (processAt points token)
  afterProcessing producer version parser token

/-- How the driver goes on after an item. -/
def continueWith (tokens : List Parser.Internal.Input) :
    (Version × P) ⊕ R → PM H (Option (R × List Parser.Internal.Input))
  | .inl (version, parser) => driveParse points producer version parser tokens
  | .inr result => pure (some (result, tokens))

theorem driveParse_cons (version : Version) (parser : P) (token : Parser.Internal.Input)
    (tokens : List Parser.Internal.Input) :
    driveParse points producer version parser (token :: tokens) =
      afterToken points producer version parser token >>= continueWith points producer tokens := by
  simp only [driveParse, afterToken, afterProcessing, bind_assoc]
  refine bind_ext fun _ => bind_ext fun _ => bind_ext fun _ => bind_ext fun flow => ?_
  cases flow with
  | more => simp [continueWith]
  | done => simp [continueWith]
  | switchVersion declared resume =>
    simp only [bind_assoc]
    refine bind_ext fun result => ?_
    cases result with
    | error => simp
    | ok =>
      simp only [bind_assoc]
      refine bind_ext fun step => ?_
      cases step <;> simp [continueWith]
  | discardRest resume =>
    simp only [bind_assoc]
    refine bind_ext fun _ => ?_
    refine bind_ext fun step => ?_
    cases step <;> simp [continueWith]

end
/-! ## An item in a recording run -/

section

/-- The recording run's driver of the script parser. -/
abbrev recAfter (version : Version) (parser : ScriptParser (List Event))
    (token : Parser.Internal.Input) :
    Quiet.RPM ((Version × ScriptParser (List Event)) ⊕ Unit) :=
  afterToken recordingPoints recordingProducer version parser token

/-- The calls due at an item's arrival: the start of a recursive body, when the item begins a body
that is due. -/
def arrivalCalls (parser : ScriptParser (List Event))
    (token : Parser.Internal.Input) : List Event :=
  match token with
  | .parenClose => []
  | _ =>
    match ScriptParser.Internal.command parser with
    | .payload (.defineFunsRecBodies signatures state) =>
      if state.opened && state.outside then
        match signatures[state.items.size]? with
        | some signature =>
          [.call .nothing (.startRecursiveBody (Bridge.signature (H := List Event) signature))]
        | none => []
      else []
    | _ => []

theorem run_bind_ok {α β : Type} {x : Quiet.RPM α} {f : α → Quiet.RPM β}
    {events events' : List Event}
    {a : α} (h : (x.run.run events) = (.ok a, events')) :
    ((x >>= f).run.run events) = ((f a).run.run events') := by
  simp only [ExceptT.run_bind, StateT.run_bind]
  rw [h]
  rfl

theorem silent_setVersion (version : BSmtLibSpec.Lexicon.Version) :
    Quiet.Silent (ExceptT.lift (recordingProducer.setVersion version).run :
      Quiet.RPM (Except Traversal.VersionRefused Unit)) := by
  constructor
  intro events
  exact ⟨[.producerSwitch version], rfl, by simp [Quiet.isPoint], fun _ _ => trivial⟩

theorem silent_discardRest :
    Quiet.Silent (ExceptT.lift recordingProducer.discardRest : Quiet.RPM Unit) := by
  constructor
  intro events
  exact ⟨[.producerDiscard], rfl, by simp [Quiet.isPoint], fun _ _ => trivial⟩

/-- What follows an item's processing in its driver step is silent. -/
theorem afterProcessing_silent (version : Version) (parser : ScriptParser (List Event))
    (token : Parser.Internal.Input) :
    Quiet.Silent (afterProcessing recordingProducer version parser token) := by
  unfold afterProcessing
  apply Quiet.bind (scriptStep_quiet version parser token)
  intro flow hflow
  cases flow with
  | more => exact Quiet.pure trivial
  | done => exact Quiet.pure trivial
  | switchVersion declared resume =>
    apply Quiet.bind_silent (silent_setVersion _)
    intro result
    cases result with
    | error => exact Quiet.throw _
    | ok =>
      apply Quiet.bind_silent hflow
      intro step
      cases step <;> exact Quiet.pure trivial
  | discardRest resume =>
    apply Quiet.bind_silent silent_discardRest
    intro _
    apply Quiet.bind_silent hflow
    intro step
    cases step <;> exact Quiet.pure trivial

theorem arrive_run (parser : ScriptParser (List Event)) (token : Parser.Internal.Input)
    (events : List Event) :
    ((Parser.Internal.ParseByToken.arrive (H := List Event) parser token).run.run events) =
      (.ok (), arrivalCalls parser token ++ events) := by
  obtain ⟨posture, command, declarations⟩ := parser
  show ((ScriptParser.Internal.arrive ⟨posture, command, declarations⟩ token : Quiet.RPM
      Unit).run.run
      events) = _
  unfold ScriptParser.Internal.arrive arrivalCalls ScriptParser.Internal.command
  rcases command with _ | _ | payload | parser
  · cases token <;> rfl
  · cases token <;> rfl
  · cases payload <;> try (cases token <;> rfl)
    rename_i signatures state
    simp only [Parser.Command.Internal.commandArrive,
        Parser.Command.Internal.Standard.payloadArrive,
        Parser.Command.Internal.Function.bodiesArrive]
    cases (state.opened && state.outside) <;> cases token <;>
      cases signatures[state.items.size]? <;> rfl
  · exact Empty.elim parser

/--
An item in the recording run: its arrival, the calls due at it, its processing, then silent
events.
-/
theorem afterToken_shape (version : Version) (parser : ScriptParser (List Event))
    {token : Parser.Internal.Input} {received : Received}
        (htoken : Bridge.received token = some received)
    (events : List Event) :
    ∃ silent, ((recAfter version parser token).run.run events).2 =
        silent ++ [.process received] ++ arrivalCalls parser token ++ [.arrive received] ++
          events ∧
      ∀ e ∈ silent, Quiet.isPoint e = false := by
  have h₁ : ((ExceptT.lift (arriveAt recordingPoints token) : Quiet.RPM Unit).run.run events) =
      (.ok (), .arrive received :: events) := by
    simp [arriveAt, htoken, recordingPoints, emit]; rfl
  have h₂ := arrive_run parser token (.arrive received :: events)
  have h₃ : ((ExceptT.lift (processAt recordingPoints token) : Quiet.RPM Unit).run.run
      (arrivalCalls parser token ++ .arrive received :: events)) =
      (.ok (), .process received ::
        (arrivalCalls parser token ++ .arrive received :: events)) := by
    simp [processAt, htoken, recordingPoints, emit]; rfl
  obtain ⟨silent, hstate, hpoints, -⟩ :=
    (afterProcessing_silent version parser token).holds
      (.process received :: (arrivalCalls parser token ++ .arrive received :: events))
  refine ⟨silent, ?_, hpoints⟩
  show ((afterToken recordingPoints recordingProducer version parser token).run.run events).2 = _
  unfold afterToken
  rw [run_bind_ok h₁, run_bind_ok h₂, run_bind_ok h₃]
  rw [hstate]
  simp

end
/-! ## The cut functions over shared events -/

/-- The event is an arrival. -/
def isArrival : Event → Bool
  | .arrive _ => true
  | _ => false

theorem eventsBefore_append (prefix_ rest : List Event) (k : Nat) :
    eventsBefore (prefix_.countP isArrival + k) (prefix_ ++ rest) =
      prefix_ ++ eventsBefore k rest := by
  induction prefix_ with
  | nil => simp
  | cons event prefix_ ih =>
    cases event with
    | arrive item =>
      simp only [List.countP_cons, isArrival, ite_true, List.cons_append]
      rw [show prefix_.countP isArrival + 1 + k = (prefix_.countP isArrival + k) + 1 by omega]
      simp [eventsBefore, ih]
    | _ =>
      simp only [List.countP_cons, isArrival, Bool.false_eq_true, ite_false, Nat.add_zero,
        List.cons_append]
      rw [eventsBefore.eq_def]
      simp [ih]

theorem eventsBeforeProcessing_append (prefix_ rest : List Event) (k : Nat) :
    eventsBeforeProcessing (prefix_.countP isProcessing + k) (prefix_ ++ rest) =
      eventsBeforeProcessing (prefix_.countP isProcessing + k) prefix_ ++
        eventsBeforeProcessing k rest := by
  induction prefix_ with
  | nil => simp [eventsBeforeProcessing]
  | cons event prefix_ ih =>
    cases event with
    | process item =>
      simp only [List.countP_cons, isProcessing, ite_true, List.cons_append]
      rw [show prefix_.countP isProcessing + 1 + k = (prefix_.countP isProcessing + k) + 1 by
        omega]
      simp [eventsBeforeProcessing, ih]
    | arrive item =>
      simp only [List.countP_cons, isProcessing, Bool.false_eq_true, ite_false, Nat.add_zero,
        List.cons_append]
      cases h : prefix_.countP isProcessing + k with
      | zero =>
        rw [eventsBeforeProcessing.eq_def, eventsBeforeProcessing.eq_def _ (_ :: prefix_)]
        simp only
        rw [h] at ih
        exact ih
      | succ count =>
        rw [eventsBeforeProcessing.eq_def, eventsBeforeProcessing.eq_def _ (_ :: prefix_)]
        simp only
        rw [h] at ih
        simp [ih]
    | _ =>
      simp only [List.countP_cons, isProcessing, Bool.false_eq_true, ite_false, Nat.add_zero,
        List.cons_append]
      rw [eventsBeforeProcessing.eq_def, eventsBeforeProcessing.eq_def (prefix_.countP _ + k)]
      simp [ih]
/-! ## Two runs that share their first items -/

theorem run_bind_split {α β : Type} (x : Quiet.RPM α) (f : α → Quiet.RPM β) (events : List Event) :
    ((x >>= f).run.run events) = match x.run.run events with
      | (.ok a, events') => (f a).run.run events'
      | (.error e, events') => (.error e, events') := by
  simp only [ExceptT.run_bind, StateT.run_bind]
  rcases x.run.run events with ⟨result, events'⟩
  cases result <;> rfl

theorem recordedRun_nil (version : Version) (parser : ScriptParser (List Event))
    (events : List Event) : recordedRun version parser [] events = events.reverse := rfl

theorem recordedRun_cons (version : Version) (parser : ScriptParser (List Event))
    (token : Parser.Internal.Input) (tokens : List Parser.Internal.Input) (events : List Event) :
    recordedRun version parser (token :: tokens) events =
      match (recAfter version parser token).run.run events with
      | (.ok (.inl (version', parser')), events') => recordedRun version' parser' tokens events'
      | (_, events') => events'.reverse := by
  unfold recordedRun
  rw [driveParse_cons, run_bind_split]
  rcases (recAfter version parser token).run.run events with ⟨result, events'⟩
  rcases result with _ | (⟨version', parser'⟩ | result) <;> rfl

theorem countP_silent {p : Event → Bool} (hp : ∀ e, Quiet.isPoint e = false → p e = false)
    {silent : List Event} (hsilent : ∀ e ∈ silent, Quiet.isPoint e = false) :
    silent.countP p = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  simp [hp e (hsilent e he)]

theorem arrivalCalls_countP {p : Event → Bool}
    (hp : ∀ signature, p (.call .nothing (.startRecursiveBody signature)) = false)
    (parser : ScriptParser (List Event)) (token : Parser.Internal.Input) :
    (arrivalCalls parser token).countP p = 0 := by
  unfold arrivalCalls
  split
  · simp
  · split
    · split
      · split <;> (try simp) <;> exact hp _
      · simp
    · simp

/-- The calls due at an item's arrival process no item. -/
theorem arrivalCalls_processed (parser : ScriptParser (List Event))
    (token : Parser.Internal.Input) :
    (arrivalCalls parser token).reverse.filterMap Event.processed = [] := by
  unfold arrivalCalls
  split
  · rfl
  · split
    · split
      · split <;> rfl
      · rfl
    · rfl

/-- A `)` gets no call due at its arrival. -/
theorem arrivalCalls_parenClose (parser : ScriptParser (List Event)) :
    arrivalCalls parser .parenClose = [] := rfl

/-- The calls due at an item's arrival depend on the item only in whether it is a `)`. -/
theorem arrivalCalls_congr (parser : ScriptParser
    (List Event)) {token token' : Parser.Internal.Input}
    (h : token ≠ .parenClose) (h' : token' ≠ .parenClose) :
    arrivalCalls parser token = arrivalCalls parser token' := by
  cases token <;> cases token' <;> first | rfl | exact absurd rfl h | exact absurd rfl h'

/-- After an item, one more arrival and one more processing. -/
theorem afterToken_counts (version : Version) (parser : ScriptParser (List Event))
    {token : Parser.Internal.Input} {received : Received}
        (htoken : Bridge.received token = some received)
    (events : List Event) :
    ((recAfter version parser token).run.run events).2.reverse.countP isArrival =
        events.reverse.countP isArrival + 1 ∧
      ((recAfter version parser token).run.run events).2.reverse.countP isProcessing =
        events.reverse.countP isProcessing + 1 := by
  obtain ⟨silent, hstate, hsilent⟩ := afterToken_shape version parser htoken events
  rw [hstate]
  have h₁ := countP_silent (p := isArrival)
    (fun e he => by cases e <;> simp_all [Quiet.isPoint, isArrival]) hsilent
  have h₂ := countP_silent (p := isProcessing)
    (fun e he => by cases e <;> simp_all [Quiet.isPoint, isProcessing]) hsilent
  have h₃ := arrivalCalls_countP (p := isArrival) (fun _ => rfl) parser token
  have h₄ := arrivalCalls_countP (p := isProcessing) (fun _ => rfl) parser token
  simp only [List.countP_reverse, List.countP_append, h₁, h₂, h₃, h₄]
  simp [isArrival, isProcessing]
  omega
theorem recordedRun_grows : (items : List Parser.Internal.Input) → NoLayout items →
    ∀ (version : Version) (parser : ScriptParser (List Event)) (events : List Event),
    ∃ more, recordedRun version parser items events = events.reverse ++ more
  | [], _, version, parser, events => ⟨[], by simp [recordedRun_nil]⟩
  | token :: tokens, hlayout, version, parser, events => by
    obtain ⟨received, hreceived⟩ := Option.ne_none_iff_exists'.mp
      (hlayout token (List.mem_cons_self ..))
    obtain ⟨silent, hstate, -⟩ := afterToken_shape version parser hreceived events
    rw [recordedRun_cons]
    rcases hrun : (recAfter version parser token).run.run events with ⟨result, events'⟩
    have hevents : events' = silent ++ [.process received] ++ arrivalCalls parser token ++
        [.arrive received] ++ events := by
      rw [← hstate, hrun]
    subst hevents
    have hreverse : (silent ++ [Event.process received] ++ arrivalCalls parser token ++
        [Event.arrive received] ++
        events).reverse =
          events.reverse ++ (.arrive received :: ((arrivalCalls parser token).reverse ++
          .process received :: silent.reverse)) := by simp
    rcases result with _ | (⟨version', parser'⟩ | _)
    · exact ⟨_, hreverse⟩
    · obtain ⟨more, hmore⟩ := recordedRun_grows tokens
        (fun t ht => hlayout t (List.mem_cons_of_mem _ ht)) version' parser'
        (silent ++ [.process received] ++ arrivalCalls parser token ++ [.arrive received] ++ events)
      exact ⟨_, by dsimp only; rw [hmore, hreverse, List.append_assoc]⟩
    · exact ⟨_, hreverse⟩

/-- The events of a run from an item on: its arrival, the calls due at it, its processing, then
the rest. -/
theorem recordedRun_cons_form (version : Version) (parser : ScriptParser (List Event))
    {token : Parser.Internal.Input} {received : Received}
        (hreceived : Bridge.received token = some received)
    {tokens : List Parser.Internal.Input} (hlayout : NoLayout tokens) (events : List Event) :
    ∃ rest, recordedRun version parser (token :: tokens) events =
      events.reverse ++ .arrive received :: ((arrivalCalls parser token).reverse ++
        .process received :: rest) := by
  obtain ⟨silent, hstate, -⟩ := afterToken_shape version parser hreceived events
  rw [recordedRun_cons]
  rcases hrun : (recAfter version parser token).run.run events with ⟨result, events'⟩
  have hevents : events' = silent ++ [.process received] ++ arrivalCalls parser token ++
      [.arrive received] ++ events := by
    rw [← hstate, hrun]
  subst hevents
  have hreverse : (silent ++ [Event.process received] ++ arrivalCalls parser token ++
      [Event.arrive received] ++
      events).reverse =
        events.reverse ++ (.arrive received :: ((arrivalCalls parser token).reverse ++
        .process received :: silent.reverse)) := by simp
  rcases result with _ | (⟨version', parser'⟩ | _)
  · exact ⟨silent.reverse, by dsimp only; rw [hreverse]⟩
  · obtain ⟨more, hmore⟩ := recordedRun_grows tokens hlayout version' parser'
      (silent ++ [.process received] ++ arrivalCalls parser token ++ [.arrive received] ++ events)
    refine ⟨silent.reverse ++ more, ?_⟩
    dsimp only
    rw [hmore, hreverse]
    simp
  · exact ⟨silent.reverse, by dsimp only; rw [hreverse]⟩

theorem take_succ_cons {α : Type} {a : α} {as bs : List α} {k : Nat}
    (h : (a :: as).take (k + 1) = bs.take (k + 1)) :
    ∃ bs', bs = a :: bs' ∧ as.take k = bs'.take k := by
  cases bs with
  | nil => simp at h
  | cons b bs' =>
    simp only [List.take_succ_cons, List.cons.injEq] at h
    exact ⟨bs', by rw [h.1], h.2⟩

/--
Two runs whose items agree before the item at position `k` have written the same events before
that item arrives.
-/
theorem recordedRun_eventsBefore : (k : Nat) →
    ∀ (version : Version) (parser : ScriptParser (List Event))
      (items items' : List Parser.Internal.Input) (events : List Event),
          NoLayout items → NoLayout items' →
    items.take k = items'.take k →
    eventsBefore (events.reverse.countP isArrival + k) (recordedRun version parser items events) =
      eventsBefore (events.reverse.countP isArrival + k)
        (recordedRun version parser items' events)
  | 0, version, parser, items, items', events, hlayout, hlayout', _ => by
    have hbase : ∀ items, NoLayout items →
        eventsBefore (events.reverse.countP isArrival + 0)
          (recordedRun version parser items events) = events.reverse := by
      intro items hlayout
      cases items with
      | nil => simpa [recordedRun_nil, eventsBefore] using eventsBefore_append events.reverse [] 0
      | cons token tokens =>
        obtain ⟨received, hreceived⟩ := Option.ne_none_iff_exists'.mp
          (hlayout token (List.mem_cons_self ..))
        obtain ⟨rest, hrest⟩ := recordedRun_cons_form version parser hreceived
          (fun t ht => hlayout t (List.mem_cons_of_mem _ ht)) events
        rw [hrest, eventsBefore_append]
        simp [eventsBefore]
    rw [hbase items hlayout, hbase items' hlayout']
  | k + 1, version, parser, items, items', events, hlayout, hlayout', htake => by
    cases items with
    | nil =>
      have : items' = [] := by simpa using htake.symm
      subst this
      rfl
    | cons token tokens =>
      obtain ⟨tokens', rfl, htake'⟩ := take_succ_cons htake
      obtain ⟨received, hreceived⟩ := Option.ne_none_iff_exists'.mp
        (hlayout token (List.mem_cons_self ..))
      have hcount := (afterToken_counts version parser hreceived events).1
      rw [recordedRun_cons, recordedRun_cons]
      rcases hrun : (recAfter version parser token).run.run events with ⟨result, events'⟩
      rw [hrun] at hcount
      rcases result with _ | (⟨version', parser'⟩ | _)
      · rfl
      · simp only at hcount ⊢
        rw [show events.reverse.countP isArrival + (k + 1) =
          events'.reverse.countP isArrival + k by omega]
        exact recordedRun_eventsBefore k version' parser' tokens tokens' events'
          (fun t ht => hlayout t (List.mem_cons_of_mem _ ht))
          (fun t ht => hlayout' t (List.mem_cons_of_mem _ ht)) htake'
      · rfl

/-- Before a processing, with no point among them: the events before the processing. -/
theorem eventsBeforeProcessing_calls (calls : List Event) (received : Received)
    (rest : List Event) (harrive : calls.countP isArrival = 0)
    (hprocess : calls.countP isProcessing = 0) :
    eventsBeforeProcessing 0 (calls ++ .process received :: rest) = calls := by
  induction calls with
  | nil => simp [eventsBeforeProcessing]
  | cons call calls ih =>
    simp only [List.countP_cons] at harrive hprocess
    have ha : isArrival call = false := by
      cases h : isArrival call <;> simp_all
    have hp : isProcessing call = false := by
      cases h : isProcessing call <;> simp_all
    simp only [ha, hp, Bool.false_eq_true, ite_false, Nat.add_zero] at harrive hprocess
    cases call with
    | arrive => simp [isArrival] at ha
    | process => simp [isProcessing] at hp
    | _ => simp [eventsBeforeProcessing, ih harrive hprocess]

/--
Two runs whose items agree before the item at position `k`, and have an item there, have written
the same events before that item is processed, its arrival left out.
-/
theorem recordedRun_eventsBeforeProcessing : (k : Nat) →
    ∀ (version : Version) (parser : ScriptParser (List Event))
      (items items' : List Parser.Internal.Input) (events : List Event),
          NoLayout items → NoLayout items' →
    k < items.length → k < items'.length → items.take k = items'.take k →
    (items[k]? = some .parenClose ↔ items'[k]? = some .parenClose) →
    eventsBeforeProcessing (events.reverse.countP isProcessing + k)
        (recordedRun version parser items events) =
      eventsBeforeProcessing (events.reverse.countP isProcessing + k)
        (recordedRun version parser items' events)
  | 0, version, parser, items, items', events, hlayout, hlayout', hlength, hlength', _,
      hclass => by
    have hbase : ∀ token tokens, NoLayout (token :: tokens) →
        eventsBeforeProcessing (events.reverse.countP isProcessing + 0)
          (recordedRun version parser (token :: tokens) events) =
          eventsBeforeProcessing (events.reverse.countP isProcessing + 0) events.reverse ++
            (arrivalCalls parser token).reverse := by
      intro token tokens hlayout
      obtain ⟨received, hreceived⟩ := Option.ne_none_iff_exists'.mp
        (hlayout token (List.mem_cons_self ..))
      obtain ⟨rest, hrest⟩ := recordedRun_cons_form version parser hreceived
        (fun t ht => hlayout t (List.mem_cons_of_mem _ ht)) events
      rw [hrest, eventsBeforeProcessing_append]
      congr 1
      rw [eventsBeforeProcessing.eq_def]
      simp only
      apply eventsBeforeProcessing_calls
      · rw [List.countP_reverse]; exact arrivalCalls_countP (fun _ => rfl) parser token
      · rw [List.countP_reverse]; exact arrivalCalls_countP (fun _ => rfl) parser token
    cases items with
    | nil => simp at hlength
    | cons token tokens =>
      cases items' with
      | nil => simp at hlength'
      | cons token' tokens' =>
        rw [hbase token tokens hlayout, hbase token' tokens' hlayout']
        congr 2
        by_cases h : token = .parenClose
        · have h' : token' = .parenClose := by simpa using hclass.mp (by simp [h])
          rw [h, h']
        · have h' : token' ≠ .parenClose := fun h' => h (by simpa using hclass.mpr (by simp [h']))
          exact arrivalCalls_congr parser h h'
  | k + 1, version, parser, items, items', events, hlayout, hlayout', hlength, hlength',
      htake, hclass => by
    cases items with
    | nil => simp at hlength
    | cons token tokens =>
      obtain ⟨tokens', rfl, htake'⟩ := take_succ_cons htake
      obtain ⟨received, hreceived⟩ := Option.ne_none_iff_exists'.mp
        (hlayout token (List.mem_cons_self ..))
      have hcount := (afterToken_counts version parser hreceived events).2
      rw [recordedRun_cons, recordedRun_cons]
      rcases hrun : (recAfter version parser token).run.run events with ⟨result, events'⟩
      rw [hrun] at hcount
      rcases result with _ | (⟨version', parser'⟩ | _)
      · rfl
      · simp only at hcount ⊢
        rw [show events.reverse.countP isProcessing + (k + 1) =
          events'.reverse.countP isProcessing + k by omega]
        exact recordedRun_eventsBeforeProcessing k version' parser' tokens tokens' events'
          (fun t ht => hlayout t (List.mem_cons_of_mem _ ht))
          (fun t ht => hlayout' t (List.mem_cons_of_mem _ ht))
          (by simpa using hlength) (by simpa using hlength') htake' (by simpa using hclass)
      · rfl
/-! ## The parser's recording run against the traversal's -/

theorem policyOf_unrestricted : policyOf unrestrictedPosture = VersionPolicy.unrestricted := by
  simp [policyOf, unrestrictedPosture, VersionPolicy.unrestricted, Bridge.version]

/-- The recording run as the parse adapter makes it: the handler told the version first. -/
theorem driveInput_run (version : Version) (parser : ScriptParser (List Event))
    (items : List Parser.Internal.Input) :
    (driveInput recordingPoints recordingProducer version parser items).run.run [] =
      (driveParse recordingPoints recordingProducer version parser items).run.run
        (startEvents version) := by
  unfold driveInput
  exact run_bind_ok rfl

theorem noLayout_of_stands {inputs : List Parser.Internal.Input} {items : List Received}
    (hs : inputs.map Bridge.received = items.map some) : NoLayout inputs := by
  intro token htoken hnone
  have : Bridge.received token ∈ items.map some := hs ▸ List.mem_map_of_mem htoken
  simp [hnone] at this

theorem parserRecord_script {version : Version} {commands : List Tree.Command}
    (hscript : Script (Bridge.version version) commands) {inputs : List Parser.Internal.Input}
    (hs : inputs.map Bridge.received = (BSmtLibSpec.Parser.Properties.received commands).map some) :
    parserRecord version inputs = record (Bridge.version version) commands := by
  have hrun := script_correct (H := List Event) (m := Id) (points := recordingPoints)
    (h := (recordingHandlerU :
      Traversal.Handler (StateT (List Event) Id) Unit (valuesOf (List Event))))
    agrees_recording recordingProducer unrestrictedPosture hscript hs []
  rw [List.append_nil] at hrun
  unfold parserRecord recordedRun
  rw [← driveInput_run, hrun, ← record_eq_U hscript, policyOf_unrestricted]
  congr 1
  rw [state_bind_pure]
  exact state_adapt _ _ _

theorem eventsBefore_of_le : (events : List Event) → ∀ k, events.countP isArrival ≤ k →
    eventsBefore k events = events
  | [], _, _ => by simp [eventsBefore]
  | event :: events, k, h => by
    cases event with
    | arrive item =>
      simp only [List.countP_cons, isArrival, ite_true] at h
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [eventsBefore, eventsBefore_of_le events k (by omega)]
    | _ =>
      simp only [List.countP_cons, isArrival, Bool.false_eq_true, ite_false, Nat.add_zero] at h
      rw [eventsBefore.eq_def]
      simp [eventsBefore_of_le events k h]

theorem recordedRun_arrivals : (items : List Parser.Internal.Input) → NoLayout items →
    ∀ (version : Version) (parser : ScriptParser (List Event)) (events : List Event),
    (recordedRun version parser items events).countP isArrival ≤
      events.reverse.countP isArrival + items.length
  | [], _, version, parser, events => by simp [recordedRun_nil]
  | token :: tokens, hlayout, version, parser, events => by
    obtain ⟨received, hreceived⟩ := Option.ne_none_iff_exists'.mp
      (hlayout token (List.mem_cons_self ..))
    have hcount := (afterToken_counts version parser hreceived events).1
    rw [recordedRun_cons]
    rcases hrun : (recAfter version parser token).run.run events with ⟨result, events'⟩
    rw [hrun] at hcount
    simp only at hcount
    rcases result with _ | (⟨version', parser'⟩ | _)
    · simp only [List.length_cons]; omega
    · have := recordedRun_arrivals tokens (fun t ht => hlayout t (List.mem_cons_of_mem _ ht))
        version' parser' events'
      simp only [List.length_cons]
      omega
    · simp only [List.length_cons]; omega

/--
What the parser has done before the item at position `k` arrives, on any input that agrees
with what a parser receives for a valid script before that item, is what the traversal of the
script has done before it.
-/
theorem placement_arrival {version : Version} {commands : List Tree.Command}
    (hscript : Script (Bridge.version version) commands) {inputs : List Parser.Internal.Input}
    (hs : inputs.map Bridge.received = (BSmtLibSpec.Parser.Properties.received commands).map some)
    {items : List Parser.Internal.Input} (hlayout : NoLayout items) (k : Nat)
    (htake : items.take k = inputs.take k) :
    eventsBefore k (parserRecord version items) =
      eventsBefore k (record (Bridge.version version) commands) := by
  rw [← parserRecord_script hscript hs]
  have := recordedRun_eventsBefore k version (ScriptParser.new unrestrictedPosture) items inputs
    (startEvents version) hlayout (noLayout_of_stands hs) htake
  simpa [parserRecord, isArrival] using this

/--
What the parser has done before the item at position `k` is processed, its arrival left out, on
any input that agrees with what a parser receives for a valid script before that item and has an
item there that is a `)` where the script's is and only there, is what the traversal of the
script has done before that item is processed.
-/
theorem placement_processing {version : Version} {commands : List Tree.Command}
    (hscript : Script (Bridge.version version) commands) {inputs : List Parser.Internal.Input}
    (hs : inputs.map Bridge.received = (BSmtLibSpec.Parser.Properties.received commands).map some)
    {items : List Parser.Internal.Input} (hlayout : NoLayout items) (k : Nat)
        (hk : k < items.length)
    (hk' : k < inputs.length) (htake : items.take k = inputs.take k)
    (hclass : items[k]? = some .parenClose ↔ inputs[k]? = some .parenClose) :
    eventsBeforeProcessing k (parserRecord version items) =
      eventsBeforeProcessing k (record (Bridge.version version) commands) := by
  rw [← parserRecord_script hscript hs]
  have := recordedRun_eventsBeforeProcessing k version (ScriptParser.new unrestrictedPosture)
    items inputs (startEvents version) hlayout (noLayout_of_stands hs) hk hk'
    htake hclass
  simpa [parserRecord, isProcessing] using this

/--
Where its input stops before the item at position `k` of what a parser receives for a valid
script, the parser has done what the traversal of the script does before that item arrives.
-/
theorem placement_prefix {version : Version} {commands : List Tree.Command}
    (hscript : Script (Bridge.version version) commands) {inputs : List Parser.Internal.Input}
    (hs : inputs.map Bridge.received = (BSmtLibSpec.Parser.Properties.received commands).map some)
    (k : Nat) :
    parserRecord version (inputs.take k) =
      eventsBefore k (record (Bridge.version version) commands) := by
  have hlayout : NoLayout (inputs.take k) := fun t ht =>
    noLayout_of_stands hs t (List.mem_of_mem_take ht)
  rw [← placement_arrival hscript hs hlayout k (List.take_take .. ▸ by simp)]
  symm
  apply eventsBefore_of_le
  have := recordedRun_arrivals (inputs.take k) hlayout version
    (ScriptParser.new unrestrictedPosture) (startEvents version)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.countP_singleton,
    isArrival, Bool.false_eq_true, ite_false, Nat.zero_add] at this
  exact Nat.le_trans this (List.length_take_le _ _)

end BSmtLib.Facts.Proofs.Parser.Cut
