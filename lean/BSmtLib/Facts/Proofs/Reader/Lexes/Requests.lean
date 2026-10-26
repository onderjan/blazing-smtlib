module

public import BSmtLib.Facts.Proofs.Reader.Param.Link

@[expose] public section

/-!
# The parser as a consumer of the formalism, and the script consumer

After each item, the library's parser asks its producer for at most one thing: a version switch or
discarding (`recAfter_single`). So what its run asked for after its last item is read alike whether
the first request or the last one counts (`requests_parse`), and the parser as a consumer in the
specification formalism (`BSmtLibSpec`), `BSmtLibSpec.Reader.consumer` with the item `libItem` for
each token, answers and asks as the script consumer `scriptConsumer` does (`consumer_agrees`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Lexes.Requests

open BSmtLibSpec BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Parser.Adapters.Run.Rejection BSmtLib.Facts.Proofs.Parser.Cut
open BSmtLib.Facts.Proofs.Parser.Rejection.Script BSmtLib.Facts.Proofs.Parser.Trace
open BSmtLib.Facts.Proofs.Reader.Param.Adapter BSmtLib.Facts.Proofs.Reader.Param.Erase
open BSmtLib.Facts.Proofs.Reader.Param.EraseSteps BSmtLib.Facts.Proofs.Reader.Param.Link
open BSmtLib.Facts.Reader.Adapters

/-! ## Reading the requests -/

/-- One event of the fold in `BSmtLibSpec.Reader.requestsAfterLast`. -/
def reqStep (event : Event) (requests : Option Lexicon.Version × Bool) :
    Option Lexicon.Version × Bool :=
  match event with
  | .producerSwitch version => (some version, requests.2)
  | .producerDiscard => (requests.1, true)
  | _ => requests

theorem processed_isNone_eq : (fun event : Event => event.processed.isNone) =
    (fun event => !isProcessing event) := by
  funext event
  cases event <;> rfl

theorem requestsAfterLast_eq (events : List Event) :
    BSmtLibSpec.Reader.requestsAfterLast events =
      (afterLastProcess events).foldl (fun acc e => reqStep e acc) (none, false) := by
  unfold BSmtLibSpec.Reader.requestsAfterLast afterLastProcess
  rw [processed_isNone_eq, List.foldl_reverse]
  rfl

theorem quiet_switchIn {L : List Event} (h : L.filter isProducer = []) :
    switchIn L = none ∧ discardIn L = false := by
  have hq : ∀ e ∈ L, isProducer e = false := by
    intro e he
    cases hp : isProducer e
    · rfl
    · have : e ∈ L.filter isProducer := List.mem_filter.mpr ⟨he, hp⟩
      rw [h] at this
      cases this
  have h₁ := switchIn_append_quiet (Y := []) hq
  have h₂ := discardIn_append_quiet (Y := []) hq
  rw [List.append_nil] at h₁ h₂
  exact ⟨h₁, h₂⟩

theorem foldl_reqStep : ∀ (L : List Event) (acc : Option Lexicon.Version × Bool),
    (L.filter isProducer).length ≤ 1 →
    L.foldl (fun acc e => reqStep e acc) acc = ((switchIn L).or acc.1, acc.2 || discardIn L)
  | [], acc, _ => by simp [switchIn, discardIn]
  | e :: L, acc, h => by
    rw [List.foldl_cons]
    cases e with
    | producerSwitch v =>
      simp only [List.filter_cons, isProducer, ite_true, List.length_cons] at h
      have hL : L.filter isProducer = [] := List.length_eq_zero_iff.mp (by omega)
      obtain ⟨hs, hd⟩ := quiet_switchIn hL
      rw [foldl_reqStep L _ (by rw [hL]; simp)]
      have e₁ : switchIn (.producerSwitch v :: L) = some v := rfl
      have e₂ : discardIn (.producerSwitch v :: L) = discardIn L := rfl
      rw [e₁, e₂, hs, hd]
      rfl
    | producerDiscard =>
      simp only [List.filter_cons, isProducer, ite_true, List.length_cons] at h
      have hL : L.filter isProducer = [] := List.length_eq_zero_iff.mp (by omega)
      obtain ⟨hs, hd⟩ := quiet_switchIn hL
      rw [foldl_reqStep L _ (by rw [hL]; simp)]
      have e₁ : switchIn (.producerDiscard :: L) = switchIn L := rfl
      have e₂ : discardIn (.producerDiscard :: L) = true := rfl
      rw [e₁, e₂, hs, hd]
      simp [reqStep]
    | arrive r =>
      show L.foldl _ acc = _
      rw [foldl_reqStep L acc (by simpa [isProducer] using h)]
      rfl
    | process r =>
      show L.foldl _ acc = _
      rw [foldl_reqStep L acc (by simpa [isProducer] using h)]
      rfl
    | call returns request =>
      show L.foldl _ acc = _
      rw [foldl_reqStep L acc (by simpa [isProducer] using h)]
      rfl
    | handlerSwitch v =>
      show L.foldl _ acc = _
      rw [foldl_reqStep L acc (by simpa [isProducer] using h)]
      rfl

/-- Where at most one request follows the last processing, the first and the last request are
the same. -/
theorem requestsAfterLast_of_single {events : List Event}
    (h : ((afterLastProcess events).filter isProducer).length ≤ 1) :
    BSmtLibSpec.Reader.requestsAfterLast events = (switchOf events, discardOf events) := by
  rw [requestsAfterLast_eq, foldl_reqStep _ _ h, switchOf_eq_switchIn, discardOf_eq_discardIn]
  simp

/-! ## At most one request after an item -/

/-- A log, latest event first, with at most one request of the producer after its last
processing. -/
def Single (log : List Event) : Prop :=
  ((log.takeWhile fun e => !isProcessing e).filter isProducer).length ≤ 1

theorem single_shape {pre rest : List Event} (r : Received)
    (hpre : ∀ e ∈ pre, isProcessing e = false) (hp : (pre.filter isProducer).length ≤ 1) :
    Single (pre ++ .process r :: rest) := by
  unfold Single
  rw [List.takeWhile_append_of_pos (by simpa using hpre)]
  simpa [isProcessing] using hp

theorem calls_quiet {added : List Event} (h : ∀ e ∈ added, e.isCall = true) :
    (∀ e ∈ added, isProcessing e = false) ∧ added.filter isProducer = [] := by
  refine ⟨fun e he => isProcessing_of_isCall (h e he), ?_⟩
  rw [List.filter_eq_nil_iff]
  intro e he
  have := h e he
  cases e <;> simp_all [Event.isCall, isProducer]

theorem single_calls {added : List Event} (h : ∀ e ∈ added, e.isCall = true) (r : Received)
    (rest : List Event) : Single (added ++ .process r :: rest) := by
  obtain ⟨h₁, h₂⟩ := calls_quiet h
  exact single_shape r h₁ (by rw [h₂]; simp)

theorem single_request {added added' : List Event} (h : ∀ e ∈ added, e.isCall = true)
    (h' : ∀ e ∈ added', e.isCall = true) (request : Event) (hreq : isProcessing request = false)
    (r : Received) (rest : List Event) :
    Single (added' ++ request :: (added ++ .process r :: rest)) := by
  obtain ⟨h₁, h₂⟩ := calls_quiet h
  obtain ⟨h₁', h₂'⟩ := calls_quiet h'
  rw [show added' ++ request :: (added ++ .process r :: rest) =
    (added' ++ request :: added) ++ .process r :: rest by simp]
  refine single_shape r ?_ ?_
  · intro e he
    simp only [List.mem_append, List.mem_cons] at he
    rcases he with he | rfl | he
    · exact h₁' e he
    · exact hreq
    · exact h₁ e he
  · simp only [List.filter_append, List.filter_cons, h₂, h₂', List.nil_append]
    split <;> simp

/-- After an item, the recording run asks its producer for at most one thing. -/
theorem recAfter_single (version : Version) (parser : ScriptParser (List Event))
    {item : Parser.Internal.Input}
    {received : Received} (hr : Bridge.received item = some received) (events : List Event) :
    Single ((recAfter version parser item).run.run events).2 := by
  rw [recAfter_eq _ _ hr]
  have hE := scriptStep_erasing version parser item
  obtain ⟨added, hlog, hcalls⟩ :=
    hE.adds (.process received :: (arrivalCalls parser item ++ .arrive received :: events))
  have hpost :=
    hE.post (.process received :: (arrivalCalls parser item ++ .arrive received :: events))
  rcases hS : (Parser.Internal.ParseByToken.step (H := List Event) version parser item).run.run
    (.process received :: (arrivalCalls parser item ++ .arrive received :: events)) with ⟨res, log₀⟩
  rw [hS] at hlog hpost
  simp only at hlog hpost
  subst hlog
  unfold afterProcessing
  rcases res with e | flow
  · rw [run_bind_error hS]
    exact single_calls hcalls _ _
  · rw [run_bind_ok hS]
    cases flow with
    | more p => exact single_calls hcalls _ _
    | done result => exact single_calls hcalls _ _
    | switchVersion declared resume =>
      have hres : Erases resume := hpost (.switchVersion declared resume) rfl
      have hset : ((ExceptT.lift (recordingProducer.setVersion (Bridge.version declared)).run :
          Parser.Quiet.RPM (Except Traversal.VersionRefused Unit)).run.run
          (added ++ .process received ::
            (arrivalCalls parser item ++ .arrive received :: events))) =
          (.ok (.ok ()), .producerSwitch (Bridge.version declared) ::
            (added ++ .process received ::
              (arrivalCalls parser item ++ .arrive received :: events))) :=
            rfl
      rw [run_bind_ok hset]
      obtain ⟨added', hlog', hcalls'⟩ := hres.adds (.producerSwitch (Bridge.version declared) ::
        (added ++ .process received :: (arrivalCalls parser item ++ .arrive received :: events)))
      rcases hR : resume.run.run (.producerSwitch (Bridge.version declared) ::
        (added ++ .process received ::
          (arrivalCalls parser item ++ .arrive received :: events))) with
        ⟨res₂, log₂⟩
      rw [hR] at hlog'
      simp only at hlog'
      subst hlog'
      have hsingle := single_request hcalls hcalls' (.producerSwitch (Bridge.version declared))
        rfl received (arrivalCalls parser item ++ .arrive received :: events)
      rcases res₂ with e | step
      · simp only [run_bind_error hR]
        exact hsingle
      · simp only [run_bind_ok hR]
        cases step with
        | more p => exact hsingle
        | done r => exact hsingle
    | discardRest resume =>
      have hres : Erases resume := hpost (.discardRest resume) rfl
      have hdisc : ((ExceptT.lift recordingProducer.discardRest : Parser.Quiet.RPM Unit).run.run
          (added ++ .process received ::
            (arrivalCalls parser item ++ .arrive received :: events))) =
          (.ok (), .producerDiscard ::
            (added ++ .process received ::
              (arrivalCalls parser item ++ .arrive received :: events))) :=
            rfl
      rw [run_bind_ok hdisc]
      obtain ⟨added', hlog', hcalls'⟩ := hres.adds (.producerDiscard ::
        (added ++ .process received :: (arrivalCalls parser item ++ .arrive received :: events)))
      rcases hR : resume.run.run (.producerDiscard ::
        (added ++ .process received ::
          (arrivalCalls parser item ++ .arrive received :: events))) with
        ⟨res₂, log₂⟩
      rw [hR] at hlog'
      simp only at hlog'
      subst hlog'
      have hsingle := single_request hcalls hcalls' .producerDiscard rfl received
        (arrivalCalls parser item ++ .arrive received :: events)
      rcases res₂ with e | step
      · simp only [run_bind_error hR]
        exact hsingle
      · simp only [run_bind_ok hR]
        cases step with
        | more p => exact hsingle
        | done r => exact hsingle

/-- The driver's run over items, from a log with at most one request after its last processing
if there are no items: its log has at most one request after its last processing. -/
theorem driveScript_single : ∀ (items : List LibItem) (version : Version)
    (parser : ScriptParser (List Event)) (events : List Event), (items = [] → Single events) →
    Single ((driveScript version parser (items.map Subtype.val)).run.run events).2
  | [], _, _, events, h => h rfl
  | item :: items, version, parser, events, _ => by
    obtain ⟨received, hr⟩ := Option.ne_none_iff_exists'.mp item.2
    simp only [List.map_cons, driveScript]
    rw [run_bind_split]
    have hs := recAfter_single version parser hr events
    rcases hrun : (recAfter version parser item.val).run.run events with ⟨res, log⟩
    rw [hrun] at hs
    rcases res with e | (⟨v', p'⟩ | u)
    · exact hs
    · exact driveScript_single items v' p' log fun _ => hs
    · exact hs

/-- The library's parser's run asks its producer for at most one thing after its last
processing. -/
theorem parse_single (version : Lexicon.Version) (items : List LibItem) :
    ((afterLastProcess (libraryParser.parse version items).1).filter isProducer).length ≤ 1 := by
  rw [parse_recRun]
  have hs := driveScript_single items (Bridge.libVersion version)
    (ScriptParser.new unrestrictedPosture) (startEvents (Bridge.libVersion version))
    (fun _ => by simp [Single, startEvents, isProcessing, isProducer])
  unfold recRun
  unfold Single at hs
  unfold afterLastProcess
  rw [List.reverse_reverse, List.filter_reverse, List.length_reverse]
  exact hs

/-- What the library's parser's run asked of its producer after its last item, read with the
last request counting, is what the first request says. -/
theorem requests_parse (version : Lexicon.Version) (items : List LibItem) :
    BSmtLibSpec.Reader.requestsAfterLast (libraryParser.parse version items).1 =
      (switchOf (libraryParser.parse version items).1,
        discardOf (libraryParser.parse version items).1) :=
  requestsAfterLast_of_single (parse_single version items)

/-! ## The two consumers -/

/-- The library's parser as a consumer in the formalism. -/
abbrev specConsumer (version : Lexicon.Version) : BSmtLibSpec.Lexer.Consumer :=
  Reader.consumer libraryParser libItem version

/-- Two consumers in the formalism that answer alike: the same kind of answer, the
same switch and discarding, and both take whitespace and comments or neither. -/
structure AnswersAlike (c₁ c₂ : BSmtLibSpec.Lexer.Consumer) : Prop where
  concrete : c₁.concrete = c₂.concrete
  switchTo : c₁.switchTo = c₂.switchTo
  discards : c₁.discards = c₂.discards
  fail : ∀ taken e, c₁.answer taken = .fail e → ∃ e', c₂.answer taken = .fail e'
  brk : ∀ taken r, c₁.answer taken = .break r → ∃ r', c₂.answer taken = .break r'
  cont : ∀ taken, c₁.answer taken = .continue → c₂.answer taken = .continue
  fail' : ∀ taken e, c₂.answer taken = .fail e → ∃ e', c₁.answer taken = .fail e'
  brk' : ∀ taken r, c₂.answer taken = .break r → ∃ r', c₁.answer taken = .break r'
  cont' : ∀ taken, c₂.answer taken = .continue → c₁.answer taken = .continue

/-- The script consumer and the library's parser as a consumer of the formalism answer
alike. -/
theorem consumer_agrees (version : Lexicon.Version) :
    AnswersAlike (scriptConsumer version) (specConsumer version) := by
  have hreq : ∀ taken : List Handed,
      BSmtLibSpec.Reader.requestsAfterLast (libraryParser.parse version (taken.map libItem)).1 =
        ((scriptConsumer version).switchTo taken, (scriptConsumer version).discards taken) :=
    fun taken => requests_parse version (taken.map libItem)
  refine ⟨rfl, funext fun taken => ?_, funext fun taken => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show _ = (BSmtLibSpec.Reader.requestsAfterLast _).1
    rw [hreq]
  · show _ = (BSmtLibSpec.Reader.requestsAfterLast _).2
    rw [hreq]
  all_goals
    intro taken
    have h₁ : (scriptConsumer version).answer taken =
        answerOf (decide (taken.getLast?.map (·.type) = some .endOfFile))
          (libraryParser.parse version (taken.map libItem)).2 := rfl
    have h₂ : (specConsumer version).answer taken =
        match (libraryParser.parse version (taken.map libItem)).2 with
        | .finished => .break ()
        | .waiting =>
          if taken.getLast?.map (·.type) = some .endOfFile then .fail () else .continue
        | .rejected | .failed _ => .fail () := rfl
    rw [h₁, h₂]
    generalize (libraryParser.parse version (taken.map libItem)).2 = ending
    by_cases hc : taken.getLast?.map (·.type) = some .endOfFile <;>
      cases ending <;> simp only [answerOf, hc, decide_true, decide_false, ite_true,
        ite_false, Bool.false_eq_true] <;>
      first
        | (intro _ _; exact ⟨_, rfl⟩)
        | (intro _ h; cases h; done)
        | (intro _; rfl)
        | (intro h; cases h; done)
        | (intro _; trivial)

end BSmtLib.Facts.Proofs.Reader.Lexes.Requests
