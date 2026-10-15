module

public import BSmtLib.Facts.Proofs.Parser.Rejection.Lexical
public import BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
public import BSmtLib.Facts.Proofs.Parser.RefusedRecord
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Command
import all BSmtLib.Parser.Command.Internal.Function
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Parser.Script
import all BSmtLib.Plain
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# The library's parser as a recording parser

The library's script parser, run by its driver in a recording run under the posture that
restricts nothing, as a `BSmtLibSpec.Parser.Properties.RecordingParser`: its items are the parser's
tokens other than whitespace and comments, each standing for what `Bridge.received` says, and its
run ends as its result says: waiting where the items run out, finished, failed on a version
declaration, or rejected with any other cause.

The two properties of where a parser rejects its input are proved from the two sides proved
before: on what a parser takes, the parser does what the traversal does (`parserRecord_takes`,
`parserResult_takes`), and every item the parser takes keeps what it has taken viable
(`script_runs`, `recAfter_post`); that what a parser takes for some commands is no proper start
of what it takes for others (`takes_prefix`) ties the two together.
-/

namespace BSmtLib.Facts.Proofs.Parser.Rejection.Library

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Bridge.Rejection
open BSmtLib.Facts.Parser.Adapters.Run BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Facts.Proofs.Parser.Cut BSmtLib.Facts.Proofs.Parser.RefusedRecord
open BSmtLib.Facts.Proofs.Parser.Rejection.Basic BSmtLib.Facts.Proofs.Parser.Rejection.Lexical
open BSmtLib.Facts.Proofs.Parser.Rejection.Payload BSmtLib.Facts.Proofs.Parser.Rejection.Script
open BSmtLib.Facts.Proofs.Parser.Rejection.Unique BSmtLib.Facts.Proofs.Parser.Script
open BSmtLib.Facts.Proofs.Parser.Tokens BSmtLib.Plain

theorem libEnding_benign {e : Parser.ParseErrorCause Unit} (h : Benign e) :
    libEnding (.error e) = .rejected := by
  rcases e with (_ | _) | _ <;> first | rfl | exact absurd h id

/-! ## Runs over items -/

theorem noLayout_items (items : List LibItem) : NoLayout (items.map Subtype.val) := by
  intro token htoken
  obtain ⟨item, -, rfl⟩ := List.mem_map.mp htoken
  exact item.2

theorem map_rcv (items : List LibItem) :
    (items.map Subtype.val).map rcv = items.map (rcv ∘ Subtype.val) := by
  rw [List.map_map]

theorem received_items {items : List LibItem} {taken : List Received}
    (h : items.map (rcv ∘ Subtype.val) = taken) :
    (items.map Subtype.val).map Bridge.received = taken.map some := by
  rw [← h, List.map_map, List.map_map]
  apply List.map_congr_left
  intro item _
  exact received_rcv item.2

theorem scriptInv_new (version : Token.Version) :
    ScriptInv (Bridge.version version) [] version (ScriptParser.new unrestrictedPosture) :=
  ⟨rfl, Or.inl ⟨[], [], .nil, rfl, cmdInv_awaiting _ _ markers_nonempty,
    cmdInv_awaiting _ _ scriptFollows_nonempty⟩⟩

/-- The run of the driver, through `driveScript`. -/
theorem driveParse_run (version : Token.Version) (parser : ScriptParser (List Event))
    (items : List Parser.Internal.Input) (events : List Event) :
    (driveParse recordingPoints recordingProducer version parser items).run.run events =
      match (driveScript version parser items).run.run events with
      | (.ok (.inl _), events') => (.ok none, events')
      | (.ok (.inr result), events') => (.ok (some result), events')
      | (.error e, events') => (.error e, events') := by
  rw [driveParse_eq_driveScript, run_bind_split]
  rcases (driveScript version parser items).run.run events with ⟨_ | _ | _, events'⟩ <;> rfl

/-- A run that fails over the first items fails over more. -/
theorem driveScript_fails {version : Token.Version} {parser : ScriptParser (List Event)}
    {items more : List Parser.Internal.Input} {events events' : List Event}
        {e : Parser.ParseErrorCause Unit}
    (h : (driveScript version parser items).run.run events = (.error e, events')) :
    (driveScript version parser (items ++ more)).run.run events = (.error e, events') := by
  rw [driveScript_append, run_bind_split, h]

/-- A run that finishes over the first items finishes over more, before them. -/
theorem driveScript_finishes {version : Token.Version} {parser : ScriptParser (List Event)}
    {items more : List Parser.Internal.Input} {events events' : List Event}
        {rest : List Parser.Internal.Input}
    (h : (driveScript version parser items).run.run events = (.ok (.inr ((), rest)), events')) :
    (driveScript version parser (items ++ more)).run.run events =
      (.ok (.inr ((), rest ++ more)), events') := by
  rw [driveScript_append, run_bind_split, h]
  rfl

/-- A run that goes on over the first items goes on over more from where it is. -/
theorem driveScript_goes_on {version version' : Token.Version}
    {parser parser' : ScriptParser (List Event)} {items more : List Parser.Internal.Input}
    {events events' : List Event}
    (h : (driveScript version parser items).run.run events =
      (.ok (.inl (version', parser')), events')) :
    (driveScript version parser (items ++ more)).run.run events =
      (driveScript version' parser' more).run.run events' := by
  rw [driveScript_append, run_bind_split, h]

/-- The events of the driver's run are those of `driveScript`. -/
theorem recordedRun_driveScript (version : Token.Version) (parser : ScriptParser (List Event))
    (items : List Parser.Internal.Input) (events : List Event) :
    recordedRun version parser items events =
      ((driveScript version parser items).run.run events).2.reverse := by
  unfold recordedRun
  rw [driveParse_run]
  rcases (driveScript version parser items).run.run events with ⟨_ | _ | _, events'⟩ <;> rfl

/-- Tokens that stand for items are taken as those items. -/
theorem map_rcv_of_received {inputs : List Parser.Internal.Input} {taken : List Received}
    (h : inputs.map Bridge.received = taken.map some) : inputs.map rcv = taken := by
  have := congrArg (List.map fun r => r.getD Received.endOfInput) h
  simp only [List.map_map, Function.comp_def, Option.getD_some, List.map_id'] at this
  exact this

/-- Where its input stops before the item at position `count` of what a parser takes, the parser
has done what the traversal does before that item arrives. -/
theorem placement_prefix_takes {version : Token.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending}
    (htakes : Takes
        (Bridge.version version) commands taken ending) {inputs : List Parser.Internal.Input}
    (hs : inputs.map Bridge.received = taken.map some) (count : Nat) :
    parserRecord version (inputs.take count) =
      eventsBefore count (record (Bridge.version version) commands) := by
  have hlayout : NoLayout (inputs.take count) := fun t ht =>
    noLayout_of_stands hs t (List.mem_of_mem_take ht)
  have hplace := recordedRun_eventsBefore count version (ScriptParser.new unrestrictedPosture)
    (inputs.take count) inputs (startEvents version) hlayout (noLayout_of_stands hs)
    (List.take_take .. ▸ by simp)
  simp only [startEvents, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.countP_singleton, isArrival, Bool.false_eq_true, ite_false, Nat.zero_add] at hplace
  rw [← parserRecord_takes htakes hs]
  unfold parserRecord
  rw [← hplace]
  symm
  apply eventsBefore_of_le
  have := recordedRun_arrivals (inputs.take count) hlayout version
    (ScriptParser.new unrestrictedPosture) (startEvents version)
  simp only [startEvents, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.countP_singleton, isArrival, Bool.false_eq_true, ite_false, Nat.zero_add] at this
  exact Nat.le_trans this (List.length_take_le _ _)

/-- The items processed in a run that goes on over items are those items. -/
theorem driveScript_processed : ∀ (items : List Parser.Internal.Input), NoLayout items →
    ∀ (version : Token.Version) (parser : ScriptParser (List Event)) (events : List Event)
      {version' : Token.Version} {parser' : ScriptParser (List Event)} {events' : List Event},
    (driveScript version parser items).run.run events =
      (.ok (.inl (version', parser')), events') →
    events'.reverse.filterMap Event.processed =
      events.reverse.filterMap Event.processed ++ items.map rcv
  | [], _, version, parser, events, _, _, _, h => by
    simp only [driveScript] at h
    cases h
    simp
  | token :: tokens, hlayout, version, parser, events, _, _, _, h => by
    have hitem := received_rcv (hlayout token (List.mem_cons_self ..))
    obtain ⟨silent, hstate, hsilent⟩ := afterToken_shape version parser hitem events
    simp only [driveScript] at h
    rw [run_bind_split] at h
    rcases hrun : (recAfter version parser token).run.run events with ⟨_ | (⟨v, p⟩ | u), e⟩
    · rw [hrun] at h
      cases h
    · rw [hrun] at h
      have hrest := driveScript_processed tokens (fun t ht => hlayout t (List.mem_cons_of_mem _ ht))
        v p e h
      rw [hrest]
      have he : e = silent ++ [.process (rcv token)] ++ arrivalCalls parser token ++
          [.arrive (rcv token)] ++ events := by rw [← hstate, hrun]
      subst he
      have hs : silent.reverse.filterMap Event.processed = [] := by
        rw [List.filterMap_eq_nil_iff]
        intro ev hev
        have := hsilent ev (List.mem_reverse.mp hev)
        cases ev <;> simp_all [Quiet.isPoint, Event.processed]
      have ha := arrivalCalls_processed parser token
      simp only [List.reverse_append, List.filterMap_append, hs, ha]
      simp [Event.processed]
    · rw [hrun] at h
      cases h

/-- The reserved words of the items before a position are those of the version in force, as
every reading of the items says, where they are as one reading says. -/
theorem lexical_of_witness {start : BSmtLibSpec.Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes start commands taken ending)
    {items : List Parser.Internal.Input} (hlen : items.length ≤ taken.length)
    (hagree : items.map rcv = taken.take items.length)
    (hlex : ∀ j < items.length, ∀ item, taken[j]? = some item →
      item.OfVersion (versionAt start commands j)) :
    ∀ j (hj : j < items.length), ∀ commands' taken' ending',
      Takes start commands' taken' ending' →
      ([] : List Received).length + j < taken'.length →
      (([] : List Received) ++ items.map rcv).take (([] : List Received).length + j) =
        taken'.take (([] : List Received).length + j) →
      (rcv items[j]).OfVersion (versionAt start commands' (([] : List Received).length + j)) := by
  intro j hj commands' taken' ending' htakes' hj' htake
  simp only [List.length_nil, Nat.zero_add, List.nil_append] at hj' htake ⊢
  have hitem : taken[j]? = some (rcv items[j]) := by
    have := congrArg (·[j]?) hagree
    simp only [List.getElem?_map, List.getElem?_take, hj, ite_true, List.getElem?_eq_getElem hj,
      Option.map_some] at this
    exact this.symm
  have heq : taken.take j = taken'.take j := by
    rw [← htake, hagree, List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [← versionAt_unique htakes htakes' (by omega) hj' heq]
  exact hlex j hj _ hitem


/-- After `exit`, the item of the items, where they are as one reading of what a parser takes
says, is the end of the input. -/
theorem afterExit_of_witness {start : BSmtLibSpec.Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes start commands taken ending)
    {items : List Parser.Internal.Input} (hlen : items.length ≤ taken.length)
    (hagree : items.map rcv = taken.take items.length) :
    ∀ j (hj : j < items.length),
      AfterExit start ((([] : List Received) ++ items.map rcv).take
        (([] : List Received).length + j)) →
      rcv items[j] = .endOfInput := by
  intro j hj hafter
  simp only [List.length_nil, Nat.zero_add, List.nil_append] at hafter
  have hitem : taken[j]? = some (rcv items[j]) := by
    have := congrArg (·[j]?) hagree
    simp only [List.getElem?_map, List.getElem?_take, hj, ite_true, List.getElem?_eq_getElem hj,
      Option.map_some] at this
    exact this.symm
  rw [hagree, List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hafter
  have := takes_afterExit htakes (by omega) hafter
  rw [hitem] at this
  exact Option.some.inj this

theorem not_benign_causeOf (error : VersionPolicy.Error) : ¬ Benign (causeOf (.syntax error)) := by
  cases error <;> exact id

/-- What a parser takes for some commands is no shorter start of it for others. -/
theorem takes_prefix_length {start : BSmtLibSpec.Lexicon.Version}
    {commands commands' : List Tree.Command}
    {taken : List Received} {ending ending' : Ending} (htakes : Takes start commands taken ending)
    {j : Nat} (h : Takes start commands' (taken.take j) ending') :
    taken.length ≤ j ∧ ending' = ending := by
  obtain ⟨heq, hend⟩ := takes_prefix htakes h (List.take_prefix j taken)
  refine ⟨?_, hend⟩
  have := congrArg List.length heq
  simp only [List.length_take] at this
  omega

/-- Over a start of what a parser takes, of items whose reserved words are those of the version
in force, the parser goes on, in a state that says what it has taken. -/
theorem prefix_goes_on {version : Token.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending}
    (htakes : Takes
        (Bridge.version version) commands taken ending) {all : List Parser.Internal.Input}
    (hall : all.map Bridge.received = taken.map some) {count : Nat} (hcount : count < taken.length)
    (hlex : ∀ j < count, ∀ item, taken[j]? = some item →
      item.OfVersion (versionAt (Bridge.version version) commands j)) :
    ∃ version' parser' events,
      (driveScript version (ScriptParser.new unrestrictedPosture) (all.take count)).run.run
          (startEvents version) =
        (.ok (.inl (version', parser')), events) ∧
      ScriptInv (Bridge.version version) (taken.take count) version' parser' := by
  have hrcv := map_rcv_of_received hall
  have hlength : all.length = taken.length := by simpa using congrArg List.length hall
  have hlayout : NoLayout (all.take count) := fun t ht =>
    noLayout_of_stands hall t (List.mem_of_mem_take ht)
  have htake : (all.take count).map rcv = taken.take count := by rw [List.map_take, hrcv]
  have hlen' : (all.take count).length = count := by simp [hlength]; omega
  have hsound := script_runs (Bridge.version version) (all.take count) [] version
    (ScriptParser.new unrestrictedPosture) (scriptInv_new version) hlayout
    (lexical_of_witness htakes (by omega) (by rw [htake, hlen'])
      (fun j hj => hlex j (by omega)))
    (afterExit_of_witness htakes (by omega) (by rw [htake, hlen']))
  have htake' : ∀ j, j ≤ count → ((all.take count).take j).map rcv = taken.take j := by
    intro j hj
    rw [List.map_take, htake, List.take_take, Nat.min_eq_left hj]
  rcases hrun : (driveScript version (ScriptParser.new unrestrictedPosture)
    (all.take count)).run.run (startEvents version) with ⟨_ | (⟨v, p⟩ | ⟨u, rest⟩), events⟩
  · rename_i e
    rcases hsound.error _ _ _ hrun with hb | ⟨-, j, cs, hj, hcs⟩
    · -- a failure over the start is a failure over all of it, which is no handler's
      exfalso
      have hfull := driveScript_fails (more := all.drop count) hrun
      rw [List.take_append_drop] at hfull
      have hres := parserResult_takes htakes hall []
      rw [List.append_nil, driveParse_run, hfull] at hres
      rcases hres with hres | ⟨error, hres⟩
      · cases hres
      · cases hres
        exact not_benign_causeOf error hb
    · rw [List.nil_append, htake' (j + 1) (by rw [hlen'] at hj; omega)] at hcs
      have := (takes_prefix_length htakes hcs).1
      rw [hlen'] at hj
      omega
  · have hpost := hsound.ok _ _ _ hrun
    simp only [RunPost, List.nil_append, htake] at hpost
    exact ⟨v, p, events, rfl, hpost⟩
  · obtain ⟨j, cs, hj, -, hcs⟩ := hsound.ok _ _ _ hrun
    rw [List.nil_append, htake' (j + 1) (by rw [hlen'] at hj; omega)] at hcs
    have := (takes_prefix_length htakes hcs).1
    rw [hlen'] at hj
    omega

/-! ## The two properties -/

/-- The library's parser takes what a parser takes as the traversal does. -/
theorem library_follows : FollowsTheTraversal libraryParser := by
  intro version commands taken ending all htakes hstands count hcount
  have hlex := takes_ofVersion htakes
  have hv : Bridge.version (Bridge.libVersion version) = version := version_libVersion version
  have htakes' : Takes (Bridge.version (Bridge.libVersion version)) commands taken ending := by
    rw [hv]
    exact htakes
  have hlex' : ∀ j, ∀ item : Received, taken[j]? = some item →
      item.OfVersion (versionAt (Bridge.version (Bridge.libVersion version)) commands j) := by
    rw [hv]
    exact hlex
  have hall : (all.map Subtype.val).map Bridge.received = taken.map some := received_items hstands
  have hlength : (all.map Subtype.val).length = taken.length := by
    simpa using congrArg List.length hall
  have hmap : (all.take count).map Subtype.val = (all.map Subtype.val).take count :=
    List.map_take ..
  simp only [libraryParser, driveInput_run]
  erw [hmap]
  refine Prod.ext (by
    have hplace := placement_prefix_takes htakes' hall count
    rw [hv] at hplace
    exact hplace) ?_
  simp only
  by_cases hlt : count < taken.length
  · obtain ⟨v', p', events, hrun, -⟩ := prefix_goes_on htakes' hall hlt
      (fun j _ item h => hlex' j item h)
    rw [driveParse_run, hrun]
    simp [libEnding, hlt]
  · have hfull : (all.map Subtype.val).take count = all.map Subtype.val :=
      List.take_of_length_le (by omega)
    rw [hfull]
    simp only [hlt, ite_false]
    have hrcv := map_rcv_of_received hall
    have hsound := script_runs (Bridge.version (Bridge.libVersion version)) (all.map Subtype.val)
      [] (Bridge.libVersion version) (ScriptParser.new unrestrictedPosture)
      (scriptInv_new _) (noLayout_items all)
      (lexical_of_witness htakes' (by omega) (by rw [hrcv, hlength, List.take_length])
        (fun j _ item h => hlex' j item h))
      (afterExit_of_witness htakes' (by omega) (by rw [hrcv, hlength, List.take_length]))
    have hres := parserResult_takes htakes' hall []
    rw [List.append_nil] at hres
    rw [driveParse_run] at hres ⊢
    have htake : ∀ j, ((all.map Subtype.val).take j).map rcv = taken.take j := by
      intro j
      rw [List.map_take, hrcv]
    rcases hrun : (driveScript (Bridge.libVersion version) (ScriptParser.new unrestrictedPosture)
      (all.map Subtype.val)).run.run (startEvents (Bridge.libVersion version)) with
          ⟨_ | (⟨v, p⟩ | ⟨u, rest⟩), events⟩
    · rename_i e
      rw [hrun] at hres
      rcases hsound.error _ _ _ hrun with hb | ⟨he, j, cs, -, hcs⟩
      · rcases hres with hres | ⟨error, hres⟩
        · cases hres
        · cases hres
          exact absurd hb (not_benign_causeOf error)
      · rw [List.nil_append, htake] at hcs
        obtain ⟨-, hend⟩ := takes_prefix_length htakes' hcs
        subst he
        simp [libEnding, ← hend]
    · rw [hrun] at hres
      rcases hres with hres | ⟨error, hres⟩ <;> cases hres
    · obtain ⟨j, cs, -, -, hcs⟩ := hsound.ok _ _ _ hrun
      rw [List.nil_append, htake] at hcs
      obtain ⟨-, hend⟩ := takes_prefix_length htakes' hcs
      simp [libEnding, ← hend]

/-! ## The events before an item's processing -/

theorem eventsBeforeProcessing_of_lt : (events : List Event) → ∀ k,
    events.countP isProcessing < k → eventsBeforeProcessing k events = events
  | [], _, _ => by simp [eventsBeforeProcessing]
  | event :: events, k, h => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    cases event with
    | process item =>
      simp only [List.countP_cons, isProcessing, ite_true] at h
      simp [eventsBeforeProcessing, eventsBeforeProcessing_of_lt events k (by omega)]
    | _ =>
      simp only [List.countP_cons, isProcessing, Bool.false_eq_true, ite_false,
        Nat.add_zero] at h
      rw [eventsBeforeProcessing.eq_def]
      simp [eventsBeforeProcessing_of_lt events (k + 1) h]

theorem eventsBeforeProcessing_silent : (silent : List Event) →
    (∀ e ∈ silent, Quiet.isPoint e = false) → eventsBeforeProcessing 0 silent = silent
  | [], _ => by simp [eventsBeforeProcessing]
  | event :: silent, h => by
    have hrest := eventsBeforeProcessing_silent silent fun e he => h e (List.mem_cons_of_mem _ he)
    have hpoint := h event List.mem_cons_self
    cases event with
    | arrive => simp [Quiet.isPoint] at hpoint
    | process => simp [Quiet.isPoint] at hpoint
    | _ => simp [eventsBeforeProcessing, hrest]

theorem eventsBeforeProcessing_calls_succ : (calls : List Event) →
    calls.countP isProcessing = 0 → ∀ (k : Nat) (received : Received) (rest : List Event),
    eventsBeforeProcessing (k + 1) (calls ++ .process received :: rest) =
      calls ++ .process received :: eventsBeforeProcessing k rest
  | [], _, k, received, rest => by simp [eventsBeforeProcessing]
  | call :: calls, h, k, received, rest => by
    simp only [List.countP_cons] at h
    have hp : isProcessing call = false := by cases hc : isProcessing call <;> simp_all
    simp only [hp, Bool.false_eq_true, ite_false, Nat.add_zero] at h
    cases call with
    | process => simp [isProcessing] at hp
    | _ => simp [eventsBeforeProcessing, eventsBeforeProcessing_calls_succ calls h]

/-- The events of a run are settled: those before the processing of the item after the last
processed one are all of them. -/
def Settled (events : List Event) : Prop :=
  eventsBeforeProcessing (events.countP isProcessing) events = events

theorem settled_start (version : Token.Version) : Settled (startEvents version).reverse := by
  simp [Settled, startEvents, eventsBeforeProcessing, isProcessing]

theorem recAfter_settled (version : Token.Version) (parser : ScriptParser (List Event))
    {token : Parser.Internal.Input} {received : Received}
        (htoken : Bridge.received token = some received)
    (events : List Event) :
    Settled ((recAfter version parser token).run.run events).2.reverse := by
  obtain ⟨silent, hstate, hsilent⟩ := afterToken_shape version parser htoken events
  rw [hstate]
  have hcalls := arrivalCalls_countP (p := isProcessing) (fun _ => rfl) parser token
  have hsilentP := countP_silent (p := isProcessing)
    (fun e he => by cases e <;> simp_all [Quiet.isPoint, isProcessing]) hsilent
  unfold Settled
  have hform : (silent ++ [Event.process received] ++ arrivalCalls parser token ++
      [Event.arrive received] ++ events).reverse =
      events.reverse ++ (Event.arrive received :: ((arrivalCalls parser token).reverse ++
        Event.process received :: silent.reverse)) := by simp
  rw [hform]
  have hcount : (events.reverse ++ (Event.arrive received :: ((arrivalCalls parser token).reverse ++
      Event.process received :: silent.reverse))).countP isProcessing =
      events.reverse.countP isProcessing + 1 := by
    simp only [List.countP_append, List.countP_reverse, List.countP_cons, hcalls, hsilentP,
      isProcessing]
    simp
  rw [hcount, eventsBeforeProcessing_append, eventsBeforeProcessing_of_lt _ _ (by omega)]
  congr 1
  simp only [eventsBeforeProcessing]
  rw [eventsBeforeProcessing_calls_succ _ (by rw [List.countP_reverse]; exact hcalls),
    eventsBeforeProcessing_silent _ fun e he => hsilent e (List.mem_reverse.mp he)]

/-- A run that goes on over items ends settled, one arrival and one processing more per item. -/
theorem driveScript_settled : ∀ (items : List Parser.Internal.Input), NoLayout items →
    ∀ (version : Token.Version) (parser : ScriptParser (List Event)) (events : List Event)
      {version' : Token.Version} {parser' : ScriptParser (List Event)} {events' : List Event},
    Settled events.reverse →
    (driveScript version parser items).run.run events =
      (.ok (.inl (version', parser')), events') →
    Settled events'.reverse ∧
      events'.reverse.countP isArrival = events.reverse.countP isArrival + items.length ∧
      events'.reverse.countP isProcessing = events.reverse.countP isProcessing + items.length
  | [], _, version, parser, events, _, _, _, hsettled, h => by
    simp only [driveScript] at h
    cases h
    exact ⟨hsettled, by simp, by simp⟩
  | token :: tokens, hlayout, version, parser, events, _, _, _, _, h => by
    obtain ⟨received, hreceived⟩ := Option.ne_none_iff_exists'.mp
      (hlayout token List.mem_cons_self)
    simp only [driveScript] at h
    rw [run_bind_split] at h
    have hcounts := afterToken_counts version parser hreceived events
    have hsettled := recAfter_settled version parser hreceived events
    rcases hrun : (recAfter version parser token).run.run events with ⟨_ | (⟨v, p⟩ | u), e⟩
    · rw [hrun] at h
      cases h
    · rw [hrun] at h hcounts hsettled
      obtain ⟨h₁, h₂, h₃⟩ := driveScript_settled tokens
        (fun t ht => hlayout t (List.mem_cons_of_mem _ ht)) v p e hsettled h
      refine ⟨h₁, ?_, ?_⟩
      · rw [h₂, hcounts.1]; simp; omega
      · rw [h₃, hcounts.2]; simp; omega
    · rw [hrun] at h
      cases h

/-- Calls due at an item's arrival: a body of `define-funs-rec` is due. -/
theorem arrivalCalls_ne_nil {parser : ScriptParser (List Event)} {token : Parser.Internal.Input}
    (h : arrivalCalls parser token ≠ []) :
    ∃ signatures state signature,
      parser.command = .payload (.defineFunsRecBodies signatures state) ∧
      state.opened = true ∧ state.outside = true ∧
      signatures[state.items.size]? = some signature := by
  revert h
  unfold arrivalCalls
  split
  · simp
  · split
    · rename_i signatures state heq
      split
      · rename_i hc
        split
        · rename_i signature hs
          intro _
          simp only [Bool.and_eq_true] at hc
          exact ⟨signatures, state, signature, heq, hc.1, hc.2, hs⟩
        · simp
      · simp
    · simp

/-- Where a body of `define-funs-rec` is due, a `)` fails the parse, with a cause that is no
version's. -/
theorem recAfter_close_fails {parser : ScriptParser (List Event)} {token : Parser.Internal.Input}
    (h : arrivalCalls parser token ≠ []) (version : Token.Version) (events : List Event) :
    ∃ e events', (recAfter version parser .parenClose).run.run events = (.error e, events') ∧
      Benign e := by
  obtain ⟨signatures, state, signature, hphase, hopened, houtside, hsignature⟩ :=
    arrivalCalls_ne_nil h
  have hlt : state.items.size < signatures.size := by
    rcases Nat.lt_or_ge state.items.size signatures.size with hlt | hge
    · exact hlt
    · rw [Array.getElem?_eq_none hge] at hsignature
      cases hsignature
  obtain ⟨posture, phase, declarations⟩ := parser
  simp only at hphase
  subst hphase
  refine ⟨.syntax .expectedFunctionBody,
    .process (.token .parenClose) :: .arrive (.token .parenClose) :: events, ?_, trivial⟩
  have h₁ : ((ExceptT.lift
      (arriveAt recordingPoints Parser.Internal.Input.parenClose) : Quiet.RPM Unit).run.run
      events) = (.ok (), .arrive (.token .parenClose) :: events) := rfl
  have h₂ := arrive_run ⟨posture, .payload (.defineFunsRecBodies signatures state),
    declarations⟩ .parenClose (.arrive (.token .parenClose) :: events)
  rw [arrivalCalls_parenClose, List.nil_append] at h₂
  have h₃ : ((ExceptT.lift
      (processAt recordingPoints Parser.Internal.Input.parenClose) : Quiet.RPM Unit).run.run
      (.arrive (.token .parenClose) :: events)) =
      (.ok (), .process (.token .parenClose) :: .arrive (.token .parenClose) :: events) := rfl
  change ((afterToken recordingPoints recordingProducer version _
      Parser.Internal.Input.parenClose).run.run
    events) = _
  unfold afterToken
  rw [run_bind_ok h₁, run_bind_ok h₂, run_bind_ok h₃]
  simp [afterProcessing, Parser.Internal.ParseByToken.step, ScriptParser.Internal.step,
      Parser.Command.Internal.commandStep,
    Parser.Command.Internal.Standard.payloadStep, Parser.Command.Internal.Function.bodiesStep,
        Parser.Category.Combinator.Internal.ListState.step, hopened, houtside,
    Parser.Internal.syntaxError, show ¬ state.items.size = signatures.size by omega]
  rfl

/-- `library_rejects`, for items of the parser's own type. -/
theorem rejects_core (version : BSmtLibSpec.Lexicon.Version) (commands : List Tree.Command)
    (taken : List Received) (ending : Ending) (all items : List LibItem) (count : Nat)
    (htakes : Takes version commands taken ending)
    (hstands : all.map (rcv ∘ Subtype.val) = taken) (hcount : count < taken.length)
    (rejected : LibItem) (hrejected : items[count]? = some rejected)
    (hagree : items.take count = all.take count)
    (hlexI : ∀ position ≤ count, ∀ item : Received,
      (items.map (rcv ∘ Subtype.val))[position]? = some item →
      item.OfVersion (versionAt version commands position))
    (hexit : ¬ AfterExit version (taken.take count))
    (hunviable : ¬ Viable version ((items.map (rcv ∘ Subtype.val)).take (count + 1))) :
    (libraryParser.parse version items).2 = .rejected ∧
      (libraryParser.parse version items).1.filterMap Event.processed =
        (items.map (rcv ∘ Subtype.val)).take (count + 1) ∧
      (libraryParser.parse version items).1.getLast? =
        ((items.map (rcv ∘ Subtype.val))[count]?).map .process ∧
      eventsBeforeProcessing count (libraryParser.parse version items).1 =
        eventsBeforeProcessingOf (rcv rejected.1) count (record version commands) := by
  have hcitems : count < items.length := by
    by_cases h : count < items.length
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hrejected
      cases hrejected
  have hv : Bridge.version (Bridge.libVersion version) = version := version_libVersion version
  have htakes' : Takes (Bridge.version (Bridge.libVersion version)) commands taken ending := by
    rw [hv]
    exact htakes
  have hall : (all.map Subtype.val).map Bridge.received = taken.map some := received_items hstands
  have hlength : (all.map Subtype.val).length = taken.length := by
    simpa using congrArg List.length hall
  -- the items as tokens, and what they stand for
  have hstandsI : items.map (rcv ∘ Subtype.val) = (items.map Subtype.val).map rcv :=
    (map_rcv items).symm
  have hlenI : (items.map Subtype.val).length = items.length := List.length_map ..
  have hagree' : (items.map Subtype.val).take count = (all.map Subtype.val).take count := by
    have := congrArg (List.map Subtype.val) hagree
    rwa [List.map_take, List.map_take] at this
  have hstake : (items.map (rcv ∘ Subtype.val)).take count = taken.take count := by
    rw [hstandsI, ← List.map_take, hagree', List.map_take, map_rcv_of_received hall]
  have hget : ∀ j < count, (items.map (rcv ∘ Subtype.val))[j]? = taken[j]? := by
    intro j hj
    have := congrArg (·[j]?) hstake
    simpa [List.getElem?_take, hj] using this
  -- the items before the one at `count` keep the parser going
  obtain ⟨version', parser', events₁, hrun₁, hinv⟩ := prefix_goes_on htakes' hall hcount
    (fun j hj item h => by
      rw [hv]
      exact hlexI j (Nat.le_of_lt hj) item (by rw [hget j hj]; exact h))
  -- the item at `count`
  have hci : count < (items.map Subtype.val).length := by omega
  obtain ⟨x, hx⟩ : ∃ x, x = (items.map Subtype.val)[count] := ⟨_, rfl⟩
  have hxl : Bridge.received x ≠ none := by
    rw [hx, List.getElem_map]
    exact items[count].2
  have hitem := received_rcv hxl
  have hxs : (items.map (rcv ∘ Subtype.val))[count]? = some (rcv x) := by
    rw [hstandsI, List.getElem?_map, List.getElem?_eq_getElem hci, hx]
    rfl
  have htake₁ : (items.map (rcv ∘ Subtype.val)).take (count + 1) = taken.take count ++ [rcv x] := by
    rw [List.take_add_one, hstake, hxs]
    rfl
  have hlen₁ : (taken.take count).length = count := by simp; omega
  have hlex₀ : (rcv x).OfVersion (Bridge.version version') := by
    obtain ⟨cs, t, e, ht, hlt, htk, hver⟩ := scriptInv_witness hinv
    rw [hlen₁] at hlt htk hver
    have hu := versionAt_unique htakes' ht hcount hlt htk.symm
    rw [← hver, ← hu, hv]
    exact hlexI count (Nat.le_refl _) _ hxs
  have hviable : ∀ cs t e, Takes version cs t e → taken.take count ++ [rcv x] <+: t → False :=
    fun cs t e ht hp => hunviable ⟨cs, t, e, ht, by rw [htake₁]; exact hp⟩
  have hsplit : items.map Subtype.val =
      (all.map Subtype.val).take count ++ x :: (items.map Subtype.val).drop (count + 1) := by
    rw [← hagree', hx, ← List.drop_eq_getElem_cons hci, List.take_append_drop]
  have hexit₀ : AfterExit (Bridge.version (Bridge.libVersion version)) (taken.take count) →
      rcv x = .endOfInput := fun h => (hexit (by rw [hv] at h; exact h)).elim
  have hstep := recAfter_post hinv hitem hlex₀ hexit₀
  rcases hrun₂ : (recAfter version' parser' x).run.run events₁ with
    ⟨_ | (⟨v, p⟩ | u), events₂⟩
  case ok.inl =>
    obtain ⟨cs, t, e, ht, hlt, htk, -⟩ := scriptInv_witness (hstep.ok _ _ _ hrun₂)
    rw [hv] at ht
    exact (hviable cs t e ht (htk ▸ List.take_prefix _ t)).elim
  case ok.inr =>
    obtain ⟨cs, hcs⟩ := hstep.ok _ _ _ hrun₂
    rw [hv] at hcs
    exact (hviable cs _ _ hcs (List.prefix_refl _)).elim
  case error e =>
    rcases hstep.error _ _ _ hrun₂ with hb | ⟨-, cs, hcs⟩
    case inr =>
      rw [hv] at hcs
      exact (hviable cs _ _ hcs (List.prefix_refl _)).elim
    -- the parser fails at the item, with a cause that is no version's
    have hrun : (driveScript (Bridge.libVersion version) (ScriptParser.new unrestrictedPosture)
        (items.map Subtype.val)).run.run (startEvents (Bridge.libVersion version)) =
            (.error e, events₂) := by
      rw [hsplit, driveScript_goes_on hrun₁]
      simp only [driveScript]
      rw [run_bind_split, hrun₂]
    have hparse : libraryParser.parse version items = (events₂.reverse, .rejected) := by
      simp only [libraryParser, driveInput_run]
      rw [driveParse_run, hrun]
      exact Prod.ext rfl (libEnding_benign hb)
    refine ⟨by rw [hparse], ?_, ?_, ?_⟩
    · rw [hparse, htake₁]
      obtain ⟨silent, hstate, hsilent⟩ := afterToken_shape version' parser' hitem events₁
      rw [hrun₂] at hstate
      simp only at hstate
      subst hstate
      have hp₁ := driveScript_processed _ (fun t ht => noLayout_of_stands hall t
        (List.mem_of_mem_take ht)) _ _ _ hrun₁
      rw [List.map_take, map_rcv_of_received hall] at hp₁
      have hs : silent.reverse.filterMap Event.processed = [] := by
        rw [List.filterMap_eq_nil_iff]
        intro ev hev
        have := hsilent ev (List.mem_reverse.mp hev)
        cases ev <;> first | rfl | (simp [Quiet.isPoint] at this)
      have ha := arrivalCalls_processed parser' x
      simp only [List.reverse_append, List.filterMap_append, hs, ha]
      simp [Event.processed, hp₁, startEvents, List.filterMap_cons]
    · -- the item's processing is the last event: processing it makes no call
      rw [hparse, hxs, recAfter_rejects_quiet hinv hitem hlex₀ hexit₀ hrun₂ hb]
      simp [List.getLast?_cons, List.getLast?_append]
    · -- the events before the item: those of the items before it, then the calls due at its
      -- arrival, as in the run on the script's items, where the script's item is no `)`
      have hevents₂ := recAfter_rejects_quiet hinv hitem hlex₀ hexit₀ hrun₂ hb
      have hlenTake : ((all.map Subtype.val).take count).length = count := by
        simp only [List.length_take]; omega
      obtain ⟨hset₁, harr₁, hproc₁⟩ := driveScript_settled _
        (fun t ht => noLayout_of_stands hall t (List.mem_of_mem_take ht)) _ _ _
        (settled_start (Bridge.libVersion version)) hrun₁
      rw [hlenTake] at harr₁ hproc₁
      simp only [startEvents, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.countP_singleton, isArrival, isProcessing, Bool.false_eq_true, ite_false,
        Nat.zero_add] at harr₁ hproc₁
      -- the run on the items
      have hlhs : eventsBeforeProcessing count events₂.reverse =
          events₁.reverse ++ (arrivalCalls parser' x).reverse := by
        rw [hevents₂]
        have hform : (Event.process (rcv x) :: (arrivalCalls parser' x ++
            Event.arrive (rcv x) :: events₁)).reverse =
            events₁.reverse ++ (Event.arrive (rcv x) :: ((arrivalCalls parser' x).reverse ++
              Event.process (rcv x) :: [])) := by simp
        rw [hform, show count = events₁.reverse.countP isProcessing + 0 by omega,
          eventsBeforeProcessing_append]
        have hset' : eventsBeforeProcessing (events₁.reverse.countP isProcessing + 0)
            events₁.reverse = events₁.reverse := hset₁
        rw [hset']
        congr 1
        rw [eventsBeforeProcessing.eq_def]
        simp only
        apply eventsBeforeProcessing_calls
        · rw [List.countP_reverse]; exact arrivalCalls_countP (fun _ => rfl) parser' x
        · rw [List.countP_reverse]; exact arrivalCalls_countP (fun _ => rfl) parser' x
      -- the run on the script's items
      have hcountAll : count < (all.map Subtype.val).length := by omega
      obtain ⟨y, hy⟩ : ∃ y, y = (all.map Subtype.val)[count] := ⟨_, rfl⟩
      have hyl : Bridge.received y ≠ none := by
        rw [hy, List.getElem_map]
        exact (all[count]'(by simpa using hcountAll)).2
      have hyitem := received_rcv hyl
      have hsplitAll : all.map Subtype.val =
          (all.map Subtype.val).take count ++ y :: (all.map Subtype.val).drop (count + 1) := by
        rw [hy, ← List.drop_eq_getElem_cons hcountAll, List.take_append_drop]
      have hrecord : record version commands =
          recordedRun version' parser' (y :: (all.map Subtype.val).drop (count + 1)) events₁ := by
        have := parserRecord_takes htakes' hall
        rw [hv] at this
        rw [← this]
        unfold parserRecord
        rw [recordedRun_driveScript]
        conv => lhs; rw [hsplitAll]
        rw [driveScript_goes_on hrun₁, ← recordedRun_driveScript]
      obtain ⟨rest, hrest⟩ := recordedRun_cons_form version' parser' hyitem
        (fun t ht => noLayout_of_stands hall t (List.mem_of_mem_drop ht)) events₁
      have hrhsBefore : eventsBefore count (record version commands) = events₁.reverse := by
        rw [hrecord, hrest, show count = events₁.reverse.countP isArrival + 0 by omega,
          eventsBefore_append]
        simp [eventsBefore]
      have hrhsProcessing : eventsBeforeProcessing count (record version commands) =
          events₁.reverse ++ (arrivalCalls parser' y).reverse := by
        rw [hrecord, hrest, show count = events₁.reverse.countP isProcessing + 0 by omega,
          eventsBeforeProcessing_append]
        have hset' : eventsBeforeProcessing (events₁.reverse.countP isProcessing + 0)
            events₁.reverse = events₁.reverse := hset₁
        rw [hset']
        congr 1
        rw [eventsBeforeProcessing.eq_def]
        simp only
        apply eventsBeforeProcessing_calls
        · rw [List.countP_reverse]; exact arrivalCalls_countP (fun _ => rfl) parser' y
        · rw [List.countP_reverse]; exact arrivalCalls_countP (fun _ => rfl) parser' y
      have hrej : rejected.1 = x := by
        rw [hx, List.getElem_map]
        have := List.getElem?_eq_getElem (l := items) (by omega : count < items.length)
        rw [hrejected] at this
        cases this
        rfl
      rw [hparse, hrej]
      simp only
      by_cases hxclose : x = .parenClose
      · -- a `)`: no call due at its arrival
        subst hxclose
        rw [hlhs, arrivalCalls_parenClose]
        simp only [rcv, Bridge.received, Option.getD_some, eventsBeforeProcessingOf,
          List.reverse_nil, List.append_nil]
        exact hrhsBefore.symm
      · have hof : eventsBeforeProcessingOf (rcv x) count (record version commands) =
            eventsBeforeProcessing count (record version commands) := by
          unfold eventsBeforeProcessingOf
          split
          · rename_i hrcv
            exact absurd (Parser.Internal.Input.received_parenClose (hitem.trans
                (by rw [hrcv]))) hxclose
          · rfl
        rw [hof, hlhs, hrhsProcessing]
        by_cases hyclose : y = .parenClose
        · -- no body is due where the script has a `)`: a `)` there would fail its run
          have hcalls : arrivalCalls parser' x = [] := by
            apply Classical.byContradiction
            intro hcalls
            obtain ⟨e', events', hfail, hb'⟩ := recAfter_close_fails hcalls version' events₁
            have hres := parserResult_takes htakes' hall []
            rw [List.append_nil, driveParse_run, hsplitAll, driveScript_goes_on hrun₁,
              hyclose] at hres
            simp only [driveScript] at hres
            rw [run_bind_split, hfail] at hres
            rcases hres with hres | ⟨error, hres⟩
            · cases hres
            · cases hres
              exact not_benign_causeOf error hb'
          rw [hcalls, hyclose, arrivalCalls_parenClose]
        · rw [arrivalCalls_congr parser' hxclose hyclose]

/-! ## Items for what a parser takes -/

open BSmtLibSpec.Lexicon (basicReservedWords commandNames)

/-- Every reserved word of a version is one of the library's. -/
theorem decodeReserved_isSome : ∀ v : BSmtLibSpec.Lexicon.Version,
    ∀ s ∈ basicReservedWords v ++ commandNames v,
    (decodeReserved (BSmtLibSpec.Regex.chars s)).isSome := by
  intro v
  cases v <;> decide

theorem decodeReserved_spec {w : BSmtLibSpec.Regex.Chars} {r : Token.Reserved}
    (h : decodeReserved w = some r) : Bridge.reserved r = w := by
  unfold decodeReserved at h
  have := List.find?_some h
  simpa using this

theorem chars_bytesOf (c : BSmtLibSpec.Regex.Chars) : Bridge.chars (bytesOf c) = c := by
  simp [Bridge.chars, bytesOf, Lexer.Simulation.Bytes.toByteArray_toByteSlice,
    Lexer.Simulation.Bytes.byteArray_toList]

/-- A parser's token that stands for the item: one for every item but a reserved word that is
none of the library's. -/
def inputOf : Received → Option Parser.Internal.Input
  | .endOfInput => some .endOfInput
  | .token .parenOpen => some .parenOpen
  | .token .parenClose => some .parenClose
  | .token (.numeral d) => some (.constant (.numeral (NumeralView.Internal.newUnchecked (bytesOf d))))
  | .token (.decimal d) => some (.constant (.decimal (DecimalView.Internal.newUnchecked (bytesOf d))))
  | .token (.hexadecimal d) =>
    some (.constant (.hexadecimal (HexDigitsView.Internal.newUnchecked (bytesOf d))))
  | .token (.binary d) => some (.constant (.binary (BinDigitsView.Internal.newUnchecked (bytesOf d))))
  | .token (.string c) => some (.constant (.string (StringContentView.Internal.newUnchecked (bytesOf c))))
  | .token (.symbol s) => some (.symbol ⟨SymbolView.Internal.newUnchecked (bytesOf s.name), s.quoted⟩)
  | .token (.keyword k) => some (.keyword (KeywordView.Internal.newUnchecked (bytesOf k)))
  | .token (.reserved w) => (decodeReserved w).map .reserved

theorem received_inputOf {r : Received} {t : Parser.Internal.Input} (h : inputOf r = some t) :
    Bridge.received t = some r := by
  rcases r with t' | _
  · cases t' with
    | reserved w =>
      simp only [inputOf, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      simp [Bridge.received, decodeReserved_spec hr]
    | numeral d =>
      simp only [inputOf, Option.some.injEq] at h; subst h
      show some (Received.token (.numeral (Bridge.chars (bytesOf d)))) = _
      rw [chars_bytesOf]
    | decimal d =>
      simp only [inputOf, Option.some.injEq] at h; subst h
      show some (Received.token (.decimal (Bridge.chars (bytesOf d)))) = _
      rw [chars_bytesOf]
    | hexadecimal d =>
      simp only [inputOf, Option.some.injEq] at h; subst h
      show some (Received.token (.hexadecimal (Bridge.chars (bytesOf d)))) = _
      rw [chars_bytesOf]
    | binary d =>
      simp only [inputOf, Option.some.injEq] at h; subst h
      show some (Received.token (.binary (Bridge.chars (bytesOf d)))) = _
      rw [chars_bytesOf]
    | string c =>
      simp only [inputOf, Option.some.injEq] at h; subst h
      show some (Received.token (.string (Bridge.chars (bytesOf c)))) = _
      rw [chars_bytesOf]
    | symbol s =>
      simp only [inputOf, Option.some.injEq] at h; subst h
      show some (Received.token (.symbol ⟨Bridge.chars (bytesOf s.name), s.quoted⟩)) = _
      rw [chars_bytesOf]
    | keyword k =>
      simp only [inputOf, Option.some.injEq] at h; subst h
      show some (Received.token (.keyword (Bridge.chars (bytesOf k)))) = _
      rw [chars_bytesOf]
    | parenOpen => simp only [inputOf, Option.some.injEq] at h; subst h; rfl
    | parenClose => simp only [inputOf, Option.some.injEq] at h; subst h; rfl
  · simp only [inputOf, Option.some.injEq] at h
    subst h
    rfl

theorem inputOf_isSome {v : BSmtLibSpec.Lexicon.Version} {r : Received} (h : r.OfVersion v) :
    (inputOf r).isSome := by
  rcases r with t | _
  · cases t
    case reserved w =>
      simp only [Received.OfVersion, List.mem_map] at h
      obtain ⟨s, hs, rfl⟩ := h
      simpa [inputOf] using decodeReserved_isSome v s hs
    all_goals rfl
  · rfl

/-- Items that stand for each of the given ones, where each has a token that stands for it. -/
theorem items_for : ∀ l : List Received, (∀ (i : Nat) r, l[i]? = some r → (inputOf r).isSome) →
    ∃ items : List LibItem, items.map (rcv ∘ Subtype.val) = l
  | [], _ => ⟨[], rfl⟩
  | r :: l, h => by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h 0 r rfl)
    obtain ⟨items, hitems⟩ := items_for l fun i r' hr' => h (i + 1) r' (by simpa using hr')
    have hrec := received_inputOf ht
    refine ⟨⟨t, by rw [hrec]; simp⟩ :: items, ?_⟩
    simp only [List.map_cons, hitems, Function.comp_apply, List.cons.injEq, and_true]
    simp [rcv, hrec]

/-- `library_rejects`, for items of the parser's own type that stand for what a parser takes
before the rejected one, where they do not end with `exit`. -/
theorem rejects_items (version : BSmtLibSpec.Lexicon.Version) (commands : List Tree.Command)
    (taken : List Received) (ending : Ending) (items : List LibItem) (count : Nat)
    (htakes : Takes version commands taken ending) (hcount : count < taken.length)
    (rejected : LibItem) (hrejected : items[count]? = some rejected)
    (hagree : (items.map (rcv ∘ Subtype.val)).take count = taken.take count)
    (hlexC : ∀ item : Received, (items.map (rcv ∘ Subtype.val))[count]? = some item →
      item.OfVersion (versionAt version commands count))
    (hexit : ¬ AfterExit version (taken.take count))
    (hunviable : ¬ Viable version ((items.map (rcv ∘ Subtype.val)).take (count + 1))) :
    (libraryParser.parse version items).2 = .rejected ∧
      (libraryParser.parse version items).1.filterMap Event.processed =
        (items.map (rcv ∘ Subtype.val)).take (count + 1) ∧
      (libraryParser.parse version items).1.getLast? =
        ((items.map (rcv ∘ Subtype.val))[count]?).map .process ∧
      eventsBeforeProcessing count (libraryParser.parse version items).1 =
        eventsBeforeProcessingOf (rcv rejected.1) count (record version commands) := by
  have hcitems : count < items.length := by
    by_cases h : count < items.length
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hrejected
      cases hrejected
  have hof := takes_ofVersion htakes
  obtain ⟨rest, hrest⟩ := items_for (taken.drop count) fun i r hr => by
    rw [List.getElem?_drop] at hr
    exact inputOf_isSome (hof _ r hr)
  have hlen : (items.take count).length = count := by simp; omega
  have hstands : (items.take count ++ rest).map (rcv ∘ Subtype.val) = taken := by
    rw [List.map_append, hrest, List.map_take, hagree, List.take_append_drop]
  have hag : items.take count = (items.take count ++ rest).take count := by
    rw [List.take_append_of_le_length (Nat.le_of_eq hlen.symm),
      List.take_of_length_le (Nat.le_of_eq hlen)]
  refine rejects_core version commands taken ending (items.take count ++ rest) items count htakes
    hstands hcount rejected hrejected hag ?_ hexit hunviable
  intro position hposition item hitem
  rcases Nat.lt_or_eq_of_le hposition with hlt | rfl
  · have heq : (items.map (rcv ∘ Subtype.val))[position]? = taken[position]? := by
      have := congrArg (·[position]?) hagree
      simp only [List.getElem?_take, hlt, ite_true] at this
      exact this
    exact hof position item (heq ▸ hitem)
  · exact hlexC item hitem

/-! ## What the parser has done before an item is processed -/

/-- A parser takes for a valid script what it receives for it, and finishes. -/
theorem takes_of_script {version : BSmtLibSpec.Lexicon.Version} {commands : List Tree.Command}
    (h : Script version commands) :
    Takes version commands (BSmtLibSpec.Parser.Properties.received commands) .finished := by
  induction h with
  | done => exact .done
  | command hv hm _ ih =>
    rw [received_cons (modeAfter_read hm).1]
    exact .command hv hm ih
  | stop hv hm =>
    have := modeAfter_unparsed hm
    subst this
    exact .stop hv hm

/--
What the parser has done before the item at position `k` is processed, its arrival left out, on
any input that agrees with what a parser receives for a valid script before that item, is what
the traversal of the script has done before it, where a `)` gets none of the calls due at its
arrival. Where the script has a `)` there, no call is due at the arrival of the input's item
either: a body due there would fail the script's run at its `)`.
-/
theorem placement_processingOf {version : Token.Version} {commands : List Tree.Command}
    (hscript : Script (Bridge.version version) commands) {inputs : List Parser.Internal.Input}
    (hs : inputs.map Bridge.received = (BSmtLibSpec.Parser.Properties.received commands).map some)
    {items : List Parser.Internal.Input} (hlayout : NoLayout items)
        (k : Nat) {item : Parser.Internal.Input}
    (hitem : items[k]? = some item) {stands : Received}
    (hstands : Bridge.received item = some stands) (hk : k < inputs.length)
    (htake : items.take k = inputs.take k) :
    eventsBeforeProcessing k (parserRecord version items) =
      eventsBeforeProcessingOf stands k (record (Bridge.version version) commands) := by
  have htakes := takes_of_script hscript
  have hlength : inputs.length = (BSmtLibSpec.Parser.Properties.received commands).length := by
    simpa using congrArg List.length hs
  have hcount : k < (BSmtLibSpec.Parser.Properties.received commands).length := by omega
  have hof := takes_ofVersion htakes
  -- the items before the one at `k` keep the parser going
  obtain ⟨version', parser', events₁, hrun₁, -⟩ := prefix_goes_on htakes hs hcount
    (fun j _ item h => hof j item h)
  have hlenTake : (inputs.take k).length = k := by simp; omega
  obtain ⟨hset₁, harr₁, hproc₁⟩ := driveScript_settled _
    (fun t ht => noLayout_of_stands hs t (List.mem_of_mem_take ht)) _ _ _
    (settled_start version) hrun₁
  rw [hlenTake] at harr₁ hproc₁
  simp only [startEvents, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.countP_singleton, isArrival, isProcessing, Bool.false_eq_true, ite_false,
    Nat.zero_add] at harr₁ hproc₁
  -- a run from the item at `k` on: the events before it, then the calls due at its arrival
  have hform : ∀ (z : Parser.Internal.Input) (zs : List Parser.Internal.Input) (r : Received),
      Bridge.received z = some r →
      NoLayout zs →
      eventsBefore k (recordedRun version' parser' (z :: zs) events₁) = events₁.reverse ∧
      eventsBeforeProcessing k (recordedRun version' parser' (z :: zs) events₁) =
        events₁.reverse ++ (arrivalCalls parser' z).reverse := by
    intro z zs r hz hzs
    obtain ⟨rest, hrest⟩ := recordedRun_cons_form version' parser' hz hzs events₁
    rw [hrest]
    constructor
    · rw [show k = events₁.reverse.countP isArrival + 0 by omega, eventsBefore_append]
      simp [eventsBefore]
    · rw [show k = events₁.reverse.countP isProcessing + 0 by omega,
        eventsBeforeProcessing_append]
      have hset' : eventsBeforeProcessing (events₁.reverse.countP isProcessing + 0)
          events₁.reverse = events₁.reverse := hset₁
      rw [hset']
      congr 1
      rw [eventsBeforeProcessing.eq_def]
      simp only
      apply eventsBeforeProcessing_calls
      · rw [List.countP_reverse]; exact arrivalCalls_countP (fun _ => rfl) parser' z
      · rw [List.countP_reverse]; exact arrivalCalls_countP (fun _ => rfl) parser' z
  -- the run on the items
  obtain ⟨hki, hxi⟩ := List.getElem?_eq_some_iff.mp hitem
  have hsplit : items = inputs.take k ++ item :: items.drop (k + 1) := by
    rw [← htake, ← hxi, ← List.drop_eq_getElem_cons hki, List.take_append_drop]
  have hrunItems : parserRecord version items =
      recordedRun version' parser' (item :: items.drop (k + 1)) events₁ := by
    unfold parserRecord
    rw [recordedRun_driveScript]
    conv => lhs; rw [hsplit]
    rw [driveScript_goes_on hrun₁, ← recordedRun_driveScript]
  -- the run on the script's items
  obtain ⟨y, hy⟩ : ∃ y, inputs[k]? = some y := ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨_, hyi⟩ := List.getElem?_eq_some_iff.mp hy
  have hyl : Bridge.received y ≠ none :=
    noLayout_of_stands hs y (List.mem_of_getElem? hy)
  have hsplitIn : inputs = inputs.take k ++ y :: inputs.drop (k + 1) := by
    rw [← hyi, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hrecord : record (Bridge.version version) commands =
      recordedRun version' parser' (y :: inputs.drop (k + 1)) events₁ := by
    rw [← parserRecord_script hscript hs]
    unfold parserRecord
    rw [recordedRun_driveScript]
    conv => lhs; rw [hsplitIn]
    rw [driveScript_goes_on hrun₁, ← recordedRun_driveScript]
  obtain ⟨-, hlhs⟩ := hform item (items.drop (k + 1)) stands hstands
    (fun t ht => hlayout t (List.mem_of_mem_drop ht))
  obtain ⟨hyBefore, hyProc⟩ := hform y (inputs.drop (k + 1)) (rcv y) (received_rcv hyl)
    (fun t ht => noLayout_of_stands hs t (List.mem_of_mem_drop ht))
  rw [hrunItems, hlhs, hrecord]
  by_cases hxclose : item = .parenClose
  · -- a `)`: no call due at its arrival
    subst hxclose
    have hclose : stands = .token .parenClose := (Option.some.inj hstands).symm
    subst hclose
    rw [arrivalCalls_parenClose, List.reverse_nil, List.append_nil]
    exact hyBefore.symm
  · have hof' : ∀ events, eventsBeforeProcessingOf stands k events =
        eventsBeforeProcessing k events := by
      intro events
      by_cases hc : stands = .token .parenClose
      · exact absurd (Parser.Internal.Input.received_parenClose (hc ▸ hstands)) hxclose
      · unfold eventsBeforeProcessingOf
        split
        · first | exact absurd rfl hc | simp_all
        · rfl
    rw [hof', hyProc]
    by_cases hyclose : y = .parenClose
    · -- no body is due where the script has a `)`: a `)` there would fail its run
      have hcalls : arrivalCalls parser' item = [] := by
        apply Classical.byContradiction
        intro hcalls
        obtain ⟨e', events', hfail, hb'⟩ := recAfter_close_fails hcalls version' events₁
        have hres := parserResult_takes htakes hs []
        rw [List.append_nil, driveParse_run, hsplitIn, driveScript_goes_on hrun₁,
          hyclose] at hres
        simp only [driveScript] at hres
        rw [run_bind_split, hfail] at hres
        rcases hres with hres | ⟨error, hres⟩
        · cases hres
        · cases hres
          exact not_benign_causeOf error hb'
      rw [hcalls, hyclose, arrivalCalls_parenClose]
    · rw [arrivalCalls_congr parser' hxclose hyclose]

end BSmtLib.Facts.Proofs.Parser.Rejection.Library
