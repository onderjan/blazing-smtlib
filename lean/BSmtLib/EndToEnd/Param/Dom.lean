import BSmtLib.EndToEnd.Param.Link
import BSmtLib.EndToEnd.Outcome

/-!
# Where the parser's run depends only on what its items stand for

The library's parser takes items of its own type (`LibItem`), and the parse adapter's items for
a token are not the stand-in consumer's (`libItem`): they hold the same characters, read from
other bytes. The parser's properties say what its run does on items that stand for a start of
what a parser takes (`FollowsTheTraversal`), and on items that stand for such a start followed by
the first item no script continues with, an item a lexer can hand over in the version in force,
where the start does not end with `exit` (`RejectsFirstUnviable`). On such items (`Dom`), the
run's calls, its ending and what it asks of its producer after the last item do not depend on
which items stand for them (`obs_congr`).

`Good` says this of every start of the tokens taken, and that the stand-in consumer went on at
each token but the last: what holds of the tokens a run of the lexer with the stand-in consumer
takes, and so what the parse adapter and the stand-in consumer need to answer alike.
-/

namespace BSmtLib.EndToEnd.Param

open BSmtLibSpec BSmtLibSpec.Grammar BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.ParserProofs BSmtLib.ParserProofs.Rejection

/-- What a parser receives, on which the library's parser's run depends only on what its items
stand for: a start of what a parser takes, or such a start followed by the first item that no
script continues with, an item of the version in force, where the start does not end with
`exit`. -/
def Dom (version : Lexicon.Version) (items : List Received) : Prop :=
  BSmtLibSpec.Parser.Properties.Viable version items ∨
    ∃ commands taken ending pre last, Takes version commands taken ending ∧
      items = pre ++ [last] ∧ pre <+: taken ∧ pre.length < taken.length ∧
      last.OfVersion (versionAt version commands pre.length) ∧
      ¬ BSmtLibSpec.Parser.Properties.Viable version items ∧ ¬ AfterExit version pre

/-- What is read of a recording run: its calls, its ending, and what it asked of its producer
after its last processing. -/
def Obs (run : List Event × Ending) : List Event × Ending × Option Lexicon.Version × Bool :=
  (run.1.filter Event.isCall, run.2, switchOf run.1, discardOf run.1)

/-- The calls of events that end with the processing of the item at the position: those before
that processing. -/
theorem calls_eventsBeforeProcessing : ∀ (events : List Event) (count : Nat),
    (events.filterMap Event.processed).length = count + 1 →
    (∃ received, events.getLast? = some (.process received)) →
    events.filter Event.isCall = (eventsBeforeProcessing count events).filter Event.isCall
  | [], _, h, _ => by simp at h
  | e :: rest, count, hlen, ⟨received, hlast⟩ => by
    have hrest : rest ≠ [] → rest.getLast? = some (.process received) := by
      intro hne
      rw [List.getLast?_cons, List.getLast?_eq_some_getLast hne] at hlast
      rw [List.getLast?_eq_some_getLast hne]
      simpa using hlast
    cases e with
    | process r =>
      simp only [List.filterMap_cons, Event.processed, List.length_cons] at hlen
      cases count with
      | zero =>
        have hnil : rest = [] := by
          refine Classical.byContradiction fun hne => ?_
          have h := hrest hne
          have hmem : Event.process received ∈ rest := List.mem_of_getLast? h
          have : received ∈ rest.filterMap Event.processed :=
            List.mem_filterMap.mpr ⟨_, hmem, rfl⟩
          have h0 : (rest.filterMap Event.processed).length = 0 := by omega
          rw [List.length_eq_zero_iff] at h0
          rw [h0] at this
          cases this
        subst hnil
        rfl
      | succ c =>
        have hne : rest ≠ [] := by
          rintro rfl
          simp at hlen
        have ih := calls_eventsBeforeProcessing rest c (by omega) ⟨received, hrest hne⟩
        simp only [List.filter_cons, Event.isCall, eventsBeforeProcessing]
        exact ih
    | arrive a =>
      simp only [List.filterMap_cons, Event.processed] at hlen
      have hne : rest ≠ [] := by
        rintro rfl
        simp at hlen
      have ih := calls_eventsBeforeProcessing rest count hlen ⟨received, hrest hne⟩
      cases count with
      | zero =>
        simp only [List.filter_cons, Event.isCall, eventsBeforeProcessing]
        exact ih
      | succ c =>
        simp only [List.filter_cons, Event.isCall, eventsBeforeProcessing]
        exact ih
    | call returns request =>
      simp only [List.filterMap_cons, Event.processed] at hlen
      have hne : rest ≠ [] := by
        rintro rfl
        simp at hlast
      have ih := calls_eventsBeforeProcessing rest count hlen ⟨received, hrest hne⟩
      cases count <;> simp only [List.filter_cons, Event.isCall, eventsBeforeProcessing] <;>
        rw [ih] <;> rfl
    | handlerSwitch v =>
      simp only [List.filterMap_cons, Event.processed] at hlen
      have hne : rest ≠ [] := by
        rintro rfl
        simp at hlast
      have ih := calls_eventsBeforeProcessing rest count hlen ⟨received, hrest hne⟩
      cases count <;> simp only [List.filter_cons, Event.isCall, eventsBeforeProcessing] <;>
        rw [ih] <;> rfl
    | producerSwitch v =>
      simp only [List.filterMap_cons, Event.processed] at hlen
      have hne : rest ≠ [] := by
        rintro rfl
        simp at hlast
      have ih := calls_eventsBeforeProcessing rest count hlen ⟨received, hrest hne⟩
      cases count <;> simp only [List.filter_cons, Event.isCall, eventsBeforeProcessing] <;>
        exact ih
    | producerDiscard =>
      simp only [List.filterMap_cons, Event.processed] at hlen
      have hne : rest ≠ [] := by
        rintro rfl
        simp at hlast
      have ih := calls_eventsBeforeProcessing rest count hlen ⟨received, hrest hne⟩
      cases count <;> simp only [List.filter_cons, Event.isCall, eventsBeforeProcessing] <;>
        exact ih

/-- Events that end with a processing ask nothing of the producer after it. -/
theorem afterLastProcess_of_last {events : List Event} {received : Received}
    (h : events.getLast? = some (.process received)) : afterLastProcess events = [] := by
  obtain ⟨init, rfl⟩ : ∃ init, events = init ++ [.process received] := by
    have hne : events ≠ [] := by rintro rfl; simp at h
    refine ⟨events.dropLast, ?_⟩
    rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at h
    rw [← h]
    exact (List.dropLast_concat_getLast hne).symm
  simp [afterLastProcess, isProcessing]

/-- The library's parser's run on items that stand for a start of what a parser takes: the
traversal's events before the next item, and waiting, or at the end, ending as what it takes
does. -/
theorem parse_viable {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes version commands taken ending)
    {received : List Received} (hpre : received <+: taken) {zs : List LibItem}
    (hz : zs.map (rcv ∘ Subtype.val) = received) :
    libraryParser.parse version zs =
      (eventsBefore received.length (record version commands),
        if received.length < taken.length then .waiting else ending) := by
  have hl : zs.length = received.length := by rw [← hz, List.length_map]
  have hst : zs.map (rcv ∘ Subtype.val) = taken.take zs.length := by
    rw [hz, hl]
    exact List.prefix_iff_eq_take.mp hpre
  rw [parse_items htakes hst (by rw [hl]; exact hpre.length_le), hl]

/-- The library's parser's run on items that stand for a start of what a parser takes that does not
end with `exit`, followed by the first item that no script continues with, an item of the version
in force: it rejects that item, having made the traversal's calls before the item's processing,
and asks nothing of its producer after it. -/
theorem obs_first_unviable {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes version commands taken ending)
    {pre : List Received} {last : Received} (hpre : pre <+: taken)
    (hlt : pre.length < taken.length)
    (hof : last.OfVersion (versionAt version commands pre.length))
    (hnot : ¬ BSmtLibSpec.Parser.Properties.Viable version (pre ++ [last])) (hne : ¬ AfterExit version pre)
    {zs : List LibItem}
    (hz : zs.map (rcv ∘ Subtype.val) = pre ++ [last]) :
    Obs (libraryParser.parse version zs) =
      ((eventsBeforeProcessingOf last pre.length (record version commands)).filter
        Event.isCall, .rejected, none, false) := by
  have hzl : zs.length = pre.length + 1 := by
    rw [← List.length_map (f := rcv ∘ Subtype.val), hz]; simp
  have hstands : zs.map libraryParser.stands = pre ++ [last] := hz
  obtain ⟨rejected, hrejected⟩ : ∃ r, zs[pre.length]? = some r := by
    refine ⟨zs[pre.length]'(by omega), ?_⟩
    simp
  have hrs : libraryParser.stands rejected = last := by
    have h1 : (zs.map (rcv ∘ Subtype.val))[pre.length]? = some (rcv rejected.val) := by
      rw [List.getElem?_map, hrejected]; rfl
    have h2 : (pre ++ [last])[pre.length]? = some last := by simp
    rw [hz, h2] at h1
    exact (Option.some.inj h1).symm
  have hpre' : pre = taken.take pre.length := List.prefix_iff_eq_take.mp hpre
  have hagree : (zs.map libraryParser.stands).take pre.length = taken.take pre.length := by
    rw [hstands, List.take_append_of_le_length (Nat.le_refl _), List.take_length, ← hpre']
  have hlex : ∀ item, (zs.map libraryParser.stands)[pre.length]? = some item →
      item.OfVersion (versionAt version commands pre.length) := by
    intro item hitem
    rw [hstands, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hitem
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hitem
    rw [← hitem]
    exact hof
  have hunv : ¬ BSmtLibSpec.Parser.Properties.Viable version
      ((zs.map libraryParser.stands).take (pre.length + 1)) := by
    rw [hstands, List.take_of_length_le (by simp)]
    exact hnot
  obtain ⟨hend, hproc, hlast, hbefore⟩ := rejects_items version commands taken ending zs
    pre.length htakes hlt rejected hrejected hagree hlex (by rw [← hpre']; exact hne) hunv
  change _ = (zs.map libraryParser.stands).take (pre.length + 1) at hproc
  change _ = ((zs.map libraryParser.stands)[pre.length]?).map _ at hlast
  change _ = eventsBeforeProcessingOf (libraryParser.stands rejected) _ _ at hbefore
  rw [hrs] at hbefore
  have hlast' : (libraryParser.parse version zs).1.getLast? = some (.process last) := by
    rw [hlast, hstands, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hproclen : ((libraryParser.parse version zs).1.filterMap Event.processed).length =
      pre.length + 1 := by
    rw [hproc, hstands, List.take_of_length_le (by simp)]
    simp
  unfold Obs
  rw [calls_eventsBeforeProcessing _ pre.length hproclen ⟨last, hlast'⟩, hbefore, hend]
  unfold switchOf discardOf
  rw [afterLastProcess_of_last hlast']
  rfl

/-- On what a parser receives where the library's parser's run depends only on what its items
stand for, two runs on items that stand for it are read alike. -/
theorem obs_congr {version : Lexicon.Version} {received : List Received}
    (hdom : Dom version received) {xs ys : List LibItem}
    (hx : xs.map (rcv ∘ Subtype.val) = received) (hy : ys.map (rcv ∘ Subtype.val) = received) :
    Obs (libraryParser.parse version xs) = Obs (libraryParser.parse version ys) := by
  rcases hdom with ⟨commands, taken, ending, htakes, hpre⟩ | ⟨commands, taken, ending, pre, last,
      htakes, rfl, hpre, hlt, hof, hnot, hne⟩
  · rw [parse_viable htakes hpre hx, parse_viable htakes hpre hy]
  · rw [obs_first_unviable htakes hpre hlt hof hnot hne hx,
      obs_first_unviable htakes hpre hlt hof hnot hne hy]

/-- On such items, the library's parser does not wait after the end of the input. -/
theorem parse_endOfInput {version : Lexicon.Version} {received : List Received}
    (hdom : Dom version received) (hend : received.getLast? = some .endOfInput)
    {zs : List LibItem} (hz : zs.map (rcv ∘ Subtype.val) = received) :
    (libraryParser.parse version zs).2 ≠ .waiting := by
  rcases hdom with ⟨commands, taken, ending, htakes, hpre⟩ | ⟨commands, taken, ending, pre, last,
      htakes, rfl, hpre, hlt, hof, hnot, hne⟩
  · rw [parse_viable htakes hpre hz]
    have hne : received ≠ [] := by rintro rfl; simp at hend
    have hle := hpre.length_le
    have hall : ¬ received.length < taken.length := by
      intro hlt'
      have hat : taken[received.length - 1]? = some .endOfInput := by
        rw [← hend, List.getLast?_eq_getElem?]
        obtain ⟨rest, rfl⟩ := hpre
        rw [List.getElem?_append_left (by have := List.length_pos_iff.mpr hne; omega)]
      exact takes_endOfInput_last htakes (received.length - 1)
        (by have := List.length_pos_iff.mpr hne; omega) hat
    simp only [hall, ite_false]
    rcases takes_ending htakes with rfl | rfl <;> nofun
  · have := congrArg (fun o => o.2.1) (obs_first_unviable htakes hpre hlt hof hnot hne hz)
    simp only [Obs] at this
    rw [this]
    nofun

/-! ## The tokens a run takes -/

/-- What the tokens taken stand for, from the version, is where the parser's run depends only
on what its items stand for, at every start of them, and the stand-in consumer went on at every
token but the last. -/
def Good (version : Lexicon.Version) (taken : List Handed) : Prop :=
  (∀ n ≤ taken.length, Dom version ((taken.take n).map (rcv ∘ itemOf))) ∧
    ∀ n, 0 < n → n < taken.length → (scriptConsumer version).answer (taken.take n) = .continue

theorem Good.of_append {version : Lexicon.Version} {taken more : List Handed}
    (h : Good version (taken ++ more)) : Good version taken := by
  refine ⟨fun n hn => ?_, fun n hn hlt => ?_⟩
  · have := h.1 n (by simp; omega)
    rwa [List.take_append_of_le_length hn] at this
  · have := h.2 n hn (by simp; omega)
    rwa [List.take_append_of_le_length (by omega)] at this

end BSmtLib.EndToEnd.Param
