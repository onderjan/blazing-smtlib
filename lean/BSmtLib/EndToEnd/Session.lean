import BSmtLib.EndToEnd.Classify
import BSmtLib.EndToEnd.Valid

/-!
# A lexer correct with every consumer, with the script consumer, on any input

A lexer that is `Spec.Lexer.CorrectWithConsumers`, fed any slices and then the end of the input,
with the script consumer, ends as `Classified` says (`lexing_classified`); with the parser
properties, the parser's recording run on the tokens taken is then the one the specification
gives (`lexing_session`):

- **finished**: the tokens stand for what a parser takes for a script, and the run has the
  traversal's events (`record`);
- **refused**: they stand for commands that a declaration naming no supported version ends, the
  run has the traversal's events, the last of which is the call of that `set-info`, and fails
  with `unsupportedVersion`;
- **rejected**: the run rejects the last token, the first that no script continues with, having
  made the traversal's events before its processing, where a `)` gets none of the calls due at
  its arrival, and no call at it (`RejectsFirstUnviable`);
  an end of the input that comes too early is such a token;
- **lexical**: the run waits, having made the traversal's events before the next item; the lexer
  failed as `Spec.Lexer` states on the input read from where the last version declaration
  ended, in its version: that input has no tokenisation, and the tokens taken from it are those
  maximal to hand over on its longest viable start.
-/

namespace BSmtLib.EndToEnd

open BSmtLib.Spec BSmtLib.Spec.Grammar BSmtLib.Spec.Lexer
open BSmtLib.Spec.Parser (Takes Ending versionAt record received eventsBefore eventsBeforeProcessing
  eventsBeforeProcessingOf Event)
open BSmtLib.Spec.Parser.Traversal
open BSmtLib.ParserProofs (isArrival)
open BSmtLib.ParserProofs.Rejection (libraryParser rcv rejects_items)

/-- A lexer correct with every consumer, with the script consumer, ends as `Classified` says. -/
theorem lexing_classified (lexing : Lexing) (h : CorrectWithConsumers lexing)
    (version : Lexicon.Version) (slices : List Lexicon.Chars) :
    Classified lexing.fed version slices.flatten
      (lexing (scriptConsumer version) version [] slices true) := by
  have hruns := h.2.1 (scriptConsumer version) version slices true
    (scriptConsumer_breaksAtEnd version)
  rw [scriptConsumer_concrete, readyFrom_false] at hruns
  exact runs_classified h.1 hruns [] [.endOfInput] .finished .done (by simp) (by simp) rfl 0 []
    [] rfl (Or.inl ⟨rfl, rfl⟩) (by simp) (by simp) (Nat.zero_le _) (hist_init version _)
    (fun _ _ hlt => absurd hlt (by simp)) (Or.inl rfl)

/-- What a correct lexer has done where it failed after handing over the tokens: the input has
no tokenisation, and the tokens are those maximal to hand over on its longest viable start. -/
theorem segment_failed {feed : Lexicon.Version → List Lexicon.Chars → Bool → Fed}
    (hc : Correct feed) {version : Lexicon.Version} {input : Lexicon.Chars} {offset : Nat}
    {current : List Handed} (hseg : segment feed version input true offset = ⟨current, true⟩) :
    (¬ ∃ tokens, Lexicon.Tokenization version (input.drop offset) tokens) ∧
      ∀ start, LongestViableStart version (input.drop offset) start →
        ∃ tokens, HandoverMaximal version start tokens ∧
          current = tokens.map fun token =>
            (token.handed version (input.drop offset)).after (input.take offset) := by
  have hf : [input.drop offset].flatten = input.drop offset := by simp
  have hfailed : (feed version [input.drop offset] true).failed = true := by
    have := congrArg Fed.failed hseg
    simpa [segment] using this
  have hfc := SpecChecks.Lexer.failsCorrectly_of_correct hc version [input.drop offset] true
  simp only [FailsCorrectly, ite_true, hf] at hfc
  have hnot := hfc.mp hfailed
  refine ⟨hnot, fun start hs => ?_⟩
  have hcomp : ¬ Complete version [input.drop offset].flatten true := by
    rw [hf]
    exact fun hc' => hnot hc'.2
  obtain ⟨t, hmax, e⟩ := SpecChecks.Lexer.handsOverMaximal_of_correct hc hcomp start
    (by rwa [hf])
  refine ⟨t, hmax, ?_⟩
  have := congrArg Fed.handed hseg
  simp only [segment] at this
  rw [← this, e, hf, List.map_map]
  rfl

/-- What a parser takes for a script, finished, is what a parser receives for it. -/
theorem received_of_takes {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (h : Takes version commands taken ending) :
    ending = .finished → taken = received commands := by
  induction h with
  | done => intro; rfl
  | @command v next rest items ending c hv hm _ ih =>
    intro he
    rw [SpecChecks.Parser.received_cons (ParserProofs.modeAfter_read hm).1, ih he]
  | @stop v last hv hm =>
    obtain rfl := ParserProofs.modeAfter_unparsed hm
    intro; rfl
  | refused => intro he; cases he

/-- The recording run of the library's parser on tokens that stand for all of what a parser
takes: the traversal's events, ending as what it takes does. -/
theorem parse_all {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes version commands taken ending)
    {handed : List Handed} (hst : handed.map (rcv ∘ itemOf) = taken) :
    libraryParser.parse version (handed.map libItem) = (record version commands, ending) := by
  have hlen : handed.length = taken.length := by simpa using congrArg List.length hst
  rw [parse_takes htakes (by rw [hst, hlen, List.take_length]) (Nat.le_of_eq hlen)]
  simp only [hlen, Nat.lt_irrefl, ↓reduceIte]
  rw [← (record_takes htakes).1, eventsBefore_all]

/--
A lexer correct with every consumer, fed any slices and then the end of the input, with the
script consumer: the session and the parser's recording run on the tokens taken end in one of the
four ways of the module's documentation.
-/
theorem lexing_session (lexing : Lexing) (h : CorrectWithConsumers lexing)
    (version : Lexicon.Version) (slices : List Lexicon.Chars) :
    let session := lexing (scriptConsumer version) version [] slices true
    let input := slices.flatten
    let items := session.taken.map (rcv ∘ itemOf)
    let run := libraryParser.parse version (session.taken.map libItem)
    (session.outcome.isFinished = true ∧
        ∃ commands, File version input commands ∧ items = received commands ∧
          run = (record version commands, .finished)) ∨
      (session.outcome = .failed (.consumer (.failed .unsupportedVersion)) ∧
        ∃ commands, Takes version commands items (.failed .unsupportedVersion) ∧
          run = (record version commands, .failed .unsupportedVersion) ∧
          ∃ handled, run.1.getLast? = some (.call .nothing (.commandSetInfo handled))) ∨
      (session.outcome = .failed (.consumer .rejected) ∧
        ∃ commands taken ending, Takes version commands taken ending ∧
          items.dropLast <+: taken ∧ items.dropLast.length < taken.length ∧
          ¬ Spec.Parser.Viable version items ∧
          run.2 = .rejected ∧ run.1.filterMap Event.processed = items ∧
          run.1.getLast? = items.getLast?.map .process ∧
          ∃ last, items.getLast? = some last ∧
            eventsBeforeProcessing items.dropLast.length run.1 =
              eventsBeforeProcessingOf last items.dropLast.length (record version commands)) ∨
      (session.outcome = .failed .lexical ∧
        ∃ commands taken ending, Takes version commands taken ending ∧
          items <+: taken ∧ items.length < taken.length ∧
          run = (eventsBefore items.length (record version commands), .waiting) ∧
          session.version = versionAt version commands items.length ∧
          ∃ offset before current, session.taken = before ++ current ∧
            (before = [] ∧ offset = 0 ∨ before.getLast?.map (·.«end».offset) = some offset) ∧
            (¬ ∃ tokens, Lexicon.Tokenization session.version (input.drop offset) tokens) ∧
            ∀ start, LongestViableStart session.version (input.drop offset) start →
              ∃ tokens, HandoverMaximal session.version start tokens ∧
                current = tokens.map fun token =>
                  (token.handed session.version (input.drop offset)).after
                    (input.take offset)) := by
  intro session input items run
  rcases lexing_classified lexing h version slices with
    ⟨hfin, commands, ht, hfile⟩ | ⟨hout, commands, ht⟩ |
    ⟨hout, commands, taken, ending, before, last, htaken, ht, hp, hlt, hof, hnv, hne⟩ |
    ⟨hout, commands, taken, ending, ht, hp, hlt, hver, offset, before, current, htaken, hoff,
      hseg⟩
  · exact Or.inl ⟨hfin, commands, hfile, received_of_takes ht rfl, parse_all ht rfl⟩
  · refine Or.inr (Or.inl ⟨hout, commands, ht, parse_all ht rfl, ?_⟩)
    obtain ⟨handled, hl⟩ := (record_takes ht).2.1 (by intro h; cases h)
    refine ⟨handled, ?_⟩
    simp only [run]
    rw [parse_all ht rfl]
    exact hl
  · refine Or.inr (Or.inr (Or.inl ⟨hout, commands, taken, ending, ht, ?_⟩))
    have hitems : items = before.map (rcv ∘ itemOf) ++ [rcv (itemOf last)] := by
      simp only [items]
      rw [htaken, List.map_append, List.map_singleton, Function.comp_apply]
    have hdrop : items.dropLast = before.map (rcv ∘ itemOf) := by
      rw [hitems, List.dropLast_concat]
    have hdl : items.dropLast.length = before.length := by rw [hdrop, List.length_map]
    have hmap : ((session.taken.map libItem : List ParserProofs.Rejection.LibItem).map
        (rcv ∘ Subtype.val)) = items := by
      simp [items, libItem, Function.comp_def]
    have hpre : before.map (rcv ∘ itemOf) = taken.take before.length := by
      have := List.prefix_iff_eq_take.mp hp
      simpa using this
    have h₁ : (((session.taken.map libItem : List ParserProofs.Rejection.LibItem).map
        (rcv ∘ Subtype.val))).take before.length = taken.take before.length := by
      rw [hmap, hitems, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
        hpre]
    have h₂ : ∀ item, (((session.taken.map libItem : List ParserProofs.Rejection.LibItem).map
        (rcv ∘ Subtype.val)))[before.length]? = some item →
        item.OfVersion (versionAt version commands before.length) := by
      rw [hmap, hitems]
      intro item hitem
      rw [List.getElem?_append_right (by simp)] at hitem
      simp only [List.length_map, Nat.sub_self, List.getElem?_cons_zero,
        Option.some.injEq] at hitem
      rw [← hitem]
      exact hof
    have hlen : items.length = before.length + 1 := by rw [hitems]; simp
    have h₃ : ¬ Spec.Parser.Viable version ((((session.taken.map libItem :
        List ParserProofs.Rejection.LibItem).map (rcv ∘ Subtype.val))).take
          (before.length + 1)) := by
      rw [hmap, List.take_of_length_le (by omega)]
      exact hnv
    have hrejected : (session.taken.map libItem)[before.length]? = some (libItem last) := by
      rw [htaken]; simp
    obtain ⟨hr₁, hr₂, hr₃, hr₄⟩ := rejects_items version commands taken ending
      (session.taken.map libItem) before.length ht hlt (libItem last) hrejected h₁ h₂
      (by rw [← hpre]; exact hne) h₃
    have hst : (session.taken.map libItem).map libraryParser.stands = items := hmap
    erw [hst] at hr₂
    rw [List.take_of_length_le (by omega)] at hr₂
    erw [hst] at hr₃
    refine ⟨by rw [hdrop]; exact hp, by rw [hdl]; exact hlt, hnv, hr₁, hr₂, ?_, ?_⟩
    · erw [hr₃]
      rw [List.getLast?_eq_getElem?, hlen]
      rfl
    · refine ⟨rcv (itemOf last), by rw [hitems]; simp, ?_⟩
      rw [hdl]
      exact hr₄
  · refine Or.inr (Or.inr (Or.inr ⟨hout, commands, taken, ending, ht, hp,
      by simp only [items, List.length_map]; exact hlt, ?_,
      by simp only [items, List.length_map]; exact hver, offset, before, current, htaken, hoff,
      segment_failed h.1 hseg⟩))
    have hst : session.taken.map (rcv ∘ itemOf) = taken.take session.taken.length := by
      have := List.prefix_iff_eq_take.mp hp
      simpa using this
    simp only [run, items]
    rw [parse_takes ht hst (Nat.le_of_lt hlt)]
    have hlt' : session.taken.length < taken.length := hlt
    simp only [List.length_map, hlt', ↓reduceIte]

/-- A lexer correct with every consumer, with the script consumer, finishes on an input exactly
when the input reads as a file. -/
theorem lexing_finishes_iff (lexing : Lexing) (h : CorrectWithConsumers lexing)
    (version : Lexicon.Version) (slices : List Lexicon.Chars) :
    (lexing (scriptConsumer version) version [] slices true).outcome.isFinished = true ↔
      ∃ commands, File version slices.flatten commands := by
  constructor
  · intro hfin
    rcases lexing_session lexing h version slices with ⟨_, commands, hfile, -⟩ | ⟨hout, -⟩ |
      ⟨hout, -⟩ | ⟨hout, -⟩
    · exact ⟨commands, hfile⟩
    all_goals
      rw [hout] at hfin
      cases hfin
  · rintro ⟨commands, hfile⟩
    exact (lexing_file lexing h version slices hfile).1

/--
A lexer correct with every consumer, fed slices that do not read as a file and then the end of the
input, with the script consumer: the session fails, on a declaration that names no supported
version, at the first token no script continues with, or with a lexical error, as
`lexing_session` states.
-/
theorem lexing_fails (lexing : Lexing) (h : CorrectWithConsumers lexing)
    (version : Lexicon.Version) (slices : List Lexicon.Chars)
    (hnot : ¬ ∃ commands, File version slices.flatten commands) :
    let session := lexing (scriptConsumer version) version [] slices true
    let input := slices.flatten
    let items := session.taken.map (rcv ∘ itemOf)
    let run := libraryParser.parse version (session.taken.map libItem)
    (session.outcome = .failed (.consumer (.failed .unsupportedVersion)) ∧
        ∃ commands, Takes version commands items (.failed .unsupportedVersion) ∧
          run = (record version commands, .failed .unsupportedVersion) ∧
          ∃ handled, run.1.getLast? = some (.call .nothing (.commandSetInfo handled))) ∨
      (session.outcome = .failed (.consumer .rejected) ∧
        ∃ commands taken ending, Takes version commands taken ending ∧
          items.dropLast <+: taken ∧ items.dropLast.length < taken.length ∧
          ¬ Spec.Parser.Viable version items ∧
          run.2 = .rejected ∧ run.1.filterMap Event.processed = items ∧
          run.1.getLast? = items.getLast?.map .process ∧
          ∃ last, items.getLast? = some last ∧
            eventsBeforeProcessing items.dropLast.length run.1 =
              eventsBeforeProcessingOf last items.dropLast.length (record version commands)) ∨
      (session.outcome = .failed .lexical ∧
        ∃ commands taken ending, Takes version commands taken ending ∧
          items <+: taken ∧ items.length < taken.length ∧
          run = (eventsBefore items.length (record version commands), .waiting) ∧
          session.version = versionAt version commands items.length ∧
          ∃ offset before current, session.taken = before ++ current ∧
            (before = [] ∧ offset = 0 ∨ before.getLast?.map (·.«end».offset) = some offset) ∧
            (¬ ∃ tokens, Lexicon.Tokenization session.version (input.drop offset) tokens) ∧
            ∀ start, LongestViableStart session.version (input.drop offset) start →
              ∃ tokens, HandoverMaximal session.version start tokens ∧
                current = tokens.map fun token =>
                  (token.handed session.version (input.drop offset)).after
                    (input.take offset)) := by
  intro session input items run
  rcases lexing_session lexing h version slices with ⟨_, commands, hfile, -⟩ | hr | hr | hr
  · exact absurd ⟨commands, hfile⟩ hnot
  · exact Or.inl hr
  · exact Or.inr (Or.inl hr)
  · exact Or.inr (Or.inr hr)

end BSmtLib.EndToEnd
