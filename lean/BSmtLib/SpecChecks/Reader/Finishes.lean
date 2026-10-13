import BSmtLib.SpecChecks.Reader.Commands

/-!
# A lexer with a parser finishes only on a file

A correct lexer with a parser that follows the traversal and rejects the first item that no
script continues with as its consumer finishes only when the parser has taken what a parser
takes for a script (`finishes_script`): as long as the parser continues, the items it took stand
for a strict start of what a parser takes for commands, as it would otherwise have rejected an
item or finished; the lexer hands over reserved words of the version in force, which is the
version the traversal has switched to, and after the parser has asked for the discarding, as
the traversal does after `exit`, nothing but the end of the file (`viable_step`). The tokens the parser took are then those
of a file with that script, each command read in the version in force (`finishes_file`): the
lexer has handed them over from a readout of the input after the last switch (`next_command`).

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Reader

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Lexer BSmtLib.Spec.Grammar
open BSmtLib.Spec.Parser BSmtLib.Spec.Reader
open BSmtLib.SpecChecks.Lexicon BSmtLib.SpecChecks.Lexer BSmtLib.SpecChecks.Grammar

/-! ## Scripts among what a parser takes -/

theorem ne_exit_of_exitFlag {command : Tree.Command} (h : exitFlag command = false) :
    command ≠ .exit := by
  rintro rfl; simp [exitFlag] at h

/-- What a parser takes for a script is what it receives for it. -/
theorem script_takes {version : Version} {commands : List Tree.Command}
    (h : Script version commands) : Takes version commands (received commands) .finished := by
  induction h with
  | done => exact .done
  | command hv hm _ ih =>
    have hne := ne_exit_of_exitFlag (read_next hm).2
    rw [Parser.received_cons hne]
    exact .command hv hm ih
  | stop hv hm =>
    obtain rfl := Parser.modeAfter_unparsed hm
    exact .stop hv hm

/-- What a parser takes, finishing, is what it receives for a script. -/
theorem takes_finished {version : Version} {commands : List Tree.Command}
    {taken : List Traversal.Received} {ending : Ending} (h : Takes version commands taken ending)
    (he : ending = .finished) : Script version commands ∧ taken = received commands := by
  induction h with
  | done => exact ⟨.done, rfl⟩
  | command hv hm _ ih =>
    have hne := ne_exit_of_exitFlag (read_next hm).2
    obtain ⟨hs, rfl⟩ := ih he
    exact ⟨.command hv hm hs, (Parser.received_cons hne _).symm⟩
  | stop hv hm =>
    obtain rfl := Parser.modeAfter_unparsed hm
    exact ⟨.stop hv hm, rfl⟩
  | refused => cases he

/-- What a parser receives for a script ends with the end of the input. -/
theorem received_getLast (commands : List Tree.Command) :
    (received commands).getLast? = some .endOfInput := by
  induction commands with
  | nil => rfl
  | cons first rest ih =>
    by_cases hne : first = .exit
    · subst hne; simp [received]
    · rw [Parser.received_cons hne, List.getLast?_append, ih]
      rfl

/-! ## Runs -/

/-- The versions after the tokens agree when the switches agree up to them. -/
theorem foldVersion_congr_le (start : Version) {switch switch' : Nat → Option Version} :
    ∀ count, (∀ j, 1 ≤ j → j ≤ count → switch j = switch' j) →
      foldVersion start switch count = foldVersion start switch' count
  | 0, _ => rfl
  | count + 1, h => by
    simp only [foldVersion, h (count + 1) (by omega) (Nat.le_refl _),
      foldVersion_congr_le start count (fun j h₁ h₂ => h j h₁ (by omega))]

variable {lexing : Lexing} {parser : RecordingParser} {item : Handed → parser.Item}

/-- Every token that a correct lexer hands over after reading from the offset on in a version
stands for an item that a lexer of that version hands over. -/
theorem segment_ofVersion (hL : Correct lexing.fed) (version : Version) (input : Chars)
    (offset : Nat) :
    ∀ handed ∈ (Spec.Lexer.segment lexing.fed version input true offset).handed,
      ∃ received, handed.received = some received ∧ received.OfVersion version := by
  obtain ⟨tokens, ⟨other, all, _, hall, hp, -, -⟩, he⟩ :=
    fed_readout hL version (input.drop offset)
  have htok : ∀ token ∈ tokens, ∀ before,
      ∃ received, ((token.handed version (input.drop offset)).after before).received =
        some received ∧ received.OfVersion version := by
    intro token ht before
    obtain ⟨more, rfl⟩ := hp
    have hreg := (tokenizationFrom_mem hall token (by simp [ht])).1
    exact ⟨_, (received_handed hreg (input.drop offset)).1,
      (received_handed hreg (input.drop offset)).2⟩
  intro handed hh
  simp only [Spec.Lexer.segment, List.mem_map] at hh
  obtain ⟨handed, hh, rfl⟩ := hh
  rcases he with he | ⟨-, he⟩ <;> rw [he] at hh <;> simp only [List.mem_append, List.mem_map,
    List.mem_singleton] at hh
  · obtain ⟨token, ht, rfl⟩ := hh
    exact htok token ht _
  · rcases hh with ⟨token, ht, rfl⟩ | rfl
    · exact htok token ht _
    · exact ⟨.endOfInput, rfl, trivial⟩

variable (hF : FollowsTheTraversal parser) (hR : RejectsFirstUnviable parser)
  (hI : StandsFor parser item)

include hF hR hI in
/-- A parser that continues on tokens that stand for a strict start of what a parser takes
rejects the next token, or the tokens with it are a start of what a parser takes, when the next
token stands for the end of the input wherever the traversal has asked for the discarding before
it. -/
theorem viable_step {start : Version} {commands : List Tree.Command}
    {all : List Traversal.Received} {ending : Ending} (ht : Takes start commands all ending)
    {taken : List Handed} {handed : Handed} {received : Traversal.Received}
    (hs : stood parser item taken = all.take taken.length) (hlt : taken.length < all.length)
    (hr : parser.stands (item handed) = received)
    (hv : received.OfVersion (versionAt start commands taken.length))
    (hd : .producerDiscard ∈ eventsBefore taken.length (record start commands) →
      received = .endOfInput) :
    (parser.parse start ((taken ++ [handed]).map item)).2 = .rejected ∨
      ∃ commands' all' ending', Takes start commands' all' ending' ∧
        stood parser item (taken ++ [handed]) = all'.take (taken.length + 1) ∧
        taken.length + 1 ≤ all'.length ∧
        (parser.parse start ((taken ++ [handed]).map item)).2 =
          if taken.length + 1 < all'.length then .waiting else ending' := by
  have hstood : ((taken ++ [handed]).map item).map parser.stands =
      stood parser item (taken ++ [handed]) := by simp [stood]
  have hlen : (taken ++ [handed]).length = taken.length + 1 := by simp
  by_cases hviable : Viable start (stood parser item (taken ++ [handed]))
  · obtain ⟨commands', all', ending', ht', hp⟩ := hviable
    have hle : taken.length + 1 ≤ all'.length := by
      have := hp.length_le
      simpa [stood] using this
    have hs' : stood parser item (taken ++ [handed]) = all'.take (taken ++ [handed]).length := by
      have := List.prefix_iff_eq_take.mp hp
      simpa [stood] using this
    refine Or.inr ⟨commands', all', ending', ht', by rw [hs', hlen], hle, ?_⟩
    rw [parse_of_takes hF hI ht' hs' (by rw [hlen]; exact hle), hlen]
  · left
    refine (hR start commands all ending ((taken ++ [handed]).map item) taken.length (item handed)
      ht hlt (by simp) ?_ ?_ ?_ ?_).1
    · rw [hstood, stood_append, List.take_left' (by simp [stood]), hs]
    · intro r hr'
      rw [hstood, stood_append] at hr'
      simp [stood, hr] at hr'
      rw [← hr']; exact hv
    · intro hm
      rw [hstood, stood_append]
      simp [stood, hr, hd hm]
    · rw [hstood, List.take_of_length_le (by simp [stood])]
      exact hviable

/-- A parser that takes what a parser takes for commands does not wait at their end. -/
theorem takes_not_waiting {version : Version} {commands : List Tree.Command}
    {taken : List Traversal.Received} {ending : Ending} (h : Takes version commands taken ending) :
    ending ≠ .waiting := by
  induction h with
  | command _ _ _ ih => exact ih
  | _ => simp

/-- Only the end of the file stands for the end of the input. -/
theorem type_of_received_endOfInput {handed : Handed}
    (h : handed.received = some .endOfInput) : handed.type = .endOfFile := by
  cases ht : handed.type <;> simp only [Handed.received, ht] at h
  all_goals first | rfl | (split at h <;> simp at h) | simp at h

omit hF hR hI in
/-- A parser that breaks as a consumer has finished. -/
theorem parse_of_break {start : Version} {taken : List Handed} {result : Unit}
    (h : (parser.consumer item start).answer taken = .break result) :
    (parser.parse start (taken.map item)).2 = .finished := by
  rw [answer_eq] at h
  revert h
  cases (parser.parse start (taken.map item)).2 <;> simp
  split <;> simp

omit hF hR hI in
/-- A parser that continues as a consumer waits. -/
theorem parse_of_continue {start : Version} {taken : List Handed}
    (h : (parser.consumer item start).answer taken = .continue) :
    (parser.parse start (taken.map item)).2 = .waiting := by
  rw [answer_eq] at h
  revert h
  cases (parser.parse start (taken.map item)).2 <;> simp

omit hF hR hI in
/-- A parser that rejects as a consumer fails. -/
theorem answer_of_rejected {start : Version} {taken : List Handed}
    (h : (parser.parse start (taken.map item)).2 = .rejected) :
    (parser.consumer item start).answer taken = .fail () := by
  rw [answer_eq, h]

include hF hI in
/-- The version in force after tokens that stand for a start of what a parser takes, switched as
the parser asks, is the version in force there. -/
theorem foldVersion_of_takes {start : Version} {commands : List Tree.Command}
    {all : List Traversal.Received} {ending : Ending} (ht : Takes start commands all ending)
    {taken : List Handed} (hs : stood parser item taken = all.take taken.length)
    (hl : taken.length ≤ all.length) :
    foldVersion start (fun j => (parser.consumer item start).switchTo (taken.take j))
      taken.length = versionAt start commands taken.length := by
  rw [← foldVersion_requestsAt]
  refine foldVersion_congr_le start _ fun j h₁ h₂ => ?_
  have hlj : (taken.take j).length = j := by simp; omega
  have hsj : stood parser item (taken.take j) = all.take (taken.take j).length := by
    rw [hlj]
    have := congrArg (List.take j) hs
    simpa [stood, List.map_take, List.take_take, Nat.min_eq_left h₂] using this
  rw [switchTo_of_takes hF hI ht hsj (by omega) (by omega), hlj]

include hF hR hI in
/--
A correct lexer with a parser that follows the traversal and rejects the first item that no
script continues with as its consumer, from a point where the parser has taken tokens that stand
for a strict start of what a parser takes, the lexer is in the version the parser switched to,
and every token ready stands for an item of that version: if the run finishes, the parser has
taken what a parser takes for a script.
-/
theorem finishes_script (hL : Correct lexing.fed) {start : Version} {input : Chars} :
    ∀ {version ready failed taken session},
      Runs lexing.fed (parser.consumer item start) start input true version ready failed taken
        session →
      (∃ commands all ending, Takes start commands all ending ∧
        stood parser item taken = all.take taken.length ∧ taken.length < all.length) →
      version = foldVersion start
        (fun j => (parser.consumer item start).switchTo (taken.take j)) taken.length →
      (∀ handed ∈ ready, ∃ received, handed.received = some received ∧
        received.OfVersion version) →
      (taken = [] ∨ (parser.consumer item start).discards taken = false) →
      session.outcome.isFinished = true →
      ∃ commands, Script start commands ∧ stood parser item session.taken = received commands := by
  intro version ready failed taken session hruns
  -- the next token: the parser rejects it or the tokens with it are a start of a script
  have next : ∀ {taken : List Handed} {handed : Handed},
      (∃ commands all ending, Takes start commands all ending ∧
        stood parser item taken = all.take taken.length ∧ taken.length < all.length) →
      (∃ received, handed.received = some received ∧ received.OfVersion (foldVersion start
        (fun j => (parser.consumer item start).switchTo (taken.take j)) taken.length)) →
      (taken = [] ∨ (parser.consumer item start).discards taken = false ∨
        handed.received = some .endOfInput) →
      (parser.consumer item start).answer (taken ++ [handed]) ≠ .fail () →
      ∃ commands' all' ending', Takes start commands' all' ending' ∧
        stood parser item (taken ++ [handed]) = all'.take (taken.length + 1) ∧
        taken.length + 1 ≤ all'.length ∧
        (parser.parse start ((taken ++ [handed]).map item)).2 =
          if taken.length + 1 < all'.length then .waiting else ending' := by
    intro taken handed ⟨commands, all, ending, ht, hs, hlt⟩ ⟨received, hr, hof⟩ hdisc hans
    rw [foldVersion_of_takes hF hI ht hs (Nat.le_of_lt hlt)] at hof
    -- where the traversal has asked for the discarding, the parser has, and the lexer has handed
    -- over the end of the file
    have hend : .producerDiscard ∈ eventsBefore taken.length (record start commands) →
        received = .endOfInput := by
      intro hm
      obtain ⟨h₁, hreq⟩ := discard_record ht hlt hm
      rcases hdisc with rfl | hd | he
      · simp at h₁
      · rw [discards_of_takes hF hI ht hs h₁ (Nat.le_of_lt hlt), hreq] at hd
        cases hd
      · rw [hr] at he
        exact Option.some.inj he
    rcases viable_step hF hR hI ht hs hlt (hI _ _ _ hr hof) hof hend with hrej | hok
    · exact absurd (answer_of_rejected hrej) hans
    · exact hok
  -- the parser finishes only on what a parser takes for a script
  have finished : ∀ {taken : List Handed} {commands' : List Tree.Command}
      {all' : List Traversal.Received} {ending' : Ending},
      Takes start commands' all' ending' →
      stood parser item taken = all'.take taken.length → taken.length ≤ all'.length →
      (parser.parse start (taken.map item)).2 =
        (if taken.length < all'.length then .waiting else ending') →
      (parser.parse start (taken.map item)).2 = .finished →
      Script start commands' ∧ stood parser item taken = received commands' := by
    intro taken commands' all' ending' ht' hs' hle' hp hfin
    rw [hfin] at hp
    split at hp
    · cases hp
    · obtain ⟨hscript, hrec'⟩ := takes_finished ht' hp.symm
      refine ⟨hscript, ?_⟩
      rw [hs', List.take_of_length_le (by omega), hrec']
  -- the parser continues only on a strict start of what a parser takes
  have waiting : ∀ {taken : List Handed} {commands' : List Tree.Command}
      {all' : List Traversal.Received} {ending' : Ending},
      Takes start commands' all' ending' →
      (parser.parse start (taken.map item)).2 =
        (if taken.length < all'.length then .waiting else ending') →
      (parser.parse start (taken.map item)).2 = .waiting → taken.length < all'.length := by
    intro taken commands' all' ending' ht' hp hw
    rw [hw] at hp
    split at hp
    · assumption
    · exact absurd hp.symm (takes_not_waiting ht')
  -- a token that is not the end of the file stands for no end of the input
  have notEnd : ∀ {version : Version} {handed : Handed}, handed.type ≠ .endOfFile →
      (∃ received, handed.received = some received ∧ received.OfVersion version) →
      parser.stands (item handed) ≠ .endOfInput := by
    intro version handed htype ⟨received, hr, hof⟩ he
    rw [hI _ _ _ hr hof] at he
    subst he
    exact htype (type_of_received_endOfInput hr)
  -- the parser cannot break at a token that is not the end of the file
  have noBreak : ∀ {taken : List Handed} {handed : Handed} {result : Unit},
      (∃ commands all ending, Takes start commands all ending ∧
        stood parser item taken = all.take taken.length ∧ taken.length < all.length) →
      (∃ received, handed.received = some received ∧ received.OfVersion (foldVersion start
        (fun j => (parser.consumer item start).switchTo (taken.take j)) taken.length)) →
      (taken = [] ∨ (parser.consumer item start).discards taken = false) →
      handed.type ≠ .endOfFile →
      (parser.consumer item start).answer (taken ++ [handed]) = .break result → False := by
    intro taken handed result hinv hrec hd0 htype hans
    obtain ⟨commands', all', ending', ht', hs', hle', hp⟩ :=
      next hinv hrec (hd0.imp_right Or.inl) (by rw [hans]; simp)
    obtain ⟨-, hfull⟩ := finished ht' (by simpa using hs') (by simpa using hle')
      (by simpa using hp) (parse_of_break hans)
    have := congrArg List.getLast? hfull
    rw [received_getLast, stood_append] at this
    simp [stood] at this
    exact notEnd htype hrec this
  induction hruns with
  | waiting => intros; simp_all [settle, Outcome.isFinished]
  | lexical => intros; simp_all [settle, Outcome.isFinished]
  | fails => intros; simp_all [settle, Outcome.isFinished]
  | discardsHeld => intros; simp_all
  | discardsWaiting => intros; simp_all
  | discardsFailsAtEnd => intros; simp_all [settle, Outcome.isFinished]
  | @ends taken token result version ready failed htype hans =>
    intro hinv hv hready hd0 _
    obtain ⟨commands', all', ending', ht', hs', hle', hp⟩ :=
      next hinv (hv ▸ hready token (by simp)) (hd0.imp_right Or.inl) (by rw [hans]; simp)
    obtain ⟨hscript, hfull⟩ := finished ht' (by simpa using hs') (by simpa using hle')
      (by simpa using hp) (parse_of_break hans)
    refine ⟨commands', hscript, ?_⟩
    simpa [settle, Outcome.isFinished] using hfull
  | @breaks taken token result ready failed outcome version htype hans _ _ =>
    intro hinv hv hready hd0 _
    exact (noBreak hinv (hv ▸ hready token (by simp)) hd0 htype hans).elim
  | @discardsEnds taken token result version ready failed htype hans _ _ =>
    intro hinv hv hready hd0 _
    exact (noBreak hinv (hv ▸ hready token (by simp)) hd0 htype hans).elim
  | @continues taken token version ready failed session htype hans hdisc _ ih =>
    intro hinv hv hready hd0 hfin
    obtain ⟨commands', all', ending', ht', hs', hle', hp⟩ :=
      next hinv (hv ▸ hready token (by simp)) (hd0.imp_right Or.inl) (by rw [hans]; simp)
    have hlen : (taken ++ [token]).length = taken.length + 1 := by simp
    have hlt := waiting ht' (by simpa using hp) (parse_of_continue hans)
    rw [hlen] at hlt
    refine ih ⟨commands', all', ending', ht', by rw [hlen]; exact hs', by rw [hlen]; exact hlt⟩
      ?_ ?_ (Or.inr hdisc) hfin
    · rw [hlen]
      simp only [foldVersion]
      rw [List.take_of_length_le (by simp), hv]
      congr 1
      exact foldVersion_congr_le start _ fun j _ h₂ => by
        rw [List.take_append_of_le_length h₂]
    · cases hsw : (parser.consumer item start).switchTo (taken ++ [token]) with
      | none =>
        simp only [following, Option.getD_none]
        exact fun handed hh => hready handed (by simp [hh])
      | some declared =>
        simp only [following, readyFrom, withLayout, Option.getD_some]
        exact segment_ofVersion hL declared input _
  | @discardsToEnd taken token result version ready failed htype hans hdisc hended hans' =>
    intro hinv hv hready hd0 _
    obtain ⟨commands', all', ending', ht', hs', hle', hp⟩ :=
      next hinv (hv ▸ hready token (by simp)) (hd0.imp_right Or.inl) (by rw [hans]; simp)
    have hlen : (taken ++ [token]).length = taken.length + 1 := by simp
    have hlt := waiting ht' (by simpa using hp) (parse_of_continue hans)
    rw [hlen] at hlt
    have hans'' : (parser.consumer item start).answer
        ((taken ++ [token]) ++ [endOfFileAt token.«end»]) = .break result := by
      rw [List.append_assoc, List.singleton_append]; exact hans'
    obtain ⟨commands'', all'', ending'', ht'', hs'', hle'', hp''⟩ :=
      next (taken := taken ++ [token]) (handed := endOfFileAt token.«end»)
        ⟨commands', all', ending', ht', by rw [hlen]; exact hs', by rw [hlen]; exact hlt⟩
        ⟨.endOfInput, rfl, trivial⟩ (Or.inr (Or.inr rfl)) (by rw [hans'']; simp)
    obtain ⟨hscript, hfull⟩ := finished ht'' (by simpa using hs'') (by simpa using hle'')
      (by simpa using hp'') (parse_of_break hans'')
    refine ⟨commands'', hscript, ?_⟩
    simpa [settle, Outcome.isFinished] using hfull

/-! ## The file a lexer with a parser has read -/

/-- What a correct lexer hands over reading the input on its own in the version, as
`fed_readout` describes it. -/
def ReadoutFed (lexing : Lexing) (version : Version) (input : Chars) (tokens : List Token) :
    Prop :=
  (lexing.fed version [input] true).handed = tokens.map (·.handed version input) ∨
    (Tokenization version input tokens ∧
      (lexing.fed version [input] true).handed =
        tokens.map (·.handed version input) ++ [endOfFile input])

omit hF hR in
/-- A token handed over from a readout stands for no end of the input. -/
theorem stands_blockHanded (hI : StandsFor parser item) {version : Version} {input : Chars}
    {offset : Nat} {tokens : List Token} (hread : Readout version (input.drop offset) tokens)
    {handed : Handed} (h : handed ∈ blockHanded version input offset tokens) :
    parser.stands (item handed) ≠ .endOfInput := by
  simp only [blockHanded, List.mem_map] at h
  obtain ⟨token, ht, rfl⟩ := h
  have := stood_blockHanded hI hread (rel := [token]) (by simpa using ht)
  simp [stood, blockHanded] at this
  rw [this]
  simp

include hF hI in
/--
The next command of a script whose tokens a parser takes from a correct lexer: the lexer has
handed over its tokens, after the block it reads, the parser continued on them, and they are the
tokens of characters that follow the block and are the command.
-/
theorem next_command {start : Version} {input : Chars} {all : List Tree.Command}
    {session : Session (parser.consumer item start).Result (parser.consumer item start).Error}
    (hS : Takes start all (received all) .finished)
    (hfull : stood parser item session.taken = received all)
    {version : Version} {command : Tree.Command} {commands : List Tree.Command}
    {taken : List Handed} {offset stop : Nat} {block tokens : List Token}
    (hruns : Runs lexing.fed (parser.consumer item start) start input true version
      ((Spec.Lexer.segment lexing.fed version input true offset).handed.drop block.length)
      (Spec.Lexer.segment lexing.fed version input true offset).failed taken session)
    (hrec : received all = stood parser item taken ++ command.tokens.map .token ++
      received commands)
    (hreq : ∀ i, 1 ≤ i → requestsAt all (taken.length + i) = requestsAt (command :: commands) i)
    (hos : offset ≤ stop) (hle : stop ≤ input.length)
    (hclosed : stop = offset ∧ block = [] ∨ EndsWithClose block (stop - offset))
    (hread : Readout version (input.drop offset) tokens)
    (hfed : ReadoutFed lexing version (input.drop offset) tokens)
    (hblockEq : block = tokens.take block.length) (hv : command.Valid version) :
    ∃ handed last more segment rel,
      stood parser item handed = command.tokens.map .token ∧
      handed = handed.dropLast ++ [last] ∧ last.type ≠ .endOfFile ∧
      Runs lexing.fed (parser.consumer item start) start input true version (last :: more)
        (Spec.Lexer.segment lexing.fed version input true offset).failed
        (taken ++ handed.dropLast) session ∧
      (Spec.Lexer.segment lexing.fed version input true offset).handed.drop
        (block ++ rel).length = more ∧
      (parser.consumer item start).answer (taken ++ handed) = .continue ∧
      (parser.consumer item start).switchTo (taken ++ handed) = command.declaredVersion ∧
      (parser.consumer item start).discards (taken ++ handed) = exitFlag command ∧
      input.drop stop = segment ++ input.drop (stop + segment.length) ∧
      TokenizationExactly version stop segment (rel.map (Token.moveBy offset)) ∧
      IsCommand version ((rel.map (Token.moveBy offset)).map (SyntaxToken.ofToken version))
        command ∧
      block ++ rel = tokens.take (block ++ rel).length ∧
      Tokenization version ((input.drop offset).take (stop + segment.length - offset))
        (block ++ rel) ∧
      EndsWithClose (block ++ rel) (stop + segment.length - offset) ∧
      last.«end».offset = stop + segment.length ∧ stop + segment.length ≤ input.length := by
  obtain ⟨rest, hrest⟩ := runs_prefix hruns
  have hstoodRest : stood parser item rest = command.tokens.map .token ++ received commands := by
    have := hfull
    rw [← hrest, stood_append, hrec, List.append_assoc] at this
    exact List.append_cancel_left this
  have hk₁ : 1 ≤ command.tokens.length := List.length_pos_iff.mpr (tokens_ne_nil command)
  have hlenRest : command.tokens.length + 1 ≤ rest.length := by
    have h₁ := congrArg List.length hstoodRest
    have h₂ := List.length_pos_iff.mpr (received_ne_nil commands)
    simp [stood] at h₁
    omega
  have hstoodToks : stood parser item (rest.take command.tokens.length) =
      command.tokens.map .token := by
    have : stood parser item (rest.take command.tokens.length) =
        (stood parser item rest).take command.tokens.length := by
      simp [stood, List.map_take]
    rw [this, hstoodRest, List.take_left' (by simp)]
  have htype : ∀ handed ∈ rest.take command.tokens.length, handed.type ≠ .endOfFile := by
    intro handed hh he
    have hmem : Traversal.Received.endOfInput ∈ stood parser item
        (rest.take command.tokens.length) := by
      rw [← stands_endOfFile hI he]; exact List.mem_map_of_mem hh
    rw [hstoodToks] at hmem
    simp at hmem
  have steps := command_steps hF hI hS hrec hreq hstoodToks htype
  have hlenToks : (rest.take command.tokens.length).length = command.tokens.length := by
    simp; omega
  obtain ⟨htake, last, more, hdrop, htk, hlastRun⟩ := runs_command hk₁ (by omega) hruns hrest.symm
    (fun i h₁ h₂ => by
      obtain ⟨ha, hs, hd⟩ := steps i h₁ (by omega)
      rw [List.take_take, Nat.min_eq_left (by omega)] at ha hs hd
      simp only [requestsAt, h₂, ite_true] at hs hd
      exact ⟨ha, hd, hs⟩) htype
  obtain ⟨ha, hs, hd⟩ := steps command.tokens.length hk₁ (by omega)
  rw [List.take_of_length_le (by omega)] at ha hs hd
  simp only [requestsAt, Nat.lt_irrefl, ite_false, ite_true] at hs hd
  have hhandedEq : rest.take command.tokens.length =
      (rest.take command.tokens.length).dropLast ++ [last] := by
    rw [htk]; simp
  have hlastMem : last ∈ rest.take command.tokens.length := by rw [htk]; simp
  obtain ⟨segment, rel, hdropc, htokEx, hic, hhanded, htakeTok, htokNew, hcloseNew, hlastEnd,
    hleNew⟩ := command_of_handed hI hread hfed hblockEq hos hle hclosed htake hstoodToks hv
  have hrelLen : rel.length = command.tokens.length := by
    have := congrArg List.length hhanded
    simp [blockHanded] at this
    omega
  refine ⟨rest.take command.tokens.length, last, more, segment, rel, hstoodToks, hhandedEq,
    htype last hlastMem, ?_, ?_, ha, hs, hd, hdropc, htokEx, hic, ?_, htokNew, hcloseNew, ?_,
    hleNew⟩
  · rw [htk]; simpa using hlastRun
  · rw [List.length_append, hrelLen, show block.length + command.tokens.length =
      block.length + (command.tokens.length - 1) + 1 by omega, ← List.drop_drop,
      ← List.drop_drop, hdrop]
    simp
  · rw [List.length_append, htakeTok]
  · rw [hhandedEq, List.getLast?_append] at hlastEnd
    simpa using hlastEnd

include hF hI in
/--
A correct lexer with a parser that follows the traversal as its consumer, which takes what a
parser takes for a script: from a point between two commands, where the parser has taken the
tokens of the commands before, the lexer reads from `offset` on in the version in force, and the
commands from there to `stop` are a block of the tokens it has handed over, the rest of the input
from `stop` on is a file with the rest of the commands.
-/
theorem finishes_file (hL : Correct lexing.fed) {start : Version} {input : Chars}
    {all : List Tree.Command}
    {session : Session (parser.consumer item start).Result (parser.consumer item start).Error}
    (hS : Takes start all (received all) .finished)
    (hfull : stood parser item session.taken = received all) :
    ∀ {version commands}, Script version commands →
    ∀ (taken : List Handed) (offset stop : Nat) (block tokens : List Token),
      Runs lexing.fed (parser.consumer item start) start input true version
        ((Spec.Lexer.segment lexing.fed version input true offset).handed.drop block.length)
        (Spec.Lexer.segment lexing.fed version input true offset).failed taken session →
      received all = stood parser item taken ++ received commands →
      (∀ i, 1 ≤ i → requestsAt all (taken.length + i) = requestsAt commands i) →
      offset ≤ stop → stop ≤ input.length →
      Tokenization version ((input.drop offset).take (stop - offset)) block →
      (stop = offset ∧ block = [] ∨ EndsWithClose block (stop - offset)) →
      Readout version (input.drop offset) tokens →
      ReadoutFed lexing version (input.drop offset) tokens →
      block = tokens.take block.length →
      FileFrom version stop (input.drop stop) commands := by
  intro version commands hscript
  induction hscript with
  | @done version =>
    intro taken offset stop block tokens hruns hrec _ hos hle hblock hclosed hread hfed
      hblockEq
    obtain ⟨rest, hrest⟩ := runs_prefix hruns
    have hstoodRest : stood parser item rest = [.endOfInput] := by
      have := hfull
      rw [← hrest, stood_append, hrec] at this
      simpa [received] using List.append_cancel_left this
    obtain ⟨handed, rfl⟩ : ∃ handed, rest = [handed] := by
      cases rest with
      | nil => simp [stood] at hstoodRest
      | cons handed more =>
        cases more with
        | nil => exact ⟨handed, rfl⟩
        | cons _ _ => simp [stood] at hstoodRest
    have hend : parser.stands (item handed) = .endOfInput := by simpa [stood] using hstoodRest
    have hseg : (Spec.Lexer.segment lexing.fed version input true offset).handed =
        blockHanded version input offset tokens ∨
        (Tokenization version (input.drop offset) tokens ∧
          (Spec.Lexer.segment lexing.fed version input true offset).handed =
            blockHanded version input offset tokens ++
              [(endOfFile (input.drop offset)).after (input.take offset)]) := by
      rcases hfed with h | ⟨ht, h⟩
      · left; simp [Spec.Lexer.segment, h, blockHanded, Function.comp_def]
      · right; exact ⟨ht, by simp [Spec.Lexer.segment, h, blockHanded, Function.comp_def]⟩
    -- the token the parser took last is the end of the file, after the whole block
    cases hready : (Spec.Lexer.segment lexing.fed version input true offset).handed.drop
        block.length with
    | nil =>
      rw [hready] at hruns
      have := congrArg List.length (runs_nil hruns)
      rw [← hrest] at this
      simp at this
    | cons token more =>
      rw [hready] at hruns
      obtain ⟨more', hmore'⟩ := runs_head hruns
      rw [← hrest] at hmore'
      have htoken : token = handed := (by simpa using hmore' : token = handed ∧ _).1
      subst htoken
      have hall : Tokenization version (input.drop offset) block := by
        rcases hseg with h | ⟨ht, h⟩
        · rw [h] at hready
          have hmem : token ∈ blockHanded version input offset tokens :=
            List.mem_of_mem_drop (by rw [hready]; simp)
          exact absurd hend (stands_blockHanded hI hread hmem)
        · by_cases hm : block.length < tokens.length
          · rw [h, List.drop_append_of_le_length (by simp [blockHanded]; omega),
              List.drop_eq_getElem_cons (by simp [blockHanded]; omega)] at hready
            simp only [List.cons_append, List.cons.injEq] at hready
            have hmem : token ∈ blockHanded version input offset tokens := by
              rw [← hready.1]; exact List.getElem_mem _
            exact absurd hend (stands_blockHanded hI hread hmem)
          · rw [hblockEq, List.take_of_length_le (by omega)]
            exact ht
      rcases hclosed with ⟨he, hb⟩ | hc
      · subst hb he
        exact .done (tokenizationFrom_nil_offset hall)
      · obtain ⟨-, -, -, h₄⟩ := tokenizationFrom_split (rest := [])
          (by simpa [Tokenization] using hall) hc
        have e : (input.drop offset).drop (stop - offset) = input.drop stop := by
          rw [List.drop_drop]; congr 1; omega
        simp only [Nat.sub_zero] at h₄
        rw [e] at h₄
        exact .done (tokenizationFrom_nil_offset h₄)
  | @command next commands version command hv hm _ ih =>
    intro taken offset stop block tokens hruns hrec hreq hos hle hblock hclosed hread hfed
      hblockEq
    have hexit := (read_next hm).2
    have hrec' : received all = stood parser item taken ++ command.tokens.map .token ++
        received commands := by
      rw [hrec, Parser.received_cons (ne_exit_of_exitFlag hexit), List.append_assoc]
    obtain ⟨handed, last, more, segment, rel, hstood, hhanded, htype, hlastRun, hmore, ha, hs, hd,
      hdropc, htokEx, hic, hblockEq', htokNew, hcloseNew, hlastEnd, hleNew⟩ :=
      next_command hF hI hS hfull hruns hrec' hreq hos hle hclosed hread hfed hblockEq hv
    have hinv := runs_continue_inv hlastRun htype (by rw [List.append_assoc, ← hhanded]; exact ha)
      (by rw [List.append_assoc, ← hhanded, hd]; exact hexit)
    rw [List.append_assoc, ← hhanded, hs] at hinv
    have hrec'' : received all = stood parser item (taken ++ handed) ++ received commands := by
      rw [stood_append, hstood, hrec']
    have hl : handed.length = command.tokens.length := by
      simpa [stood] using congrArg List.length hstood
    have hreq'' : ∀ i, 1 ≤ i →
        requestsAt all ((taken ++ handed).length + i) = requestsAt commands i := by
      intro i hi
      rw [List.length_append, hl, Nat.add_assoc, hreq _ (by omega)]
      have h₁ : ¬ (command.tokens.length + i < command.tokens.length) := by omega
      have h₂ : ¬ (command.tokens.length + i = command.tokens.length) := by omega
      simp only [requestsAt, h₁, h₂, ite_false, Nat.add_sub_cancel_left]
    rw [hdropc]
    refine FileFrom.command htokEx hic hm ?_
    obtain ⟨hnext, -⟩ := read_next hm
    cases hdecl : command.declaredVersion with
    | none =>
      rw [hdecl] at hinv hnext
      simp only [Option.getD_none, following] at hinv hnext
      subst hnext
      rw [← hmore] at hinv
      exact ih (taken ++ handed) offset (stop + segment.length) (block ++ rel) tokens hinv
        hrec'' hreq'' (by omega) hleNew htokNew (Or.inr hcloseNew) hread hfed hblockEq'
    | some declared =>
      rw [hdecl] at hinv hnext
      simp only [Option.getD_some, following, readyFrom, withLayout, hlastEnd] at hinv hnext
      subst hnext
      obtain ⟨tokens', hread', hfed'⟩ := fed_readout hL next
        (input.drop (stop + segment.length))
      exact ih (taken ++ handed) (stop + segment.length) (stop + segment.length) [] tokens'
        (by simpa [RecordingParser.consumer] using hinv) hrec'' hreq'' (Nat.le_refl _) hleNew
        (by simpa using tokenization_nil next) (Or.inl ⟨rfl, rfl⟩) hread' hfed' (by simp)
  | @stop version command hv hm =>
    intro taken offset stop block tokens hruns hrec hreq hos hle hblock hclosed hread hfed
      hblockEq
    have hrec' : received all = stood parser item taken ++ command.tokens.map .token ++
        received [] := by
      obtain rfl := Parser.modeAfter_unparsed hm
      rw [hrec]; simp [received]
    obtain ⟨handed, last, more, segment, rel, hstood, hhanded, htype, hlastRun, hmore, ha, hs, hd,
      hdropc, htokEx, hic, -⟩ :=
      next_command hF hI hS hfull hruns hrec' hreq hos hle hclosed hread hfed hblockEq hv
    rw [hdropc]
    exact FileFrom.stop htokEx hic hm

end BSmtLib.SpecChecks.Reader
