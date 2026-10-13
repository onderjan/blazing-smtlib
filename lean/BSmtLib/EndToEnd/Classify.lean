import BSmtLib.EndToEnd.Reading
import BSmtLib.EndToEnd.Split

/-!
# How a session with the script consumer ends, on any input

A lexer that does what `BSmtLibSpec.Lexer.Runs` states with the script consumer, fed any input and then
the end of the input, ends in one of four ways (`runs_classified`):

- **finished**: the tokens it handed over stand for what a parser takes for a script, and the
  input reads as a file of that script's commands (`BSmtLibSpec.Grammar.File`);
- **refused**: they stand for commands that a declaration naming no supported version ends, and
  the consumer failed at that declaration's `)`;
- **rejected**: all but the last stand for a start of what a parser takes, and with the last they
  stand for no such start, and do not end with `exit`: the consumer rejected the last;
- **lexical**: they stand for a start of what a parser takes, and they are everything the lexer
  hands over, read from where the last version declaration ended, in its version, where the
  lexer fails.

The proof walks `Runs` with an invariant: the tokens taken stand for a start of what a parser
takes, the lexer's version is the one in force there (`versionAt`), and the tokens ready are the
rest of what the lexer hands over from where the last declaration ended (`BSmtLibSpec.Lexer.segment`).
For the file it also carries the readings before the current one (`Hist`): for every reading of
the tokens taken as what a parser takes, the commands they stand for and how the characters of
the input before the current reading read as those commands.
-/

namespace BSmtLib.EndToEnd

open BSmtLibSpec BSmtLibSpec.Grammar BSmtLibSpec.Lexer
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLibSpec.Parser.Properties (Takes Ending versionAt)
open BSmtLibSpec.Parser.Traversal
open BSmtLib.ParserProofs.Rejection (rcv)
open BSmtLib.ParserProofs (requestsAt)

variable {feed : Lexicon.Version → List Regex.Chars → Bool → Fed}

/-! ## The readings before the current one -/

/--
The tokens `before`, taken up to where the reading in `version` from `offset` began, stand, in
every reading of what a parser takes that they start, for whole commands, after which that reading
goes on in `version`; and the characters from `offset` that read as some commands make the input
read, from `start`, as the commands before followed by those.
-/
def Hist (start : Lexicon.Version) (input : Regex.Chars) (before : List Handed)
    (version : Lexicon.Version) (offset : Nat) : Prop :=
  ∀ commands taken ending, Takes start commands taken ending →
    before.map (rcv ∘ itemOf) <+: taken →
    ∃ done rest, commands = done ++ rest ∧
      (doneTokens done).map .token = before.map (rcv ∘ itemOf) ∧
      Takes version rest (taken.drop before.length) ending ∧
      ∀ more, File.From version offset (input.drop offset) more → File start input (done ++ more)

/-- No switch of the version was asked for at the tokens taken since `before`. -/
def Quiet (start : Lexicon.Version) (before taken : List Handed) : Prop :=
  ∀ k, before.length ≤ k → k < taken.length →
    (scriptConsumer start).switchTo (taken.take (k + 1)) = none

theorem hist_init (start : Lexicon.Version) (input : Regex.Chars) :
    Hist start input [] start 0 := by
  intro commands taken ending ht _
  exact ⟨[], commands, rfl, by simp [doneTokens], by simpa using ht,
    fun more hf => by simpa [File] using hf⟩

theorem quiet_snoc {start : Lexicon.Version} {before taken : List Handed} {token : Handed}
    (hquiet : Quiet start before taken)
    (hs : (scriptConsumer start).switchTo (taken ++ [token]) = none) :
    Quiet start before (taken ++ [token]) := by
  intro k hk hlt
  simp only [List.length_append, List.length_singleton] at hlt
  by_cases h : k < taken.length
  · rw [List.take_append_of_le_length (by omega)]
    exact hquiet k hk h
  · rw [show k + 1 = (taken ++ [token]).length by simp; omega, List.take_length]
    exact hs

/-- Tokens taken that stand for a start of what a parser takes stand for the start of every start
of it. -/
theorem take_items {pre : List Handed} {taken : List Received}
    (hp : pre.map (rcv ∘ itemOf) <+: taken) (m : Nat) (hm : m ≤ pre.length) :
    (pre.take m).map (rcv ∘ itemOf) = taken.take (pre.take m).length := by
  have h := List.prefix_iff_eq_take.mp hp
  rw [List.length_map] at h
  rw [List.map_take, h, List.take_take, List.length_take, Nat.min_eq_left hm]

/-- Since the reading began, no switch was asked for in the rest of a reading of what a parser
takes. -/
theorem quiet_requests {start : Lexicon.Version} {before current : List Handed}
    (hquiet : Quiet start before (before ++ current)) {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (ht : Takes start commands taken ending)
    (hp : (before ++ current).map (rcv ∘ itemOf) <+: taken) {done rest : List Tree.Command}
    (hcs : commands = done ++ rest)
    (hdone : (doneTokens done).map .token = before.map (rcv ∘ itemOf)) :
    ∀ k < current.length, (requestsAt rest k).1 = none := by
  intro k hk
  have hlen : (doneTokens done).length = before.length := by
    simpa using congrArg List.length hdone
  have hpre := take_items hp (before.length + k + 1) (by simp; omega)
  have hpre := take_items hp (before.length + k + 1) (by simp; omega)
  have hpl := hp.length_le
  simp only [List.length_map, List.length_append] at hpl
  have hreq := (requests_takes_prefix ht hpre
    (by simp only [List.length_take, List.length_append]; omega)
    (by simp only [List.length_take, List.length_append]; omega)).1
  have hq := hquiet (before.length + k) (by omega) (by simp; omega)
  rw [hq] at hreq
  have hX : (List.take (before.length + k + 1) (before ++ current)).length - 1 =
      (doneTokens done).length + k := by
    simp only [List.length_take, List.length_append]; omega
  rw [hX, hcs, requestsAt_append] at hreq
  exact hreq.symm

/-- A token a correct lexer hands over from an offset within the input, other than the end of
file, ends within the input. -/
theorem segment_end_le (hc : Correct feed) {version : Lexicon.Version} {input : Regex.Chars}
    {offset : Nat} (hoff : offset ≤ input.length) {h : Handed}
    (hh : h ∈ (segment feed version input true offset).handed) (htype : h.type ≠ .endOfFile) :
    h.«end».offset ≤ input.length := by
  obtain ⟨L, E, s, ext, all, hseg, hs, -, -, hwithin, hE⟩ :=
    segment_structure hc version hoff (feed := feed)
  rw [hseg] at hh
  rcases List.mem_append.mp hh with hh | hh
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hh
    have := hwithin t ht
    have := hs.length_le
    simp only [Lexicon.Token.handed, locate, Lexicon.Token.moveBy, List.length_drop] at *
    omega
  · rcases hE with rfl | ⟨rfl, -⟩
    · simp at hh
    · rw [List.mem_singleton.mp hh] at htype
      exact absurd rfl htype

/-! ## At a switch, and at the end -/

/-- At a token where the consumer goes on and switches the version, the reading ends: the
readings before the next one are those before the current one and the current one. -/
theorem hist_switch (hc : Correct feed) {start : Lexicon.Version} {input : Regex.Chars}
    {version declared : Lexicon.Version} {offset : Nat} (hoff : offset ≤ input.length)
    {before current ready : List Handed} {token : Handed} {failed : Bool}
    (hhist : Hist start input before version offset)
    (hquiet : Quiet start before (before ++ current))
    (hseg : segment feed version input true offset = ⟨current ++ token :: ready, failed⟩)
    (hcur : ∀ h ∈ current, h.type ≠ .endOfFile) (htype : token.type ≠ .endOfFile)
    (hcont : (scriptConsumer start).answer (before ++ current ++ [token]) = .continue)
    (hsw : (scriptConsumer start).switchTo (before ++ current ++ [token]) = some declared) :
    Hist start input (before ++ current ++ [token]) declared token.«end».offset := by
  intro commands taken ending ht hp
  have hpb : before.map (rcv ∘ itemOf) <+: taken := by
    have : before.map (rcv ∘ itemOf) <+: (before ++ current ++ [token]).map (rcv ∘ itemOf) := by
      rw [List.append_assoc, List.map_append]
      exact List.prefix_append _ _
    exact this.trans hp
  obtain ⟨done, rest, hcs, hdone, hrest, hfile⟩ := hhist commands taken ending ht hpb
  have hlen : (doneTokens done).length = before.length := by
    simpa using congrArg List.length hdone
  have hst : (before ++ current ++ [token]).map (rcv ∘ itemOf) =
      taken.take (before ++ current ++ [token]).length := by
    have := List.prefix_iff_eq_take.mp hp
    simpa using this
  have hle : (before ++ current ++ [token]).length ≤ taken.length := by
    have := hp.length_le; simpa using this
  have hlt : (before ++ current ++ [token]).length < taken.length := by
    refine Nat.lt_of_le_of_ne hle fun heq => ?_
    have hans := answer_takes ht hst hle
    rw [hans] at hcont
    split at hcont
    · omega
    · rcases takes_ending ht with rfl | rfl <;> simp [answerOf] at hcont
  have hreq := (requests_takes_prefix ht hst
    (by simp only [List.length_append, List.length_singleton]; omega) hle).1
  rw [hsw] at hreq
  -- the current reading's items, split off the rest of the reading of the witness
  have hP : (current ++ [token]).map (rcv ∘ itemOf) <+: taken.drop before.length := by
    rw [List.append_assoc, List.map_append] at hp
    obtain ⟨r, hr⟩ := hp
    refine ⟨r, ?_⟩
    rw [← hr, List.append_assoc, List.drop_left' (by simp)]
  obtain ⟨init, decl, rest', hrest', htoks, hinit, hdv, hdm, hrest''⟩ :=
    takes_switch hrest ((current ++ [token]).map (rcv ∘ itemOf)) declared hP (by simp)
      (by simp only [List.length_append, List.length_singleton, List.length_map,
        List.length_drop] at hlt ⊢; omega)
      (by
        rw [hreq]
        simp only [List.length_append, List.length_singleton] at hreq ⊢
        rw [hcs, show before.length + current.length + 1 - 1 =
          (doneTokens done).length + current.length by omega, requestsAt_append]
        simp only [List.length_map, List.length_append, List.length_singleton,
          Nat.add_sub_cancel])
      (by
        intro k hk
        exact quiet_requests hquiet ht (by
          have : (before ++ current).map (rcv ∘ itemOf) <+:
              (before ++ current ++ [token]).map (rcv ∘ itemOf) := by simp
          exact this.trans hp) hcs hdone k (by simpa using hk))
  obtain ⟨S₁, D₂, hD, hend, hconts, -⟩ := reading_split hc hoff (Y := current ++ [token])
    (by rw [hseg]; exact ⟨ready, by simp⟩)
    (by
      intro h hh
      rcases List.mem_append.mp hh with hh | hh
      · exact hcur h hh
      · rw [List.mem_singleton.mp hh]; exact htype)
    (by rw [← htoks]; rfl) hinit hdv
  have hendo : token.«end».offset = offset + S₁.length := by
    simpa using hend
  refine ⟨done ++ (init ++ [decl]), rest', by rw [hcs, hrest']; simp, ?_, ?_, ?_⟩
  · rw [List.map_append, List.map_append]
    simp only [doneTokens, List.flatMap_append, List.map_append] at htoks hdone ⊢
    rw [hdone, htoks, List.append_assoc]
  · rw [show (before ++ current ++ [token]).length =
      before.length + ((current ++ [token]).map (rcv ∘ itemOf)).length by simp,
      ← List.drop_drop]
    exact hrest''
  · intro more hf
    have hD₂ : input.drop token.«end».offset = D₂ := by
      rw [hendo, ← List.drop_drop, hD, List.drop_left]
    rw [hD₂] at hf
    have := hfile _ (hconts declared more hdm (by rw [← hendo]; exact hf))
    simpa using this

/-- At the end of the input, handed over after a reading: the input reads as the file whose
script the tokens taken stand for. -/
theorem file_ends (hc : Correct feed) {start : Lexicon.Version} {input : Regex.Chars}
    {version : Lexicon.Version} {offset : Nat} (hoff : offset ≤ input.length)
    {before current ready : List Handed} {token : Handed} {failed : Bool}
    (hhist : Hist start input before version offset)
    (hquiet : Quiet start before (before ++ current))
    (hseg : segment feed version input true offset = ⟨current ++ token :: ready, failed⟩)
    (hcur : ∀ h ∈ current, h.type ≠ .endOfFile) (htype : token.type = .endOfFile)
    {commands : List Tree.Command}
    (ht : Takes start commands ((before ++ current ++ [token]).map (rcv ∘ itemOf)) .finished) :
    File start input commands := by
  obtain ⟨done, rest, hcs, hdone, hrest, hfile⟩ := hhist commands _ _ ht (by simp)
  have heoi : rcv (itemOf token) = .endOfInput := (rcv_itemOf_endOfInput_iff token).mpr htype
  have hdrop : ((before ++ current ++ [token]).map (rcv ∘ itemOf)).drop before.length =
      current.map (rcv ∘ itemOf) ++ [.endOfInput] := by
    simp [heoi]
  rw [hdrop] at hrest
  obtain ⟨cmds, hvalid, hcases⟩ := takes_final hrest rfl _ rfl (by
    intro k hk
    exact quiet_requests hquiet ht (by simp) hcs hdone k (by simpa using hk))
  have hhanded : (segment feed version input true offset).handed = current ++ token :: ready :=
    by rw [hseg]
  rcases hcases with ⟨hr, htoks⟩ | ⟨hr, hev, hem, htoks⟩
  · have := reading_end hc hoff hhanded htype (commands := cmds) (by rw [← htoks]; rfl) hvalid
    rw [hcs, hr]
    exact hfile cmds this
  · obtain ⟨-, -, -, -, -, hstop⟩ := reading_split hc hoff (Y := current)
      (by rw [hseg]; exact ⟨token :: ready, rfl⟩) hcur (by rw [← htoks]; rfl) hvalid hev
    rw [hcs, hr]
    exact hfile _ (hstop hem)

/-- At `exit`, after which the rest of the input is discarded: the input reads as the file whose
script the tokens taken stand for. -/
theorem file_exit (hc : Correct feed) {start : Lexicon.Version} {input : Regex.Chars}
    {version : Lexicon.Version} {offset : Nat} (hoff : offset ≤ input.length)
    {before current ready : List Handed} {token : Handed} {failed : Bool}
    (hhist : Hist start input before version offset)
    (hquiet : Quiet start before (before ++ current))
    (hseg : segment feed version input true offset = ⟨current ++ token :: ready, failed⟩)
    (hcur : ∀ h ∈ current, h.type ≠ .endOfFile) (htype : token.type ≠ .endOfFile)
    (hdisc : (scriptConsumer start).discards (before ++ current ++ [token]) = true)
    {commands : List Tree.Command}
    (ht : Takes start commands
      ((before ++ current ++ [token, endOfFile input]).map (rcv ∘ itemOf)) .finished) :
    File start input commands := by
  obtain ⟨done, rest, hcs, hdone, hrest, hfile⟩ := hhist commands _ _ ht (by simp)
  have hlen : (doneTokens done).length = before.length := by
    simpa using congrArg List.length hdone
  have hdrop : ((before ++ current ++ [token, endOfFile input]).map (rcv ∘ itemOf)).drop
      before.length = (current ++ [token]).map (rcv ∘ itemOf) ++ [.endOfInput] := by
    simp [rcv_itemOf_endOfFile]
  rw [hdrop] at hrest
  -- the discarding is asked for at the token, which is the `)` of `exit`
  have h₁ : before ++ current ++ [token, endOfFile input] =
      (before ++ current ++ [token]) ++ [endOfFile input] := by simp
  have hp' : (before ++ current ++ [token]).map (rcv ∘ itemOf) <+:
      (before ++ current ++ [token, endOfFile input]).map (rcv ∘ itemOf) := by
    rw [h₁]
    exact (List.prefix_append _ _).map _
  have hti := take_items hp' _ (Nat.le_refl _)
  rw [List.take_length] at hti
  have hreq := (requests_takes_prefix ht hti
    (by simp only [List.length_append, List.length_singleton]; omega)
    (by rw [h₁]; simp)).2
  rw [hdisc, hcs, show (before ++ current ++ [token]).length - 1 =
    (doneTokens done).length + current.length by simp; omega, requestsAt_append] at hreq
  obtain ⟨hnone, hexit⟩ := requestsAt_discard rest _ hreq.symm
  obtain ⟨cmds, hvalid, hcases⟩ := takes_final hrest rfl _ rfl (by
    intro k hk
    simp only [List.length_map, List.length_append, List.length_singleton] at hk
    by_cases hk' : k < current.length
    · exact quiet_requests hquiet ht (by simp) hcs hdone k hk'
    · rw [show k = current.length by omega]
      exact hnone)
  rcases hcases with ⟨hr, -⟩ | ⟨hr, hev, hem, htoks⟩
  · rw [hr] at hexit
    exact absurd (hvalid _ hexit).2 (by simp [Tree.Command.modeAfter])
  · obtain ⟨-, -, -, -, -, hstop⟩ := reading_split hc hoff (Y := current ++ [token])
      (by rw [hseg]; exact ⟨ready, by simp⟩)
      (by
        intro h hh
        rcases List.mem_append.mp hh with hh | hh
        · exact hcur h hh
        · rw [List.mem_singleton.mp hh]; exact htype)
      (by rw [← htoks]; rfl) hvalid hev
    rw [hcs, hr]
    exact hfile _ (hstop hem)

/-! ## How a session ends -/

/--
How a session with the script consumer, read from the version, ends on the input after the end of
the input: as one of the four ways of the module's documentation. `feed` is what the lexer hands
over to the collector.
-/
def Classified (feed : Lexicon.Version → List Regex.Chars → Bool → Fed)
    (version : Lexicon.Version) (input : Regex.Chars)
    (session : Session Unit ScriptError) : Prop :=
  (session.outcome.isFinished = true ∧
      ∃ commands, Takes version commands (session.taken.map (rcv ∘ itemOf)) .finished ∧
        File version input commands) ∨
    (session.outcome = .failed (.consumer (.failed .unsupportedVersion)) ∧
      ∃ commands, Takes version commands (session.taken.map (rcv ∘ itemOf))
        (.failed .unsupportedVersion)) ∨
    (session.outcome = .failed (.consumer .rejected) ∧
      ∃ commands taken ending before last, session.taken = before ++ [last] ∧
        Takes version commands taken ending ∧ before.map (rcv ∘ itemOf) <+: taken ∧
        before.length < taken.length ∧
        (rcv (itemOf last)).OfVersion (versionAt version commands before.length) ∧
        ¬ BSmtLibSpec.Parser.Properties.Viable version (session.taken.map (rcv ∘ itemOf)) ∧
        ¬ ParserProofs.Rejection.AfterExit version (before.map (rcv ∘ itemOf))) ∨
    (session.outcome = .failed .lexical ∧
      ∃ commands taken ending, Takes version commands taken ending ∧
        session.taken.map (rcv ∘ itemOf) <+: taken ∧ session.taken.length < taken.length ∧
        session.version = versionAt version commands session.taken.length ∧
        ∃ offset before current, session.taken = before ++ current ∧
          (before = [] ∧ offset = 0 ∨ before.getLast?.map (·.«end».offset) = some offset) ∧
          segment feed session.version input true offset = ⟨current, true⟩)

/--
A lexer that does what `Runs` states with the script consumer, after the end of the input, from a
point where the tokens taken stand for a proper start of what a parser takes, the version is the
one in force there, the tokens ready are the rest of what the lexer hands over from where the
last version declaration ended, the readings before are as `Hist` states, and the consumer did
not have the rest discarded at the last token taken: the session ends as
`Classified` says.
-/
theorem runs_classified (hc : Correct feed) {v₀ : Lexicon.Version} {input : Regex.Chars}
    {version : Lexicon.Version} {ready : List Handed} {failed : Bool} {pre : List Handed}
    {session : Session (scriptConsumer v₀).Result (scriptConsumer v₀).Error}
    (hruns : Runs feed (scriptConsumer v₀) v₀ input true version ready failed pre session) :
    ∀ (commands : List Tree.Command) (taken : List Received) (ending : Ending),
      Takes v₀ commands taken ending → pre.map (rcv ∘ itemOf) <+: taken →
      pre.length < taken.length → version = versionAt v₀ commands pre.length →
      ∀ (offset : Nat) (before current : List Handed), pre = before ++ current →
        (before = [] ∧ offset = 0 ∨ before.getLast?.map (·.«end».offset) = some offset) →
        segment feed version input true offset = ⟨current ++ ready, failed⟩ →
        (∀ h ∈ current, h.type ≠ .endOfFile) →
        offset ≤ input.length → Hist v₀ input before version offset → Quiet v₀ before pre →
        (pre = [] ∨ (scriptConsumer v₀).discards pre = false) →
        Classified feed v₀ input session := by
  induction hruns with
  | @waiting version taken =>
    intro commands taken' ending htakes hp hlt hv offset before current hpre hoff hseg hcur _ _ _
      hnd
    obtain ⟨init, last, hend, htype⟩ := segment_ends hc version input offset (by rw [hseg])
    rw [hseg] at hend
    simp only [List.append_nil] at hend
    exact absurd htype (hcur last (by rw [hend]; simp))
  | @lexical version taken =>
    intro commands taken' ending htakes hp hlt hv offset before current hpre hoff hseg hcur _ _ _
      hnd
    right; right; right
    refine ⟨rfl, commands, taken', ending, htakes, hp, hlt, hv, offset, before, current, hpre,
      hoff, ?_⟩
    simpa [settle, Outcome.isFinished] using hseg
  | @fails taken token error version ready failed hf =>
    intro commands taken' ending htakes hp hlt hv offset before current hpre hoff hseg hcur _ _ _
      hnd
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact segment_ofVersion hc version input offset token (by rw [hseg]; simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨hnv, ha⟩ | ⟨_, _, _, _, _, _, ha, _⟩ |
        ⟨_, _, ha, _⟩ | ⟨commands', ht', ha⟩
    · rw [ha] at hf
      cases hf
      right; right; left
      exact ⟨rfl, commands, taken', ending, taken, token, rfl, htakes, hp, hlt, hof, hnv,
        not_afterExit htakes hp hlt hnd⟩
    · rw [ha] at hf; cases hf
    · rw [ha] at hf; cases hf
    · rw [ha] at hf
      cases hf
      right; left
      exact ⟨rfl, commands', ht'⟩
  | @ends taken token result version ready failed htype hb =>
    intro commands taken' ending htakes hp hlt hv offset before current hpre hoff hseg hcur hin
      hhist hquiet hnd
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact segment_ofVersion hc version input offset token (by rw [hseg]; simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ | ⟨_, _, _, _, _, _, ha, _⟩ |
        ⟨commands', ht', _, _⟩ | ⟨_, _, ha⟩
    · rw [ha] at hb; cases hb
    · rw [ha] at hb; cases hb
    · left
      subst hpre
      exact ⟨rfl, commands', ht', file_ends hc hin hhist hquiet hseg hcur htype ht'⟩
    · rw [ha] at hb; cases hb
  | @continues taken token version ready failed session htype hcont hdisc _ ih =>
    intro commands taken' ending htakes hp hlt hv offset before current hpre hoff hseg hcur hin
      hhist hquiet hnd
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact segment_ofVersion hc version input offset token (by rw [hseg]; simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ |
        ⟨commands', taken'', ending', ht', hp', hlt', ha, hsw, hdi, hver⟩ | ⟨_, _, ha, _⟩ |
        ⟨_, _, ha⟩
    · rw [ha] at hcont; cases hcont
    · have hv' : (((scriptConsumer v₀).switchTo (taken ++ [token])).getD version) =
          versionAt v₀ commands' (taken ++ [token]).length := by
        rw [List.length_append, List.length_singleton, versionAt_succ, hsw, hver, hv]
      cases hs : (scriptConsumer v₀).switchTo (taken ++ [token]) with
      | none =>
        rw [hs] at ih hv'
        simp only [following, Option.getD_none] at ih hv'
        exact ih commands' taken'' ending' ht' hp' (by simpa using hlt') hv' offset before
          (current ++ [token]) (by rw [hpre, List.append_assoc]) hoff (by simpa using hseg)
          (by
            intro h hh
            rcases List.mem_append.mp hh with hh | hh
            · exact hcur h hh
            · rw [List.mem_singleton.mp hh]; exact htype)
          hin hhist (quiet_snoc hquiet hs) (Or.inr hdisc)
      | some declared =>
        rw [hs] at ih hv'
        simp only [following, Option.getD_some, scriptConsumer_concrete, readyFrom_false] at ih hv'
        subst hpre
        exact ih commands' taken'' ending' ht' hp'
          (by simp only [List.length_append, List.length_singleton] at hlt' ⊢; omega) hv'
          token.«end».offset
          (before ++ current ++ [token]) [] (by simp) (Or.inr (by simp)) (by simp) (by simp)
          (segment_end_le hc hin (by rw [hseg]; simp) htype)
          (hist_switch hc hin hhist hquiet hseg hcur htype hcont hs)
          (fun k hk hlt => absurd hlt (by omega)) (Or.inr hdisc)
    · rw [ha] at hcont; cases hcont
    · rw [ha] at hcont; cases hcont
  | @breaks taken token result ready failed outcome version htype hb _ _ =>
    intro commands taken' ending htakes hp hlt hv offset before current hpre hoff hseg hcur _ _ _
      hnd
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact segment_ofVersion hc version input offset token (by rw [hseg]; simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ | ⟨_, _, _, _, _, _, ha, _⟩ |
        ⟨_, _, _, htype'⟩ | ⟨_, _, ha⟩
    · rw [ha] at hb; cases hb
    · rw [ha] at hb; cases hb
    · exact absurd htype' htype
    · rw [ha] at hb; cases hb
  | discardsHeld _ _ _ hended => cases hended
  | @discardsEnds taken token result version ready failed htype hb _ _ =>
    intro commands taken' ending htakes hp hlt hv offset before current hpre hoff hseg hcur _ _ _
      hnd
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact segment_ofVersion hc version input offset token (by rw [hseg]; simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ | ⟨_, _, _, _, _, _, ha, _⟩ |
        ⟨_, _, _, htype'⟩ | ⟨_, _, ha⟩
    · rw [ha] at hb; cases hb
    · rw [ha] at hb; cases hb
    · exact absurd htype' htype
    · rw [ha] at hb; cases hb
  | discardsWaiting _ _ _ hended => cases hended
  | @discardsToEnd taken token result version ready failed htype hcont hdisc _ hb =>
    intro commands taken' ending htakes hp hlt hv offset before current hpre hoff hseg hcur hin
      hhist hquiet hnd
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact segment_ofVersion hc version input offset token (by rw [hseg]; simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ |
        ⟨commands', taken'', ending', ht', hp', hlt', ha, hsw, hdi, hver⟩ | ⟨_, _, ha, _⟩ |
        ⟨_, _, ha⟩
    · rw [ha] at hcont; cases hcont
    · have hdisc' := hdisc
      rw [hdi] at hdisc
      obtain ⟨hlen, hlast, rfl⟩ := takes_discards ht' taken.length (by omega) hdisc
      have hst : (taken ++ [token]).map (rcv ∘ itemOf) = taken''.take (taken.length + 1) := by
        have := List.prefix_iff_eq_take.mp hp'
        simpa using this
      have hall : (taken ++ [token, endOfFileAt token.end]).map (rcv ∘ itemOf) = taken'' := by
        rw [eq_take_append_last (n := taken.length + 1) (by omega) hlast, ← hst]
        simp [rcv_itemOf_endOfFileAt]
      have ht'' : Takes v₀ commands'
          ((taken ++ [token, endOfFileAt token.end]).map (rcv ∘ itemOf)) .finished := by
        rw [hall]; exact ht'
      left
      refine ⟨rfl, commands', ht'', ?_⟩
      subst hpre
      exact file_exit hc hin hhist hquiet hseg hcur htype hdisc'
        (by simpa [rcv_itemOf_endOfFile, rcv_itemOf_endOfFileAt] using ht'')
    · rw [ha] at hcont; cases hcont
    · rw [ha] at hcont; cases hcont
  | @discardsFailsAtEnd taken token error version ready failed htype hcont hdisc _ hf =>
    intro commands taken' ending htakes hp hlt hv offset before current hpre hoff hseg hcur _ _ _
      hnd
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact segment_ofVersion hc version input offset token (by rw [hseg]; simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ |
        ⟨commands', taken'', ending', ht', hp', hlt', ha, hsw, hdi, hver⟩ | ⟨_, _, ha, _⟩ |
        ⟨_, _, ha⟩
    · rw [ha] at hcont; cases hcont
    · rw [hdi] at hdisc
      obtain ⟨hlen, hlast, rfl⟩ := takes_discards ht' taken.length (by omega) hdisc
      have hst : (taken ++ [token]).map (rcv ∘ itemOf) = taken''.take (taken.length + 1) := by
        have := List.prefix_iff_eq_take.mp hp'
        simpa using this
      have hall : (taken ++ [token, endOfFileAt token.end]).map (rcv ∘ itemOf) = taken'' := by
        rw [eq_take_append_last (n := taken.length + 1) (by omega) hlast, ← hst]
        simp [rcv_itemOf_endOfFileAt]
      have hans := answer_takes ht' (handed := taken ++ [token, endOfFileAt token.end])
        (by rw [List.take_of_length_le (by rw [← hall]; simp)]; exact hall) (by rw [← hall]; simp)
      rw [hans] at hf
      simp only [← hall, List.length_map, Nat.lt_irrefl, ↓reduceIte] at hf
      cases hf
    · rw [ha] at hcont; cases hcont
    · rw [ha] at hcont; cases hcont

end BSmtLib.EndToEnd
