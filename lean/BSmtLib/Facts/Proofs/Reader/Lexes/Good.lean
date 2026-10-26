module

public import BSmtLib.Facts.Proofs.Reader.Param.Only
public import BSmtLib.Facts.Proofs.Reader.Lexes.Congr

@[expose] public section

/-!
# The tokens a run with the script consumer takes are good, ended or not

`Param.good_of_classified` says that the tokens a lexer correct with every consumer takes with
the script consumer are `Param.Good` once the input has ended. Here the same is proved whether or
not the input has ended, by a lighter walk of `BSmtLibSpec.Lexer.Runs` than `runs_classified`: the
tokens taken stand for a proper start of what a parser takes, the version is the one in force there,
and every token ready stands for an item of that version (`runs_good`, `lexing_good`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Lexes.Good

open BSmtLibSpec BSmtLibSpec.Grammar BSmtLibSpec.Lexer
open BSmtLibSpec.Parser.Properties (Takes Ending versionAt)
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection (rcv)
open BSmtLib.Facts.Proofs.Reader.Consumer BSmtLib.Facts.Proofs.Reader.Lexes.Congr
open BSmtLib.Facts.Proofs.Reader.Outcome BSmtLib.Facts.Proofs.Reader.Param
open BSmtLib.Facts.Reader.Adapters

variable {feed : Lexicon.Version → List Regex.Chars → Bool → Fed}

/-- A token a correct lexer hands over from an offset on, the input ended or not, stands for an
item that a lexer can hand over in the version. -/
theorem segment_ofVersion' (hc : Correct feed) (version : Lexicon.Version)
    (input : Regex.Chars) (ended : Bool) (offset : Nat) :
    ∀ h ∈ (segment feed version input ended offset).handed,
      (rcv (itemOf h)).OfVersion version := by
  cases ended with
  | true => exact segment_ofVersion hc version input offset
  | false =>
    intro h hh
    refine segment_ofVersion hc version input offset h ?_
    have hpre := (Facts.Lexer.sequential hc version [input.drop offset] []).2.1
    simp only [segment] at hh ⊢
    exact (hpre.map _).subset hh

/-- Good tokens, and one more where the parser's run depends only on what the tokens stand for,
the script consumer having gone on at the good ones. -/
theorem snoc {version : Lexicon.Version} {pre : List Handed} {token : Handed}
    (hgood : Param.Dom.Good version pre)
    (hcont : pre ≠ [] → (scriptConsumer version).answer pre = .continue)
    (hdom : Dom version ((pre ++ [token]).map (rcv ∘ itemOf))) :
    Param.Dom.Good version (pre ++ [token]) := by
  refine ⟨fun n hn => ?_, fun n hn hlt => ?_⟩
  · simp only [List.length_append, List.length_singleton] at hn
    rcases Nat.lt_or_ge n (pre.length + 1) with hn' | hn'
    · rw [List.take_append_of_le_length (by omega)]
      exact hgood.1 n (by omega)
    · rw [show n = (pre ++ [token]).length by simp; omega, List.take_length]
      exact hdom
  · simp only [List.length_append, List.length_singleton] at hlt
    rw [List.take_append_of_le_length (by omega)]
    rcases Nat.lt_or_ge n pre.length with hn' | hn'
    · exact hgood.2 n hn hn'
    · rw [show n = pre.length by omega, List.take_length]
      exact hcont (by rintro rfl; simp at hlt; omega)

/-- Tokens that stand for a start of what a parser takes are where the parser's run depends only
on what they stand for. -/
theorem dom_of_prefix {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes version commands taken ending)
    {handed : List Handed} (hp : handed.map (rcv ∘ itemOf) <+: taken) :
    Dom version (handed.map (rcv ∘ itemOf)) :=
  .inl ⟨commands, taken, ending, htakes, hp⟩

/--
A lexer that does what `Runs` states with the script consumer, the input ended or not, takes good
tokens in its session from a point where:
- the tokens taken are good and stand for a proper start of what a parser takes;
- the version is the one in force there;
- every token ready stands for an item of that version;
- the consumer did not have the rest discarded at the last token taken.
-/
theorem runs_good (hc : Correct feed) {v₀ : Lexicon.Version} {input : Regex.Chars}
    {ended : Bool} {version : Lexicon.Version} {ready : List Handed} {failed : Bool}
    {pre : List Handed}
    {session : Session (scriptConsumer v₀).Result (scriptConsumer v₀).Error}
    (hruns : Runs feed (scriptConsumer v₀) v₀ input ended version ready failed pre session) :
    ∀ (commands : List Tree.Command) (taken : List Received) (ending : Ending),
      Takes v₀ commands taken ending → pre.map (rcv ∘ itemOf) <+: taken →
      pre.length < taken.length → version = versionAt v₀ commands pre.length →
      (∀ h ∈ ready, (rcv (itemOf h)).OfVersion version) → Param.Dom.Good v₀ pre →
      (pre ≠ [] → (scriptConsumer v₀).answer pre = .continue) →
      (pre = [] ∨ (scriptConsumer v₀).discards pre = false) →
      Param.Dom.Good v₀ session.taken := by
  induction hruns with
  | waiting =>
    intro _ _ _ _ _ _ _ _ hgood _ _
    rwa [settle_taken]
  | lexical =>
    intro _ _ _ _ _ _ _ _ hgood _ _
    rwa [settle_taken]
  | @fails taken token error version ready failed hf =>
    intro commands taken' ending htakes hp hlt hv hready hgood hcont hnd
    rw [settle_taken]
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact hready token (by simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨hnv, ha⟩ | ⟨_, _, _, _, _, _, ha, _⟩ |
        ⟨_, _, ha, _⟩ | ⟨commands', ht', ha⟩
    · refine (snoc hgood) hcont (.inr ⟨commands, taken', ending, taken.map (rcv ∘ itemOf),
        rcv (itemOf token), htakes, by simp, hp, by simpa using hlt, by simpa using hof, hnv,
        not_afterExit htakes hp hlt hnd⟩)
    · rw [ha] at hf; cases hf
    · rw [ha] at hf; cases hf
    · exact (snoc hgood) hcont (dom_of_prefix ht' (List.prefix_refl _))
  | @ends taken token result version ready failed htype hb =>
    intro commands taken' ending htakes hp hlt hv hready hgood hcont hnd
    rw [settle_taken]
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact hready token (by simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ | ⟨_, _, _, _, _, _, ha, _⟩ |
        ⟨commands', ht', _, _⟩ | ⟨_, _, ha⟩
    · rw [ha] at hb; cases hb
    · rw [ha] at hb; cases hb
    · exact (snoc hgood) hcont (dom_of_prefix ht' (List.prefix_refl _))
    · rw [ha] at hb; cases hb
  | @continues taken token version ready failed session htype hcont' hdisc _ ih =>
    intro commands taken' ending htakes hp hlt hv hready hgood hcont hnd
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact hready token (by simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ |
        ⟨commands', taken'', ending', ht', hp', hlt', ha, hsw, hdi, hver⟩ | ⟨_, _, ha, _⟩ |
        ⟨_, _, ha⟩
    · rw [ha] at hcont'; cases hcont'
    · have hv' : (((scriptConsumer v₀).switchTo (taken ++ [token])).getD version) =
          versionAt v₀ commands' (taken ++ [token]).length := by
        rw [List.length_append, List.length_singleton, versionAt_succ, hsw, hver, hv]
      have hgood' := (snoc hgood) hcont (dom_of_prefix ht' hp')
      refine ih commands' taken'' ending' ht' hp' (by simpa using hlt') hv' ?_ hgood'
        (fun _ => hcont') (Or.inr hdisc)
      cases hs : (scriptConsumer v₀).switchTo (taken ++ [token]) with
      | none =>
        simp only [following, Option.getD_none]
        intro h hh
        exact hready h (by simp [hh])
      | some declared =>
        simp only [following, Option.getD_some, scriptConsumer_concrete, readyFrom_false]
        exact segment_ofVersion' hc declared input _ _
    · rw [ha] at hcont'; cases hcont'
    · rw [ha] at hcont'; cases hcont'
  | @breaks taken token result ready failed outcome version htype hb _ _ =>
    intro commands taken' ending htakes hp hlt hv hready _ _ hnd
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact hready token (by simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ | ⟨_, _, _, _, _, _, ha, _⟩ |
        ⟨_, _, _, htype'⟩ | ⟨_, _, ha⟩
    · rw [ha] at hb; cases hb
    · rw [ha] at hb; cases hb
    · exact absurd htype' htype
    · rw [ha] at hb; cases hb
  | @discardsHeld taken token result version ready failed htype hb _ _ =>
    intro commands taken' ending htakes hp hlt hv hready _ _ hnd
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact hready token (by simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ | ⟨_, _, _, _, _, _, ha, _⟩ |
        ⟨_, _, _, htype'⟩ | ⟨_, _, ha⟩
    · rw [ha] at hb; cases hb
    · rw [ha] at hb; cases hb
    · exact absurd htype' htype
    · rw [ha] at hb; cases hb
  | @discardsEnds taken token result version ready failed htype hb _ _ =>
    intro commands taken' ending htakes hp hlt hv hready _ _ hnd
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact hready token (by simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ | ⟨_, _, _, _, _, _, ha, _⟩ |
        ⟨_, _, _, htype'⟩ | ⟨_, _, ha⟩
    · rw [ha] at hb; cases hb
    · rw [ha] at hb; cases hb
    · exact absurd htype' htype
    · rw [ha] at hb; cases hb
  | @discardsWaiting taken token version ready failed htype hcont' hdisc _ =>
    intro commands taken' ending htakes hp hlt hv hready hgood hcont hnd
    rw [settle_taken]
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact hready token (by simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ |
        ⟨commands', taken'', ending', ht', hp', hlt', ha, hsw, hdi, hver⟩ | ⟨_, _, ha, _⟩ |
        ⟨_, _, ha⟩
    · rw [ha] at hcont'; cases hcont'
    · exact (snoc hgood) hcont (dom_of_prefix ht' hp')
    · rw [ha] at hcont'; cases hcont'
    · rw [ha] at hcont'; cases hcont'
  | @discardsToEnd taken token result version ready failed htype hcont' hdisc _ hb =>
    intro commands taken' ending htakes hp hlt hv hready hgood hcont hnd
    rw [settle_taken]
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact hready token (by simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ |
        ⟨commands', taken'', ending', ht', hp', hlt', ha, hsw, hdi, hver⟩ | ⟨_, _, ha, _⟩ |
        ⟨_, _, ha⟩
    · rw [ha] at hcont'; cases hcont'
    · rw [hdi] at hdisc
      obtain ⟨hlen, hlast, rfl⟩ := takes_discards ht' taken.length (by omega) hdisc
      have hst : (taken ++ [token]).map (rcv ∘ itemOf) = taken''.take (taken.length + 1) := by
        have := List.prefix_iff_eq_take.mp hp'
        simpa using this
      have hall : (taken ++ [token, endOfFileAt token.end]).map (rcv ∘ itemOf) = taken'' := by
        rw [eq_take_append_last (n := taken.length + 1) (by omega) hlast, ← hst]
        simp [rcv_itemOf_endOfFileAt]
      have hgood' := (snoc hgood) hcont (dom_of_prefix ht' hp')
      have hgood'' := (snoc hgood') (fun _ => hcont')
        (dom_of_prefix ht' (by
          rw [List.append_assoc]
          simp only [List.singleton_append]
          rw [hall]
          exact List.prefix_refl _))
      simpa using hgood''
    · rw [ha] at hcont'; cases hcont'
    · rw [ha] at hcont'; cases hcont'
  | @discardsFailsAtEnd taken token error version ready failed htype hcont' hdisc _ hf =>
    intro commands taken' ending htakes hp hlt hv hready _ _ hnd
    have hof : (rcv (itemOf token)).OfVersion (versionAt v₀ commands taken.length) := by
      rw [← hv]
      exact hready token (by simp)
    rcases consumer_step htakes hp hlt token hof hnd with ⟨_, ha⟩ |
        ⟨commands', taken'', ending', ht', hp', hlt', ha, hsw, hdi, hver⟩ | ⟨_, _, ha, _⟩ |
        ⟨_, _, ha⟩
    · rw [ha] at hcont'; cases hcont'
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
    · rw [ha] at hcont'; cases hcont'
    · rw [ha] at hcont'; cases hcont'

/-- A lexer correct with every consumer takes good tokens with the script consumer, whether or
not the input has ended. -/
theorem lexing_good (lexing : Lexing) (h : CorrectWithConsumers lexing)
    (version : Lexicon.Version) (slices : List Regex.Chars) (ended : Bool) :
    Param.Dom.Good version (lexing (scriptConsumer version) version [] slices ended).taken := by
  have hruns := h.2.1 (scriptConsumer version) version slices ended
    (scriptConsumer_breaksAtEnd version)
  rw [scriptConsumer_concrete, readyFrom_false] at hruns
  refine runs_good h.1 hruns [] [.endOfInput] .finished .done (by simp) (by simp) rfl
    (segment_ofVersion' h.1 version _ ended 0) ⟨fun n _ => ?_, fun n hn hlt => ?_⟩
    (fun h => absurd rfl h) (Or.inl rfl)
  · exact .inl ⟨[], [.endOfInput], .finished, .done, by simp⟩
  · simp at hlt

end BSmtLib.Facts.Proofs.Reader.Lexes.Good
