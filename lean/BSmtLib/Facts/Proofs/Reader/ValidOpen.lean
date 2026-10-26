module

public import BSmtLib.Facts.Proofs.Reader.Valid
public import BSmtLibSpec.Facts.Proofs.Grammar.RoundTrip
public import BSmtLibSpec.Facts.Proofs.Grammar.Files

@[expose] public section

/-!
# From characters to the calls of the traversal, before the end of the input

`runs_group_open`: any lexer correct with every consumer goes through the readings of a file with
the script consumer before the end of the input as it does with the end (`Valid.runs_group`),
with two differences:
- `exit` leaves it discarding from the end of its `)`;
- no end of file is handed over, so with no `exit` it waits or has failed, and does not discard.

The lexer is fed the file without the end of the input.
-/

open BSmtLib.Facts.Proofs.Reader.Consumer BSmtLib.Facts.Proofs.Reader.Feed
open BSmtLib.Facts.Proofs.Reader.Valid BSmtLib.Facts.Reader.Adapters

namespace BSmtLib.Facts.Proofs.Reader.ValidOpen

open BSmtLibSpec BSmtLibSpec.Lexicon BSmtLibSpec.Grammar BSmtLibSpec.Lexer
open BSmtLibSpec.Regex (Chars)
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection
open BSmtLibSpec.Facts.Proofs.Grammar.RoundTrip (FileReadingFrom fileReadingFrom_inv)
open BSmtLibSpec.Facts.Proofs.Grammar.Files (segment_eq)

variable {feed : Lexicon.Version → List Chars → Bool → Fed} {input : Chars}
  {v₀ : Lexicon.Version} {allCmds : List Tree.Command}

/-- The last command is `exit` exactly when the last after one that is not `exit` is. -/
theorem getLast?_cons_exit {command : Tree.Command} (hexit : command ≠ .exit)
    (commands : List Tree.Command) :
    (command :: commands).getLast? = some .exit ↔ commands.getLast? = some .exit := by
  cases commands with
  | nil => simp [hexit]
  | cons c cs => simp [List.getLast?_cons_cons]

/--
Through the readings of a file, before the end of the input: from the start of a reading, after
the commands before it, a lexer that does what `Runs` states with the script consumer began to
discard at the end of `exit` if the file ends with it, where the unread rest begins, and did not
discard otherwise.
-/
theorem runs_group_open (hc : Correct feed) (hscript : Script v₀ allCmds) :
    ∀ (commands done : List Tree.Command) (version : Lexicon.Version) (offset : Nat)
      (tokens : List Lexicon.Token) (eof : Bool) (pre tail : List Handed) (failed : Bool)
      (segments : List (Lexicon.Version × Facts.Proofs.Lexicon.RoundTrip.Tokens.Concrete))
          (final : Chars)
      (session : Session (scriptConsumer v₀).Result (scriptConsumer v₀).Error),
      allCmds = done ++ commands → (∀ d ∈ done, d ≠ .exit) →
      pre.map (rcv ∘ itemOf) = (doneTokens done).map .token →
      Group version offset (input.drop offset) commands tokens eof → offset ≤ input.length →
      FileReadingFrom version offset (input.drop offset) commands segments final →
      (eof = true → tail = []) →
      Runs feed (scriptConsumer v₀) v₀ input false version
        (tokens.map (·.handed version input) ++ tail) failed pre session →
      (commands.getLast? = some .exit →
          session.discardedFrom.map (·.offset) = some (input.length - final.length)) ∧
        (commands.getLast? ≠ some .exit → session.discardedFrom = none) := by
  intro commands
  induction commands with
  | nil =>
    intro done version offset tokens eof pre tail failed segments final session hall hne hpre hg
      hoff hfr htail hruns
    generalize hR : input.drop offset = R at hg
    cases hg with
    | done ht =>
      rw [htail rfl] at hruns
      simp only [List.map_nil, List.nil_append] at hruns
      cases hruns with
      | waiting => exact ⟨fun h => by simp at h, fun _ => by simp only [settle]; split <;> rfl⟩
      | lexical => exact ⟨fun h => by simp at h, fun _ => by simp only [settle]; split <;> rfl⟩
  | cons command commands ih =>
    intro done version offset tokens eof pre tail failed segments final session hall hne hpre hg
      hoff hfr htail hruns
    generalize hR : input.drop offset = R at hg hfr
    cases hg with
    | @stop _ part tokens _ rest hte hic hm =>
      obtain rfl := Parser.Script.modeAfter_unparsed hm
      have hrest : rest = final := by
        rcases fileReadingFrom_inv hfr with ⟨h, -⟩ | ⟨_, _, _, _, _, _, _, -, -, -, h₃, -, h, -⟩ |
            ⟨_, _, _, heq, h₁, h₂, -, -, -⟩
        · cases h
        · obtain ⟨rfl, -⟩ := List.cons.inj h
          rw [hm] at h₃; cases h₃
        · exact (segment_eq hte hic h₁ h₂ heq).2.1
      subst hrest
      obtain ⟨hhs, htypes, hlen, hend⟩ := command_handed input hte hic
      obtain ⟨hne', hruns'⟩ := walk_init hscript hall hne hpre hhs htypes hruns
      have hlhs : (tokens.map (·.handed version input)).length = Tree.Command.exit.tokens.length :=
        by simpa using hlen
      have hex : Tree.Command.exit.tokens.length = 3 := rfl
      obtain ⟨ha, hs, hd⟩ := at_command hscript hall hne hpre hhs
        (Tree.Command.exit.tokens.length - 1) (by omega)
      rw [requestsAt_exit (by omega)] at hs hd
      have htake : (tokens.map (·.handed version input)).take
          (Tree.Command.exit.tokens.length - 1 + 1) =
          (tokens.map (·.handed version input)).dropLast ++
            [(tokens.map (·.handed version input)).getLast hne'] := by
        rw [show Tree.Command.exit.tokens.length - 1 + 1 = Tree.Command.exit.tokens.length by
          omega, ← hlhs, List.take_length, ← init_last hne']
      rw [htake, ← List.append_assoc] at ha hd
      have hlastEnd := hend _ (List.getLast?_eq_some_getLast hne')
      have hlenR := congrArg List.length hR
      simp only [List.length_drop, List.length_append] at hlenR
      refine ⟨fun _ => ?_, fun hl => absurd (by simp) hl⟩
      cases hruns' with
      | discardsWaiting _ _ _ _ =>
        simp only [settle, Outcome.isFinished, Bool.false_eq_true, ↓reduceIte, Option.map_some]
        rw [hlastEnd]
        congr 1
        omega
      | discardsToEnd _ _ _ he => cases he
      | discardsFailsAtEnd _ _ _ he => cases he
      | continues _ _ hd' => rw [hd] at hd'; cases hd'
      | fails hf => rw [ha] at hf; cases hf
      | breaks _ hb => rw [ha] at hb; cases hb
      | discardsHeld _ hb => rw [ha] at hb; cases hb
      | discardsEnds _ hb => rw [ha] at hb; cases hb
      | ends he => exact absurd he (htypes _ (List.getLast_mem hne'))
    | @switch _ part tokens _ next rest _ hte hic hm hd hfile =>
      have hexit : command ≠ .exit := by
        rintro rfl; simp [Tree.Command.declaredVersion] at hd
      obtain ⟨segments', hfr'⟩ : ∃ segments',
          FileReadingFrom next (offset + part.length) rest commands segments' final := by
        rcases fileReadingFrom_inv hfr with ⟨h, -⟩ |
            ⟨_, _, _, _, _, segments', _, heq, h₁, h₂, h₃, h₄, h, -⟩ |
            ⟨_, _, _, heq, h₁, h₂, h₃, h, -⟩
        · cases h
        · obtain ⟨rfl, rfl, rfl⟩ := segment_eq hte hic h₁ h₂ heq
          obtain ⟨-, rfl⟩ := List.cons.inj h
          rw [hm] at h₃; cases h₃
          exact ⟨segments', h₄⟩
        · obtain ⟨-, -, rfl⟩ := segment_eq hte hic h₁ h₂ heq
          rw [hm] at h₃; cases h₃
      obtain ⟨hhs, htypes, hlen, hend⟩ := command_handed input hte hic
      obtain ⟨hne', hruns'⟩ := walk_init hscript hall hne hpre hhs htypes hruns
      have hlhs : (tokens.map (·.handed version input)).length = command.tokens.length := by
        simpa using hlen
      have hpos := command_tokens_pos command
      obtain ⟨ha, hs, hdisc⟩ := at_command hscript hall hne hpre hhs (command.tokens.length - 1)
        (by omega)
      rw [requestsAt_last (by omega) hexit, hd] at hs hdisc
      have htake : (tokens.map (·.handed version input)).take (command.tokens.length - 1 + 1) =
          (tokens.map (·.handed version input)).dropLast ++
            [(tokens.map (·.handed version input)).getLast hne'] := by
        rw [show command.tokens.length - 1 + 1 = command.tokens.length by omega, ← hlhs,
          List.take_length, ← init_last hne']
      rw [htake, ← List.append_assoc] at ha hs hdisc
      obtain ⟨hdrop, hle⟩ := drop_after_part hoff hR
      have hlastEnd := hend _ (List.getLast?_eq_some_getLast hne')
      cases hruns' with
      | continues _ _ _ hrest =>
        rw [hs] at hrest
        simp only [following, Option.getD_some, scriptConsumer_concrete, readyFrom_false] at hrest
        rw [hlastEnd] at hrest
        obtain ⟨tokens', eof', hg'⟩ := group_of_file hfile
        rw [← hdrop] at hg' hfr'
        obtain ⟨tail', hseg, htail'⟩ := segment_group_open hc hg' hle
        rw [hseg] at hrest
        obtain ⟨h₁, h₂⟩ := ih (done ++ [command]) next (offset + part.length) tokens' eof'
          (pre ++ tokens.map (·.handed version input)) tail'
          (segment feed next input false (offset + part.length)).failed segments' final session
          (by simp [hall])
          (by
            intro d hd'
            rcases List.mem_append.mp hd' with hd' | hd'
            · exact hne d hd'
            · rw [List.mem_singleton.mp hd']; exact hexit)
          (by rw [List.map_append, hpre, hhs]; simp [doneTokens]) hg' hle hfr' htail'
          (by rw [init_last hne', ← List.append_assoc]; exact hrest)
        exact ⟨fun hl => h₁ ((getLast?_cons_exit hexit _).mp hl),
          fun hl => h₂ fun he => hl ((getLast?_cons_exit hexit _).mpr he)⟩
      | fails hf => rw [ha] at hf; cases hf
      | ends he => exact absurd he (htypes _ (List.getLast_mem hne'))
      | breaks _ hb => rw [ha] at hb; cases hb
      | discardsHeld _ hb => rw [ha] at hb; cases hb
      | discardsEnds _ hb => rw [ha] at hb; cases hb
      | discardsWaiting _ _ hd' => rw [hdisc] at hd'; cases hd'
      | discardsToEnd _ _ hd' => rw [hdisc] at hd'; cases hd'
      | discardsFailsAtEnd _ _ hd' => rw [hdisc] at hd'; cases hd'
    | @keep _ part toks _ rest _ others eof hte hic hm hd hg' =>
      have hexit : command ≠ .exit := by
        rintro rfl; simp [Tree.Command.modeAfter] at hm
      obtain ⟨segments', hfr'⟩ : ∃ segments',
          FileReadingFrom version (offset + part.length) rest commands segments' final := by
        rcases fileReadingFrom_inv hfr with ⟨h, -⟩ |
            ⟨_, _, _, _, _, segments', _, heq, h₁, h₂, h₃, h₄, h, -⟩ |
            ⟨_, _, _, heq, h₁, h₂, h₃, h, -⟩
        · cases h
        · obtain ⟨rfl, rfl, rfl⟩ := segment_eq hte hic h₁ h₂ heq
          obtain ⟨-, rfl⟩ := List.cons.inj h
          rw [hm] at h₃; cases h₃
          exact ⟨segments', h₄⟩
        · obtain ⟨-, -, rfl⟩ := segment_eq hte hic h₁ h₂ heq
          rw [hm] at h₃; cases h₃
      obtain ⟨hhs, htypes, hlen, -⟩ := command_handed input hte hic
      obtain ⟨hdrop, hle⟩ := drop_after_part hoff hR
      rw [← hdrop] at hg' hfr'
      have hlhs : (toks.map (·.handed version input)).length = command.tokens.length := by
        simpa using hlen
      rw [List.map_append, List.append_assoc] at hruns
      have hwalk := runs_walk (consumer := scriptConsumer v₀) (toks.map (·.handed version input))
        (others.map (·.handed version input) ++ tail) version failed pre session
        (fun j hj => by
          obtain ⟨ha, hs, hdisc⟩ := at_command hscript hall hne hpre hhs j (by omega)
          by_cases hj' : j + 1 < command.tokens.length
          · rw [requestsAt_inner hj'] at hs hdisc
            exact ⟨ha, hdisc, hs, htypes⟩
          · rw [requestsAt_last (by omega) hexit, hd] at hs hdisc
            exact ⟨ha, hdisc, hs, htypes⟩) hruns
      obtain ⟨h₁, h₂⟩ := ih (done ++ [command]) version (offset + part.length) others eof
        (pre ++ toks.map (·.handed version input)) tail failed segments' final session
        (by simp [hall])
        (by
          intro d hd'
          rcases List.mem_append.mp hd' with hd' | hd'
          · exact hne d hd'
          · rw [List.mem_singleton.mp hd']; exact hexit)
        (by rw [List.map_append, hpre, hhs]; simp [doneTokens]) hg' hle hfr' htail hwalk
      exact ⟨fun hl => h₁ ((getLast?_cons_exit hexit _).mp hl),
        fun hl => h₂ fun he => hl ((getLast?_cons_exit hexit _).mpr he)⟩

end BSmtLib.Facts.Proofs.Reader.ValidOpen
