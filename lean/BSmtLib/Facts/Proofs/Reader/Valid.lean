module

public import BSmtLib.Facts.Proofs.Reader.Consumer
public import BSmtLib.Facts.Proofs.Reader.Feed

@[expose] public section

/-!
# A file, read by a correct lexer with the script consumer

On the input of a file of commands, a lexer that handles consumers as `BSmtLibSpec.Lexer.Runs`
states, given the script consumer, goes through the readings of the file: the consumer takes every
token of every command, goes on at each, switches the version after each version declaration, has
the rest discarded after `exit`, and breaks at the end of the input, which the lexer then returns
(`runs_file`). So the tokens the consumer takes stand for what a parser receives for the
script.
-/

namespace BSmtLib.Facts.Proofs.Reader.Valid

open BSmtLibSpec BSmtLibSpec.Lexicon BSmtLibSpec.Grammar BSmtLibSpec.Lexer
open BSmtLibSpec.Grammar.Syntax
open BSmtLibSpec.Regex (Chars)
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Facts.Proofs.Parser.Cut BSmtLib.Facts.Proofs.Parser.Rejection.Library
open BSmtLib.Facts.Proofs.Parser.Trace BSmtLib.Facts.Proofs.Reader.Consumer
open BSmtLib.Facts.Proofs.Reader.Feed BSmtLib.Facts.Reader.Adapters

variable {feed : Lexicon.Version → List Chars → Bool → Fed} {consumer : Consumer}
  {start : Lexicon.Version} {input : Chars} {ended : Bool}

/-- Over tokens at each of which the consumer goes on and asks for nothing, the lexer takes them
one after another. -/
theorem runs_walk : ∀ (handed ready : List Handed) (version : Lexicon.Version) (failed : Bool)
    (taken : List Handed) (session : Session consumer.Result consumer.Error),
    (∀ j < handed.length, consumer.answer (taken ++ handed.take (j + 1)) = .continue ∧
      consumer.discards (taken ++ handed.take (j + 1)) = false ∧
      consumer.switchTo (taken ++ handed.take (j + 1)) = none ∧
      ∀ h ∈ handed, h.type ≠ .endOfFile) →
    Runs feed consumer start input ended version (handed ++ ready) failed taken session →
    Runs feed consumer start input ended version ready failed (taken ++ handed) session
  | [], ready, version, failed, taken, session, _, hruns => by simpa using hruns
  | h :: handed, ready, version, failed, taken, session, hstep, hruns => by
    obtain ⟨hcont, hdisc, hswitch, htype⟩ := hstep 0 (by simp)
    simp only [List.take_succ_cons, List.take_zero] at hcont hdisc hswitch
    have htype' : h.type ≠ .endOfFile := htype h (by simp)
    have hnext : ∀ j < handed.length,
        consumer.answer (taken ++ [h] ++ handed.take (j + 1)) = .continue ∧
        consumer.discards (taken ++ [h] ++ handed.take (j + 1)) = false ∧
        consumer.switchTo (taken ++ [h] ++ handed.take (j + 1)) = none ∧
        ∀ h' ∈ handed, h'.type ≠ .endOfFile := by
      intro j hj
      obtain ⟨a, b, c, _⟩ := hstep (j + 1) (by simp; omega)
      simp only [List.take_succ_cons] at a b c
      exact ⟨by simpa using a, by simpa using b, by simpa using c,
        fun h' hh' => htype h' (by simp [hh'])⟩
    rw [List.cons_append] at hruns
    cases hruns with
    | fails hf => rw [hcont] at hf; cases hf
    | ends he => exact absurd he htype'
    | continues _ _ _ hrest =>
      rw [hswitch] at hrest
      simp only [following, Option.getD_none] at hrest
      have := runs_walk handed ready version failed (taken ++ [h]) session hnext hrest
      simpa using this
    | breaks _ hb => rw [hcont] at hb; cases hb
    | discardsHeld _ hb => rw [hcont] at hb; cases hb
    | discardsEnds _ hb => rw [hcont] at hb; cases hb
    | discardsWaiting _ _ hd => rw [hdisc] at hd; cases hd
    | discardsToEnd _ _ hd => rw [hdisc] at hd; cases hd
    | discardsFailsAtEnd _ _ hd => rw [hdisc] at hd; cases hd

/-! ## The tokens of a command -/

/-- The tokens of the commands, one after another. -/
def doneTokens (commands : List Tree.Command) : List Grammar.SyntaxToken :=
  commands.flatMap Tree.Command.tokens

theorem received_append {done : List Tree.Command} (hne : ∀ c ∈ done, c ≠ .exit)
    (commands : List Tree.Command) :
    received (done ++ commands) = (doneTokens done).map .token ++ received commands := by
  induction done with
  | nil => rfl
  | cons c done ih =>
    rw [List.cons_append, Facts.Proofs.Parser.Simulation.received_cons (hne c (by simp)),
      ih fun d hd => hne d (by simp [hd])]
    simp [doneTokens, Facts.Proofs.Parser.Simulation.items]

theorem command_tokens_pos (command : Tree.Command) : 0 < command.tokens.length := by
  obtain ⟨inner, h⟩ := Facts.Proofs.Parser.Simulation.command_tokens_open command
  rw [h]
  simp

theorem requestsAt_append {done : List Tree.Command} (commands : List Tree.Command) (j : Nat) :
    requestsAt (done ++ commands) ((doneTokens done).length + j) = requestsAt commands j := by
  induction done with
  | nil => simp [doneTokens]
  | cons c done ih =>
    have hpos := command_tokens_pos c
    have hlen : (doneTokens (c :: done)).length = c.tokens.length + (doneTokens done).length := by
      simp [doneTokens]
    have h1 : ¬ (c.tokens.length + (doneTokens done).length + j + 1 < c.tokens.length) := by
      omega
    have h2 : ¬ (c.tokens.length + (doneTokens done).length + j + 1 = c.tokens.length) := by
      omega
    rw [hlen, List.cons_append]
    simp only [requestsAt]
    simp only [h1, h2, ite_false]
    rw [show c.tokens.length + (doneTokens done).length + j - c.tokens.length =
      (doneTokens done).length + j by omega]
    exact ih

theorem received_cons_take (command : Tree.Command) (commands : List Tree.Command) :
    (received (command :: commands)).take command.tokens.length = command.tokens.map .token := by
  by_cases hex : command = .exit
  · subst hex
    simp [received]
  · rw [Facts.Proofs.Parser.Simulation.received_cons hex]
    simp [Facts.Proofs.Parser.Simulation.items]

theorem received_cons_length (command : Tree.Command) (commands : List Tree.Command) :
    command.tokens.length < (received (command :: commands)).length := by
  by_cases hex : command = .exit
  · subst hex
    simp [received]
  · rw [Facts.Proofs.Parser.Simulation.received_cons hex]
    have : 0 < (received commands).length := by
      cases commands with
      | nil => simp [received]
      | cons c cs =>
        by_cases hc : c = .exit
        · subst hc; simp [received]
        · rw [Facts.Proofs.Parser.Simulation.received_cons hc]
          have := command_tokens_pos c
          simp [Facts.Proofs.Parser.Simulation.items]
          omega
    simp [Facts.Proofs.Parser.Simulation.items]
    omega

/-- The handed tokens of a command of a reading. -/
theorem command_handed {version : Lexicon.Version} (input : Chars) {offset : Nat}
    {part : Chars} {tokens : List Lexicon.Token} {command : Tree.Command}
    (hte : Tokenization.Exactly version offset part tokens)
    (hic : IsCommand version (tokens.map (SyntaxToken.ofToken version)) command) :
    (tokens.map (·.handed version input)).map (rcv ∘ itemOf) = command.tokens.map .token ∧
      (∀ h ∈ tokens.map (·.handed version input), h.type ≠ .endOfFile) ∧
      tokens.length = command.tokens.length ∧
      ∀ last, (tokens.map (·.handed version input)).getLast? = some last →
        last.«end».offset = offset + part.length := by
  have hmem := Facts.Proofs.Lexer.StreamingFacts.tokenizationFrom_mem hte.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hic.2, List.map_map, List.map_map]
    refine List.map_congr_left fun token htoken => ?_
    exact rcv_itemOf_handed input (hmem token htoken).1
  · intro h hh
    obtain ⟨token, -, rfl⟩ := List.mem_map.mp hh
    obtain ⟨category, offset, text⟩ := token
    cases category <;> simp [Lexicon.Token.handed, Category.type]
  · rw [hic.2]; simp
  · intro last hlast
    obtain ⟨-, l, hl, hend⟩ := hte
    rw [List.getLast?_map, hl] at hlast
    simp only [Option.map_some, Option.some.injEq] at hlast
    subst hlast
    simp [Lexicon.Token.handed, locate, hend]

/-! ## The consumer inside a command -/

/-- At a token of a command of a script, after the commands before it, the script consumer goes on,
and asks for what `requestsAt` says. -/
theorem at_command {v₀ : Lexicon.Version} {allCmds : List Tree.Command}
    (hscript : Script v₀ allCmds)
    {done : List Tree.Command} {command : Tree.Command} {commands : List Tree.Command}
    (hall : allCmds = done ++ command :: commands) (hne : ∀ d ∈ done, d ≠ .exit)
    {pre : List Handed} (hpre : pre.map (rcv ∘ itemOf) = (doneTokens done).map .token)
    {handed : List Handed} (hhs : handed.map (rcv ∘ itemOf) = command.tokens.map .token)
    (j : Nat) (hj : j < command.tokens.length) :
    (scriptConsumer v₀).answer (pre ++ handed.take (j + 1)) = .continue ∧
      (scriptConsumer v₀).switchTo (pre ++ handed.take (j + 1)) =
        (requestsAt (command :: commands) j).1 ∧
      (scriptConsumer v₀).discards (pre ++ handed.take (j + 1)) =
        (requestsAt (command :: commands) j).2 := by
  have hlhs : handed.length = command.tokens.length := by
    simpa using congrArg List.length hhs
  have hlpre : pre.length = (doneTokens done).length := by
    simpa using congrArg List.length hpre
  have hrec : received allCmds = (doneTokens done).map .token ++ received (command :: commands) :=
    hall ▸ received_append hne _
  have hcl := received_cons_length command commands
  have hlen : (pre ++ handed.take (j + 1)).length = (doneTokens done).length + j + 1 := by
    simp [hlpre, hlhs]; omega
  have hitems : (pre ++ handed.take (j + 1)).map (rcv ∘ itemOf) =
      (received allCmds).take (pre ++ handed.take (j + 1)).length := by
    rw [hlen, hrec, List.map_append, hpre, List.take_append,
      List.take_of_length_le (l := (doneTokens done).map Received.token) (by simp; omega)]
    congr 1
    rw [show (doneTokens done).length + j + 1 - ((doneTokens done).map Received.token).length =
      j + 1 by simp; omega]
    rw [List.map_take, hhs, ← received_cons_take command commands,
      List.take_take, Nat.min_eq_left (by omega)]
  have hlt : (pre ++ handed.take (j + 1)).length < (received allCmds).length := by
    rw [hlen, hrec]
    simp only [List.length_append, List.length_map]
    omega
  have htakes := takes_of_script hscript
  refine ⟨?_, ?_⟩
  · rw [answer_takes htakes hitems (Nat.le_of_lt hlt)]
    simp only [hlt, ↓reduceIte]
    rfl
  · have hreq := requests_takes hscript hitems (by rw [hlen]; omega) (Nat.le_of_lt hlt)
    rw [hlen, show (doneTokens done).length + j + 1 - 1 = (doneTokens done).length + j by omega,
      hall, requestsAt_append] at hreq
    exact hreq

theorem requestsAt_inner {command : Tree.Command} {commands : List Tree.Command} {j : Nat}
    (hj : j + 1 < command.tokens.length) : requestsAt (command :: commands) j = (none, false) := by
  simp [requestsAt, hj]

theorem requestsAt_last {command : Tree.Command} {commands : List Tree.Command} {j : Nat}
    (hj : j + 1 = command.tokens.length) (hne : command ≠ .exit) :
    requestsAt (command :: commands) j = (command.declaredVersion, false) := by
  cases command <;> simp_all [requestsAt]

theorem requestsAt_exit {commands : List Tree.Command} {j : Nat}
    (hj : j + 1 = Tree.Command.exit.tokens.length) :
    requestsAt (.exit :: commands) j = (none, true) := by
  simp_all [requestsAt, Tree.Command.declaredVersion]

theorem init_last {α : Type} {l : List α} (h : l ≠ []) :
    l = l.dropLast ++ [l.getLast h] := (List.dropLast_concat_getLast h).symm

/-! ## Through the readings of a file -/

section

variable {v₀ : Lexicon.Version} {allCmds : List Tree.Command}

/-- Through every token of a command but its last, the lexer takes them one by one. -/
theorem walk_init (hscript : Script v₀ allCmds) {done : List Tree.Command}
    {command : Tree.Command} {commands : List Tree.Command}
    (hall : allCmds = done ++ command :: commands) (hne : ∀ d ∈ done, d ≠ .exit)
    {pre : List Handed} (hpre : pre.map (rcv ∘ itemOf) = (doneTokens done).map .token)
    {handed : List Handed} (hhs : handed.map (rcv ∘ itemOf) = command.tokens.map .token)
    (htypes : ∀ h ∈ handed, h.type ≠ .endOfFile) {version : Lexicon.Version}
    {ready : List Handed} {failed : Bool} {session : Session Unit ScriptError}
    (hruns : Runs feed (scriptConsumer v₀) v₀ input ended version (handed ++ ready) failed pre
      session) :
    ∃ (hne' : handed ≠ []), Runs feed (scriptConsumer v₀) v₀ input ended version
      (handed.getLast hne' :: ready) failed (pre ++ handed.dropLast) session := by
  have hlhs : handed.length = command.tokens.length := by simpa using congrArg List.length hhs
  have hpos := command_tokens_pos command
  have hne' : handed ≠ [] := by
    intro h; rw [h] at hlhs; simp at hlhs; omega
  refine ⟨hne', ?_⟩
  rw [init_last hne', List.append_assoc, List.singleton_append] at hruns
  refine runs_walk (consumer := scriptConsumer v₀) handed.dropLast (handed.getLast hne' :: ready)
    version failed pre session (fun j hj => ?_) hruns
  have hj' : j < command.tokens.length := by
    simp only [List.length_dropLast] at hj; omega
  have htake : handed.dropLast.take (j + 1) = handed.take (j + 1) := by
    rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left (by simp at hj; omega)]
  obtain ⟨ha, hs, hd⟩ := at_command hscript hall hne hpre hhs j hj'
  rw [requestsAt_inner (by simp at hj; omega)] at hs hd
  rw [htake]
  exact ⟨ha, hd, hs, fun h hh => htypes h (List.dropLast_subset _ hh)⟩

theorem drop_after_part {input part rest : Chars} {offset : Nat} (hoff : offset ≤ input.length)
    (h : input.drop offset = part ++ rest) :
    input.drop (offset + part.length) = rest ∧ offset + part.length ≤ input.length := by
  have hlen := congrArg List.length h
  simp only [List.length_drop, List.length_append] at hlen
  refine ⟨?_, by omega⟩
  rw [← List.drop_drop, h, List.drop_left]

/-- The answer at the end of the input after all of a script's tokens: the consumer breaks. -/
theorem answer_end (hscript : Script v₀ allCmds) {handed : List Handed}
    (hst : handed.map (rcv ∘ itemOf) = received allCmds) :
    (scriptConsumer v₀).answer handed = .break () := by
  have hlen : handed.length = (received allCmds).length := by
    simpa using congrArg List.length hst
  rw [answer_takes (takes_of_script hscript) (by rw [hst, hlen, List.take_length])
    (Nat.le_of_eq hlen)]
  simp only [hlen, Nat.lt_irrefl, ↓reduceIte]
  rfl

/--
Through the readings of a file: from the start of a reading, after the commands before it, a
lexer that does what `Runs` states with the script consumer finishes, the consumer having taken
what stands for what a parser receives for the script.
-/
theorem runs_group (hc : Correct feed) (hscript : Script v₀ allCmds) :
    ∀ (commands done : List Tree.Command) (version : Lexicon.Version) (offset : Nat)
      (tokens : List Lexicon.Token) (eof : Bool) (pre tail : List Handed) (failed : Bool)
      (session : Session (scriptConsumer v₀).Result (scriptConsumer v₀).Error),
      allCmds = done ++ commands → (∀ d ∈ done, d ≠ .exit) →
      pre.map (rcv ∘ itemOf) = (doneTokens done).map .token →
      Group version offset (input.drop offset) commands tokens eof → offset ≤ input.length →
      (eof = true → tail = [endOfFile input]) →
      Runs feed (scriptConsumer v₀) v₀ input true version
        (tokens.map (·.handed version input) ++ tail) failed pre session →
      session.outcome.isFinished = true ∧ session.taken.map (rcv ∘ itemOf) = received allCmds := by
  intro commands
  induction commands with
  | nil =>
    intro done version offset tokens eof pre tail failed session hall hne hpre hg hoff htail hruns
    generalize hR : input.drop offset = R at hg
    cases hg with
    | done ht =>
      rw [htail rfl] at hruns
      simp only [List.map_nil, List.nil_append] at hruns
      have hst : (pre ++ [endOfFile input]).map (rcv ∘ itemOf) = received allCmds := by
        rw [hall, received_append hne, List.map_append, hpre]
        rfl
      have hans := answer_end hscript hst
      cases hruns with
      | fails hf => rw [hans] at hf; cases hf
      | ends _ _ =>
        refine ⟨by simp [settle, Outcome.isFinished], ?_⟩
        simpa [settle, Outcome.isFinished] using hst
      | continues ht' => exact absurd rfl ht'
      | breaks ht' => exact absurd rfl ht'
      | discardsHeld ht' => exact absurd rfl ht'
      | discardsEnds ht' => exact absurd rfl ht'
      | discardsWaiting ht' => exact absurd rfl ht'
      | discardsToEnd ht' => exact absurd rfl ht'
      | discardsFailsAtEnd ht' => exact absurd rfl ht'
  | cons command commands ih =>
    intro done version offset tokens eof pre tail failed session hall hne hpre hg hoff htail hruns
    generalize hR : input.drop offset = R at hg
    cases hg with
    | @stop _ part tokens _ rest hte hic hm =>
      obtain rfl := Parser.Script.modeAfter_unparsed hm
      obtain ⟨hhs, htypes, hlen, -⟩ := command_handed input hte hic
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
      have hst : (pre ++ (tokens.map (·.handed version input)).dropLast ++
          [(tokens.map (·.handed version input)).getLast hne',
            endOfFileAt
              ((tokens.map (fun t : Lexicon.Token => t.handed version input)).getLast
                hne').«end»]).map
            (rcv ∘ itemOf) = received allCmds := by
        have e : ∀ x : Handed, pre ++ (tokens.map (·.handed version input)).dropLast ++
            [(tokens.map (·.handed version input)).getLast hne', x] =
            pre ++ tokens.map (·.handed version input) ++ [x] := by
          intro x
          conv => rhs; rw [init_last hne']
          simp
        rw [e, hall, received_append hne, List.map_append, List.map_append, hpre, hhs]
        simp [received, rcv_itemOf_endOfFileAt]
      have hans := answer_end hscript hst
      cases hruns' with
      | discardsToEnd _ _ _ _ _ =>
        refine ⟨by simp [settle, Outcome.isFinished], ?_⟩
        simpa [settle, Outcome.isFinished, List.append_assoc] using hst
      | discardsFailsAtEnd _ _ _ _ hf =>
        rw [hans] at hf; cases hf
      | continues _ _ hd' => rw [hd] at hd'; cases hd'
      | discardsWaiting _ _ _ he => cases he
      | fails hf => rw [ha] at hf; cases hf
      | breaks _ hb => rw [ha] at hb; cases hb
      | discardsHeld _ hb => rw [ha] at hb; cases hb
      | discardsEnds _ hb => rw [ha] at hb; cases hb
      | ends he => exact absurd he (htypes _ (List.getLast_mem hne'))
    | @switch _ part tokens _ next rest _ hte hic hm hd hfile =>
      have hexit : command ≠ .exit := by
        rintro rfl; simp [Tree.Command.declaredVersion] at hd
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
        rw [← hdrop] at hg'
        obtain ⟨tail', hseg, htail'⟩ := segment_group hc hg' hle
        rw [hseg] at hrest
        refine ih (done ++ [command]) next (offset + part.length) tokens' eof'
          (pre ++ tokens.map (·.handed version input)) tail'
          (segment feed next input true (offset + part.length)).failed session (by simp [hall])
          (by
            intro d hd'
            rcases List.mem_append.mp hd' with hd' | hd'
            · exact hne d hd'
            · rw [List.mem_singleton.mp hd']; exact hexit)
          ?_ hg' hle htail' ?_
        · rw [List.map_append, hpre, hhs]; simp [doneTokens]
        · rw [init_last hne', ← List.append_assoc]
          exact hrest
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
      obtain ⟨hhs, htypes, hlen, -⟩ := command_handed input hte hic
      obtain ⟨hdrop, hle⟩ := drop_after_part hoff hR
      rw [← hdrop] at hg'
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
      refine ih (done ++ [command]) version (offset + part.length) others eof
        (pre ++ toks.map (·.handed version input)) tail failed session (by simp [hall])
        (by
          intro d hd'
          rcases List.mem_append.mp hd' with hd' | hd'
          · exact hne d hd'
          · rw [List.mem_singleton.mp hd']; exact hexit)
        ?_ hg' hle htail hwalk
      rw [List.map_append, hpre, hhs]; simp [doneTokens]

end

/-! ## A file -/

/-- The commands of a file make a script. -/
theorem script_of_file {version : Lexicon.Version} {offset : Nat} {chars : Chars}
    {commands : List Tree.Command} (h : File.From version offset chars commands) :
    Script version commands := by
  induction h with
  | done => exact .done
  | command _ hic hm _ ih => exact .command hic.1 hm ih
  | stop _ hic hm => exact .stop hic.1 hm

theorem eventsBefore_all (events : List Event) :
    eventsBefore (events.countP isArrival) events = events := by
  have := eventsBefore_append events [] 0
  simpa [eventsBefore] using this

/--
A lexer that handles consumers as the formalism states finishes on a file with the script
consumer, the consumer having taken what stands for what a parser receives for the script. The
recording run of the library's parser on those tokens has the traversal's events. The lexer is
fed the slices of the file and then the end of the input.
-/
theorem lexing_file (lexing : Lexing) (h : CorrectWithConsumers lexing)
    (version : Lexicon.Version) (slices : List Chars) {commands : List Tree.Command}
    (hfile : File version slices.flatten commands) :
    (lexing (scriptConsumer version) version [] slices true).outcome.isFinished = true ∧
      (lexing (scriptConsumer version) version [] slices true).taken.map (rcv ∘ itemOf) =
        received commands ∧
      (libraryParser.parse version
        ((lexing (scriptConsumer version) version [] slices true).taken.map libItem)).1 =
        record version commands := by
  have hscript := script_of_file hfile
  have hruns := h.2.1 (scriptConsumer version) version slices true
    (scriptConsumer_breaksAtEnd version)
  rw [scriptConsumer_concrete, readyFrom_false] at hruns
  obtain ⟨tokens, eof, hg⟩ := group_of_file hfile
  have hg' : Group version 0 (slices.flatten.drop 0) commands tokens eof := by simpa using hg
  obtain ⟨tail, hseg, htail⟩ := segment_group h.1 hg' (Nat.zero_le _)
  rw [hseg] at hruns
  obtain ⟨hfin, htaken⟩ := runs_group h.1 hscript commands [] version 0 tokens eof [] tail _ _
    rfl (by simp) (by simp [doneTokens]) hg' (Nat.zero_le _) htail hruns
  refine ⟨hfin, htaken, ?_⟩
  have hlen : (lexing (scriptConsumer version) version [] slices true).taken.length =
      (received commands).length := by simpa using congrArg List.length htaken
  rw [parse_takes (takes_of_script hscript) (by rw [htaken, hlen, List.take_length])
    (Nat.le_of_eq hlen)]
  have harr : (record version commands).countP isArrival = (received commands).length := by
    rw [countP_arrival, (Facts.Proofs.Parser.Calls.record_items hscript).1]
  simp only [hlen, ← harr, eventsBefore_all]

end BSmtLib.Facts.Proofs.Reader.Valid
