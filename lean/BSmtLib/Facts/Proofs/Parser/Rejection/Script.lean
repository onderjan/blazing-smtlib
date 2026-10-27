module

public import BSmtLib.Facts.Proofs.Parser.Rejection.CommandStep
public import BSmtLib.Facts.Proofs.Parser.Cut
import all BSmtLib.Parser.Command
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# What the script parser has taken

The script parser runs the command parser on one command after another. What it has taken is
the commands it completed, a chain of valid commands each read in the version the ones before it
leave (`Chain`), and the items of the command it is in.

The command parser's remainders are taken with two kinds of continuations:
- what a parser takes for the rest of a script (`scriptFollows`), which says that the items so
  far are the start of what a parser takes;
- one item that marks how the command ends (`markers`), from which a completed command is read
  back exactly.
-/

namespace BSmtLib.Facts.Proofs.Parser.Rejection.Script

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Version (VersionPosture)
open BSmtLib.Parser.Command (CommandOutcome)
open BSmtLib.Parser.Command.Internal (CommandState commandStep)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Bridge.Rejection
open BSmtLib.Facts.Parser.Adapters.Run BSmtLib.Facts.Proofs.Parser.Cut
open BSmtLib.Facts.Proofs.Parser.Rejection.Basic BSmtLib.Facts.Proofs.Parser.Rejection.Command
open BSmtLib.Facts.Proofs.Parser.Rejection.CommandStep BSmtLib.Facts.Proofs.Parser.Rejection.SExpr
open BSmtLib.Facts.Proofs.Parser.Rejection.«Sort» BSmtLib.Facts.Proofs.Parser.Script
open BSmtLib.Facts.Proofs.Parser.Tokens BSmtLib.Parser.Script.Internal.VersionPosture

open BSmtLib.Facts.Proofs.Parser.Rejection.Basic.Lang

/-! ## Continuations -/

/-- What a parser takes from a version on: a script, or commands that a refused declaration
ends. -/
def TakenFrom (version : BSmtLibSpec.Lexicon.Version) : Lang :=
  fun u => ∃ commands ending, Takes version commands u ending

/-- What follows a command in a script, as the command ends. -/
def scriptFollows : CmdEnd → Lang
  | .next version => TakenFrom version
  | .exit => tok .endOfInput
  | .refused => eps
  | .endOfInput => eps

/-- The number that marks how a command ends. -/
def endCode : CmdEnd → BSmtLibSpec.Regex.Chars
  | .next .v2_0 => [0]
  | .next .v2_5 => [1]
  | .next .v2_6 => [2]
  | .next .v2_7 => [3]
  | .exit => [4]
  | .refused => [5]
  | .endOfInput => [6]

/-- The item that marks how a command ends. -/
def markerItem (e : CmdEnd) : Received := .token (.numeral (endCode e))

/-- One marker item, as what follows a command. -/
def markers (e : CmdEnd) : Lang := tok (markerItem e)

theorem markerItem_injective {e e' : CmdEnd} (h : markerItem e = markerItem e') : e = e' := by
  rcases e with (_ | _ | _ | _) | _ | _ | _ <;> rcases e' with (_ | _ | _ | _) | _ | _ | _ <;>
    first | rfl | (simp [markerItem, endCode] at h)

theorem takenFrom_nonempty (version : BSmtLibSpec.Lexicon.Version) : ∃ u, TakenFrom version u :=
  ⟨_, [], .finished, .done⟩

theorem scriptFollows_nonempty (e : CmdEnd) : ∃ u, scriptFollows e u := by
  cases e with
  | next version => exact takenFrom_nonempty version
  | exit => exact ⟨_, tok_intro _⟩
  | refused => exact ⟨[], rfl⟩
  | endOfInput => exact ⟨[], rfl⟩

theorem markers_nonempty (e : CmdEnd) : ∃ u, markers e u := ⟨_, tok_intro _⟩

/-- What a parser takes from a version on is what the command parser takes before a command,
with what follows a command in a script. -/
theorem takenFrom_iff (version : BSmtLibSpec.Lexicon.Version) (u : List Received) :
    TakenFrom version u ↔ commandRem version scriptFollows .awaiting u := by
  constructor
  · rintro ⟨commands, ending, h⟩
    cases h with
    | done => exact Or.inr (cat_tok rfl)
    | @command _ next _ _ _ c hvalid hmode hrest =>
      exact Or.inl ⟨c, _, hvalid, by simp only [cmdEnd, hmode]; exact ⟨_, _, hrest⟩, rfl⟩
    | stop hvalid hmode =>
      exact Or.inl ⟨_, _, hvalid, by simp only [cmdEnd, hmode]; exact tok_intro _, rfl⟩
    | refused hvalid hmode =>
      exact Or.inl ⟨_, [], hvalid, by simp only [cmdEnd, hmode]; rfl, by simp⟩
  · rintro (⟨c, w, hvalid, hw, rfl⟩ | ⟨_, w, rfl, hw, rfl⟩)
    · unfold cmdEnd at hw
      split at hw
      · rename_i next hmode
        obtain ⟨commands, ending, hrest⟩ := hw
        exact ⟨_, _, .command hvalid hmode hrest⟩
      · rename_i hmode
        cases hw
        exact ⟨_, _, .stop hvalid hmode⟩
      · rename_i hmode
        cases hw
        exact ⟨_, _, by simpa using Takes.refused hvalid hmode⟩
    · cases hw
      exact ⟨_, _, .done⟩

/-! ## Commands completed -/

/-- Commands read one after another from a version, each valid in the version in force and
followed by more commands in a version, with the version they leave. -/
inductive Chain : BSmtLibSpec.Lexicon.Version → List Tree.Command → BSmtLibSpec.Lexicon.Version →
    Prop
  | nil : Chain version [] version
  | cons {first : Tree.Command} : first.Valid version →
      first.modeAfter version = some (.read next) → Chain next rest last →
      Chain version (first :: rest) last

/-- The items of commands. -/
def cmdToks (commands : List Tree.Command) : List Received :=
  toks (commands.flatMap Tree.Command.tokens)

@[simp] theorem cmdToks_nil : cmdToks [] = [] := rfl

theorem cmdToks_cons (c : Tree.Command) (rest : List Tree.Command) :
    cmdToks (c :: rest) = toks c.tokens ++ cmdToks rest := by
  simp [cmdToks]

theorem cmdToks_append (cs cs' : List Tree.Command) :
    cmdToks (cs ++ cs') = cmdToks cs ++ cmdToks cs' := by
  simp [cmdToks]

theorem chain_snoc {version last next : BSmtLibSpec.Lexicon.Version} {cs : List Tree.Command}
    {c : Tree.Command} (h : Chain version cs last) (hc : c.Valid last)
    (hmode : c.modeAfter last = some (.read next)) : Chain version (cs ++ [c]) next := by
  induction h with
  | nil => exact .cons hc hmode .nil
  | cons hv hm _ ih => exact .cons hv hm (ih hc hmode)

theorem takes_of_chain {version last : BSmtLibSpec.Lexicon.Version} {cs : List Tree.Command}
    (h : Chain version cs last) {rest : List Tree.Command} {taken : List Received}
    {ending : Ending} (hrest : Takes last rest taken ending) :
    Takes version (cs ++ rest) (cmdToks cs ++ taken) ending := by
  induction h with
  | nil => simpa using hrest
  | cons hv hm _ ih =>
    rw [List.cons_append, cmdToks_cons, List.append_assoc]
    exact .command hv hm (ih hrest)

theorem takenFrom_of_chain {version last : BSmtLibSpec.Lexicon.Version} {cs : List Tree.Command}
    (h : Chain version cs last) {u : List Received} (hu : TakenFrom last u) :
    TakenFrom version (cmdToks cs ++ u) := by
  obtain ⟨rest, ending, hrest⟩ := hu
  exact ⟨_, _, takes_of_chain h hrest⟩

/-- The items are those of commands with the initial version, each followed by more commands in a
version, and then those of `exit`: after them, the producer is asked to discard the rest. -/
def AfterExit (version : BSmtLibSpec.Lexicon.Version) (items : List Received) : Prop :=
  ∃ done last, Chain version done last ∧ items = cmdToks done ++ toks Tree.Command.exit.tokens

theorem versionAt_chain {version last : BSmtLibSpec.Lexicon.Version} {cs : List Tree.Command}
    (h : Chain version cs last) (rest : List Tree.Command) (k : Nat) :
    versionAt version (cs ++ rest) ((cmdToks cs).length + k) = versionAt last rest k := by
  induction h generalizing k with
  | nil => simp
  | @cons version next tail last' c hv hm _ ih =>
    rw [List.cons_append, cmdToks_cons]
    simp only [versionAt, List.length_append]
    have hlen : ¬ ((toks c.tokens).length + (cmdToks tail).length + k < c.tokens.length) := by
      simp only [toks, List.length_map]
      omega
    simp only [hlen, ↓reduceIte]
    obtain ⟨-, hnext⟩ := modeAfter_read hm
    rw [← hnext]
    have harg : (toks c.tokens).length + (cmdToks tail).length + k - c.tokens.length =
        (cmdToks tail).length + k := by simp only [toks, List.length_map]; omega
    rw [harg]
    exact ih k

/-! ## The command parser's state -/

/-- The command parser's state, after the items of the command so far: each remainder of the
state completes them as one before a command, and the state has a remainder. -/
def CmdInv (version : BSmtLibSpec.Lexicon.Version) (follows : CmdEnd → Lang) (items : List Received)
    (state : CommandState Nat Nat Nat Nat Nat Empty) : Prop :=
  (∀ u, commandRem version follows state u → commandRem version follows .awaiting (items ++ u)) ∧
    ∃ u, commandRem version follows state u

theorem cmdInv_awaiting (version : BSmtLibSpec.Lexicon.Version) (follows : CmdEnd → Lang)
    (hfollows : ∀ e, ∃ w, follows e w) : CmdInv version follows [] .awaiting :=
  ⟨fun _ h => h, by
    obtain ⟨w, hw⟩ := hfollows .endOfInput
    exact ⟨_, Or.inr (cat_tok hw)⟩⟩

/-- A command completed before its marker is a command, or the end of the input. -/
theorem awaiting_marked {version : BSmtLibSpec.Lexicon.Version} {q : List Received} {e : CmdEnd}
    (h : commandRem version markers .awaiting (q ++ [markerItem e])) :
    (e = .endOfInput ∧ q = [.endOfInput]) ∨
      ∃ c, c.Valid version ∧ q = toks c.tokens ∧ cmdEnd version c = e := by
  rcases h with ⟨c, w, hvalid, hw, heq⟩ | ⟨_, w, rfl, hw, heq⟩
  · cases hw
    obtain ⟨hq, hm⟩ := List.append_inj' heq rfl
    simp only [List.cons.injEq, and_true] at hm
    exact Or.inr ⟨c, hvalid, hq, (markerItem_injective hm).symm⟩
  · cases hw
    obtain ⟨hq, hm⟩ := List.append_inj' heq rfl
    simp only [List.cons.injEq, and_true] at hm
    exact Or.inl ⟨markerItem_injective hm, hq⟩

theorem cmdInv_more {version : BSmtLibSpec.Lexicon.Version} {follows : CmdEnd → Lang}
    {items : List Received} {state state' : CommandState Nat Nat Nat Nat Nat Empty} {x : Received}
    (hinv : CmdInv version follows items state)
    {fin : CommandState Nat Nat Nat Nat Nat Empty → CommandOutcome → Lang}
    (hr : Advances (commandRem version follows) fin state x (.more state')) :
    CmdInv version follows (items ++ [x]) state' := by
  obtain ⟨himpl, hne⟩ := hr hinv.2
  exact ⟨fun u hu => by simpa using hinv.1 _ (himpl u hu), hne⟩

/-- A completed command's items, read back with its marker. -/
theorem cmdInv_done {version : BSmtLibSpec.Lexicon.Version} {items : List Received}
    {state : CommandState Nat Nat Nat Nat Nat Empty} {x : Received} {e : CmdEnd}
    (hinv : CmdInv version markers items state)
    (hdone : (∃ u, commandRem version markers state u) →
      ∀ w, markers e w → commandRem version markers state ([x] ++ w)) :
    (e = .endOfInput ∧ items ++ [x] = [.endOfInput]) ∨
      ∃ c, c.Valid version ∧ items ++ [x] = toks c.tokens ∧ cmdEnd version c = e := by
  have h := hinv.1 _ (hdone hinv.2 _ (tok_intro (markerItem e)))
  rw [← List.append_assoc] at h
  exact awaiting_marked h

/-- The posture that restricts nothing allows every declaration. -/
theorem unrestricted_check (declarations : Nat) (declared : Version) :
    (check unrestrictedPosture) declarations declared = none := by
  cases declared <;> simp [Parser.Script.Internal.VersionPosture.check,
      unrestrictedPosture] <;> decide

theorem cmdEnd_next {version next : BSmtLibSpec.Lexicon.Version} {c : Tree.Command}
    (h : cmdEnd version c = .next next) : c.modeAfter version = some (.read next) := by
  unfold cmdEnd at h
  split at h <;> simp_all

theorem cmdEnd_exit {version : BSmtLibSpec.Lexicon.Version} {c : Tree.Command}
    (h : cmdEnd version c = .exit) : c.modeAfter version = some .unparsed := by
  unfold cmdEnd at h
  split at h <;> simp_all

theorem cmdEnd_refused {version : BSmtLibSpec.Lexicon.Version} {c : Tree.Command}
    (h : cmdEnd version c = .refused) : c.modeAfter version = none := by
  unfold cmdEnd at h
  split at h <;> simp_all

theorem cmdEnd_ne_endOfInput {version : BSmtLibSpec.Lexicon.Version} {c : Tree.Command} :
    cmdEnd version c ≠ .endOfInput := by
  unfold cmdEnd
  split <;> simp

/-! ## The script parser's state -/

/-- What the script parser has taken, with the initial version `start`: the items `pre`, in the
parser's state, which it is in with the version `version`. Either it is in a command, or it has
taken `exit`, after which it waits for a command again. -/
def ScriptInv (start : BSmtLibSpec.Lexicon.Version) (pre : List Received) (version : Version)
    (parser : ScriptParser (List Event)) : Prop :=
  ScriptParser.Internal.posture parser = unrestrictedPosture ∧
  ((∃ done items, Chain start done (Bridge.version version) ∧
      pre = cmdToks done ++ items ∧ CmdInv (Bridge.version version) markers items
        (ScriptParser.Internal.command parser) ∧
      CmdInv (Bridge.version version) scriptFollows items (ScriptParser.Internal.command parser)) ∨
    (ScriptParser.Internal.command parser = .awaiting ∧
      ∃ done, Chain start done (Bridge.version version) ∧
      pre = cmdToks done ++ toks Tree.Command.exit.tokens))

/-- What follows a step of the script parser on an item, from what it has taken. -/
def ScriptPost (start : BSmtLibSpec.Lexicon.Version) (pre : List Received) (x : Received) :
    (Version × ScriptParser (List Event)) ⊕ Unit → Prop
  | .inl (version, parser) => ScriptInv start (pre ++ [x]) version parser
  | .inr () => ∃ commands, Takes start commands (pre ++ [x]) .finished

/-- A failure of a step of the script parser: no rejection of a version declaration, or one of a
declaration that names no supported version, whose `)` the item is. -/
def ScriptFailure (start : BSmtLibSpec.Lexicon.Version) (pre : List Received) (x : Received)
    (e : Parser.ParseErrorKind Unit) : Prop :=
  Benign e ∨ e = .version .unsupported ∧
    ∃ commands, Takes start commands (pre ++ [x]) (.failed .unsupportedVersion)

/-! ## A step of the script parser -/

theorem producerSetVersion_sound {Q : Parser.ParseErrorKind Unit → Prop}
    (version : BSmtLibSpec.Lexicon.Version) :
    Sound (fun r => r = .ok ()) Q
      (ExceptT.lift (recordingProducer.setVersion version).run :
        Quiet.RPM (Except Traversal.VersionRefused Unit)) :=
  ⟨fun _ _ _ h => (by cases h; rfl), fun _ _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩

/-- The items of a refused declaration completed: what a parser takes before it fails. -/
theorem refused_taken {start version : BSmtLibSpec.Lexicon.Version} {done : List Tree.Command}
    (hchain : Chain start done version) {items : List Received} {x : Received}
    {state : CommandState Nat Nat Nat Nat Nat Empty} (hm : CmdInv version markers items state)
    (hrefused : (∃ u, commandRem version markers state u) →
      ∀ w, markers .refused w → commandRem version markers state (x :: w)) :
    ∃ commands, Takes start commands (cmdToks done ++ items ++ [x])
      (.failed .unsupportedVersion) := by
  rcases cmdInv_done hm hrefused with ⟨h, -⟩ | ⟨c, hc, hitems, hend⟩
  · cases h
  · refine ⟨done ++ [c], ?_⟩
    rw [List.append_assoc, hitems]
    have := takes_of_chain hchain (Takes.refused hc (cmdEnd_refused hend))
    simpa using this

/-- Every step of the script parser, after an item's arrival, goes on in a state that says what
it has taken, or finishes the script, or fails: no rejection of a version declaration, or the
rejection of one that names no supported version at its `)`. -/
theorem afterProcessing_post {start : BSmtLibSpec.Lexicon.Version} {pre : List Received}
    {version : Version} {parser : ScriptParser (List Event)} {token : Parser.Internal.Input}
    {x : Received} (hinv : ScriptInv start pre version parser)
    (hitem : Bridge.received token = some x) (hlex : x.OfVersion (Bridge.version version))
    (hexit : AfterExit start pre → x = .endOfInput) :
    Sound (ScriptPost start pre x) (ScriptFailure start pre x)
      (afterProcessing recordingProducer version parser token) := by
  obtain ⟨posture, state, declarations⟩ := parser
  obtain ⟨hposture, hphase⟩ := hinv
  simp only [ScriptParser.Internal.posture, ScriptParser.Internal.command] at hposture hphase
  subst hposture
  rcases hphase with ⟨done, items, hchain, rfl, hm, hs⟩ | ⟨rfl, done, hchain, rfl⟩
  · unfold afterProcessing
    simp only [Parser.Internal.ParseByToken.step, ScriptParser.Internal.step, bind_assoc,
      ScriptParser.Internal.posture, ScriptParser.Internal.command,
      ScriptParser.Internal.declarations]
    have hcm := commandStep_advances version markers markers_nonempty state hitem hlex
    have hcs := commandStep_advances version scriptFollows scriptFollows_nonempty state hitem hlex
    refine Sound.bind ((hcm.and hcs).mono (fun r h => h) fun e ⟨hq, _⟩ => ?_)
      fun r ⟨hrm, hrs⟩ => ?_
    · rcases hq with hq | hq
      · exact Or.inl hq
      · obtain ⟨he, hq⟩ := hq hm.2
        exact Or.inr ⟨he, refused_taken hchain hm fun _ => hq⟩
    cases r with
    | more state' =>
      simp only [pure_bind]
      exact Sound.pure ⟨rfl, Or.inl ⟨done, items ++ [x], hchain, by simp, cmdInv_more hm hrm,
        cmdInv_more hs hrs⟩⟩
    | done outcome =>
      have hdone := cmdInv_done hm hrm
      cases outcome with
      | command =>
        rcases hdone with ⟨h, -⟩ | ⟨c, hc, hitems, hend⟩
        · cases h
        simp only [pure_bind]
        refine Sound.pure ⟨rfl, Or.inl ⟨done ++ [c], [], chain_snoc hchain hc (cmdEnd_next hend),
          ?_, cmdInv_awaiting _ _ markers_nonempty, cmdInv_awaiting _ _ scriptFollows_nonempty⟩⟩
        rw [List.append_assoc, hitems, cmdToks_append]
        simp [cmdToks]
      | setVersion declared =>
        rcases hdone with ⟨h, -⟩ | ⟨c, hc, hitems, hend⟩
        · cases h
        simp only [unrestricted_check, pure_bind]
        refine Sound.bind (producerSetVersion_sound _) fun r hr => ?_
        subst hr
        simp only [bind_assoc]
        refine Sound.bind Sound.lift fun _ _ => ?_
        refine Sound.pure ⟨rfl, Or.inl ⟨done ++ [c], [], chain_snoc hchain hc (cmdEnd_next hend),
          ?_, cmdInv_awaiting _ _ markers_nonempty, cmdInv_awaiting _ _ scriptFollows_nonempty⟩⟩
        rw [List.append_assoc, hitems, cmdToks_append]
        simp [cmdToks]
      | exit =>
        rcases hdone with ⟨h, -⟩ | ⟨c, hc, hitems, hend⟩
        · cases h
        obtain rfl := modeAfter_unparsed (cmdEnd_exit hend)
        simp only [pure_bind]
        refine Sound.bind Sound.lift fun _ _ => ?_
        exact Sound.pure ⟨rfl, Or.inr ⟨rfl, done, hchain, by rw [List.append_assoc, hitems]⟩⟩
      | endOfFile =>
        simp only [pure_bind]
        rcases hdone with ⟨-, hitems⟩ | ⟨c, -, -, hend⟩
        · refine Sound.pure ⟨done, ?_⟩
          rw [List.append_assoc, hitems]
          simpa using takes_of_chain hchain Takes.done
        · exact absurd hend cmdEnd_ne_endOfInput
  · -- after `exit`, the producer hands over the end of the input alone
    obtain rfl := hexit ⟨done, _, hchain, rfl⟩
    obtain rfl := Parser.Internal.Input.received_endOfInput hitem
    unfold afterProcessing
    simp only [Parser.Internal.ParseByToken.step, ScriptParser.Internal.step, commandStep,
        ScriptParser.Internal.posture, ScriptParser.Internal.command,
        ScriptParser.Internal.declarations,
        pure_bind]
    refine Sound.pure ⟨done ++ [.exit], ?_⟩
    rw [List.append_assoc]
    simpa using takes_of_chain hchain (Takes.stop (last := .exit) trivial rfl)

/-- The calls due at an item's arrival never fail. -/
theorem arrive_sound (parser : ScriptParser (List Event)) (token : Parser.Internal.Input) :
    Sound (fun _ => True) Benign (Parser.Internal.ParseByToken.arrive
        (H := List Event) parser token) := by
  constructor
  · intro _ _ _ _
    trivial
  · intro events e events' hrun
    rw [arrive_run] at hrun
    cases hrun
  · intro events e events' hrun
    rw [arrive_run] at hrun
    cases hrun

/-- Every step of the script parser on an item, from its arrival on. -/
theorem recAfter_post {start : BSmtLibSpec.Lexicon.Version} {pre : List Received}
    {version : Version} {parser : ScriptParser (List Event)} {token : Parser.Internal.Input}
    {x : Received} (hinv : ScriptInv start pre version parser)
    (hitem : Bridge.received token = some x) (hlex : x.OfVersion (Bridge.version version))
    (hexit : AfterExit start pre → x = .endOfInput) :
    RunSound (ScriptPost start pre x) (ScriptFailure start pre x)
      (recAfter version parser token) := by
  unfold recAfter afterToken
  refine RunSound.bind RunSound.lift fun _ _ => ?_
  refine RunSound.bind ((arrive_sound parser token).run.mono (fun _ h => h) fun _ h => Or.inl h)
    fun _ _ => ?_
  refine RunSound.bind RunSound.lift fun _ _ => ?_
  exact (afterProcessing_post hinv hitem hlex hexit).run

/-- A step of the script parser that rejects an item makes no call at it: the item's processing
is the last event of its run. -/
theorem recAfter_rejects_quiet {start : BSmtLibSpec.Lexicon.Version} {pre : List Received}
    {version : Version} {parser : ScriptParser (List Event)} {token : Parser.Internal.Input}
    {x : Received} (hinv : ScriptInv start pre version parser)
    (hitem : Bridge.received token = some x) (hlex : x.OfVersion (Bridge.version version))
    (hexit : AfterExit start pre → x = .endOfInput)
    {events events' : List Event} {e : Parser.ParseErrorKind Unit}
    (hrun : (recAfter version parser token).run.run events = (.error e, events'))
    (hb : Benign e) :
    events' = .process x :: (arrivalCalls parser token ++ .arrive x :: events) := by
  have h₁ : ((ExceptT.lift (arriveAt recordingPoints token) : Quiet.RPM Unit).run.run events) =
      (.ok (), .arrive x :: events) := by
    simp [arriveAt, hitem, recordingPoints, emit]; rfl
  have h₂ := arrive_run parser token (.arrive x :: events)
  have h₃ : ((ExceptT.lift (processAt recordingPoints token) : Quiet.RPM Unit).run.run
      (arrivalCalls parser token ++ .arrive x :: events)) =
      (.ok (), .process x :: (arrivalCalls parser token ++ .arrive x :: events)) := by
    simp [processAt, hitem, recordingPoints, emit]; rfl
  change ((afterToken recordingPoints recordingProducer version parser token).run.run events) =
    _ at hrun
  unfold afterToken at hrun
  rw [run_bind_ok h₁, run_bind_ok h₂, run_bind_ok h₃] at hrun
  exact (afterProcessing_post hinv hitem hlex hexit).quiet _ _ _ hrun hb

/-! ## Remainders are never empty -/

/-- No list of the set is empty. -/
def NoEmpty (A : Lang) : Prop := ∀ u, A u → u ≠ []

theorem noEmpty_cat {A B : Lang} (hB : NoEmpty B) : NoEmpty (cat A B) := by
  rintro _ ⟨a, b, -, hb, rfl⟩ h
  exact hB b hb (List.append_eq_nil_iff.mp h).2

theorem noEmpty_cat_left {A B : Lang} (hA : NoEmpty A) : NoEmpty (cat A B) := by
  rintro _ ⟨a, b, ha, -, rfl⟩ h
  exact hA a ha (List.append_eq_nil_iff.mp h).1

theorem noEmpty_tok (x : Received) : NoEmpty (tok x) := by
  rintro _ rfl h
  cases h

theorem noEmpty_closeNext (v : BSmtLibSpec.Lexicon.Version) (follows : CmdEnd → Lang) :
    NoEmpty (closeNext v follows) :=
  fun u hu h => by
    obtain ⟨_, _, rfl, _, rfl⟩ := hu
    cases h

theorem noEmpty_union {A B : Lang} (hA : NoEmpty A) (hB : NoEmpty B) : NoEmpty (union A B) :=
  fun u hu => hu.elim (hA u) (hB u)

theorem noEmpty_attrRem (v : BSmtLibSpec.Lexicon.Version) (need : Bool)
    (state : Parser.Category.Attribute.Internal.AttributeState Nat Nat) :
    NoEmpty (attrRem v true need state) := by
  have htail : NoEmpty (attrTail v true) := by
    simp only [attrTail, ite_true]
    exact noEmpty_tok _
  obtain ⟨mode, attributes⟩ := state
  cases mode with
  | start =>
    simp only [attrRem, ite_true]
    split
    · exact noEmpty_cat (noEmpty_tok _)
    · exact noEmpty_tok _
  | afterName => exact noEmpty_cat htail
  | inside _ _ sExpr outside =>
    have hrest : NoEmpty (valueRest v true) := noEmpty_cat (noEmpty_cat htail)
    simp only [attrRem]
    split
    · exact noEmpty_union (noEmpty_cat htail) (noEmpty_cat hrest)
    · exact noEmpty_cat hrest

/-- Each list of the set is some items, then what follows a command. -/
def EndsFollowed (follows : CmdEnd → Lang) (A : Lang) : Prop :=
  ∀ u, A u → ∃ a e w, a ≠ [] ∧ follows e w ∧ u = a ++ w

theorem endsFollowed_cat {follows : CmdEnd → Lang} {A B : Lang} (hB : EndsFollowed follows B) :
    EndsFollowed follows (cat A B) := by
  rintro _ ⟨a, b, -, hb, rfl⟩
  obtain ⟨c, e, w, hc, hw, rfl⟩ := hB b hb
  exact ⟨a ++ c, e, w, by simp [hc], hw, by simp⟩

theorem endsFollowed_closeNext (v : BSmtLibSpec.Lexicon.Version) (follows : CmdEnd → Lang) :
    EndsFollowed follows (closeNext v follows) := by
  rintro _ ⟨_, w, rfl, hw, rfl⟩
  exact ⟨[closeItem], _, w, by simp, hw, rfl⟩

/-- Every remainder of a command parser's state is some items, then what follows the command. -/
theorem commandRem_endsFollowed (v : BSmtLibSpec.Lexicon.Version) (follows : CmdEnd → Lang)
    (state : CommandState Nat Nat Nat Nat Nat Empty) :
    EndsFollowed follows (commandRem v follows state) := by
  have hc := endsFollowed_closeNext v follows
  have hcmd : ∀ (c : Tree.Command), toks c.tokens ≠ [] := fun c => by
    cases c <;> simp [Tree.Command.tokens, commandTokens, paren]
  cases state with
  | awaiting =>
    rintro u (⟨c, w, -, hw, rfl⟩ | ⟨_, w, rfl, hw, rfl⟩)
    · exact ⟨_, _, w, hcmd c, hw, rfl⟩
    · exact ⟨[.endOfInput], _, w, by simp, hw, rfl⟩
  | opened =>
    rintro u ⟨c, w, -, hw, heq⟩
    obtain ⟨inner, hinner⟩ : ∃ inner, toks c.tokens = openItem :: inner := by
      cases c <;> exact ⟨_, rfl⟩
    rw [hinner, List.cons_append, List.cons.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    refine ⟨inner, _, w, ?_, hw, rfl⟩
    rintro rfl
    have := congrArg List.length hinner
    cases c <;> simp [Tree.Command.tokens, commandTokens, paren] at this
  | payload payload =>
    cases payload <;> simp only [commandRem, payloadRem]
    case closing final =>
      split
      · rintro _ ⟨_, w, rfl, hw, rfl⟩
        exact ⟨[closeItem], _, w, by simp, hw, rfl⟩
      · exact hc
    case named command => cases command <;> exact endsFollowed_cat (by
      simp only [namedTail]
      repeat (first | exact hc | apply endsFollowed_cat))
    case declareDatatypesSorts state =>
      rintro u ⟨n, -, hu⟩
      exact endsFollowed_cat (endsFollowed_cat (endsFollowed_cat (endsFollowed_cat hc))) u hu
    case defineFunsRecDeclarations state =>
      rintro u ⟨n, -, hu⟩
      exact endsFollowed_cat (endsFollowed_cat (endsFollowed_cat (endsFollowed_cat hc))) u hu
    case setInfo declaration state =>
      rintro u ⟨-, a, b, ha, hb, rfl⟩
      exact ⟨a, _, b, noEmpty_attrRem v false state a ha, hb, rfl⟩
    case setOption state =>
      rintro u ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, _, b, noEmpty_attrRem v false state a ha, hb, rfl⟩
    all_goals repeat (first | exact hc | apply endsFollowed_cat)
  | nonstandard parser => nomatch parser

/-- No remainder of a command parser's state is empty. -/
theorem commandRem_noEmpty (v : BSmtLibSpec.Lexicon.Version) (follows : CmdEnd → Lang)
    (state : CommandState Nat Nat Nat Nat Nat Empty) : NoEmpty (commandRem v follows state) := by
  intro u hu h
  obtain ⟨a, e, w, ha, -, rfl⟩ := commandRem_endsFollowed v follows state u hu
  exact ha (List.append_eq_nil_iff.mp h).1

/-- A valid command, then what a parser takes as the command ends. -/
theorem takes_command {version : BSmtLibSpec.Lexicon.Version} {c : Tree.Command}
    (hc : c.Valid version) :
    ∃ tail ending, Takes version [c] (toks c.tokens ++ tail) ending := by
  cases hmode : c.modeAfter version with
  | none => exact ⟨[], _, by simpa using Takes.refused hc hmode⟩
  | some mode =>
    cases mode with
    | read next => exact ⟨_, _, Takes.command hc hmode Takes.done⟩
    | unparsed => exact ⟨_, _, Takes.stop hc hmode⟩

/-- What the script parser has taken is the start of what a parser takes for some commands, and
the version the parser is in is the one in force at the next item. -/
theorem scriptInv_witness {start : BSmtLibSpec.Lexicon.Version} {pre : List Received}
    {version : Version} {parser : ScriptParser (List Event)}
    (hinv : ScriptInv start pre version parser) :
    ∃ commands taken ending, Takes start commands taken ending ∧ pre.length < taken.length ∧
      taken.take pre.length = pre ∧
      versionAt start commands pre.length = Bridge.version version := by
  obtain ⟨posture, state, declarations⟩ := parser
  obtain ⟨-, hphase⟩ := hinv
  rcases hphase with ⟨done, items, hchain, rfl, hm, -⟩ | ⟨-, done, hchain, rfl⟩
  · obtain ⟨u, hu⟩ := hm.2
    obtain ⟨a, e, w, ha, hw, rfl⟩ := commandRem_endsFollowed _ _ state u hu
    cases hw
    have hall := hm.1 _ hu
    rw [← List.append_assoc] at hall
    rcases awaiting_marked hall with ⟨-, hitems⟩ | ⟨c, hc, hitems, -⟩
    · have hnil : items = [] := by
        cases items with
        | nil => rfl
        | cons y ys =>
          exfalso
          have hl := congrArg List.length hitems
          simp only [List.length_append, List.length_cons, List.length_nil] at hl
          have : a.length ≠ 0 := fun h => ha (List.length_eq_zero_iff.mp h)
          omega
      subst hnil
      refine ⟨done, cmdToks done ++ [.endOfInput], _,
        by simpa using takes_of_chain hchain Takes.done,
        by simp, by simp, ?_⟩
      have := versionAt_chain hchain [] 0
      simpa [versionAt] using this
    · obtain ⟨tail, ending, htakes⟩ := takes_command hc
      refine ⟨done ++ [c], cmdToks done ++ (toks c.tokens ++ tail), ending,
        takes_of_chain hchain htakes, ?_, ?_, ?_⟩
      · rw [← hitems]
        simp only [List.length_append]
        have : a.length ≠ 0 := fun h => ha (List.length_eq_zero_iff.mp h)
        omega
      · rw [← hitems, List.append_assoc, ← List.append_assoc (cmdToks done) items]
        exact List.take_left' rfl
      · rw [List.length_append, versionAt_chain hchain]
        simp only [versionAt]
        have : items.length < c.tokens.length := by
          have := congrArg List.length hitems
          simp only [List.length_append, toks, List.length_map] at this
          have : a.length ≠ 0 := fun h => ha (List.length_eq_zero_iff.mp h)
          omega
        simp [this]
  · refine ⟨done ++ [.exit], cmdToks done ++ (toks Tree.Command.exit.tokens ++ [.endOfInput]),
      _, takes_of_chain hchain (Takes.stop (last := .exit) trivial rfl), by simp, ?_, ?_⟩
    · rw [← List.append_assoc]
      exact List.take_left' (by simp)
    rw [List.length_append, versionAt_chain hchain]
    simp [versionAt, Tree.Command.tokens, commandTokens, paren, Tree.Command.declaredVersion]

/-! ## Runs of the script parser -/

/-- The script parser's recording run over items, with the state it is in where they run out. -/
def driveScript : Version → ScriptParser (List Event) → List Parser.Internal.Input →
    Quiet.RPM ((Version × ScriptParser (List Event)) ⊕ (Unit × List Parser.Internal.Input))
  | version, parser, [] => pure (.inl (version, parser))
  | version, parser, token :: tokens => do
    match ← recAfter version parser token with
    | .inl (version', parser') => driveScript version' parser' tokens
    | .inr () => pure (.inr ((), tokens))

/-- The driver's run is the run with the state forgotten. -/
theorem driveParse_eq_driveScript (version : Version) (parser : ScriptParser (List Event))
    (items : List Parser.Internal.Input) :
    driveParse recordingPoints recordingProducer version parser items =
      driveScript version parser items >>= fun r => match r with
        | .inl _ => pure none
        | .inr result => pure (some result) := by
  induction items generalizing version parser with
  | nil => simp [driveParse, driveScript]
  | cons token tokens ih =>
    rw [driveParse_cons]
    simp only [driveScript, bind_assoc]
    refine bind_ext fun r => ?_
    rcases r with ⟨version', parser'⟩ | u
    · simp [continueWith, ih]
    · simp [continueWith]

theorem driveScript_append (version : Version) (parser : ScriptParser (List Event))
    (items items' : List Parser.Internal.Input) :
    driveScript version parser (items ++ items') =
      driveScript version parser items >>= fun r => match r with
        | .inl (version', parser') => driveScript version' parser' items'
        | .inr (u, rest) => pure (.inr (u, rest ++ items')) := by
  induction items generalizing version parser with
  | nil => simp [driveScript]
  | cons token tokens ih =>
    simp only [List.cons_append, driveScript, bind_assoc]
    refine bind_ext fun r => ?_
    rcases r with ⟨version', parser'⟩ | u
    · simp [ih]
    · simp

theorem received_rcv {token : Parser.Internal.Input} (h : Bridge.received token ≠ none) :
    Bridge.received token = some (rcv token) := by
  unfold rcv
  cases hr : Bridge.received token with
  | none => exact absurd hr h
  | some r => rfl

/-- What a run of the script parser over items ends in: going on in a state that says what it
has taken, or finished at an item after which a script ends, with the items after it. -/
def RunPost (start : BSmtLibSpec.Lexicon.Version) (pre : List Received)
    (items : List Parser.Internal.Input) :
    (Version × ScriptParser (List Event)) ⊕ (Unit × List Parser.Internal.Input) → Prop
  | .inl (version, parser) => ScriptInv start (pre ++ items.map rcv) version parser
  | .inr (_, rest) => ∃ j commands, j < items.length ∧ rest = items.drop (j + 1) ∧
      Takes start commands (pre ++ (items.take (j + 1)).map rcv) .finished

/-- A failure of a run of the script parser over items: no rejection of a version declaration,
or the rejection of a declaration that names no supported version at its `)`. -/
def RunFailure (start : BSmtLibSpec.Lexicon.Version) (pre : List Received)
    (items : List Parser.Internal.Input)
    (e : Parser.ParseErrorKind Unit) : Prop :=
  Benign e ∨ e = .version .unsupported ∧ ∃ j commands, j < items.length ∧
    Takes start commands (pre ++ (items.take (j + 1)).map rcv) (.failed .unsupportedVersion)

/-- The script parser's run over items, from a state that says what it has taken, where no item
is whitespace or a comment, each item's reserved words are reserved by the version in force
there, as every reading of the items before it says, and every item after `exit` is the end of
the input: the run goes on in a state that says what it has taken, or finishes at an item after
which a script ends, or fails. It fails without rejecting a version declaration, or by rejecting
a declaration that names no supported version at an item after which a parser takes no more. -/
theorem script_runs (start : BSmtLibSpec.Lexicon.Version) :
    ∀ (items : List Parser.Internal.Input) (pre : List Received) (version : Version)
      (parser : ScriptParser (List Event)), ScriptInv start pre version parser →
    NoLayout items →
    (∀ j (hj : j < items.length), ∀ commands taken ending, Takes start commands taken ending →
      pre.length + j < taken.length →
      (pre ++ items.map rcv).take (pre.length + j) = taken.take (pre.length + j) →
      (rcv items[j]).OfVersion (versionAt start commands (pre.length + j))) →
    (∀ j (hj : j < items.length),
      AfterExit start ((pre ++ items.map rcv).take (pre.length + j)) →
      rcv items[j] = .endOfInput) →
    RunSound (RunPost start pre items) (RunFailure start pre items)
      (driveScript version parser items)
  | [], pre, version, parser, hinv, _, _, _ =>
    RunSound.pure (by simpa [RunPost] using hinv)
  | token :: tokens, pre, version, parser, hinv, hlayout, hlex, hexit => by
    -- after `exit`, the item is the end of the input
    have hexit₀ : AfterExit start pre → rcv token = .endOfInput := fun h =>
      hexit 0 (by simp) (by rw [Nat.add_zero, List.take_left' rfl]; exact h)
    have hitem := received_rcv (hlayout token (List.mem_cons_self ..))
    simp only [driveScript]
    -- the version the parser is in is the one in force at the item
    have hlex₀ : (rcv token).OfVersion (Bridge.version version) := by
      obtain ⟨cs, taken, e, htakes, hlen, htake, hver⟩ := scriptInv_witness hinv
      have := hlex 0 (by simp) cs taken e htakes (by simpa using hlen)
        (by rw [Nat.add_zero, List.take_left' rfl, htake])
      simpa [hver] using this
    have hshift : ∀ j, pre ++ [rcv token] ++ (tokens.take (j + 1)).map rcv =
        pre ++ ((token :: tokens).take (j + 1 + 1)).map rcv := fun j => by simp
    refine RunSound.bind
      ((recAfter_post hinv hitem hlex₀ hexit₀).mono (fun r h => h) fun e he => ?_)
      fun r hr => ?_
    · rcases he with he | ⟨he, cs, hcs⟩
      · exact Or.inl he
      · exact Or.inr ⟨he, 0, cs, by simp, by simpa using hcs⟩
    rcases r with ⟨version', parser'⟩ | u
    · have := script_runs start tokens (pre ++ [rcv token]) version' parser' hr
        (fun t ht => hlayout t (List.mem_cons_of_mem _ ht))
        (fun j hj cs taken e htakes hlen htake => by
          have := hlex (j + 1) (by simp; omega) cs taken e htakes (by simp at hlen ⊢; omega)
            (by simpa [Nat.add_assoc, Nat.add_comm 1] using htake)
          simpa [Nat.add_assoc, Nat.add_comm 1] using this)
        (fun j hj hafter => by
          have := hexit (j + 1) (by simp; omega)
            (by simpa [Nat.add_assoc, Nat.add_comm 1] using hafter)
          simpa using this)
      refine this.mono (fun r h => ?_) fun e he => ?_
      · rcases r with ⟨version'', parser''⟩ | ⟨u, rest⟩
        · simpa [RunPost] using h
        · obtain ⟨j, cs, hj, hrest, hcs⟩ := h
          exact ⟨j + 1, cs, by simp; omega, by simpa using hrest, by rw [← hshift]; exact hcs⟩
      · rcases he with he | ⟨he, j, cs, hj, hcs⟩
        · exact Or.inl he
        · exact Or.inr ⟨he, j + 1, cs, by simp; omega, by rw [← hshift]; exact hcs⟩
    · obtain ⟨cs, hcs⟩ := hr
      exact RunSound.pure ⟨0, cs, by simp, by simp, by simpa using hcs⟩

end BSmtLib.Facts.Proofs.Parser.Rejection.Script
