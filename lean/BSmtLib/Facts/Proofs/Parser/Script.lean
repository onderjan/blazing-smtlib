import BSmtLib.Facts.Proofs.Parser.Command

/-!
# The script parser against the traversal

The script parser runs the command parser on its commands; its proof takes the command
parser's lemma (`command_runs`) and composes it over a script.

- `script_embed`: the script parser steps as the command parser, with
  the command parser's calls due at a token's arrival, and goes on after each command as the
  command's outcome says (`scriptAfter`).
- `check_policyOf`, `switch_eq`: the posture's check of a version declaration is the policy's
  check of the spec, through `policyOf`; with the producer's and the handler's switches, it is
  the spec's `switchVersion`.
- `commands_runs`: by induction over `Script`, the script parser before a
  command reads what a parser receives for the commands, with the effects of the spec's
  `commands`; with the handler told the version first, the spec's `script` (`script_correct`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Script

open BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.File
open BSmtLib.Parser (Input PM Step Flow Parse)
open BSmtLib.Parser.Command (CommandOutcome CommandState commandStep)
open BSmtLib.Token (VersionPosture)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Command BSmtLib.Facts.Proofs.Parser.Drive
open BSmtLib.Facts.Proofs.Parser.Lemmas BSmtLib.Facts.Proofs.Parser.Tokens
open BSmtLib.Parser.Script.VersionPosture

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal

/-! ## Versions -/

theorem Bridge.version_injective {a b : Token.Version}
    (h : Bridge.version a = Bridge.version b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

@[simp]
theorem Bridge.version_libVersion (version : BSmtLibSpec.Lexicon.Version) :
    Bridge.version (Bridge.libVersion version) = version := by
  cases version <;> rfl

@[simp]
theorem Bridge.libVersion_version (version : Token.Version) :
    Bridge.libVersion (Bridge.version version) = version := by
  cases version <;> rfl

/- The library's version derives `BEq` only; its equality is the structural one. -/
instance : LawfulBEq Token.Version where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | cases h
  rfl {a} := by cases a <;> rfl

theorem mem_policyOf (posture : VersionPosture) (version : Token.Version) :
    Bridge.version version ∈ (policyOf posture).allowed ↔ posture.allowed.contains version := by
  rw [Array.contains_iff_mem]
  simp only [policyOf, List.mem_map, Array.mem_toList_iff]
  constructor
  · rintro ⟨allowed, hmem, heq⟩
    rwa [← Bridge.version_injective heq]
  · intro hmem
    exact ⟨version, hmem, rfl⟩

/-- The posture's check is the policy's, with the policy's errors as the parser's. -/
theorem check_policyOf (posture : VersionPosture) (declarations : Nat)
    (version : Token.Version) :
    (check posture) declarations version =
      match (policyOf posture).check declarations (Bridge.version version) with
      | .ok () => none
      | .error .unsupportedVersion => some .unsupportedVersion
      | .error (.tooManyDeclarations limit) => some (.tooManyVersionDeclarations limit) := by
  have hmem := mem_policyOf posture version
  rw [Array.contains_iff_mem] at hmem
  unfold Parser.Script.VersionPosture.check VersionPolicy.check
  simp only [policyOf] at hmem ⊢
  cases hmax : posture.maxDeclarations with
  | none =>
    by_cases hallowed : version ∈ posture.allowed <;> simp [hallowed, hmem]
  | some limit =>
    by_cases hlimit : limit ≤ declarations
    · simp [hlimit]
    · by_cases hallowed : version ∈ posture.allowed <;> simp [hlimit, hallowed, hmem]

/-! ## The script parser steps as the command parser -/

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.CommandHandler H m]
variable (points : Points (StateT H m)) (producer : Producer (StateT H m))
variable (posture : VersionPosture)

/-- The script parser under the posture, with the state of its command parser. -/
abbrev scriptAt (command : Parser.Command.CommandStateOf H) (declarations : Nat) :
    ScriptParser H :=
  { posture, command, declarations }

/--
What the script parser does after a command read in the version, over the tokens after it:
after a version declaration, the posture's check and the producer's and the handler's switches;
after `exit`, the discarding and the end of the input.
-/
def scriptAfter (version : Token.Version) (declarations : Nat) (rest : List Input) :
    CommandOutcome → PM H (Option (Unit × List Input))
  | .command =>
    driveParse points producer version
      (scriptAt (H := H) posture .awaiting declarations) rest
  | .setVersion declared =>
    match (check posture) declarations declared with
    | some kind => Parser.syntaxError kind
    | none => do
      match ← ExceptT.lift (producer.setVersion (Bridge.version declared)).run with
      | .error _ => throw (.syntax .unsupportedVersion)
      | .ok () => do
        ExceptT.lift (Traits.Handler.setVersion (H := H) declared)
        driveParse points producer declared
          (scriptAt (H := H) posture .awaiting (declarations + 1)) rest
  | .exit => do
    ExceptT.lift producer.discardRest
    driveParse points producer version (scriptAt (H := H) posture .awaiting declarations) rest
  | .endOfInput => pure (some ((), rest))

variable {points producer posture}

omit [LawfulMonad m] in
theorem arrive_scriptAt (command : Parser.Command.CommandStateOf H) (declarations : Nat)
    (token : Input) :
    Parse.arrive (scriptAt posture command declarations) token =
      Parser.Command.commandArrive command token := rfl

omit [LawfulMonad m] in
theorem step_commands (version : Token.Version) (command : Parser.Command.CommandStateOf H)
    (declarations : Nat) (token : Input) :
    Parse.step version (scriptAt posture command declarations) token =
      ScriptParser.step version (scriptAt posture command declarations)
        token := rfl

/--
The script parser runs as the command parser, with the command
parser's calls due at a token's arrival, and goes on after the command as its outcome says.
-/
theorem script_embed (version : Token.Version) (command : Parser.Command.CommandStateOf H)
    (declarations : Nat) (tokens : List Input) :
    driveParse points producer version (scriptAt posture command declarations)
        tokens =
      drive points (commandStep version) command tokens Parser.Command.commandArrive >>= fun
        | none => pure none
        | some (outcome, rest) => scriptAfter points producer posture version declarations rest
            outcome := by
  induction tokens generalizing command with
  | nil => simp [driveParse, drive_nil]
  | cons token tokens ih =>
    simp only [driveParse, drive_cons', arrivalTick, arrive_scriptAt, step_commands, resume,
      bind_assoc]
    congr 1; funext _
    congr 1; funext _
    congr 1; funext _
    simp only [ScriptParser.step, bind_assoc]
    congr 1; funext step
    cases step with
    | more state =>
      simp only [pure_bind]
      rw [ih state]
    | done outcome =>
      cases outcome with
      | command => simp [scriptAfter]
      | setVersion declared =>
        cases hck : (check posture) declarations declared <;>
          simp [scriptAfter, hck, Parser.syntaxError] <;> rfl
      | exit => simp [scriptAfter]
      | endOfInput => simp [scriptAfter]

end

/-! ## Commands of a script -/

/-- Only `exit` stops the reading. -/
theorem modeAfter_unparsed {version : BSmtLibSpec.Lexicon.Version} {command : Tree.Command}
    (h : command.modeAfter version = some .unparsed) : command = .exit := by
  cases command with
  | exit => rfl
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    by_cases hk : keyword = BSmtLibSpec.Regex.chars "smt-lib-version"
    · rcases value with _ | ((_ | d | _ | _ | _) | _ | _) <;>
        simp [Tree.Command.modeAfter, hk] at h
    · simp [Tree.Command.modeAfter, hk] at h
  | _ => cases h

/--
A command after which the script goes on in a version is not `exit`, and the version is the one
it declares, or the one it is read in if it declares none.
-/
theorem modeAfter_read {version next : BSmtLibSpec.Lexicon.Version} {command : Tree.Command}
    (h : command.modeAfter version = some (.read next)) :
    command ≠ .exit ∧ next = (command.declaredVersion.getD version) := by
  cases command with
  | exit => cases h
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    refine ⟨nofun, ?_⟩
    by_cases hk : keyword = BSmtLibSpec.Regex.chars "smt-lib-version"
    · rcases value with _ | ((_ | d | _ | _ | _) | _ | _) <;>
        simp [Tree.Command.modeAfter, Tree.Command.declaredVersion, hk] at h ⊢
      cases h' : versionOfNumber d <;> simp_all
    · rcases value with _ | ((_ | d | _ | _ | _) | _ | _) <;>
        simp [Tree.Command.modeAfter, Tree.Command.declaredVersion, hk] at h ⊢ <;>
        exact h.symm
  | _ =>
    refine ⟨nofun, ?_⟩
    simp only [Tree.Command.modeAfter, Option.some.injEq, Mode.read.injEq] at h
    simp [h, Tree.Command.declaredVersion]

/-- A command after which a script goes on is no declaration of a version that is not
supported. -/
theorem namesNoVersion_of_read {version next : BSmtLibSpec.Lexicon.Version} {command : Tree.Command}
    (h : command.modeAfter version = some (.read next)) : command.namesNoVersion = false := by
  cases command with
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    simp only [Tree.Command.modeAfter] at h
    simp only [Tree.Command.namesNoVersion]
    by_cases hk : keyword = BSmtLibSpec.Regex.chars "smt-lib-version"
    · simp only [hk, ite_true] at h
      simp only [hk]
      rcases value with _ | ((_ | decimal | _ | _ | _) | _ | _) <;> simp_all
      all_goals (cases hv : versionOfNumber decimal <;> simp_all)
    · simp [hk]
  | _ => rfl

theorem outcomeOf_of_ne_exit {command : Tree.Command} (hexit : command ≠ .exit) :
    outcomeOf command = match command.declaredVersion with
      | some version => .setVersion (Bridge.libVersion version)
      | none => .command := by
  cases command <;> first | exact absurd rfl hexit | rfl

theorem received_cons {command : Tree.Command} (hexit : command ≠ .exit)
    (commands : List Tree.Command) :
    received (command :: commands) = command.tokens.map .token ++ received commands := by
  cases command <;> first | exact absurd rfl hexit | rfl

section

variable {m : Type → Type} [Monad m] {ε : Type} {values : Values}
variable {points : Points m} {handler : Traversal.Handler m ε values}

theorem commands_cons (producer : Producer m) (policy : VersionPolicy) (declarations : Nat)
    {command : Tree.Command} (hexit : command ≠ .exit) (hn : command.namesNoVersion = false)
    (commandList : List Tree.Command) :
    Traversal.commands points handler producer policy declarations (command :: commandList) =
      Traversal.command points handler command >>= fun _ =>
        match command.declaredVersion with
        | none => Traversal.commands points handler producer policy declarations commandList
        | some version =>
          switchVersion handler producer policy declarations version >>= fun _ =>
            Traversal.commands points handler producer policy (declarations + 1) commandList := by
  cases command <;> first | exact absurd rfl hexit | rfl | (simp only [Traversal.commands, hn]; rfl)

end

/-! ## The switch to a declared version -/

section

variable {n : Type → Type} [Monad n] [LawfulMonad n]

/-- An adapted run that returns nothing, then a continuation, by the run's outcome. -/
theorem adapt_bind_eq {ε ε' β : Type} (f : ε → ε') (x : ExceptT ε n Unit)
    (k : ExceptT ε' n β) :
    (ExceptT.adapt f x >>= fun _ => k) = (do
      match ← ExceptT.lift x.run with
      | .error e => throw (f e)
      | .ok () => k) := by
  apply ExceptT.ext
  simp only [ExceptT.run_bind, ExceptT.run_adapt, ExceptT.run_lift, bind_map_left]
  congr 1
  funext result
  cases result <;> simp [Except.mapError, ExceptT.run_throw]

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.CommandHandler H m]
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

/--
The posture's check of a version declaration, the producer's switch and the handler's, as the
script parser makes them, are the spec's switch to the version under the policy of the posture.
-/
theorem switch_eq (hA : Agrees h) (producer : Producer (StateT H m)) (posture : VersionPosture)
    (declarations : Nat) (declared : Token.Version) {β : Type} (k : PM H β) :
    (match (check posture) declarations declared with
      | some kind => Parser.syntaxError kind
      | none => do
        match ← ExceptT.lift (producer.setVersion (Bridge.version declared)).run with
        | .error _ => throw (.syntax .unsupportedVersion)
        | .ok () => do
          ExceptT.lift (Traits.Handler.setVersion (H := H) declared)
          k) =
      (do
        adaptRun (switchVersion h producer (policyOf posture) declarations
          (Bridge.version declared))
        k) := by
  rw [check_policyOf, BSmtLibSpec.Facts.Proofs.Parser.Equations.switchVersion_eq]
  cases (policyOf posture).check declarations (Bridge.version declared) with
  | error error =>
    cases error <;> simp [adaptRun, Parser.syntaxError, causeOf]
  | ok u =>
    cases u
    simp only [adaptRun_bind, bind_assoc, adaptRun_lift, hA.setVersion]
    simp only [adaptRun, adapt_adapt]
    rw [adapt_bind_eq]
    congr 1
    funext result
    cases result <;> rfl

end

/-! ## The script -/

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.CommandHandler H m]
variable {points : Points (StateT H m)}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

theorem step_endOfInput (posture : VersionPosture) (version : Token.Version)
    (declarations : Nat) :
    Parse.step version (scriptAt (H := H) posture .awaiting declarations) .endOfInput =
      pure (.done ()) := by
  simp [Parse.step, ScriptParser.step, commandStep]

/-- Tokens whose spec items are one item stand for it. -/
theorem map_received_split {inputs : List Input} {items : List Received}
    {tokens : List BSmtLibSpec.Grammar.SyntaxToken}
    (hs : inputs.map Bridge.received = (tokens.map Received.token ++ items).map some) :
    ∃ first second, inputs = first ++ second ∧ Stands first tokens ∧
      second.map Bridge.received = items.map some := by
  rw [List.map_append] at hs
  obtain ⟨first, second, rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp hs
  exact ⟨first, second, rfl, by simpa [Stands, Function.comp_def] using h₁, h₂⟩

theorem map_received_endOfInput {inputs : List Input}
    (hs : inputs.map Bridge.received = [Received.endOfInput].map some) :
    inputs = [.endOfInput] := by
  match inputs, hs with
  | [token], hs =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hs
    rw [Input.received_endOfInput hs]
  | [], hs => simp at hs
  | _ :: _ :: _, hs => simp at hs

/--
The script parser under the posture before a command, over what a parser receives for the
commands of a script and any rest: the spec's commands under the policy of the posture.
-/
theorem commands_runs (hA : Agrees h) (producer : Producer (StateT H m))
    (posture : VersionPosture) {start : BSmtLibSpec.Lexicon.Version} {commands : List Tree.Command}
    (hscript : Script start commands) :
    ∀ (version : Token.Version), Bridge.version version = start →
    ∀ (declarations : Nat) {inputs : List Input},
    inputs.map Bridge.received = (received commands).map some → ∀ rest : List Input,
    driveParse points producer version
        (scriptAt (H := H) posture .awaiting declarations) (inputs ++ rest) =
      (do
        adaptRun (Traversal.commands points h producer (policyOf posture) declarations commands)
        pure (some ((), rest))) := by
  induction hscript with
  | done =>
    intro version _ declarations inputs hs rest
    rw [map_received_endOfInput hs, List.singleton_append, script_embed]
    simp [drive_cons', arrivalTick, Parser.Command.commandArrive, commandStep, scriptAfter,
      Traversal.commands, receive, arriveAt, processAt, Bridge.received]
  | stop hvalid hmode =>
    rename_i command
    intro version hversion declarations inputs hs rest
    subst hversion
    obtain rfl := modeAfter_unparsed hmode
    obtain ⟨first, second, rfl, hfirst, hsecond⟩ := map_received_split hs
    rw [map_received_endOfInput hsecond, List.append_assoc, List.singleton_append, script_embed,
      command_runs hA _ hvalid (by simp [hmode]) hfirst]
    simp [outcomeOf, scriptAfter, driveParse, step_endOfInput, Parser.Parse.arrive,
      Parser.Command.commandArrive,
      Parser.Script.ScriptParser.arrive,
      Traversal.commands, receive, arriveAt, processAt, Bridge.received]
  | @command next _ _ command hvalid hmode _ ih =>
    intro version hversion declarations inputs hs rest
    subst hversion
    obtain ⟨hexit, hnext⟩ := modeAfter_read hmode
    rw [received_cons hexit] at hs
    obtain ⟨first, second, rfl, hfirst, hsecond⟩ := map_received_split hs
    rw [List.append_assoc, script_embed, command_runs hA _ hvalid (by simp [hmode]) hfirst,
      commands_cons _ _ _ hexit (namesNoVersion_of_read hmode),
      adaptRun_bind, outcomeOf_of_ne_exit hexit]
    simp only [pure_bind, bind_assoc]
    congr 1
    funext _
    cases hdeclared : command.declaredVersion with
    | none =>
      simp only [hdeclared, Option.getD_none] at hnext
      subst next
      exact ih version rfl declarations hsecond rest
    | some declared =>
      simp only [hdeclared, Option.getD_some] at hnext
      subst next
      have hswitch := switch_eq hA producer posture declarations (Bridge.libVersion declared)
        (driveParse points producer (Bridge.libVersion declared)
          (scriptAt (H := H) posture .awaiting (declarations + 1))
          (second ++ rest))
      rw [Bridge.version_libVersion] at hswitch
      simp only [scriptAfter, Bridge.version_libVersion]
      rw [hswitch, adaptRun_bind, bind_assoc]
      congr 1
      funext _
      exact ih (Bridge.libVersion declared) (by simp) (declarations + 1) hsecond rest

end

section

variable {H : Type} {m : Type → Type} [Monad m]

/--
The script parser under a posture, from its start, over what a parser receives for a script read
from the version and any rest, with the handler told the version first as the parse adapter
does, is the spec's script under the policy of the posture, and finishes before the rest.
-/
theorem script_correct [Traits.CommandHandler H m] [LawfulMonad m] {points : Points (StateT H m)}
    {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)} (hA : Agrees h)
    (producer : Producer (StateT H m)) (posture : Token.VersionPosture)
    {version : Token.Version} {commands : List Tree.Command}
    (hscript : Script (Bridge.version version) commands) {inputs : List Parser.Input}
    (hs : inputs.map Bridge.received = (BSmtLibSpec.Parser.Properties.received commands).map some)
    (rest : List Parser.Input) :
    driveInput points producer version (Parser.Script.ScriptParser.new (H := H) posture)
        (inputs ++ rest) =
      (do adaptRun (Traversal.script points h producer (policyOf posture) (Bridge.version version)
            commands)
          pure (some ((), rest))) := by
  simp only [driveInput, Traversal.script, adaptRun_bind, adaptRun_lift, bind_assoc,
    hA.setVersion]
  congr 1
  funext _
  exact commands_runs hA producer posture hscript version rfl 0 hs rest

end

end BSmtLib.Facts.Proofs.Parser.Script
