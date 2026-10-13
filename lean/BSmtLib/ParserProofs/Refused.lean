import BSmtLib.ParserProofs.Script

/-!
# A declaration of a version that is not supported, against the traversal

A `set-info` of `:smt-lib-version` whose value names no supported version is a valid command
that ends no script: the traversal takes it as `set-info`, then fails with `unsupportedVersion`.
The command parser takes it alike: it follows its tokens with the tracker of a version
declaration, which is `.keyword` after the keyword and `.value none` from the next token on,
and at the `)`, after `set-info`, it fails.
-/

namespace BSmtLib.ParserProofs

open BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLib.Parser (Input PM Step Payload CommandOutcome FinalCall payloadStep commandStep
  AttributeState AttributeMode attributeStep Declaration CommandState)
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.SpecChecks.Parser (Program.callUnit)

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Parser.CommandHandler H m]
variable {points : Points (StateT H m)} {version : BSmtLib.Version}
variable {h : Traversal.Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H)}

/-- Two states that step alike after two first tokens that only move them read alike. -/
theorem Runs.second {σ ρ α : Type} {step : σ → Input → PM H (Step σ ρ)}
    {state state' next next' : σ}
    {first second : Input} {tokens : List Input} {program : PM H α}
    {k : α → PM H (Step σ ρ)} {arrival : σ → Input → PM H Unit}
    (h₁ : step state first = pure (.more next)) (h₁' : step state' first = pure (.more next'))
    (h₂ : step next second = step next' second)
    (h : Runs points step state' (first :: second :: tokens) program k arrival)
    (harr₁ : arrival state first = arrival state' first := by intros; rfl)
    (harr₂ : arrival next second = arrival next' second := by intros; rfl) :
    Runs points step state (first :: second :: tokens) program k arrival := by
  intro rest
  have := h rest
  simp only [List.cons_append, drive_cons', arrivalTick, h₁, h₁', resume_more, harr₁, harr₂]
    at this ⊢
  rw [h₂]
  exact this

/-- A value that names no supported version. -/
def NamesNoVersion (value : Option Tree.AttributeValue) : Prop :=
  ∀ decimal, value = some (.constant (.decimal decimal)) → versionOfNumber decimal = none

/-- After the keyword `:smt-lib-version`, a token that is no supported version's number. -/
theorem keyword_next {token : Input} {first : BSmtLibSpec.Grammar.SyntaxToken}
    (hfirst : ∀ text, first = .decimal text → versionOfNumber text = none)
    (htoken : Bridge.received token = some (.token first)) :
    Declaration.next .keyword token = .value none := by
  cases token with
  | constant c =>
    cases c with
    | decimal text =>
      have hd : first = .decimal (Bridge.chars text.asSlice) := by
        simpa [Bridge.received, Bridge.constant, Tree.SpecConstant.token] using htoken.symm
      simp only [Declaration.next, fromDecimal_eq, hfirst _ hd, Option.map_none]
    | _ => rfl
  | _ => rfl

variable (hA : Agrees h)
include hA

/-- A `set-info` of `:smt-lib-version` whose value names no supported version: `set-info` at its
`)`, then the failure. -/
theorem setInfo_payload_refused (value : Option Tree.AttributeValue) (hvalue : NamesNoVersion value)
    (hvalid : (⟨BSmtLibSpec.Regex.chars "smt-lib-version", value⟩ : Tree.Attribute).Valid
      (Bridge.version version))
    {payload : List Input}
    (hs : Stands payload (Tree.Attribute.tokens ⟨BSmtLibSpec.Regex.chars "smt-lib-version", value⟩)) :
    PayloadRuns points version (Payload.init .setInfo version)
      (payload ++ [.parenClose])
      (adaptRun (do
        take points (.keyword (BSmtLibSpec.Regex.chars "smt-lib-version"))
        let handled ← attributeThen points h (BSmtLibSpec.Regex.chars "smt-lib-version") .parenClose
          value
        Program.callUnit h (.commandSetInfo handled)))
      fun _ => Parser.syntaxError .unsupportedVersion := by
  have hruns := attributeSingle_runs (points := points) hA.toTermAgrees _ value hvalid
    (Stands.append hs (Stands.cons (token := .parenClose) rfl Stands.nil))
  have hembed := Runs.bind_next ((Runs.embedA (outer := payloadStep version)
      (outerArrival := Parser.payloadArrive)
    (Payload.setInfo (.value none))
    (fun attributes => do
      let some info := attributes[0]? | Parser.syntaxError .expectedAttribute
      Parser.call (Parser.CommandHandler.commandSetInfo info)
      Parser.syntaxError .unsupportedVersion)
    (by
      intro state token
      simp only [payloadStep]
      congr 1
      funext step
      cases step with
      | more => rfl
      | done r =>
        simp only [Step.wrap, Declaration.next]
        cases r[0]? <;> rfl) hruns).congr rfl
    (next' := fun r => Parser.call (Parser.CommandHandler.commandSetInfo r) >>=
      fun _ => Parser.syntaxError .unsupportedVersion)
    (by funext; simp [Step.wrap]))
  -- the keyword, then the token after it: the value's first, or the `)`
  obtain ⟨keywordToken, second, others, first, hpayload, hkeywordToken, hsecond, hfirst⟩ :
      ∃ keywordToken second others first,
        payload ++ [.parenClose] = keywordToken :: second :: others ∧
        Bridge.received keywordToken =
          some (.token (.keyword (BSmtLibSpec.Regex.chars "smt-lib-version"))) ∧
        Bridge.received second = some (.token first) ∧
        ∀ text, first = .decimal text → versionOfNumber text = none := by
    cases value with
    | none =>
      obtain ⟨keywordToken, rfl, hk⟩ := Stands.split_single hs
      exact ⟨keywordToken, .parenClose, [], .parenClose, rfl, hk, rfl, fun _ h => by cases h⟩
    | some value =>
      obtain ⟨keywordToken, rest, rfl, hk, hrest⟩ := Stands.split_cons hs
      obtain ⟨first, tokens, htokens⟩ : ∃ first tokens, value.tokens = first :: tokens := by
        rcases value with _ | _ | _ <;> exact ⟨_, _, rfl⟩
      rw [htokens] at hrest
      obtain ⟨second, others, rfl, hsecond, -⟩ := Stands.split_cons hrest
      refine ⟨keywordToken, second, others ++ [.parenClose], first, rfl, hk, hsecond, ?_⟩
      intro text htext
      subst htext
      apply hvalue
      rcases value with ⟨_ | _ | _ | _ | _⟩ | _ | _ <;>
        simp_all [Tree.AttributeValue.tokens, Tree.SpecConstant.token, paren]
  obtain ⟨keyword, rfl, hkeyword⟩ := Input.received_keyword hkeywordToken
  have hversionKeyword : Parser.isVersionKeyword keyword = true := by
    rw [isVersionKeyword_eq, hkeyword]
    exact decide_eq_true rfl
  have hnext := keyword_next hfirst hsecond
  rw [hpayload]
  rw [hpayload] at hembed
  refine (Runs.second
    (next := Payload.setInfo .keyword { mode := .afterName keyword, attributes := #[] })
    (next' := Payload.setInfo (.value none) { mode := .afterName keyword, attributes := #[] })
    (by simp [payloadStep, Payload.init, Declaration.next, hversionKeyword, attributeStep,
      AttributeState.init])
    (by simp [payloadStep, Declaration.next, attributeStep, AttributeState.init])
    (by simp only [payloadStep, hnext]; rfl) hembed).congr ?_ rfl
  simp [hA.commandSetInfo]

end

/-! ## The command -/

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Parser.CommandHandler H m]
variable {points : Points (StateT H m)} {version : BSmtLib.Version}
variable {h : Traversal.Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H)}

/-- The frame of a command whose payload parser fails at its end (see `command_frame`). -/
theorem command_frame_throw {name : CommandNameReserved} {s : String}
    (hname : Bridge.reserved (.commandName name) = BSmtLibSpec.Regex.chars s)
    {payload : List Input} {program : PM H Unit}
    {e : Parser.ParseErrorCause (Parser.Handler.Error H)}
    (hruns : PayloadRuns points version (Payload.init name version) payload program
      fun _ => throw e)
    (rest : List Input) :
    drive points (commandStep version) .awaiting
        (.parenOpen :: .reserved (.commandName name) :: (payload ++ rest)) Parser.commandArrive =
      (do
        adaptRun (opening points s)
        program
        (throw e : PM H (Option (CommandOutcome × List Input)))) := by
  have hembed := drive_embedA (points := points) (inner := payloadStep version)
    (outer := commandStep version) CommandState.payload (fun outcome => pure (.done outcome))
    commandStep_payload commandArrive_payload (Payload.init name version) (payload ++ rest)
  simp only [drive_cons', arrivalTick, Parser.commandArrive, commandStep, resume_more, hembed,
    hruns rest]
  simp [opening, adaptRun_take (token := .reserved (.commandName name))
    (syntaxToken := word s) (by simp [Bridge.received, hname, word]),
    adaptRun_take (token := .parenOpen) rfl, tick, arriveAt, processAt, Bridge.received, resume]

/-- A command that names no supported version: the parser reads it as the traversal does, then
fails. -/
theorem command_runs_refused (hA : Agrees h) (command : Tree.Command)
    (hvalid : command.Valid (Bridge.version version))
    (hmode : command.modeAfter (Bridge.version version) = none) {tokens : List Input}
    (hs : Stands tokens command.tokens) (rest : List Input) :
    drive points (commandStep version) .awaiting (tokens ++ rest) Parser.commandArrive =
      (do
        adaptRun (Traversal.command points h command)
        (throw (.syntax .unsupportedVersion) : PM H (Option (CommandOutcome × List Input)))) := by
  obtain ⟨value, rfl, hvalue⟩ : ∃ value, command = .setInfo ⟨BSmtLibSpec.Regex.chars "smt-lib-version",
      value⟩ ∧ NamesNoVersion value := by
    cases command with
    | setInfo info =>
      obtain ⟨keyword, value⟩ := info
      simp only [Tree.Command.modeAfter] at hmode
      by_cases hk : keyword = BSmtLibSpec.Regex.chars "smt-lib-version"
      · subst hk
        refine ⟨value, rfl, fun decimal hv => ?_⟩
        subst hv
        simpa using hmode
      · simp [hk] at hmode
    | _ => simp [Tree.Command.modeAfter] at hmode
  have htokens : (Tree.Command.setInfo ⟨BSmtLibSpec.Regex.chars "smt-lib-version", value⟩).tokens =
      commandTokens "set-info" (Tree.Attribute.tokens ⟨BSmtLibSpec.Regex.chars "smt-lib-version",
        value⟩) := rfl
  rw [htokens] at hs
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
  obtain ⟨nameToken, payload, rfl, hnameToken, hpayloadTokens⟩ := Stands.split_cons hinner
  have hname : Bridge.reserved (.commandName .setInfo) = BSmtLibSpec.Regex.chars "set-info" := rfl
  rw [Input.received_commandName hname hnameToken, SpecChecks.Parser.command_setInfo, adaptRun_bind]
  have := command_frame_throw (points := points) hname
    (setInfo_payload_refused hA value hvalue hvalid hpayloadTokens) rest
  simp only [List.cons_append, List.append_assoc] at this ⊢
  rw [this]
  simp

end

/-! ## Commands up to a declaration that names no supported version -/

/-- A declaration that names no supported version ends the traversal's commands with the
failure. -/
theorem commands_refused {m : Type → Type} [Monad m] {ε : Type} {values : Values}
    {points : Points m} {handler : Traversal.Handler m ε values}
    (producer : Producer m) (policy : VersionPolicy)
    (declarations : Nat) {version : BSmtLibSpec.Lexicon.Version} {command : Tree.Command}
    (hmode : command.modeAfter version = none) (rest : List Tree.Command) :
    Traversal.commands points handler producer policy declarations (command :: rest) =
      (Traversal.command points handler command >>= fun _ =>
        throw (.syntax .unsupportedVersion)) := by
  cases command with
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    simp only [Tree.Command.modeAfter] at hmode
    by_cases hk : keyword = BSmtLibSpec.Regex.chars "smt-lib-version"
    · subst hk
      have hd : (Tree.Command.setInfo ⟨BSmtLibSpec.Regex.chars "smt-lib-version", value⟩).declaredVersion
          = none := by
        rcases value with _ | ⟨⟨_ | decimal | _ | _ | _⟩ | _ | _⟩ <;>
          simp_all [Tree.Command.declaredVersion]
      have hn : (Tree.Command.setInfo ⟨BSmtLibSpec.Regex.chars "smt-lib-version", value⟩).namesNoVersion
          = true := by
        rcases value with _ | ⟨⟨_ | decimal | _ | _ | _⟩ | _ | _⟩ <;>
          simp_all [Tree.Command.namesNoVersion]
      simp only [Traversal.commands, hd, hn, ite_true]
    · simp [hk] at hmode
  | _ => simp [Tree.Command.modeAfter] at hmode

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Parser.CommandHandler H m]
variable {points : Points (StateT H m)}
variable {h : Traversal.Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H)}

/--
The script parser under the posture before a command, over what a parser takes for commands and
any rest: the spec's commands under the policy of the posture. Where a declaration that names no
supported version ends the commands, both fail after it.
-/
theorem takes_runs (hA : Agrees h) (producer : Producer (StateT H m))
    (posture : Parser.VersionPosture) {start : BSmtLibSpec.Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes start commands taken ending) :
    ∀ (version : BSmtLib.Version), Bridge.version version = start →
    ∀ (declarations : Nat) {inputs : List Input},
    inputs.map Bridge.received = taken.map some → ∀ rest : List Input,
    driveParse points producer version
        (scriptAt (H := H) posture .awaiting declarations) (inputs ++ rest) =
      (do
        adaptRun (Traversal.commands points h producer (policyOf posture) declarations commands)
        pure (some ((), rest))) := by
  induction htakes with
  | done =>
    intro version _ declarations inputs hs rest
    rw [map_received_endOfInput hs, List.singleton_append, script_embed]
    simp [drive_cons', arrivalTick, Parser.commandArrive, commandStep, scriptAfter,
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
      Parser.commandArrive,
      Parser.ScriptParser.arrive,
      Traversal.commands, receive, arriveAt, processAt, Bridge.received]
  | @command _ next _ _ _ command hvalid hmode _ ih =>
    intro version hversion declarations inputs hs rest
    subst hversion
    obtain ⟨hexit, hnext⟩ := modeAfter_read hmode
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
  | @refused _ last hvalid hmode =>
    intro version hversion declarations inputs hs rest
    subst hversion
    have hs' : Stands inputs last.tokens := by simpa [Stands, Function.comp_def] using hs
    rw [script_embed, command_runs_refused hA _ hvalid hmode hs' rest,
      commands_refused _ _ _ hmode, adaptRun_bind]
    simp [adaptRun, causeOf]

end

end BSmtLib.ParserProofs
