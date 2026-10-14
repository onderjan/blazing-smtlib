import BSmtLib.Facts.Proofs.Parser.Commands.Attributes

/-!
# The command parser against the traversal

From before a command, over the tokens of any command valid in the parser's version whose mode
the calls due at a token's arrival between that token's arrival and its processing, and
the calls due at the first token's arrival between that token's arrival and its processing, and
ends with the command's outcome. A version declaration is a `set-info` that ends with the
version it declares: the command parser switches nothing, as the traversal's command does not.
-/

namespace BSmtLib.Facts.Proofs.Parser.Command

open BSmtLibSpec.Grammar
open BSmtLib.Parser
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser.Equations
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Commands.Attributes
open BSmtLib.Facts.Proofs.Parser.Commands.Declarations BSmtLib.Facts.Proofs.Parser.Commands.Frame
open BSmtLib.Facts.Proofs.Parser.Commands.FunsRec BSmtLib.Facts.Proofs.Parser.Commands.Literals
open BSmtLib.Facts.Proofs.Parser.Commands.Simple BSmtLib.Facts.Proofs.Parser.Commands.Terms
open BSmtLib.Parser.Command BSmtLib.Parser.Command.Standard

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.CommandHandler H m]
variable {points : Points (StateT H m)} {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

/--
From before a command, the command parser reads the tokens of a command with the traversal's
effects, the calls due at a token's arrival made at that arrival, and ends with the
command's outcome.
-/
theorem command_runs (hA : Agrees h) (command : Tree.Command)
    (hvalid : command.Valid (Bridge.version version))
    (hmode : command.modeAfter (Bridge.version version) ≠ none) {tokens : List Input}
    (hs : Stands tokens command.tokens) (rest : List Input) :
    drive points (commandStep version) .awaiting (tokens ++ rest) Command.commandArrive =
      (do
        adaptRun (Traversal.command points h command)
        pure (some (outcomeOf command, rest))) := by
  cases command with
  | assert asserted =>
    exact command_of_payload _ (name := .assert) rfl rfl (command_assert _)
      (fun hp => assert_payload hA asserted hvalid hp) hs rest
  | checkSat =>
    exact command_of_payload _ (name := .checkSat) rfl rfl (command_checkSat)
      (fun hp => nullary_payload .checkSat (by simp [finalCall, hA.commandCheckSat]) rfl hp)
      hs rest
  | checkSatAssuming assumptions =>
    exact command_of_payload _ (name := .checkSatAssuming) rfl rfl
      (command_checkSatAssuming _)
      (fun hp => checkSatAssuming_payload hA assumptions hvalid.1 hvalid.2 hp) hs rest
  | checkSatAssumingLiterals literals =>
    exact command_of_payload _ (name := .checkSatAssuming) rfl rfl
      (command_checkSatAssumingLiterals _)
      (fun hp => checkSatAssumingLiterals_payload hA literals hvalid.2.1 hvalid.2.2 hp) hs rest
  | declareConst name sort =>
    exact command_of_payload _ (name := .declareConst) rfl rfl
      (command_declareConst _ _)
      (fun hp => declareConst_payload hA name sort hvalid.2 hp) hs rest
  | declareDatatype name declaration =>
    exact command_of_payload _ (name := .declareDatatype) rfl rfl
      (command_declareDatatype _ _)
      (fun hp => declareDatatype_payload hA name declaration hvalid.2 hp) hs rest
  | declareDatatypes sortDecs declarations =>
    exact command_of_payload _ (name := .declareDatatypes) rfl rfl
      (command_declareDatatypes _ _)
      (fun hp => declareDatatypes_payload hA sortDecs declarations hvalid.2.1 hvalid.2.2.1
        hvalid.2.2.2 hp) hs rest
  | declareFun name parameters result =>
    exact command_of_payload _ (name := .declareFun) rfl rfl
      (command_declareFun _ _ _)
      (fun hp => declareFun_payload hA name parameters result hvalid.1 hvalid.2 hp) hs rest
  | declareSort name arity =>
    exact command_of_payload _ (name := .declareSort) rfl rfl
      (command_declareSort _ _) (fun hp => declareSort_payload hA name arity hp) hs rest
  | declareSortParameter name =>
    exact command_of_payload _ (name := .declareSortParameter) rfl rfl
      (command_declareSortParameter _)
      (fun hp => declareSortParameter_payload hA name hp) hs rest
  | defineConst name sort body =>
    exact command_of_payload _ (name := .defineConst) rfl rfl
      (command_defineConst _ _ _)
      (fun hp => defineConst_payload hA name sort body hvalid.2.1 hvalid.2.2 hp) hs rest
  | defineFun definition =>
    obtain ⟨name, parameters, result, body⟩ := definition
    exact command_of_payload _ (name := .defineFun) rfl rfl
      (command_defineFun _ _ _ _)
      (fun hp => defineFun_payload hA ⟨name, parameters, result, body⟩ hvalid hp) hs rest
  | defineFunRec definition =>
    obtain ⟨name, parameters, result, body⟩ := definition
    exact command_of_payload _ (name := .defineFunRec) rfl rfl
      (command_defineFunRec _ _ _ _)
      (fun hp => defineFunRec_payload hA ⟨name, parameters, result, body⟩ hvalid.2 hp) hs rest
  | defineFunsRec declarations bodies =>
    exact command_of_payload _ (name := .defineFunsRec) rfl rfl
      (command_defineFunsRec _ _)
      (fun hp => defineFunsRec_payload hA declarations bodies hvalid.2.1 hvalid.2.2.1
        hvalid.2.2.2.1 hvalid.2.2.2.2 hp) hs rest
  | defineSort name parameters sort =>
    exact command_of_payload _ (name := .defineSort) rfl rfl
      (command_defineSort _ _ _)
      (fun hp => defineSort_payload hA name parameters sort hvalid hp) hs rest
  | echo content =>
    exact command_of_payload _ (name := .echo) rfl rfl (command_echo _)
      (fun hp => echo_payload hA content hp) hs rest
  | exit =>
    exact command_of_payload _ (name := .exit) rfl rfl (command_exit)
      (fun hp => nullary_payload .exit (by simp [finalCall, hA.commandExit]) rfl hp) hs rest
  | getAssertions =>
    exact command_of_payload _ (name := .getAssertions) rfl rfl
      (command_getAssertions)
      (fun hp => nullary_payload .getAssertions (by simp [finalCall, hA.commandGetAssertions])
        rfl hp) hs rest
  | getAssignment =>
    exact command_of_payload _ (name := .getAssignment) rfl rfl
      (command_getAssignment)
      (fun hp => nullary_payload .getAssignment (by simp [finalCall, hA.commandGetAssignment])
        rfl hp) hs rest
  | getInfo flag =>
    exact command_of_payload _ (name := .getInfo) rfl rfl (command_getInfo _)
      (fun hp => getInfo_payload hA flag hp) hs rest
  | getModel =>
    exact command_of_payload _ (name := .getModel) rfl rfl (command_getModel)
      (fun hp => nullary_payload .getModel (by simp [finalCall, hA.commandGetModel]) rfl hp)
      hs rest
  | getOption keyword =>
    exact command_of_payload _ (name := .getOption) rfl rfl
      (command_getOption _) (fun hp => getOption_payload hA keyword hp) hs rest
  | getProof =>
    exact command_of_payload _ (name := .getProof) rfl rfl (command_getProof)
      (fun hp => nullary_payload .getProof (by simp [finalCall, hA.commandGetProof]) rfl hp)
      hs rest
  | getUnsatAssumptions =>
    exact command_of_payload _ (name := .getUnsatAssumptions) rfl rfl
      (command_getUnsatAssumptions)
      (fun hp => nullary_payload .getUnsatAssumptions
        (by simp [finalCall, hA.commandGetUnsatAssumptions]) rfl hp) hs rest
  | getUnsatCore =>
    exact command_of_payload _ (name := .getUnsatCore) rfl rfl
      (command_getUnsatCore)
      (fun hp => nullary_payload .getUnsatCore (by simp [finalCall, hA.commandGetUnsatCore])
        rfl hp) hs rest
  | getValue valueTerms =>
    exact command_of_payload _ (name := .getValue) rfl rfl
      (command_getValue _)
      (fun hp => getValue_payload hA valueTerms hvalid.1 hvalid.2 hp) hs rest
  | pop count =>
    exact command_of_payload _ (name := .pop) rfl rfl (command_pop _)
      (fun hp => pop_payload hA count hp) hs rest
  | push count =>
    exact command_of_payload _ (name := .push) rfl rfl (command_push _)
      (fun hp => push_payload hA count hp) hs rest
  | reset =>
    exact command_of_payload _ (name := .reset) rfl rfl (command_reset)
      (fun hp => nullary_payload .reset (by simp [finalCall, hA.commandReset]) rfl hp) hs rest
  | resetAssertions =>
    exact command_of_payload _ (name := .resetAssertions) rfl rfl
      (command_resetAssertions)
      (fun hp => nullary_payload .resetAssertions
        (by simp [finalCall, hA.commandResetAssertions]) rfl hp) hs rest
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    by_cases hkeyword : keyword = BSmtLibSpec.Regex.chars "smt-lib-version"
    · subst hkeyword
      obtain ⟨decimal, declared, rfl, hdeclared⟩ : ∃ decimal declared,
          value = some (.constant (.decimal decimal)) ∧ versionOfNumber decimal = some declared :=
              by
        rcases value with _ | ⟨⟨_ | decimal | _ | _ | _⟩ | _ | _⟩ <;>
          simp [Tree.Command.modeAfter] at hmode
        cases hversion : versionOfNumber decimal with
        | none => simp [hversion] at hmode
        | some declared => exact ⟨decimal, declared, rfl, hversion⟩
      have houtcome : outcomeOf (.setInfo ⟨BSmtLibSpec.Regex.chars "smt-lib-version",
          some (.constant (.decimal decimal))⟩) = .setVersion (Bridge.libVersion declared) := by
        simp [outcomeOf, Tree.Command.declaredVersion, hdeclared]
      exact command_of_payload _ (name := .setInfo) rfl rfl
        (command_setInfo _ _)
        (fun hp => houtcome ▸ setInfo_payload_declaration hA decimal declared hdeclared hp) hs rest
    · exact command_of_payload _ (name := .setInfo) rfl rfl
        (command_setInfo _ _)
        (fun hp => (outcomeOf_setInfo_other hkeyword value) ▸
          setInfo_payload_other hA keyword value hkeyword hvalid hp) hs rest
  | setLogic name =>
    exact command_of_payload _ (name := .setLogic) rfl rfl
      (command_setLogic _) (fun hp => setLogic_payload hA name hp) hs rest
  | setOption option =>
    obtain ⟨keyword, value⟩ := option
    exact command_of_payload _ (name := .setOption) rfl rfl
      (command_setOption _ _) (fun hp => setOption_payload hA keyword value hvalid hp)
      hs rest

end

end BSmtLib.Facts.Proofs.Parser.Command
