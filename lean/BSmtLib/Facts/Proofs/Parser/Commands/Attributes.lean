module

public import BSmtLib.Facts.Proofs.Parser.Commands.FunsRec
import all BSmtLib.Parser.Category.Attribute
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Command.Internal.Standard

@[expose] public section

/-!
# `set-option`, `set-info` and version declarations against the traversal

`set-option` and `set-info` read one attribute with the attribute parser, which takes the
command's `)` too. `set-info` also follows its tokens with a tracker of a version declaration
(`Parser.Declaration`): with a keyword other than `:smt-lib-version`, the tracker is `other`
from the keyword on, and the payload parser steps as the attribute parser. A version
declaration, `:smt-lib-version` with a version's number, is three tokens, followed one by one;
at its `)`, `set-info`, and the command parser ends with the version.
-/

namespace BSmtLib.Facts.Proofs.Parser.Commands.Attributes

open BSmtLibSpec.Grammar
open BSmtLib.Parser.Command.Internal.Standard (Payload FinalCall payloadStep finalCall Declaration)
open BSmtLib.Parser.Command (CommandOutcome)
open BSmtLib.Parser.Category.Attribute.Internal (AttributeState AttributeMode attributeStep)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Attribute BSmtLib.Facts.Proofs.Parser.Commands.Bytes
open BSmtLib.Facts.Proofs.Parser.Commands.Frame BSmtLib.Facts.Proofs.Parser.Drive
open BSmtLib.Facts.Proofs.Parser.Lemmas BSmtLib.Facts.Proofs.Parser.Tokens

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser (Program.callUnit)
open BSmtLibSpec.Facts.Proofs.Parser.Equations (attributeThen_some)

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.CommandHandler H m]
variable {points : Points (StateT H m)} {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

theorem outcomeOf_setInfo_other {keyword : BSmtLibSpec.Regex.Chars}
    (hkeyword : keyword ≠ BSmtLibSpec.Regex.chars "smt-lib-version")
    (value : Option Tree.AttributeValue) : outcomeOf (.setInfo ⟨keyword, value⟩) = .command := by
  rcases value with _ | ⟨⟨_ | _ | _ | _ | _⟩ | _ | _⟩ <;>
    simp [outcomeOf, Tree.Command.declaredVersion, hkeyword]

variable (hA : Agrees h)
include hA

theorem setOption_payload (keyword : BSmtLibSpec.Regex.Chars) (value : Option Tree.AttributeValue)
    (hvalid : (⟨keyword, value⟩ : Tree.Attribute).Valid (Bridge.version version))
    {payload : List Parser.Internal.Input} (hs : Stands payload (Tree.Attribute.tokens ⟨keyword,
        value⟩)) :
    PayloadRuns points version (Payload.init .setOption version)
      (payload ++ [.parenClose])
      (adaptRun (do
        take points (.keyword keyword)
        let handled ← attributeThen points h keyword .parenClose value
        Program.callUnit h (.commandSetOption handled)))
      fun _ => pure (.done .command) := by
  have hruns := attributeSingle_runs (points := points) hA.toTermAgrees keyword value hvalid
    (Stands.append hs (Stands.cons (token := .parenClose) rfl Stands.nil))
  refine (Runs.bind_next ((Runs.embedA (outer := payloadStep version)
      (outerArrival := Parser.Command.Internal.Standard.payloadArrive) Payload.setOption
    (fun attributes => do
      let some option := attributes[0]? | Parser.Internal.syntaxError .expectedAttribute
      Parser.Internal.call (Traits.CommandHandler.commandSetOption option)
      return .done .command)
    (by payload_step) hruns).congr rfl
    (next' := fun r => Parser.Internal.call (Traits.CommandHandler.commandSetOption r) >>=
      fun _ => pure (.done .command))
    (by funext; simp [Parser.Internal.Step.wrap]))).congr ?_ rfl
  simp [hA.commandSetOption]

/-- `set-info` with a keyword other than `:smt-lib-version`. -/
theorem setInfo_payload_other (keyword : BSmtLibSpec.Regex.Chars)
    (value : Option Tree.AttributeValue)
    (hkeyword : keyword ≠ BSmtLibSpec.Regex.chars "smt-lib-version")
    (hvalid : (⟨keyword, value⟩ : Tree.Attribute).Valid (Bridge.version version))
    {payload : List Parser.Internal.Input} (hs : Stands payload (Tree.Attribute.tokens ⟨keyword,
        value⟩)) :
    PayloadRuns points version (Payload.init .setInfo version)
      (payload ++ [.parenClose])
      (adaptRun (do
        take points (.keyword keyword)
        let handled ← attributeThen points h keyword .parenClose value
        Program.callUnit h (.commandSetInfo handled)))
      fun _ => pure (.done .command) := by
  have hruns := attributeSingle_runs (points := points) hA.toTermAgrees keyword value hvalid
    (Stands.append hs (Stands.cons (token := .parenClose) rfl Stands.nil))
  have hfirst : ∃ view rest, payload = .keyword view :: rest ∧
      Bridge.keyword view = keyword := by
    have hs' : Stands payload (.keyword keyword :: (match value with
        | none => [] | some value => value.tokens)) := by
      cases value <;> exact hs
    obtain ⟨token, rest, rfl, htoken, -⟩ := Stands.split_cons hs'
    obtain ⟨view, rfl, hview⟩ := Parser.Internal.Input.received_keyword htoken
    exact ⟨view, rest, rfl, hview⟩
  obtain ⟨view, rest, rfl, hview⟩ := hfirst
  have hnot : Parser.Command.Internal.Standard.isVersionKeyword view = false := by
    rw [isVersionKeyword_eq, hview]
    exact decide_eq_false hkeyword
  have hembed := Runs.bind_next ((Runs.embedA (outer := payloadStep version)
      (outerArrival := Parser.Command.Internal.Standard.payloadArrive)
    (Payload.setInfo .other)
    (fun attributes => do
      let some info := attributes[0]? | Parser.Internal.syntaxError .expectedAttribute
      Parser.Internal.call (Traits.CommandHandler.commandSetInfo info)
      return .done .command)
    (by
      intro state token
      simp only [payloadStep]
      congr 1
      funext step
      cases step with
      | more => rfl
      | done r =>
        simp only [Parser.Internal.Step.wrap, Declaration.next]
        cases r[0]? <;> rfl) hruns).congr rfl
    (next' := fun r => Parser.Internal.call (Traits.CommandHandler.commandSetInfo r) >>=
      fun _ => pure (.done .command))
    (by funext; simp [Parser.Internal.Step.wrap]))
  refine (Runs.first (state' := Payload.setInfo .other .init)
    (by simp [payloadStep, Payload.init, Declaration.next, hnot]) hembed).congr ?_ rfl
  simp [hA.commandSetInfo]

/-- A version declaration: `set-info` of `:smt-lib-version` with a version's number. -/
theorem setInfo_payload_declaration (decimal : BSmtLibSpec.Regex.Chars)
    (declared : BSmtLibSpec.Lexicon.Version)
    (hdeclared : versionOfNumber decimal = some declared) {payload : List Parser.Internal.Input}
    (hs : Stands payload (Tree.Attribute.tokens ⟨BSmtLibSpec.Regex.chars "smt-lib-version",
      some (.constant (.decimal decimal))⟩)) :
    PayloadRuns points version (Payload.init .setInfo version)
      (payload ++ [.parenClose])
      (adaptRun (do
        take points (.keyword (BSmtLibSpec.Regex.chars "smt-lib-version"))
        let handled ← attributeThen points h (BSmtLibSpec.Regex.chars "smt-lib-version") .parenClose
          (some (.constant (.decimal decimal)))
        Program.callUnit h (.commandSetInfo handled)))
      fun _ => pure (.done (.setVersion (Bridge.libVersion declared))) := by
  obtain ⟨keywordToken, rest, rfl, hkeywordToken, hrest⟩ := Stands.split_cons hs
  obtain ⟨decimalToken, rfl, hdecimalToken⟩ := Stands.split_single hrest
  obtain ⟨keyword, rfl, hkeyword⟩ := Parser.Internal.Input.received_keyword hkeywordToken
  obtain ⟨text, rfl, htext⟩ := Parser.Internal.Input.received_decimal hdecimalToken
  have hversionKeyword : Parser.Command.Internal.Standard.isVersionKeyword keyword = true := by
    rw [isVersionKeyword_eq, hkeyword]
    exact decide_eq_true rfl
  have hversion : Token.Version.fromDecimal? text.asSlice = some (Bridge.libVersion declared) := by
    rw [fromDecimal_eq, htext, hdeclared]
    rfl
  rw [show [Parser.Internal.Input.keyword keyword,
      .constant (.decimal text)] ++ [Parser.Internal.Input.parenClose] =
    [.keyword keyword] ++ ([.constant (.decimal text)] ++ [.parenClose]) by rfl]
  refine (Runs.append (middle := fun _ => Payload.setInfo .keyword
      { mode := .afterName keyword, attributes := #[] })
    (Runs.token_moreA (arrival := Parser.Command.Internal.Standard.payloadArrive) (by
      simp [payloadStep, Payload.init, Declaration.next, hversionKeyword, attributeStep,
        AttributeState.init])) fun _ =>
    Runs.append (middle := fun handled => Payload.setInfo
        (.value (some (Bridge.libVersion declared))) { mode := .start, attributes := #[handled] })
      (Runs.tokenA (arrival := Parser.Command.Internal.Standard.payloadArrive)
      (program := Parser.Internal.call (Traits.Handler.handleAttribute keyword
        (some (.specialConstant (.decimal text))))) (by
        simp [payloadStep, Declaration.next, hversion, attributeStep])) fun handled =>
      Runs.tokenA (arrival := Parser.Command.Internal.Standard.payloadArrive)
          (program := Parser.Internal.call (Traits.CommandHandler.commandSetInfo handled))
        (step := payloadStep version)
        (next := fun _ => pure (.done (.setVersion (Bridge.libVersion declared)))) (by
        simp [payloadStep, Declaration.next, attributeStep,
            Parser.Category.Token.Internal.expectClose])).congr ?_ rfl
  rw [attributeThen_some]
  simp [attributeValue, Tree.SpecConstant.token, ← hkeyword, ← htext, hA.handleAttribute,
    hA.commandSetInfo, Bridge.attributeValue, Bridge.constant,
    adaptRun_take (token := .keyword keyword) rfl, adaptRun_take (token := .parenClose) rfl,
    adaptRun_take (token := .constant (.decimal text))
      (syntaxToken := .decimal (Bridge.chars text.asSlice)) rfl]

end

end BSmtLib.Facts.Proofs.Parser.Commands.Attributes
