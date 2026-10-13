import BSmtLib.ParserProofs.Commands.FunsRec

/-!
# `set-option`, `set-info` and version declarations against the traversal

`set-option` and `set-info` read one attribute with the attribute parser, which takes the
command's `)` too. `set-info` also follows its tokens with a tracker of a version declaration
(`Parser.Declaration`): with a keyword other than `:smt-lib-version`, the tracker is `other`
from the keyword on, and the payload parser steps as the attribute parser. A version
declaration, `:smt-lib-version` with a version's number, is three tokens, followed one by one;
at its `)`, `set-info`, and the command parser ends with the version.
-/

namespace BSmtLib.ParserProofs

open BSmtLib.Spec.Grammar
open BSmtLib.Parser (Input PM Step Payload CommandOutcome FinalCall payloadStep finalCall
  AttributeState AttributeMode attributeStep Declaration)
open BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal
open BSmtLib.SpecChecks.Parser (Program.callUnit attributeThen_some)

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Parser.CommandHandler H m]
variable {points : Points (StateT H m)} {version : BSmtLib.Version}
variable {h : Traversal.Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H)}

theorem outcomeOf_setInfo_other {keyword : Spec.Lexicon.Chars}
    (hkeyword : keyword ≠ Spec.Lexicon.chars "smt-lib-version")
    (value : Option Tree.AttributeValue) : outcomeOf (.setInfo ⟨keyword, value⟩) = .command := by
  rcases value with _ | ⟨⟨_ | _ | _ | _ | _⟩ | _ | _⟩ <;>
    simp [outcomeOf, Tree.Command.declaredVersion, hkeyword]

variable (hA : Agrees h)
include hA

theorem setOption_payload (keyword : Spec.Lexicon.Chars) (value : Option Tree.AttributeValue)
    (hvalid : (⟨keyword, value⟩ : Tree.Attribute).Valid (Bridge.version version))
    {payload : List Input} (hs : Stands payload (Tree.Attribute.tokens ⟨keyword, value⟩)) :
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
      (outerArrival := Parser.payloadArrive) Payload.setOption
    (fun attributes => do
      let some option := attributes[0]? | Parser.syntaxError .expectedAttribute
      Parser.call (Parser.CommandHandler.commandSetOption option)
      return .done .command)
    (by payload_step) hruns).congr rfl
    (next' := fun r => Parser.call (Parser.CommandHandler.commandSetOption r) >>=
      fun _ => pure (.done .command))
    (by funext; simp [Step.wrap]))).congr ?_ rfl
  simp [hA.commandSetOption]

/-- `set-info` with a keyword other than `:smt-lib-version`. -/
theorem setInfo_payload_other (keyword : Spec.Lexicon.Chars) (value : Option Tree.AttributeValue)
    (hkeyword : keyword ≠ Spec.Lexicon.chars "smt-lib-version")
    (hvalid : (⟨keyword, value⟩ : Tree.Attribute).Valid (Bridge.version version))
    {payload : List Input} (hs : Stands payload (Tree.Attribute.tokens ⟨keyword, value⟩)) :
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
    obtain ⟨view, rfl, hview⟩ := Input.received_keyword htoken
    exact ⟨view, rest, rfl, hview⟩
  obtain ⟨view, rest, rfl, hview⟩ := hfirst
  have hnot : Parser.isVersionKeyword view = false := by
    rw [isVersionKeyword_eq, hview]
    exact decide_eq_false hkeyword
  have hembed := Runs.bind_next ((Runs.embedA (outer := payloadStep version)
      (outerArrival := Parser.payloadArrive)
    (Payload.setInfo .other)
    (fun attributes => do
      let some info := attributes[0]? | Parser.syntaxError .expectedAttribute
      Parser.call (Parser.CommandHandler.commandSetInfo info)
      return .done .command)
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
      fun _ => pure (.done .command))
    (by funext; simp [Step.wrap]))
  refine (Runs.first (state' := Payload.setInfo .other .init)
    (by simp [payloadStep, Payload.init, Declaration.next, hnot]) hembed).congr ?_ rfl
  simp [hA.commandSetInfo]

/-- A version declaration: `set-info` of `:smt-lib-version` with a version's number. -/
theorem setInfo_payload_declaration (decimal : Spec.Lexicon.Chars) (declared : Spec.Lexicon.Version)
    (hdeclared : versionOfNumber decimal = some declared) {payload : List Input}
    (hs : Stands payload (Tree.Attribute.tokens ⟨Spec.Lexicon.chars "smt-lib-version",
      some (.constant (.decimal decimal))⟩)) :
    PayloadRuns points version (Payload.init .setInfo version)
      (payload ++ [.parenClose])
      (adaptRun (do
        take points (.keyword (Spec.Lexicon.chars "smt-lib-version"))
        let handled ← attributeThen points h (Spec.Lexicon.chars "smt-lib-version") .parenClose
          (some (.constant (.decimal decimal)))
        Program.callUnit h (.commandSetInfo handled)))
      fun _ => pure (.done (.setVersion (Bridge.libVersion declared))) := by
  obtain ⟨keywordToken, rest, rfl, hkeywordToken, hrest⟩ := Stands.split_cons hs
  obtain ⟨decimalToken, rfl, hdecimalToken⟩ := Stands.split_single hrest
  obtain ⟨keyword, rfl, hkeyword⟩ := Input.received_keyword hkeywordToken
  obtain ⟨text, rfl, htext⟩ := Input.received_decimal hdecimalToken
  have hversionKeyword : Parser.isVersionKeyword keyword = true := by
    rw [isVersionKeyword_eq, hkeyword]
    exact decide_eq_true rfl
  have hversion : BSmtLib.Version.fromDecimal? text.asSlice = some (Bridge.libVersion declared) := by
    rw [fromDecimal_eq, htext, hdeclared]
    rfl
  rw [show [Input.keyword keyword, .constant (.decimal text)] ++ [Input.parenClose] =
    [.keyword keyword] ++ ([.constant (.decimal text)] ++ [.parenClose]) by rfl]
  refine (Runs.append (middle := fun _ => Payload.setInfo .keyword
      { mode := .afterName keyword, attributes := #[] })
    (Runs.token_moreA (arrival := Parser.payloadArrive) (by
      simp [payloadStep, Payload.init, Declaration.next, hversionKeyword, attributeStep,
        AttributeState.init])) fun _ =>
    Runs.append (middle := fun handled => Payload.setInfo
        (.value (some (Bridge.libVersion declared))) { mode := .start, attributes := #[handled] })
      (Runs.tokenA (arrival := Parser.payloadArrive)
          (program := Parser.call (Parser.Handler.handleAttribute keyword
        (some (.constant (.decimal text))))) (by
        simp [payloadStep, Declaration.next, hversion, attributeStep])) fun handled =>
      Runs.tokenA (arrival := Parser.payloadArrive)
          (program := Parser.call (Parser.CommandHandler.commandSetInfo handled))
        (step := payloadStep version)
        (next := fun _ => pure (.done (.setVersion (Bridge.libVersion declared)))) (by
        simp [payloadStep, Declaration.next, attributeStep, Parser.expectClose])).congr ?_ rfl
  rw [attributeThen_some]
  simp [attributeValue, Tree.SpecConstant.token, ← hkeyword, ← htext, hA.handleAttribute,
    hA.commandSetInfo, Bridge.attributeValue, Bridge.constant,
    adaptRun_take (token := .keyword keyword) rfl, adaptRun_take (token := .parenClose) rfl,
    adaptRun_take (token := .constant (.decimal text))
      (syntaxToken := .decimal (Bridge.chars text.asSlice)) rfl]

end

end BSmtLib.ParserProofs
