module

public import BSmtLib.Facts.Proofs.Parser.Commands.Frame
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Parser.Command.Internal.Standard

@[expose] public section

/-!
# Commands of single tokens against the traversal

The payloads of the commands that take no parts but single tokens: the commands of a name alone,
and those of a symbol, a numeral, a string or a keyword. Each payload lemma is stated as
`command_of_payload` takes it.
-/

namespace BSmtLib.Facts.Proofs.Parser.Commands.Simple

open BSmtLibSpec.Grammar
open BSmtLib.Parser.Command (CommandOutcome)
open BSmtLib.Parser.Command.Internal.Standard (Payload FinalCall payloadStep finalCall)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Commands.Frame BSmtLib.Facts.Proofs.Parser.Drive
open BSmtLib.Facts.Proofs.Parser.Lemmas BSmtLib.Facts.Proofs.Parser.Tokens

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser (Program.callUnit)

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.CommandHandler H m]
variable {points : Points (StateT H m)} {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

/-- How the command parser ends after a command's last call. -/
def finalOutcome {A S T : Type} : FinalCall A S T → CommandOutcome
  | .exit => .exit
  | _ => .command

/-- The command's `)`, then its last call. -/
theorem closing_runs (final : FinalCall (Traits.Handler.Attribute H) (Traits.Handler.«Sort» H)
      (Traits.Handler.Term H)) {request : Call (valuesOf H) .nothing}
    (hfinal : finalCall final = Parser.Internal.call (Bridge.callUnit h request))
    {outcome : CommandOutcome}
    (houtcome : finalOutcome final = outcome) :
    PayloadRuns points version (.closing final) [.parenClose]
      (adaptRun (do take points .parenClose; Program.callUnit h request))
      fun _ => pure (.done outcome) := by
  refine (Runs.tokenA (arrival := Parser.Command.Internal.Standard.payloadArrive)
      (program := finalCall final) ?_).congr ?_ rfl
  · subst houtcome
    cases final <;> simp [payloadStep, Parser.Category.Token.Internal.expectClose, finalOutcome]
  · simp [hfinal, adaptRun_take (token := .parenClose) rfl]

/-- A command of its name alone. -/
theorem nullary_payload (final : FinalCall (Traits.Handler.Attribute H) (Traits.Handler.«Sort» H)
      (Traits.Handler.Term H)) {request : Call (valuesOf H) .nothing}
    (hfinal : finalCall final = Parser.Internal.call (Bridge.callUnit h request))
    {outcome : CommandOutcome}
    (houtcome : finalOutcome final = outcome)
    {payload : List Parser.Internal.Input} (hs : Stands payload []) :
    PayloadRuns points version (.closing final) (payload ++ [.parenClose])
      (adaptRun (do take points .parenClose; Program.callUnit h request))
      fun _ => pure (.done outcome) := by
  rw [Stands.eq_nil hs]
  exact closing_runs final hfinal houtcome

/-- A command of a single token: the token, then the closing. -/
theorem single_payload {payload : Parser.Command.Internal.Standard.PayloadOf H}
    {token : Parser.Internal.Input}
    {final : FinalCall (Traits.Handler.Attribute H) (Traits.Handler.«Sort» H)
      (Traits.Handler.Term H)}
    (hstep : payloadStep version payload token = pure (.more (.closing final)))
    {request : Call (valuesOf H) .nothing}
    (hfinal : finalCall final = Parser.Internal.call (Bridge.callUnit h request))
    (houtcome : finalOutcome final = .command)
    (harr : Parser.Command.Internal.Standard.payloadArrive payload token = pure () := by intros; rfl) :
    PayloadRuns points version payload ([token] ++ [.parenClose])
      (do tick points token; adaptRun (do take points .parenClose; Program.callUnit h request))
      fun _ => pure (.done .command) :=
  Runs.append (Runs.token_moreA (arrival := Parser.Command.Internal.Standard.payloadArrive)
      hstep harr) fun _ => closing_runs final hfinal houtcome

variable (hA : Agrees h)
include hA

theorem echo_payload (content : BSmtLibSpec.Regex.Chars) {payload : List Parser.Internal.Input}
    (hs : Stands payload [.string content]) :
    PayloadRuns points version (Payload.init .echo version) (payload ++ [.parenClose])
      (adaptRun (do
        takeAll points [.string content, .parenClose]
        Program.callUnit h (.commandEcho content)))
      fun _ => pure (.done .command) := by
  obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
  obtain ⟨view, rfl, rfl⟩ := Parser.Internal.Input.received_string htoken
  refine (single_payload (final := .echo view) (h := h)
      (request := .commandEcho (Bridge.chars view.asSlice)) (by simp [payloadStep, Payload.init,
    Parser.Category.Token.Internal.expectString]) (by simp [finalCall, hA.commandEcho]) rfl).congr ?_ rfl
  simp [takeAll, adaptRun_take htoken, adaptRun_take (token := .parenClose) rfl]

theorem getInfo_payload (flag : BSmtLibSpec.Regex.Chars) {payload : List Parser.Internal.Input}
    (hs : Stands payload [.keyword flag]) :
    PayloadRuns points version (Payload.init .getInfo version) (payload ++ [.parenClose])
      (adaptRun (do
        takeAll points [.keyword flag, .parenClose]
        Program.callUnit h (.commandGetInfo flag)))
      fun _ => pure (.done .command) := by
  obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
  obtain ⟨keyword, rfl, rfl⟩ := Parser.Internal.Input.received_keyword htoken
  refine (single_payload (final := .getInfo keyword) (h := h)
      (request := .commandGetInfo (Bridge.keyword keyword)) (by simp [payloadStep, Payload.init,
    Parser.Category.Token.Internal.expectKeyword]) (by simp [finalCall, hA.commandGetInfo]) rfl).congr ?_ rfl
  simp [takeAll, adaptRun_take htoken, adaptRun_take (token := .parenClose) rfl]

theorem getOption_payload (keyword : BSmtLibSpec.Regex.Chars) {payload : List Parser.Internal.Input}
    (hs : Stands payload [.keyword keyword]) :
    PayloadRuns points version (Payload.init .getOption version) (payload ++ [.parenClose])
      (adaptRun (do
        takeAll points [.keyword keyword, .parenClose]
        Program.callUnit h (.commandGetOption keyword)))
      fun _ => pure (.done .command) := by
  obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
  obtain ⟨view, rfl, rfl⟩ := Parser.Internal.Input.received_keyword htoken
  refine (single_payload (final := .getOption view) (h := h)
      (request := .commandGetOption (Bridge.keyword view)) (by simp [payloadStep, Payload.init,
    Parser.Category.Token.Internal.expectKeyword]) (by simp [finalCall, hA.commandGetOption]) rfl).congr ?_
        rfl
  simp [takeAll, adaptRun_take htoken, adaptRun_take (token := .parenClose) rfl]

theorem pop_payload (count : BSmtLibSpec.Regex.Chars) {payload : List Parser.Internal.Input}
    (hs : Stands payload [.numeral count]) :
    PayloadRuns points version (Payload.init .pop version) (payload ++ [.parenClose])
      (adaptRun (do
        takeAll points [.numeral count, .parenClose]
        Program.callUnit h (.commandPop count)))
      fun _ => pure (.done .command) := by
  obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
  obtain ⟨view, rfl, rfl⟩ := Parser.Internal.Input.received_numeral htoken
  refine (single_payload (final := .pop view) (h := h)
      (request := .commandPop (Bridge.chars view.asSlice)) (by simp [payloadStep, Payload.init,
    Parser.Category.Token.Internal.expectNumeral]) (by simp [finalCall, hA.commandPop]) rfl).congr ?_ rfl
  simp [takeAll, adaptRun_take htoken, adaptRun_take (token := .parenClose) rfl]

theorem push_payload (count : BSmtLibSpec.Regex.Chars) {payload : List Parser.Internal.Input}
    (hs : Stands payload [.numeral count]) :
    PayloadRuns points version (Payload.init .push version) (payload ++ [.parenClose])
      (adaptRun (do
        takeAll points [.numeral count, .parenClose]
        Program.callUnit h (.commandPush count)))
      fun _ => pure (.done .command) := by
  obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
  obtain ⟨view, rfl, rfl⟩ := Parser.Internal.Input.received_numeral htoken
  refine (single_payload (final := .push view) (h := h)
      (request := .commandPush (Bridge.chars view.asSlice)) (by simp [payloadStep, Payload.init,
    Parser.Category.Token.Internal.expectNumeral]) (by simp [finalCall, hA.commandPush]) rfl).congr ?_ rfl
  simp [takeAll, adaptRun_take htoken, adaptRun_take (token := .parenClose) rfl]

theorem setLogic_payload (name : Tree.Symbol) {payload : List Parser.Internal.Input}
    (hs : Stands payload [.symbol name]) :
    PayloadRuns points version (Payload.init .setLogic version) (payload ++ [.parenClose])
      (adaptRun (do
        takeAll points [.symbol name, .parenClose]
        Program.callUnit h (.commandSetLogic name)))
      fun _ => pure (.done .command) := by
  obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
  refine (single_payload (final := .setLogic symbol) (h := h)
      (request := .commandSetLogic (Bridge.symbol symbol)) (by simp [payloadStep, Payload.init,
    Parser.Category.Token.Internal.expectSymbol]) (by simp [finalCall, hA.commandSetLogic]) rfl).congr ?_ rfl
  simp [takeAll, adaptRun_take htoken, adaptRun_take (token := .parenClose) rfl]

theorem declareSortParameter_payload (name : Tree.Symbol) {payload : List Parser.Internal.Input}
    (hs : Stands payload [.symbol name]) :
    PayloadRuns points version (Payload.init .declareSortParameter version)
      (payload ++ [.parenClose])
      (adaptRun (do
        takeAll points [.symbol name, .parenClose]
        Program.callUnit h (.commandDeclareSortParameter name)))
      fun _ => pure (.done .command) := by
  obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
  refine (single_payload (final := .declareSortParameter symbol)
    (h := h) (request := .commandDeclareSortParameter (Bridge.symbol symbol)) (by simp [payloadStep,
    Payload.init, Parser.Category.Token.Internal.expectSymbol])
        (by simp [finalCall, hA.commandDeclareSortParameter])
    rfl).congr ?_ rfl
  simp [takeAll, adaptRun_take htoken, adaptRun_take (token := .parenClose) rfl]

theorem declareSort_payload (name : Tree.Symbol) (arity : BSmtLibSpec.Regex.Chars)
    {payload : List Parser.Internal.Input}
    (hs : Stands payload [.symbol name, .numeral arity]) :
    PayloadRuns points version (Payload.init .declareSort version) (payload ++ [.parenClose])
      (adaptRun (do
        takeAll points [.symbol name, .numeral arity, .parenClose]
        Program.callUnit h (.commandDeclareSort name arity)))
      fun _ => pure (.done .command) := by
  obtain ⟨symbolToken, rest, rfl, hsymbolToken, hrest⟩ := Stands.split_cons hs
  obtain ⟨numeralToken, rfl, hnumeralToken⟩ := Stands.split_single hrest
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbolToken
  obtain ⟨view, rfl, rfl⟩ := Parser.Internal.Input.received_numeral hnumeralToken
  refine (Runs.append (first := [.symbol symbol]) (middle := fun _ => .declareSort symbol)
    (Runs.token_moreA (arrival := Parser.Command.Internal.Standard.payloadArrive) (by simp [payloadStep,
      Payload.init, Parser.Category.Token.Internal.expectSymbol])) fun _ =>
    single_payload (final := .declareSort symbol view)
      (h := h) (request := .commandDeclareSort (Bridge.symbol symbol) (Bridge.chars view.asSlice))
          (by simp [payloadStep,
      Parser.Category.Token.Internal.expectNumeral]) (by simp [finalCall, hA.commandDeclareSort]) rfl).congr
          ?_ rfl
  simp [takeAll, adaptRun_take hsymbolToken, adaptRun_take hnumeralToken,
    adaptRun_take (token := .parenClose) rfl]

end

end BSmtLib.Facts.Proofs.Parser.Commands.Simple
