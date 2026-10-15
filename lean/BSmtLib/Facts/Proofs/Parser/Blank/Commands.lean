module

public import BSmtLib.Facts.Proofs.Parser.Blank.Steps
import all BSmtLib.Parser
import all BSmtLib.Token
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Parser.Command
import all BSmtLib.Parser.Command.Internal.Datatype
import all BSmtLib.Parser.Command.Internal.Function
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# The steps of the commands, blanked

Each step of the parsers of the commands, and the script parser's arrival, run with a handler
whose calls never fail, relates to the step run with the blank handler on the blanked state
(`BSim`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Blank.Commands

open BSmtLib.Multiple (FunctionSignature)
open Basic States Simp Tactic Steps
open BSmtLib.Parser.Internal (PM)

open BSmtLib.Parser BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Parser.Category.Combinator BSmtLib.Parser.Category.SortedVar
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.«Sort» BSmtLib.Parser.Category.Term
open BSmtLib.Parser.Category.«Sort».Internal
open BSmtLib.Parser.Category.Term.Internal
open BSmtLib.Parser.Command BSmtLib.Parser.Command.Internal.Datatype
open BSmtLib.Parser.Command.Internal.Definition
open BSmtLib.Parser.Command.Internal
open BSmtLib.Parser.Command.Internal.Function BSmtLib.Parser.Command.Internal.Standard
open BSmtLib.Parser.Script

variable {H : Type} [CommandHandler H Id]

/-! ## The datatypes -/

theorem SortDecState_step_blank {state : SortDecState} {token : Internal.Input} :
    BSim (SortDecState.step (H := H) state token) (SortDecState.step (H := Shell) state token) := by
  unfold SortDecState.step; blank_step []

theorem constructorStep_blank [NoFails H] {version : Token.Version}
    {state : ConstructorState (Handler.«Sort» H)} {token : Internal.Input}
    {state' : ConstructorState Unit} (hs : state' = blank state) :
    BSim (constructorStep (H := H) version state token)
      (constructorStep (H := Shell) version state' token) := by
  subst hs; unfold constructorStep; blank_step []

theorem datatypeStep_blank [NoFails H] {start : Array Plain.Symbol → PM H Unit}
    {start' : Array Plain.Symbol → PM Shell Unit} (hstart : ∀ ps, BSim (start ps) (start' ps))
    {version : Token.Version} {state : DatatypeState (Handler.«Sort» H)} {token : Internal.Input}
    {state' : DatatypeState Unit} (hs : state' = blank state) :
    BSim (datatypeStep (H := H) start version state token)
      (datatypeStep (H := Shell) start' version state' token) := by
  subst hs; unfold datatypeStep; blank_step []

/-! ## The functions -/

theorem signatureStep_blank [NoFails H] {version : Token.Version}
    {state : SignatureState (Handler.«Sort» H)} {token : Internal.Input}
    {state' : SignatureState Unit} (hs : state' = blank state) :
    BSim (signatureStep (H := H) version state token)
      (signatureStep (H := Shell) version state' token) := by
  subst hs; unfold signatureStep; blank_step []

theorem functionDecStep_blank [NoFails H] {version : Token.Version}
    {state : FunctionDecState (Handler.«Sort» H)} {token : Internal.Input}
    {state' : FunctionDecState Unit} (hs : state' = blank state) :
    BSim (functionDecStep (H := H) version state token)
      (functionDecStep (H := Shell) version state' token) := by
  subst hs; unfold functionDecStep; blank_step []

theorem bodyStep_blank [NoFails H] {version : Token.Version} {state : TermStateOf H}
    {token : Internal.Input} {state' : TermStateOf Shell} (hs : state' = blank state) :
    BSim (bodyStep (H := H) version state token) (bodyStep (H := Shell) version state' token) := by
  subst hs; unfold bodyStep; blank_step []

theorem bodiesStep_blank [NoFails H] {count : Nat} {version : Token.Version}
    {state : ListState (TermStateOf H) Unit} {token : Internal.Input}
    {state' : ListState (TermStateOf Shell) Unit} (hs : state' = blank state) :
    BSim (bodiesStep (H := H) count version state token)
      (bodiesStep (H := Shell) count version state' token) := by
  subst hs; unfold bodiesStep; blank_step []

set_option maxHeartbeats 2000000 in
theorem bodiesArrive_blank [NoFails H] {signatures : Array (FunctionSignature (Handler.«Sort» H))}
    {signatures' : Array (FunctionSignature Unit)} {state : ListState (TermStateOf H) Unit}
    {state' : ListState (TermStateOf Shell) Unit} {token : Internal.Input}
    (hg : signatures' = blank signatures) (hs : state' = blank state) :
    BSim (bodiesArrive (H := H) signatures state token)
      (bodiesArrive (H := Shell) signatures' state' token) := by
  subst hg hs; unfold bodiesArrive; blank_step []

/-! ## The other commands -/

set_option maxHeartbeats 4000000 in
theorem literalStep_blank [NoFails H] {version : Token.Version} {state : LiteralStateOf H}
    {token : Internal.Input} {state' : LiteralStateOf Shell} (hs : state' = blank state) :
    BSim (literalStep (H := H) version state token)
      (literalStep (H := Shell) version state' token) := by
  subst hs; unfold literalStep; blank_step []

theorem finalCall_blank [NoFails H]
    {final : FinalCall (Handler.Attribute H) (Handler.«Sort» H) (Handler.Term H)}
    {final' : FinalCall Unit Unit Unit} (hf : final' = blank final) :
    BSim (finalCall (H := H) final) (finalCall (H := Shell) final') := by
  subst hf; unfold finalCall; blank_step []

set_option maxHeartbeats 16000000 in
theorem payloadStep_blank [NoFails H] {version : Token.Version} {state : PayloadOf H}
    {token : Internal.Input} {state' : PayloadOf Shell} (hs : state' = blank state) :
    BSim (payloadStep (H := H) version state token)
      (payloadStep (H := Shell) version state' token) := by
  subst hs; unfold payloadStep; blank_step []

theorem payloadArrive_blank [NoFails H] {state : PayloadOf H} {token : Internal.Input}
    {state' : PayloadOf Shell} (hs : state' = blank state) :
    BSim (payloadArrive (H := H) state token) (payloadArrive (H := Shell) state' token) := by
  subst hs; unfold payloadArrive; blank_step []

theorem commandStep_blank [NoFails H] {version : Token.Version} {state : CommandStateOf H}
    {token : Internal.Input} {state' : CommandStateOf Shell} (hs : state' = blank state) :
    BSim (commandStep (H := H) version state token)
      (commandStep (H := Shell) version state' token) := by
  subst hs
  cases state with
  | nonstandard parser => exact (NoFails.noNonstandard parser).elim
  | awaiting => unfold commandStep; blank_step []
  | payload => unfold commandStep; simp only [Blanks.blank, blankCommandState]; blank_step []
  | opened =>
    unfold commandStep
    simp only [Blanks.blank, blankCommandState]
    cases token
    -- the handler names no parser of non-standard commands: its `nonstandardCommand` fails
    case symbol name => exact BSim.callNone NoFails.noNonstandard rfl
    all_goals blank_step []

theorem commandArrive_blank [NoFails H] {state : CommandStateOf H} {token : Internal.Input}
    {state' : CommandStateOf Shell} (hs : state' = blank state) :
    BSim (commandArrive (H := H) state token) (commandArrive (H := Shell) state' token) := by
  subst hs; unfold commandArrive; blank_step []

theorem ScriptParser_arrive_blank [NoFails H] {parser : ScriptParser H} {token : Internal.Input} :
    BSim (ScriptParser.Internal.arrive (H := H) parser token)
      (ScriptParser.Internal.arrive (H := Shell) (blank parser) token) := by
  unfold ScriptParser.Internal.arrive; exact commandArrive_blank rfl

end BSmtLib.Facts.Proofs.Parser.Blank.Commands
