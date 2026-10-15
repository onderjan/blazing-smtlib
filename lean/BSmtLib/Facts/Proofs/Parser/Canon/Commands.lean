module

public import BSmtLib.Facts.Proofs.Parser.Canon.Steps
import all BSmtLib.Parser
import all BSmtLib.Token
import all Std.Data.ByteSlice
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Parser.Command
import all BSmtLib.Parser.Command.Internal.Datatype
import all BSmtLib.Parser.Command.Internal.Function
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# The steps of the commands, canonicalised

Each step of the parsers of the commands and of the script parser, run on a canonicalised state
and token, relates to the step run on the state and the token as they are (`CSim`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Canon.Commands

open Basic States Simp Bridge Steps

open BSmtLib.Parser BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Parser.Category.Combinator BSmtLib.Parser.Category.SortedVar
open BSmtLib.Parser.Category.«Sort» BSmtLib.Parser.Category.Term
open BSmtLib.Parser.Command BSmtLib.Parser.Command.Internal.Datatype
open BSmtLib.Parser.Command.Internal.Definition
open BSmtLib.Parser.Command.Internal.Function BSmtLib.Parser.Command.Internal.Standard
open BSmtLib.Parser.Script
open BSmtLibSpec.Parser.Properties (Event)
open BSmtLib.Facts.Proofs.Parser.Quiet (RPM)
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.«Sort».Internal
open BSmtLib.Parser.Category.Term.Internal
open BSmtLib.Parser.Command.Internal

/-! ## What reads contents only -/

@[canon_simps] theorem beq_canonSlice (s t : ByteSlice) : (canonSlice s == t) = (s == t) := by
  show ByteSlice.beq _ _ = ByteSlice.beq _ _
  unfold ByteSlice.beq
  rw [toByteArray_canonSlice]

@[canon_simps] theorem isNot_canonSymbol (s : Symbol) :
    Standard.Symbol.isNot (canonSymbol s) = Standard.Symbol.isNot s := by
  cases s
  simp only [Standard.Symbol.isNot, canon_simps, Canon.canon]

@[canon_simps] theorem isVersionKeyword_canon (k : BSmtLib.Plain.KeywordView) :
    isVersionKeyword (BSmtLib.Plain.KeywordView.Internal.newUnchecked (canonSlice k.asSlice)) =
      isVersionKeyword k := by
  simp only [isVersionKeyword, canon_simps]

@[canon_simps] theorem fromDecimal?_canonSlice (s : ByteSlice) :
    Token.Version.fromDecimal? (canonSlice s) = Token.Version.fromDecimal? s := by
  simp only [Token.Version.fromDecimal?, beq_canonSlice]

@[canon_simps] theorem next_canonInput (d : Declaration) (t : Internal.Input) :
    d.next (canonInput t) = d.next t := by
  cases d <;> cases t <;> (try rename_i c; cases c) <;>
    simp only [Declaration.next, canonInput, canon_simps, Canon.canon]

attribute [canon_simps] Traits.CommandHandler.nonstandardCommand Array.getElem?_map

variable {token' : Internal.Input}

/-! ## The datatypes -/

theorem SortDecState_step_canon {state state' : SortDecState} {token : Internal.Input}
    (hs : state' = canon state) (ht : token' = canon token) :
    CSim (SortDecState.step (H := List Event) state token) (SortDecState.step state' token') := by
  subst hs ht; unfold SortDecState.step; canon_step []

theorem constructorStep_canon {version : Token.Version} {state state' : ConstructorState RSort}
    {token : Internal.Input} (hs : state' = canon state) (ht : token' = canon token) :
    CSim (constructorStep (H := List Event) version state token)
      (constructorStep version state' token') := by
  subst hs ht; unfold constructorStep; canon_step []

theorem datatypeStep_canon {start start' : Array Symbol → RPM Unit}
    (hstart : ∀ ps ps', ps' = canon ps → CSim (start ps) (start' ps'))
    {version : Token.Version} {state state' : DatatypeState RSort} {token : Internal.Input}
    (hs : state' = canon state) (ht : token' = canon token) :
    CSim (datatypeStep (H := List Event) start version state token)
      (datatypeStep start' version state' token') := by
  subst hs ht; unfold datatypeStep; canon_step []

/-! ## The functions -/

theorem signatureStep_canon {version : Token.Version} {state state' : SignatureState RSort}
    {token : Internal.Input} (hs : state' = canon state) (ht : token' = canon token) :
    CSim (signatureStep (H := List Event) version state token)
      (signatureStep version state' token') := by
  subst hs ht; unfold signatureStep; canon_step []

theorem functionDecStep_canon {version : Token.Version} {state state' : FunctionDecState RSort}
    {token : Internal.Input} (hs : state' = canon state) (ht : token' = canon token) :
    CSim (functionDecStep (H := List Event) version state token)
      (functionDecStep version state' token') := by
  subst hs ht; unfold functionDecStep; canon_step []

theorem bodyStep_canon {version : Token.Version} {state state' : TermStateOf (List Event)}
    {token : Internal.Input} (hs : state' = canon state) (ht : token' = canon token) :
    CSim (bodyStep (H := List Event) version state token) (bodyStep version state' token') := by
  subst hs ht; unfold bodyStep; canon_step []

theorem bodiesStep_canon {count : Nat} {version : Token.Version}
    {state state' : ListState (TermStateOf (List Event)) Unit} {token : Internal.Input}
    (hs : state' = canon state) (ht : token' = canon token) :
    CSim (bodiesStep (H := List Event) count version state token)
      (bodiesStep count version state' token') := by
  subst hs ht; unfold bodiesStep; canon_step []

set_option maxHeartbeats 2000000 in
theorem bodiesArrive_canon {signatures signatures' : Array (Signature RSort)}
    {state state' : ListState (TermStateOf (List Event)) Unit} {token : Internal.Input}
    (hg : signatures' = canon signatures) (hs : state' = canon state)
    (ht : token' = canon token) :
    CSim (bodiesArrive (H := List Event) signatures state token)
      (bodiesArrive signatures' state' token') := by
  subst hg hs ht; unfold bodiesArrive; canon_step []

/-! ## The other commands -/

set_option maxHeartbeats 4000000 in
theorem literalStep_canon {version : Token.Version} {state state' : LiteralStateOf (List Event)}
    {token : Internal.Input} (hs : state' = canon state) (ht : token' = canon token) :
    CSim (literalStep (H := List Event) version state token)
      (literalStep version state' token') := by
  subst hs ht; unfold literalStep; canon_step []

theorem finalCall_canon {final final' : FinalCall RAttribute RSort RTerm}
    (hf : final' = canon final) :
    CSim (finalCall (H := List Event) final) (finalCall final') := by
  subst hf; unfold finalCall; canon_step []

set_option maxHeartbeats 16000000 in
theorem payloadStep_canon {version : Token.Version} {state state' : PayloadOf (List Event)}
    {token : Internal.Input} (hs : state' = canon state) (ht : token' = canon token) :
    CSim (payloadStep (H := List Event) version state token)
      (payloadStep version state' token') := by
  subst hs ht; unfold payloadStep; canon_step []

theorem payloadArrive_canon {state state' : PayloadOf (List Event)} {token : Internal.Input}
    (hs : state' = canon state) (ht : token' = canon token) :
    CSim (payloadArrive (H := List Event) state token) (payloadArrive state' token') := by
  subst hs ht; unfold payloadArrive; canon_step []

theorem commandStep_canon {version : Token.Version} {state state' : CommandStateOf (List Event)}
    {token : Internal.Input} (hs : state' = canon state) (ht : token' = canon token) :
    CSim (commandStep (H := List Event) version state token)
      (commandStep version state' token') := by
  subst hs ht; unfold commandStep; canon_step []

theorem commandArrive_canon {state state' : CommandStateOf (List Event)} {token : Internal.Input}
    (hs : state' = canon state) (ht : token' = canon token) :
    CSim (commandArrive (H := List Event) state token) (commandArrive state' token') := by
  subst hs ht; unfold commandArrive; canon_step []

/-! ## The script -/

/-- What a step asks of its loop, with the views replaced: the actions that resume it give the
canonicalised step. -/
def canonFlow {σ ρ : Type} [Canon σ] [Canon ρ] :
    Internal.Flow RPM σ ρ → Internal.Flow RPM σ ρ
  | .more s => .more (canon s)
  | .done r => .done (canon r)
  | .switchVersion v resume => .switchVersion v (canonStep <$> resume)
  | .discardRest resume => .discardRest (canonStep <$> resume)

instance {σ ρ : Type} [Canon σ] [Canon ρ] : Canon (Internal.Flow RPM σ ρ) := ⟨canonFlow⟩

attribute [canon_simps] canonFlow.eq_1 canonFlow.eq_2 canonFlow.eq_3 canonFlow.eq_4 map_bind
  map_pure

theorem ScriptParser_arrive_canon {parser parser' : ScriptParser (List Event)}
    {token : Internal.Input} (hp : parser' = canon parser) (ht : token' = canon token) :
    CSim (ScriptParser.Internal.arrive (H := List Event) parser token)
      (ScriptParser.Internal.arrive parser' token') := by
  subst hp ht; unfold ScriptParser.Internal.arrive; canon_step []

theorem ScriptParser_step_canon {version : Token.Version}
    {parser parser' : ScriptParser (List Event)}
    {token : Internal.Input} (hp : parser' = canon parser) (ht : token' = canon token) :
    CSim (ScriptParser.Internal.step (H := List Event) version parser token)
      (ScriptParser.Internal.step version parser' token') := by
  subst hp ht; unfold ScriptParser.Internal.step; canon_step []

end BSmtLib.Facts.Proofs.Parser.Canon.Commands
