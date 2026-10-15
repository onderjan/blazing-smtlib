module

public import BSmtLib.Facts.Proofs.Parser.Commands.Simple
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Parser.Category.Token

@[expose] public section

/-!
# Commands of sorts and terms against the traversal

The payloads of the commands whose parts are sorts, terms, signatures and lists of them. A part
is read by its parser run inside a payload mode; a part that ends the payload is followed by the
command's `)` and last call (`part_then_close`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Commands.Terms

open BSmtLibSpec.Grammar
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Command (CommandOutcome)
open BSmtLib.Parser.Command.Internal.Standard (Payload FinalCall payloadStep finalCall)
open BSmtLib.Parser.Category.Combinator.Internal (ListState)
open BSmtLib.Parser.Command.Internal.Definition (DefinitionEnd)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Commands.Datatypes BSmtLib.Facts.Proofs.Parser.Commands.Elements
open BSmtLib.Facts.Proofs.Parser.Commands.Elements.Runs BSmtLib.Facts.Proofs.Parser.Commands.Frame
open BSmtLib.Facts.Proofs.Parser.Commands.Parts BSmtLib.Facts.Proofs.Parser.Commands.Simple
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Lemmas
open BSmtLib.Facts.Proofs.Parser.List BSmtLib.Facts.Proofs.Parser.SExpr
open BSmtLib.Facts.Proofs.Parser.«Sort» BSmtLib.Facts.Proofs.Parser.Term
open BSmtLib.Facts.Proofs.Parser.Tokens

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser (Program.callUnit)

/-- The payload parser's step into a part's parser and on, in one of its modes. -/
macro "payload_step" : tactic =>
  `(tactic| (intro state token; simp only [payloadStep]; congr 1; funext step; cases step <;> rfl))

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.CommandHandler H m]
variable {points : Points (StateT H m)} {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

/-- A part that ends the payload, run in a payload mode, then the command's `)` and last call. -/
theorem part_then_close {σ ρ : Type} {inner : σ → Parser.Internal.Input → PM H
    (Parser.Internal.Step σ ρ)} {init : σ}
    {wrap : σ → Parser.Command.Internal.Standard.PayloadOf H}
    {final : ρ → FinalCall (Traits.Handler.Attribute H) (Traits.Handler.«Sort» H)
      (Traits.Handler.Term H)}
    (hstep : ∀ state token, payloadStep version (wrap state) token =
      inner state token >>= Parser.Internal.Step.wrap wrap fun r => pure (.more (.closing
          (final r))))
    {tokens : List Parser.Internal.Input} {program : PM H ρ}
    (hruns : Runs points inner init tokens program fun r => pure (.done r))
    {request : ρ → Call (valuesOf H) .nothing}
    (hfinal : ∀ r, finalCall (final r) = Parser.Internal.call (Bridge.callUnit h (request r)))
    (houtcome : ∀ r, finalOutcome (final r) = .command)
    (hwrap : ∀ state token, Parser.Command.Internal.Standard.payloadArrive (wrap state) token = pure
        () := by
      intros; rfl) :
    PayloadRuns points version (wrap init) (tokens ++ [.parenClose])
      (do let r ← program; adaptRun (do take points .parenClose; Program.callUnit h (request r)))
      fun _ => pure (.done .command) :=
  Runs.append (middle := fun r => .closing (final r))
    ((Runs.embedA (outer := payloadStep version) (outerArrival :=
    Parser.Command.Internal.Standard.payloadArrive) wrap
      (fun r => pure (.more (.closing (final r)))) hstep hruns hwrap).congr rfl
      (by funext; simp [Parser.Internal.Step.wrap]))
    fun r => closing_runs (final r) (hfinal r) (houtcome r)

variable (hA : Agrees h)
include hA

theorem assert_payload (asserted : Tree.Term) (hvalid : asserted.Valid (Bridge.version version))
    {payload : List Parser.Internal.Input} (hs : Stands payload asserted.tokens) :
    PayloadRuns points version (Payload.init .assert version) (payload ++ [.parenClose])
      (adaptRun (do
        let handled ← Traversal.term points h asserted
        take points .parenClose
        Program.callUnit h (.commandAssert handled)))
      fun _ => pure (.done .command) :=
  (part_then_close (h := h) (wrap := Payload.assert) (final := fun t => .assert t)
    (request := fun t => .commandAssert t) (by payload_step)
    (term_runs_init hA.toTermAgrees asserted hvalid hs)
    (fun t => by simp [finalCall, hA.commandAssert]) (fun _ => rfl)).congr (by simp) rfl

theorem declareConst_payload (name : Tree.Symbol) (sort : Tree.«Sort»)
    (hvalid : sort.Valid (Bridge.version version)) {payload : List Parser.Internal.Input}
    (hs : Stands payload (.symbol name :: sort.tokens)) :
    PayloadRuns points version (Payload.init .declareConst version)
      (payload ++ [.parenClose])
      (adaptRun (do
        take points (.symbol name)
        let handled ← Traversal.sort points h sort
        take points .parenClose
        Program.callUnit h (.commandDeclareConst name handled)))
      fun _ => pure (.done .command) := by
  obtain ⟨symbolToken, sortTokens, rfl, hsymbolToken, hsort⟩ := Stands.split_cons hs
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbolToken
  refine (Runs.append (first := [.symbol symbol]) (middle := fun _ => .declareConst symbol .init)
    (Runs.token_moreA (arrival := Parser.Command.Internal.Standard.payloadArrive)
    (by simp [payloadStep, Payload.init, Parser.Category.Token.Internal.expectSymbol])) fun _ =>
    part_then_close (h := h) (wrap := Payload.declareConst symbol)
      (final := fun r => .declareConst symbol r)
      (request := fun r => .commandDeclareConst (Bridge.symbol symbol) r) (by payload_step)
      ((sort_runs hA.toTermAgrees sort hvalid hsort []).congr rfl rfl)
      (fun r => by simp [finalCall, hA.commandDeclareConst]) (fun _ => rfl)).congr ?_ rfl
  simp [adaptRun_take hsymbolToken]

theorem declareFun_payload (name : Tree.Symbol) (parameters : List Tree.«Sort»)
    (result : Tree.«Sort»)
    (hparameters : Tree.«Sort».ValidAll (Bridge.version version) parameters)
    (hresult : result.Valid (Bridge.version version)) {payload : List Parser.Internal.Input}
    (hs : Stands payload (.symbol name :: paren (Tree.«Sort».tokensAll parameters) ++
      result.tokens)) :
    PayloadRuns points version (Payload.init .declareFun version)
      (payload ++ [.parenClose])
      (adaptRun (do
        takeAll points [.symbol name, .parenOpen]
        let handledParameters ← sorts points h parameters
        take points .parenClose
        let handledResult ← Traversal.sort points h result
        take points .parenClose
        Program.callUnit h (.commandDeclareFun name handledParameters handledResult)))
      fun _ => pure (.done .command) := by
  obtain ⟨symbolToken, rest, rfl, hsymbolToken, hrest⟩ := Stands.split_cons hs
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbolToken
  obtain ⟨listTokens, sortTokens, rfl, hlist, hsort⟩ := Stands.split hrest
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hlist
  rw [sort_tokensAll] at hinner
  obtain ⟨program, hprogram, -, hlistRuns⟩ := parenList_runs (maximum := none)
    (sort_element (points := points) (version := version) hA.toTermAgrees) parameters
    (sort_validAll hparameters) hinner (by simp)
  have hlistPayload := Runs.embedA (outer := payloadStep version)
      (outerArrival := Parser.Command.Internal.Standard.payloadArrive)
    (Payload.declareFunParameters symbol)
    (fun parameters => pure (.more (.declareFunResult symbol parameters .init)))
    (by payload_step) hlistRuns
  rw [show Parser.Internal.Input.symbol symbol :: (Parser.Internal.Input.parenOpen ::
      (inner ++ [.parenClose]) ++ sortTokens) ++
      [.parenClose] = [.symbol symbol] ++ ((Parser.Internal.Input.parenOpen ::
          (inner ++ [.parenClose])) ++
      (sortTokens ++ [.parenClose])) by simp]
  refine (Runs.append (middle := fun _ => .declareFunParameters symbol (ListState.paren .init))
    (Runs.token_moreA (arrival := Parser.Command.Internal.Standard.payloadArrive)
    (by simp [payloadStep, Payload.init, Parser.Category.Token.Internal.expectSymbol])) fun _ =>
    Runs.append (middle := fun parameters =>
        .declareFunResult symbol (parameters : List _).toArray .init)
      (hlistPayload.congr rfl (by funext; simp [Parser.Internal.Step.wrap])) fun parameters =>
      part_then_close (h := h) (wrap := Payload.declareFunResult symbol
          (parameters : List _).toArray)
        (final := fun r => .declareFun symbol (parameters : List _).toArray r)
        (request := fun r => .commandDeclareFun (Bridge.symbol symbol) parameters r)
        (by payload_step) ((sort_runs hA.toTermAgrees result hresult hsort []).congr rfl rfl)
        (fun r => by simp [finalCall, hA.commandDeclareFun]) (fun _ => rfl)).congr ?_ rfl
  simp only [List.map_id_fun, id_map] at hprogram
  simp [takeAll, sorts_eq_mapM, adaptRun_mapM, ← hprogram, adaptRun_take hsymbolToken,
    adaptRun_take (token := .parenOpen) rfl, adaptRun_take (token := .parenClose) rfl]

theorem defineSort_payload (name : Tree.Symbol) (parameters : List Tree.Symbol) (sort : Tree.«Sort»)
    (hvalid : sort.Valid (Bridge.version version)) {payload : List Parser.Internal.Input}
    (hs : Stands payload (.symbol name :: paren (parameters.map .symbol) ++ sort.tokens)) :
    PayloadRuns points version (Payload.init .defineSort version)
      (payload ++ [.parenClose])
      (adaptRun (do
        takeAll points [.symbol name, .parenOpen]
        takeAll points (parameters.map .symbol)
        take points .parenClose
        Program.callUnit h (.startDefineSort name parameters)
        let handled ← Traversal.sort points h sort
        take points .parenClose
        Program.callUnit h (.endDefineSort handled)))
      fun _ => pure (.done .command) := by
  obtain ⟨symbolToken, rest, rfl, hsymbolToken, hrest⟩ := Stands.split_cons hs
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbolToken
  obtain ⟨listTokens, sortTokens, rfl, hlist, hsort⟩ := Stands.split hrest
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hlist
  obtain ⟨symbols, hsymbols, rfl, hsymbolsRuns⟩ := symbols_runs (H := H) (points := points)
    parameters hinner
  have hlistRuns : Runs points (ListState.step () Parser.Category.Token.Internal.symbolStep none)
      (ListState.paren ())
      (.parenOpen :: (symbols.map .symbol ++ [.parenClose]))
      (ticks points (.parenOpen :: (symbols.map .symbol ++ [.parenClose])))
      fun _ => pure (.done (#[] ++ symbols.toArray)) := by
    refine (Runs.append (first := [.parenOpen]) ListState.open_runs fun _ =>
      Runs.append (hsymbolsRuns #[]) fun _ =>
        Runs.token (program := pure ())
          (next := fun _ => pure (.done (#[] ++ symbols.toArray)))
          (by simp [ListState.step, ListState.between])).congr ?_ rfl
    simp [ticks_append]
  have hlistPayload := Runs.bind_next
    (following := fun _ => Parser.Internal.call (Traits.CommandHandler.startDefineSort (H := H) symbol
      (Multiple.Symbols.Internal.new (#[] ++ symbols.toArray))))
    (next := fun _ => pure (.more (Payload.defineSortBody .init)))
    ((Runs.embedA (outer := payloadStep version)
        (outerArrival := Parser.Command.Internal.Standard.payloadArrive)
            (Payload.defineSortParameters symbol)
      (fun parameters => do
        Parser.Internal.call (Traits.CommandHandler.startDefineSort (H := H) symbol
          (Multiple.Symbols.Internal.new parameters))
        pure (.more (.defineSortBody .init)))
      (by payload_step) hlistRuns).congr rfl (by funext; simp [Parser.Internal.Step.wrap]))
  rw [show Parser.Internal.Input.symbol symbol :: (Parser.Internal.Input.parenOpen ::
      (symbols.map .symbol ++ [.parenClose]) ++
      sortTokens) ++ [.parenClose] = [.symbol symbol] ++
      ((Parser.Internal.Input.parenOpen :: (symbols.map .symbol ++ [.parenClose])) ++
      (sortTokens ++ [.parenClose])) by simp]
  refine (Runs.append (middle := fun _ => .defineSortParameters symbol (ListState.paren ()))
    (Runs.token_moreA (arrival := Parser.Command.Internal.Standard.payloadArrive)
    (by simp [payloadStep, Payload.init, Parser.Category.Token.Internal.expectSymbol])) fun _ =>
    Runs.append (middle := fun _ => .defineSortBody .init) hlistPayload fun _ =>
      part_then_close (h := h) (wrap := Payload.defineSortBody)
        (final := fun r => .endDefineSort r) (request := fun r => .endDefineSort r)
        (by payload_step) ((sort_runs hA.toTermAgrees sort hvalid hsort []).congr rfl rfl)
        (fun r => by simp [finalCall, hA.endDefineSort]) (fun _ => rfl)).congr ?_ rfl
  simp only [adaptRun_bind]
  rw [adaptRun_takeAll hinner]
  simp [takeAll, ← hsymbols, hA.startDefineSort, ticks_append,
    adaptRun_take hsymbolToken, adaptRun_take (token := .parenOpen) rfl,
    adaptRun_take (token := .parenClose) rfl]
theorem defineConst_payload (name : Tree.Symbol) (sort : Tree.«Sort») (body : Tree.Term)
    (hsortValid : sort.Valid (Bridge.version version))
    (hbodyValid : body.Valid (Bridge.version version)) {payload : List Parser.Internal.Input}
    (hs : Stands payload (.symbol name :: sort.tokens ++ body.tokens)) :
    PayloadRuns points version (Payload.init .defineConst version)
      (payload ++ [.parenClose])
      (adaptRun (do
        take points (.symbol name)
        let handledSort ← Traversal.sort points h sort
        let handledBody ← Traversal.term points h body
        take points .parenClose
        Program.callUnit h (.commandDefineConst name handledSort handledBody)))
      fun _ => pure (.done .command) := by
  obtain ⟨front, bodyTokens, rfl, hfront, hbody⟩ := Stands.split hs
  obtain ⟨symbolToken, sortTokens, rfl, hsymbolToken, hsort⟩ := Stands.split_cons hfront
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbolToken
  have hsortPayload := Runs.embedA (outer := payloadStep version)
      (outerArrival := Parser.Command.Internal.Standard.payloadArrive)
    (Payload.defineConstSort symbol)
    (fun sort => pure (.more (.defineBody (.defineConst symbol sort) .init)))
    (by payload_step) (sort_runs (points := points) hA.toTermAgrees sort hsortValid hsort [])
  rw [show Parser.Internal.Input.symbol symbol :: sortTokens ++ bodyTokens ++ [.parenClose] =
      [.symbol symbol] ++ (sortTokens ++ (bodyTokens ++ [.parenClose])) by simp]
  refine (Runs.append (middle := fun _ => .defineConstSort symbol .init)
    (Runs.token_moreA (arrival := Parser.Command.Internal.Standard.payloadArrive)
    (by simp [payloadStep, Payload.init, Parser.Category.Token.Internal.expectSymbol])) fun _ =>
    Runs.append (middle := fun r => .defineBody (.defineConst symbol r) .init)
      (hsortPayload.congr rfl (by funext; simp [Parser.Internal.Step.wrap, sortPush])) fun r =>
      part_then_close (h := h) (wrap := Payload.defineBody (.defineConst symbol r))
        (final := fun t => .defineConst symbol r t)
        (request := fun t => .commandDefineConst (Bridge.symbol symbol) r t)
        (by payload_step) (term_runs_init hA.toTermAgrees body hbodyValid hbody)
        (fun t => by simp [finalCall, hA.commandDefineConst]) (fun _ => rfl)).congr ?_ rfl
  simp [adaptRun_take hsymbolToken]

/-- `define-fun` and `define-fun-rec`: the signature, its start, the body, its end. -/
theorem definition_payload (definition : Parser.Command.Internal.Definition.DefinitionEnd
    (Traits.Handler.«Sort» H))
    (start : Multiple.FunctionSignature (Traits.Handler.«Sort» H) → PM H Unit)
    (final : Traits.Handler.Term H → FinalCall (Traits.Handler.Attribute H)
      (Traits.Handler.«Sort» H) (Traits.Handler.Term H))
    (hsignatureStep : ∀ state token,
      payloadStep version (.defineSignature definition state) token =
        Parser.Command.Internal.Function.signatureStep version state token
            >>= Parser.Internal.Step.wrap
            (.defineSignature definition)
          fun signature => start signature >>= fun _ =>
            pure (.more (.defineBody definition .init)))
    (hbodyStep : ∀ state token, payloadStep version (.defineBody definition state) token =
      Parser.Category.Term.Internal.termStep version state token >>= Parser.Internal.Step.wrap
          (.defineBody definition)
        fun body => pure (.more (.closing (final body))))
    {request : Traits.Handler.Term H → Call (valuesOf H) .nothing}
    (hrequest : ∀ body, finalCall (final body) = Parser.Internal.call
        (Bridge.callUnit h (request body)))
    (houtcome : ∀ body, finalOutcome (final body) = .command)
    (functionDef : Tree.FunctionDef) (hvalid : functionDef.Valid (Bridge.version version))
    {payload : List Parser.Internal.Input} (hs : Stands payload functionDef.tokens) :
    ∃ program : PM H (Multiple.FunctionSignature (Traits.Handler.«Sort» H)),
      Bridge.signature <$> program = adaptRun (Traversal.signature points h functionDef.symbol
        functionDef.parameters functionDef.result) ∧
      PayloadRuns points version (.defineSignature definition .start)
        (payload ++ [.parenClose])
        (do
          let signature ← program
          start signature
          let body ← adaptRun (Traversal.term points h functionDef.body)
          adaptRun (do take points .parenClose; Program.callUnit h (request body)))
        fun _ => pure (.done .command) := by
  obtain ⟨symbol, parameters, result, body⟩ := functionDef
  obtain ⟨hparameters, hresult, hbody⟩ := hvalid
  obtain ⟨front, bodyTokens, rfl, hfront, hbodyTokens⟩ := Stands.split hs
  obtain ⟨program, hprogram, hruns⟩ := signature_runs (points := points) hA.toTermAgrees symbol
    parameters result hparameters hresult hfront
  have hsignature := Runs.bind_next (following := start)
    (next := fun _ => pure (.more (Payload.defineBody definition .init)))
    ((Runs.embedA (outer := payloadStep version)
        (outerArrival := Parser.Command.Internal.Standard.payloadArrive)
        (Payload.defineSignature definition)
      (fun signature => start signature >>= fun _ =>
        pure (.more (.defineBody definition .init)))
      hsignatureStep hruns).congr rfl (by funext; simp [Parser.Internal.Step.wrap]))
  refine ⟨program, hprogram, ?_⟩
  rw [List.append_assoc]
  exact (Runs.append (middle := fun _ => .defineBody definition .init) hsignature fun _ =>
    part_then_close (h := h) (wrap := Payload.defineBody definition) (final := final)
      (request := request) hbodyStep
      (term_runs_init hA.toTermAgrees body hbody hbodyTokens) hrequest houtcome).congr
    (by simp) rfl

theorem defineFun_payload (functionDef : Tree.FunctionDef)
    (hvalid : functionDef.Valid (Bridge.version version)) {payload : List Parser.Internal.Input}
    (hs : Stands payload functionDef.tokens) :
    PayloadRuns points version (Payload.init .defineFun version)
      (payload ++ [.parenClose])
      (adaptRun (do
        let handledSignature ← Traversal.signature points h functionDef.symbol
          functionDef.parameters functionDef.result
        Program.callUnit h (.startDefineFun handledSignature)
        let handledBody ← Traversal.term points h functionDef.body
        take points .parenClose
        Program.callUnit h (.endDefineFun handledBody)))
      fun _ => pure (.done .command) := by
  obtain ⟨program, hprogram, hruns⟩ := definition_payload hA .defineFun
    (fun signature => Parser.Internal.call (Traits.CommandHandler.startDefineFun signature))
    (fun body => .endDefineFun body) (by payload_step) (by payload_step)
    (request := fun body => .endDefineFun body)
    (fun body => by simp [finalCall, hA.endDefineFun]) (fun _ => rfl) functionDef hvalid hs
  refine hruns.congr ?_ rfl
  simp [← hprogram, hA.startDefineFun]

theorem defineFunRec_payload (functionDef : Tree.FunctionDef)
    (hvalid : functionDef.Valid (Bridge.version version)) {payload : List Parser.Internal.Input}
    (hs : Stands payload functionDef.tokens) :
    PayloadRuns points version (Payload.init .defineFunRec version)
      (payload ++ [.parenClose])
      (adaptRun (do
        let handledSignature ← Traversal.signature points h functionDef.symbol
          functionDef.parameters functionDef.result
        Program.callUnit h (.startDefineFunRec handledSignature)
        let handledBody ← Traversal.term points h functionDef.body
        take points .parenClose
        Program.callUnit h (.endDefineFunRec handledBody)))
      fun _ => pure (.done .command) := by
  obtain ⟨program, hprogram, hruns⟩ := definition_payload hA .defineFunRec
    (fun signature => Parser.Internal.call (Traits.CommandHandler.startDefineFunRec signature))
    (fun body => .endDefineFunRec body) (by payload_step) (by payload_step)
    (request := fun body => .endDefineFunRec body)
    (fun body => by simp [finalCall, hA.endDefineFunRec]) (fun _ => rfl) functionDef hvalid hs
  refine hruns.congr ?_ rfl
  simp [← hprogram, hA.startDefineFunRec]

/-- A list of terms with its own `(`, then the command's `)` and last call. -/
theorem terms_then_close {wrap : ListState (Parser.Category.Term.Internal.TermStateOf
    H) (Traits.Handler.Term H) →
      Parser.Command.Internal.Standard.PayloadOf H}
    {after : Array (Traits.Handler.Term H) → PM H (Parser.Internal.Step
    (Parser.Command.Internal.Standard.PayloadOf H) CommandOutcome)}
    (hstep : ∀ state token, payloadStep version (wrap state) token =
      state.step .init
          (Parser.Category.Term.Internal.termStep version) none token >>=
              Parser.Internal.Step.wrap wrap
          after)
    (terms : List Tree.Term) (hvalid : Tree.Term.ValidAll (Bridge.version version) terms)
    (final : Array (Traits.Handler.Term H) → FinalCall (Traits.Handler.Attribute H)
      (Traits.Handler.«Sort» H) (Traits.Handler.Term H))
    (hafter : ∀ l : List (Traits.Handler.Term H), l.length = terms.length →
      after l.toArray = pure (.more (.closing (final l.toArray))))
    {request : List (Traits.Handler.Term H) → Call (valuesOf H) .nothing}
    (hrequest : ∀ l : List (Traits.Handler.Term H),
      finalCall (final l.toArray) = Parser.Internal.call (Bridge.callUnit h (request l)))
    (houtcome : ∀ l, finalOutcome (final l) = .command)
    {payload : List Parser.Internal.Input} (hs : Stands payload (paren (Tree.Term.tokensAll terms)))
    (hwrap : ∀ state token, Parser.Command.Internal.Standard.payloadArrive (wrap state) token = pure
        () := by
      intros; rfl) :
    PayloadRuns points version (wrap (ListState.paren .init)) (payload ++ [.parenClose])
      (adaptRun (do
        take points .parenOpen
        let handled ← Traversal.terms points h terms
        takeAll points [.parenClose, .parenClose]
        Program.callUnit h (request handled)))
      fun _ => pure (.done .command) := by
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
  rw [term_tokensAll] at hinner
  obtain ⟨program, hprogram, hlength, hlistRuns⟩ := parenList_runs (maximum := none)
    (term_element (points := points) (version := version) hA.toTermAgrees) terms
    (term_validAll hvalid) hinner (by simp)
  have hlistPayload := Runs.congr_length (Runs.embedA (outer := payloadStep version)
    (outerArrival := Parser.Command.Internal.Standard.payloadArrive) wrap after hstep
    hlistRuns hwrap)
      (HasLength.after (HasLength.bind_pure hlength _) _)
      (next' := fun l => pure (.more (.closing (final l.toArray))))
      (fun l hl => by simp [Parser.Internal.Step.wrap, hafter l hl])
  refine (Runs.append (middle := fun l => .closing (final (l : List _).toArray)) hlistPayload
    fun l => closing_runs (h := h) (request := request l) (final l.toArray) (hrequest l)
      (houtcome _)).congr ?_ rfl
  simp only [List.map_id_fun, id_map] at hprogram
  simp [takeAll, terms_eq_mapM, adaptRun_mapM, ← hprogram,
    adaptRun_take (token := .parenOpen) rfl, adaptRun_take (token := .parenClose) rfl]

theorem getValue_payload (valueTerms : List Tree.Term) (hne : valueTerms ≠ [])
    (hvalid : Tree.Term.ValidAll
        (Bridge.version version) valueTerms) {payload : List Parser.Internal.Input}
    (hs : Stands payload (paren (Tree.Term.tokensAll valueTerms))) :
    PayloadRuns points version (Payload.init .getValue version) (payload ++ [.parenClose])
      (adaptRun (do
        take points .parenOpen
        let handled ← Traversal.terms points h valueTerms
        takeAll points [.parenClose, .parenClose]
        Program.callUnit h (.commandGetValue handled)))
      fun _ => pure (.done .command) :=
  terms_then_close hA (wrap := Payload.getValue) (by payload_step) valueTerms hvalid
    (fun values => .getValue values)
    (fun l hl => by
      cases l with
      | nil => exact absurd (List.length_eq_zero_iff.mp hl.symm) hne
      | cons => rfl)
    (fun l => by simp [finalCall, hA.commandGetValue]) (fun _ => rfl) hs

theorem checkSatAssuming_payload (assumptions : List Tree.Term)
    (hversion : versionAtLeast (Bridge.version version) .v2_7)
    (hvalid : Tree.Term.ValidAll
        (Bridge.version version) assumptions) {payload : List Parser.Internal.Input}
    (hs : Stands payload (paren (Tree.Term.tokensAll assumptions))) :
    PayloadRuns points version (Payload.init .checkSatAssuming version)
      (payload ++ [.parenClose])
      (adaptRun (do
        take points .parenOpen
        let handled ← Traversal.terms points h assumptions
        takeAll points [.parenClose, .parenClose]
        Program.callUnit h (.commandCheckSatAssuming handled)))
      fun _ => pure (.done .command) := by
  have hinit : (Payload.init .checkSatAssuming version : Parser.Command.Internal.Standard.PayloadOf
      H) =
      .checkSatAssuming (ListState.paren .init) := by
    simp [Payload.init, versionAtLeast_v2_7 hversion]
  rw [hinit]
  exact terms_then_close hA (wrap := Payload.checkSatAssuming) (by payload_step) assumptions
    hvalid (fun terms => .checkSatAssuming terms) (fun _ _ => rfl)
    (fun l => by simp [finalCall, hA.commandCheckSatAssuming]) (fun _ => rfl) hs

end

end BSmtLib.Facts.Proofs.Parser.Commands.Terms
