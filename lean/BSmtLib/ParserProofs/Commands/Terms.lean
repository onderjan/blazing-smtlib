import BSmtLib.ParserProofs.Commands.Simple

/-!
# Commands of sorts and terms against the traversal

The payloads of the commands whose parts are sorts, terms, signatures and lists of them. A part
is read by its parser run inside a payload mode; a part that ends the payload is followed by the
command's `)` and last call (`part_then_close`).
-/

namespace BSmtLib.ParserProofs

open BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLib.Parser (Input PM Step CommandState Payload CommandOutcome FinalCall commandStep
  payloadStep finalCall ListState DefinitionEnd)
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.SpecChecks.Parser (Program.callUnit)

/-- The payload parser's step into a part's parser and on, in one of its modes. -/
macro "payload_step" : tactic =>
  `(tactic| (intro state token; simp only [payloadStep]; congr 1; funext step; cases step <;> rfl))

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Parser.CommandHandler H m]
variable {points : Points (StateT H m)} {version : BSmtLib.Version}
variable {h : Traversal.Handler (StateT H m) (Parser.Handler.Error H) (valuesOf H)}

/-- A part that ends the payload, run in a payload mode, then the command's `)` and last call. -/
theorem part_then_close {σ ρ : Type} {inner : σ → Input → PM H (Step σ ρ)} {init : σ}
    {wrap : σ → Parser.PayloadOf H}
    {final : ρ → FinalCall (Parser.Handler.Attribute H) (Parser.Handler.«Sort» H)
      (Parser.Handler.Term H)}
    (hstep : ∀ state token, payloadStep version (wrap state) token =
      inner state token >>= Step.wrap wrap fun r => pure (.more (.closing (final r))))
    {tokens : List Input} {program : PM H ρ}
    (hruns : Runs points inner init tokens program fun r => pure (.done r))
    {request : ρ → Call (valuesOf H) .nothing}
    (hfinal : ∀ r, finalCall (final r) = Parser.call (Bridge.callUnit h (request r)))
    (houtcome : ∀ r, finalOutcome (final r) = .command)
    (hwrap : ∀ state token, Parser.payloadArrive (wrap state) token = pure () := by
      intros; rfl) :
    PayloadRuns points version (wrap init) (tokens ++ [.parenClose])
      (do let r ← program; adaptRun (do take points .parenClose; Program.callUnit h (request r)))
      fun _ => pure (.done .command) :=
  Runs.append (middle := fun r => .closing (final r))
    ((Runs.embedA (outer := payloadStep version) (outerArrival := Parser.payloadArrive) wrap
      (fun r => pure (.more (.closing (final r)))) hstep hruns hwrap).congr rfl
      (by funext; simp [Step.wrap]))
    fun r => closing_runs (final r) (hfinal r) (houtcome r)

variable (hA : Agrees h)
include hA

theorem assert_payload (asserted : Tree.Term) (hvalid : asserted.Valid (Bridge.version version))
    {payload : List Input} (hs : Stands payload asserted.tokens) :
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

theorem declareConst_payload (name : Tree.Symbol) (sort : Tree.Sort)
    (hvalid : sort.Valid (Bridge.version version)) {payload : List Input}
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
  obtain ⟨symbol, rfl, rfl⟩ := Input.received_symbol hsymbolToken
  refine (Runs.append (first := [.symbol symbol]) (middle := fun _ => .declareConst symbol .init)
    (Runs.token_moreA (arrival := Parser.payloadArrive)
        (by simp [payloadStep, Payload.init, Parser.expectSymbol])) fun _ =>
    part_then_close (h := h) (wrap := Payload.declareConst symbol)
      (final := fun r => .declareConst symbol r)
      (request := fun r => .commandDeclareConst (Bridge.symbol symbol) r) (by payload_step)
      ((sort_runs hA.toTermAgrees sort hvalid hsort []).congr rfl rfl)
      (fun r => by simp [finalCall, hA.commandDeclareConst]) (fun _ => rfl)).congr ?_ rfl
  simp [adaptRun_take hsymbolToken]

theorem declareFun_payload (name : Tree.Symbol) (parameters : List Tree.Sort) (result : Tree.Sort)
    (hparameters : Tree.Sort.ValidAll (Bridge.version version) parameters)
    (hresult : result.Valid (Bridge.version version)) {payload : List Input}
    (hs : Stands payload (.symbol name :: paren (Tree.Sort.tokensAll parameters) ++
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
  obtain ⟨symbol, rfl, rfl⟩ := Input.received_symbol hsymbolToken
  obtain ⟨listTokens, sortTokens, rfl, hlist, hsort⟩ := Stands.split hrest
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hlist
  rw [sort_tokensAll] at hinner
  obtain ⟨program, hprogram, -, hlistRuns⟩ := parenList_runs (maximum := none)
    (sort_element (points := points) (version := version) hA.toTermAgrees) parameters
    (sort_validAll hparameters) hinner (by simp)
  have hlistPayload := Runs.embedA (outer := payloadStep version)
      (outerArrival := Parser.payloadArrive)
    (Payload.declareFunParameters symbol)
    (fun parameters => pure (.more (.declareFunResult symbol parameters .init)))
    (by payload_step) hlistRuns
  rw [show Input.symbol symbol :: (Input.parenOpen :: (inner ++ [.parenClose]) ++ sortTokens) ++
      [.parenClose] = [.symbol symbol] ++ ((Input.parenOpen :: (inner ++ [.parenClose])) ++
      (sortTokens ++ [.parenClose])) by simp]
  refine (Runs.append (middle := fun _ => .declareFunParameters symbol (ListState.paren .init))
    (Runs.token_moreA (arrival := Parser.payloadArrive)
        (by simp [payloadStep, Payload.init, Parser.expectSymbol])) fun _ =>
    Runs.append (middle := fun parameters =>
        .declareFunResult symbol (parameters : List _).toArray .init)
      (hlistPayload.congr rfl (by funext; simp [Step.wrap])) fun parameters =>
      part_then_close (h := h) (wrap := Payload.declareFunResult symbol (parameters : List _).toArray)
        (final := fun r => .declareFun symbol (parameters : List _).toArray r)
        (request := fun r => .commandDeclareFun (Bridge.symbol symbol) parameters r)
        (by payload_step) ((sort_runs hA.toTermAgrees result hresult hsort []).congr rfl rfl)
        (fun r => by simp [finalCall, hA.commandDeclareFun]) (fun _ => rfl)).congr ?_ rfl
  simp only [List.map_id_fun, id_map] at hprogram
  simp [takeAll, sorts_eq_mapM, adaptRun_mapM, ← hprogram, adaptRun_take hsymbolToken,
    adaptRun_take (token := .parenOpen) rfl, adaptRun_take (token := .parenClose) rfl]

theorem defineSort_payload (name : Tree.Symbol) (parameters : List Tree.Symbol) (sort : Tree.Sort)
    (hvalid : sort.Valid (Bridge.version version)) {payload : List Input}
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
  obtain ⟨symbol, rfl, rfl⟩ := Input.received_symbol hsymbolToken
  obtain ⟨listTokens, sortTokens, rfl, hlist, hsort⟩ := Stands.split hrest
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hlist
  obtain ⟨symbols, hsymbols, rfl, hsymbolsRuns⟩ := symbols_runs (H := H) (points := points)
    parameters hinner
  have hlistRuns : Runs points (ListState.step () Parser.symbolStep none) (ListState.paren ())
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
    (following := fun _ => Parser.call (Parser.CommandHandler.startDefineSort (H := H) symbol
      (#[] ++ symbols.toArray)))
    (next := fun _ => pure (.more (Payload.defineSortBody .init)))
    ((Runs.embedA (outer := payloadStep version)
        (outerArrival := Parser.payloadArrive) (Payload.defineSortParameters symbol)
      (fun parameters => do
        Parser.call (Parser.CommandHandler.startDefineSort (H := H) symbol parameters)
        pure (.more (.defineSortBody .init)))
      (by payload_step) hlistRuns).congr rfl (by funext; simp [Step.wrap]))
  rw [show Input.symbol symbol :: (Input.parenOpen :: (symbols.map .symbol ++ [.parenClose]) ++
      sortTokens) ++ [.parenClose] = [.symbol symbol] ++
      ((Input.parenOpen :: (symbols.map .symbol ++ [.parenClose])) ++
      (sortTokens ++ [.parenClose])) by simp]
  refine (Runs.append (middle := fun _ => .defineSortParameters symbol (ListState.paren ()))
    (Runs.token_moreA (arrival := Parser.payloadArrive)
        (by simp [payloadStep, Payload.init, Parser.expectSymbol])) fun _ =>
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
theorem defineConst_payload (name : Tree.Symbol) (sort : Tree.Sort) (body : Tree.Term)
    (hsortValid : sort.Valid (Bridge.version version))
    (hbodyValid : body.Valid (Bridge.version version)) {payload : List Input}
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
  obtain ⟨symbol, rfl, rfl⟩ := Input.received_symbol hsymbolToken
  have hsortPayload := Runs.embedA (outer := payloadStep version)
      (outerArrival := Parser.payloadArrive)
    (Payload.defineConstSort symbol)
    (fun sort => pure (.more (.defineBody (.defineConst symbol sort) .init)))
    (by payload_step) (sort_runs (points := points) hA.toTermAgrees sort hsortValid hsort [])
  rw [show Input.symbol symbol :: sortTokens ++ bodyTokens ++ [.parenClose] =
      [.symbol symbol] ++ (sortTokens ++ (bodyTokens ++ [.parenClose])) by simp]
  refine (Runs.append (middle := fun _ => .defineConstSort symbol .init)
    (Runs.token_moreA (arrival := Parser.payloadArrive)
        (by simp [payloadStep, Payload.init, Parser.expectSymbol])) fun _ =>
    Runs.append (middle := fun r => .defineBody (.defineConst symbol r) .init)
      (hsortPayload.congr rfl (by funext; simp [Step.wrap, sortPush])) fun r =>
      part_then_close (h := h) (wrap := Payload.defineBody (.defineConst symbol r))
        (final := fun t => .defineConst symbol r t)
        (request := fun t => .commandDefineConst (Bridge.symbol symbol) r t)
        (by payload_step) (term_runs_init hA.toTermAgrees body hbodyValid hbody)
        (fun t => by simp [finalCall, hA.commandDefineConst]) (fun _ => rfl)).congr ?_ rfl
  simp [adaptRun_take hsymbolToken]

/-- `define-fun` and `define-fun-rec`: the signature, its start, the body, its end. -/
theorem definition_payload (definition : Parser.DefinitionEnd (Parser.Handler.«Sort» H))
    (start : Parser.Signature (Parser.Handler.«Sort» H) → PM H Unit)
    (final : Parser.Handler.Term H → FinalCall (Parser.Handler.Attribute H)
      (Parser.Handler.«Sort» H) (Parser.Handler.Term H))
    (hsignatureStep : ∀ state token,
      payloadStep version (.defineSignature definition state) token =
        Parser.signatureStep version state token >>= Step.wrap (.defineSignature definition)
          fun signature => start signature >>= fun _ =>
            pure (.more (.defineBody definition .init)))
    (hbodyStep : ∀ state token, payloadStep version (.defineBody definition state) token =
      Parser.termStep version state token >>= Step.wrap (.defineBody definition)
        fun body => pure (.more (.closing (final body))))
    {request : Parser.Handler.Term H → Call (valuesOf H) .nothing}
    (hrequest : ∀ body, finalCall (final body) = Parser.call (Bridge.callUnit h (request body)))
    (houtcome : ∀ body, finalOutcome (final body) = .command)
    (functionDef : Tree.FunctionDef) (hvalid : functionDef.Valid (Bridge.version version))
    {payload : List Input} (hs : Stands payload functionDef.tokens) :
    ∃ program : PM H (Parser.Signature (Parser.Handler.«Sort» H)),
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
        (outerArrival := Parser.payloadArrive) (Payload.defineSignature definition)
      (fun signature => start signature >>= fun _ =>
        pure (.more (.defineBody definition .init)))
      hsignatureStep hruns).congr rfl (by funext; simp [Step.wrap]))
  refine ⟨program, hprogram, ?_⟩
  rw [List.append_assoc]
  exact (Runs.append (middle := fun _ => .defineBody definition .init) hsignature fun _ =>
    part_then_close (h := h) (wrap := Payload.defineBody definition) (final := final)
      (request := request) hbodyStep
      (term_runs_init hA.toTermAgrees body hbody hbodyTokens) hrequest houtcome).congr
    (by simp) rfl

theorem defineFun_payload (functionDef : Tree.FunctionDef)
    (hvalid : functionDef.Valid (Bridge.version version)) {payload : List Input}
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
    (fun signature => Parser.call (Parser.CommandHandler.startDefineFun signature))
    (fun body => .endDefineFun body) (by payload_step) (by payload_step)
    (request := fun body => .endDefineFun body)
    (fun body => by simp [finalCall, hA.endDefineFun]) (fun _ => rfl) functionDef hvalid hs
  refine hruns.congr ?_ rfl
  simp [← hprogram, hA.startDefineFun]

theorem defineFunRec_payload (functionDef : Tree.FunctionDef)
    (hvalid : functionDef.Valid (Bridge.version version)) {payload : List Input}
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
    (fun signature => Parser.call (Parser.CommandHandler.startDefineFunRec signature))
    (fun body => .endDefineFunRec body) (by payload_step) (by payload_step)
    (request := fun body => .endDefineFunRec body)
    (fun body => by simp [finalCall, hA.endDefineFunRec]) (fun _ => rfl) functionDef hvalid hs
  refine hruns.congr ?_ rfl
  simp [← hprogram, hA.startDefineFunRec]

/-- A list of terms with its own `(`, then the command's `)` and last call. -/
theorem terms_then_close {wrap : ListState (Parser.TermStateOf H) (Parser.Handler.Term H) →
      Parser.PayloadOf H}
    {after : Array (Parser.Handler.Term H) → PM H (Step (Parser.PayloadOf H) CommandOutcome)}
    (hstep : ∀ state token, payloadStep version (wrap state) token =
      state.step .init (Parser.termStep version) none token >>= Step.wrap wrap after)
    (terms : List Tree.Term) (hvalid : Tree.Term.ValidAll (Bridge.version version) terms)
    (final : Array (Parser.Handler.Term H) → FinalCall (Parser.Handler.Attribute H)
      (Parser.Handler.«Sort» H) (Parser.Handler.Term H))
    (hafter : ∀ l : List (Parser.Handler.Term H), l.length = terms.length →
      after l.toArray = pure (.more (.closing (final l.toArray))))
    {request : List (Parser.Handler.Term H) → Call (valuesOf H) .nothing}
    (hrequest : ∀ l : List (Parser.Handler.Term H),
      finalCall (final l.toArray) = Parser.call (Bridge.callUnit h (request l)))
    (houtcome : ∀ l, finalOutcome (final l) = .command)
    {payload : List Input} (hs : Stands payload (paren (Tree.Term.tokensAll terms)))
    (hwrap : ∀ state token, Parser.payloadArrive (wrap state) token = pure () := by
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
  have hlistPayload := (Runs.embedA (outer := payloadStep version)
    (outerArrival := Parser.payloadArrive) wrap after hstep
    hlistRuns hwrap).congr_length
      (HasLength.after (HasLength.bind_pure hlength _) _)
      (next' := fun l => pure (.more (.closing (final l.toArray))))
      (fun l hl => by simp [Step.wrap, hafter l hl])
  refine (Runs.append (middle := fun l => .closing (final (l : List _).toArray)) hlistPayload
    fun l => closing_runs (h := h) (request := request l) (final l.toArray) (hrequest l)
      (houtcome _)).congr ?_ rfl
  simp only [List.map_id_fun, id_map] at hprogram
  simp [takeAll, terms_eq_mapM, adaptRun_mapM, ← hprogram,
    adaptRun_take (token := .parenOpen) rfl, adaptRun_take (token := .parenClose) rfl]

theorem getValue_payload (valueTerms : List Tree.Term) (hne : valueTerms ≠ [])
    (hvalid : Tree.Term.ValidAll (Bridge.version version) valueTerms) {payload : List Input}
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
    (hvalid : Tree.Term.ValidAll (Bridge.version version) assumptions) {payload : List Input}
    (hs : Stands payload (paren (Tree.Term.tokensAll assumptions))) :
    PayloadRuns points version (Payload.init .checkSatAssuming version)
      (payload ++ [.parenClose])
      (adaptRun (do
        take points .parenOpen
        let handled ← Traversal.terms points h assumptions
        takeAll points [.parenClose, .parenClose]
        Program.callUnit h (.commandCheckSatAssuming handled)))
      fun _ => pure (.done .command) := by
  have hinit : (Payload.init .checkSatAssuming version : Parser.PayloadOf H) =
      .checkSatAssuming (ListState.paren .init) := by
    simp [Payload.init, versionAtLeast_v2_7 hversion]
  rw [hinit]
  exact terms_then_close hA (wrap := Payload.checkSatAssuming) (by payload_step) assumptions
    hvalid (fun terms => .checkSatAssuming terms) (fun _ _ => rfl)
    (fun l => by simp [finalCall, hA.commandCheckSatAssuming]) (fun _ => rfl) hs

end

end BSmtLib.ParserProofs
