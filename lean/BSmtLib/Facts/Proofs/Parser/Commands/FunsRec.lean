import BSmtLib.Facts.Proofs.Parser.Commands.Declarations

/-!
# `define-funs-rec` against the traversal

The bodies of `define-funs-rec` are a list of terms, as many as the functions, which the parser
holds with the signatures of the functions. A body's `start_recursive_body` is due when the
body's first token arrives, with the signature of its function: the list makes it at the
arrival of a token that is no `)` while a body is still due (`bodiesArrive`). A body's
`end_recursive_body` comes at its last token. The traversal makes each start at the arrival of
the body's first token too, so the run of the body is that of its term with the start due at the
first token's arrival (`term_runs_first_init`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Commands.FunsRec

open BSmtLibSpec.Grammar
open BSmtLib.Parser (Input PM Step)
open BSmtLib.Parser.Command.Standard (Payload FinalCall payloadStep finalCall)
open BSmtLib.Parser.Command (CommandOutcome)
open BSmtLib.Parser.Category.Combinator (ListState)
open BSmtLib.Parser.Category.Term (TermState)
open BSmtLib.Parser.Command.Function (bodyStep bodiesStep bodiesArrive functionDecStep)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Commands.Elements
open BSmtLib.Facts.Proofs.Parser.Commands.Elements.Runs BSmtLib.Facts.Proofs.Parser.Commands.Frame
open BSmtLib.Facts.Proofs.Parser.Commands.Parts BSmtLib.Facts.Proofs.Parser.Commands.Simple
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Lemmas
open BSmtLib.Facts.Proofs.Parser.List BSmtLib.Facts.Proofs.Parser.Term
open BSmtLib.Facts.Proofs.Parser.Tokens

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser (Program.callUnit)
open BSmtLibSpec.Facts.Proofs.Parser.Equations (recursiveBodies_cons)

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.CommandHandler H m]
variable {points : Points (StateT H m)} {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

/-- The list of bodies between bodies, after `found` of them. -/
abbrev bodiesBetween (found : Nat) : ListState (Parser.Category.Term.TermStateOf H) Unit :=
  ListState.between .init (Array.replicate found ())

/-- The list of bodies inside a body, after `found` of them. -/
abbrev bodiesInside (found : Nat) (state : Parser.Category.Term.TermStateOf H) :
    ListState (Parser.Category.Term.TermStateOf H) Unit :=
  { opened := true, outside := false, inner := state, items := Array.replicate found () }

/-- Two runs one after the other, the second for values of the first program's length only. -/
theorem Runs.append_length {σ ρ α β : Type} {step : σ → Input → PM H (Step σ ρ)} {state : σ}
    {first second : List Input} {program : PM H (List α)} {middle : List α → σ} {length : Nat}
    {following : List α → PM H β} {next : β → PM H (Step σ ρ)}
    {arrival : σ → Input → PM H Unit}
    (h₁ : Runs points step state first program (fun a => pure (.more (middle a))) arrival)
    (hlength : HasLength program length)
    (h₂ : ∀ a, a.length = length → Runs points step (middle a) second (following a) next arrival) :
    Runs points step state (first ++ second) (program >>= following) next arrival := by
  intro rest
  rw [List.append_assoc, h₁, bind_assoc]
  exact hlength _ _ fun l hl => by rw [resume_more, h₂ l hl]

/-- A program of values of a length, then an effect that depends on the value. -/
theorem _root_.BSmtLib.Facts.Proofs.Parser.Commands.Elements.HasLength.bind_effect {α : Type}
    {program : PM H (List α)} {length : Nat}
    (h : HasLength program length) (effect : List α → PM H Unit) :
    HasLength (program >>= fun l => effect l >>= fun _ => pure l) length := by
  intro _ K K' hK
  simp only [bind_assoc, pure_bind]
  exact h (fun l => effect l >>= fun _ => K l) (fun l => effect l >>= fun _ => K' l)
    fun l hl => by rw [hK l hl]

theorem replicate_push (found : Nat) :
    (Array.replicate found ()).push () = Array.replicate (found + 1) () := by
  apply Array.ext'
  simp [List.replicate_succ']

omit [LawfulMonad m] in
/-- Inside a body, the bodies parser steps as the body parser; at its end, it is between bodies. -/
theorem bodiesStep_inside (count found : Nat) (state : Parser.Category.Term.TermStateOf H)
    (token : Input) :
    bodiesStep count version (bodiesInside found state) token =
      bodyStep version state token >>= Step.wrap (bodiesInside found)
        fun _ => pure (.more (bodiesBetween (found + 1))) := by
  simp only [bodiesStep, ListState.step, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  congr 1
  funext step
  cases step with
  | more => simp [Step.wrap, bodiesInside]
  | done r =>
    cases r
    simp [Step.wrap, ListState.between, replicate_push]

omit [LawfulMonad m] in
/-- Between bodies, a token other than `)` steps as inside a body, with a body left. -/
theorem bodiesStep_between (count found : Nat) (token : Input) (htoken : token ≠ .parenClose)
    (hfits : found < count) :
    bodiesStep count version (bodiesBetween found) token =
      bodiesStep count version (bodiesInside found
          (TermState.init : Parser.Category.Term.TermStateOf H))
        token := by
  have hnot : ¬ count ≤ found := by omega
  have hstep : ListState.step (TermState.init : Parser.Category.Term.TermStateOf H)
      (bodyStep version)
      (some count) (bodiesBetween found) token =
      ListState.step TermState.init (bodyStep version) (some count)
        (bodiesInside found TermState.init) token := by
    cases token <;> first | exact absurd rfl htoken |
      simp [ListState.step, ListState.between, hnot]
  simp only [bodiesStep, hstep]

omit [LawfulMonad m] in
/-- Between bodies, the `)` ends them. -/
theorem bodiesStep_close (count found : Nat) :
    bodiesStep count version (bodiesBetween found : ListState
        (Parser.Category.Term.TermStateOf H) Unit)
        .parenClose =
      pure (.done (Array.replicate found ())) := by
  simp [bodiesStep, ListState.step, ListState.between]

omit [LawfulMonad m] in
/-- Between bodies, a token other than `)` starts the body that is due, with its signature. -/
theorem bodiesArrive_between (signatures : Array (Nodes.Signature (Traits.Handler.«Sort» H)))
    (found : Nat) {token : Input} (htoken : token ≠ .parenClose)
    {signature : Nodes.Signature (Traits.Handler.«Sort» H)}
    (hsignature : signatures[found]? = some signature) :
    bodiesArrive signatures (bodiesBetween found) token =
      Parser.call (Traits.CommandHandler.startRecursiveBody signature) := by
  simp only [bodiesArrive, ListState.between, Array.size_replicate, Bool.and_self, ↓reduceIte,
    hsignature]

/-- The body parser reads a body, its start due at its first token's arrival: the term, then
its end. -/
theorem body_runs (hA : Agrees h) (signature : Nodes.Signature (Traits.Handler.«Sort» H))
    (body : Tree.Term) (hvalid : body.Valid (Bridge.version version)) {tokens : List Input}
    (hs : Stands tokens body.tokens) :
    RunsFirst points (Parser.call (Traits.CommandHandler.startRecursiveBody signature))
      (bodyStep version) TermState.init tokens
      (do
        let result ← adaptRun (Traversal.term points h body
          (Program.callUnit h (.startRecursiveBody (Bridge.signature signature))))
        Parser.call (Traits.CommandHandler.endRecursiveBody result))
      fun _ => pure (.done ()) := by
  have hruns := term_runs_first_init (points := points) hA.toTermAgrees body hvalid hs
    (Program.callUnit h (.startRecursiveBody (Bridge.signature signature)))
  rw [adaptRun_callUnit, ← hA.startRecursiveBody] at hruns
  have hembed := RunsFirst.embed (outer := bodyStep version) id
    (fun body => Parser.call (Traits.CommandHandler.endRecursiveBody body) >>=
      fun _ => pure (.done ()))
    (fun state token => by
      simp only [bodyStep]
      congr 1
      funext step
      cases step <;> rfl) hruns
  exact RunsFirst.bind_next (hembed.congr rfl (by funext; simp [Step.wrap]))

/-- The bodies from the `found`-th on, each started at its first token's arrival with the
signature of its function. -/
theorem bodies_runs (hA : Agrees h)
    (signatures : Array (Nodes.Signature (Traits.Handler.«Sort» H))) :
    (bodies : List Tree.Term) → Tree.Term.ValidAll (Bridge.version version) bodies →
    ∀ {tokens : List Input}, Stands tokens (bodies.flatMap Tree.Term.tokens) →
    ∀ found, found + bodies.length = signatures.size →
    Runs points (bodiesStep signatures.size version) (bodiesBetween found) tokens
      (adaptRun (Traversal.recursiveBodies points h
        (((signatures.toList.drop found).map Bridge.signature).zip bodies)))
      (fun _ => pure (.more (bodiesBetween signatures.size))) (bodiesArrive signatures)
  | [], _, _, hs, found, hcount => by
    have := Stands.eq_nil hs
    subst this
    simp only [List.length_nil, Nat.add_zero] at hcount
    subst hcount
    exact (Runs.nil () (by simp)).congr (by simp [Traversal.recursiveBodies]) rfl
  | body :: rest, hvalid, _, hs, found, hcount => by
    simp only [List.flatMap_cons] at hs
    obtain ⟨first, others, rfl, hs₁, hs₂⟩ := Stands.split hs
    obtain ⟨token, tokens', rfl, htoken⟩ := Stands.first_of (term_first body) hs₁
    have hlt : found < signatures.size := by simp at hcount; omega
    have hsignature : signatures[found]? = some signatures[found] := by simp [hlt]
    have hfirst := Runs.ofFirst (points := points) (outer := bodiesStep signatures.size version)
      (outerArrival := bodiesArrive signatures) (bodiesInside found)
      (fun _ => pure (.more (bodiesBetween (found + 1)))) (start := bodiesBetween found)
      (by rw [bodiesStep_between _ _ _ htoken hlt, bodiesStep_inside])
      (bodiesStep_inside signatures.size found)
      (bodiesArrive_between signatures found htoken hsignature)
      (fun _ _ => rfl)
      (body_runs (points := points) hA signatures[found] body hvalid.1 hs₁)
    refine (Runs.append (middle := fun _ => bodiesBetween (found + 1))
      (hfirst.congr rfl (by funext; simp [Step.wrap])) fun _ =>
        bodies_runs hA signatures rest hvalid.2 hs₂ (found + 1)
          (by simp at hcount; omega)).congr ?_ rfl
    have hdrop : signatures.toList.drop found =
        signatures[found] :: signatures.toList.drop (found + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp
    rw [hdrop]
    simp [recursiveBodies_cons, hA.endRecursiveBody]

theorem defineFunsRec_payload (hA : Agrees h) (declarations : List Tree.FunctionDec)
    (bodies : List Tree.Term) (hne : declarations ≠ [])
    (hlength : declarations.length = bodies.length)
    (hdeclarations : ∀ declaration ∈ declarations, declaration.Valid (Bridge.version version))
    (hbodies : Tree.Term.ValidAll (Bridge.version version) bodies) {payload : List Input}
    (hs : Stands payload (paren (declarations.flatMap Tree.FunctionDec.tokens) ++
      paren (Tree.Term.tokensAll bodies))) :
    PayloadRuns points version (Payload.init .defineFunsRec version)
      (payload ++ [.parenClose])
      (adaptRun (do
        take points .parenOpen
        let signatures ← declarations.mapM fun declaration => do
          take points .parenOpen
          let handled ← Traversal.signature points h declaration.symbol declaration.parameters
            declaration.result
          take points .parenClose
          pure handled
        take points .parenClose
        Program.callUnit h (.startDefineFunsRec signatures)
        take points .parenOpen
        Traversal.recursiveBodies points h (signatures.zip bodies)
        takeAll points [.parenClose, .parenClose]
        Program.callUnit h .endDefineFunsRec))
      fun _ => pure (.done .command) := by
  obtain ⟨declarationList, bodyList, rfl, hdeclarationList, hbodyList⟩ := Stands.split hs
  obtain ⟨declarationInner, rfl, hdeclarationInner⟩ := Stands.split_paren hdeclarationList
  obtain ⟨bodyInner, rfl, hbodyInner⟩ := Stands.split_paren hbodyList
  rw [term_tokensAll] at hbodyInner
  obtain ⟨signatures, hsignatures, hsignaturesLength, hsignaturesRuns⟩ := parenList_runs
    (maximum := none) (functionDec_element (points := points) (version := version)
      hA.toTermAgrees) declarations hdeclarations hdeclarationInner (by simp)
  have hdeclarationsPayload := Runs.bind_next (Runs.congr_length
      (Runs.embedA (outer := payloadStep version)
    (outerArrival := Parser.Command.Standard.payloadArrive)
    Payload.defineFunsRecDeclarations
    (fun signatures => do
      if signatures.isEmpty then Parser.syntaxError .emptyFunctionSignatures
      Parser.call (Traits.CommandHandler.startDefineFunsRec signatures)
      return .more (.defineFunsRecBodies signatures (ListState.paren .init)))
    (by
      intro state token
      simp only [payloadStep]
      congr 1
      funext step
      cases step <;> simp [Step.wrap]) hsignaturesRuns)
      (HasLength.after (HasLength.bind_pure hsignaturesLength _) _)
      (next' := fun found =>
        (Parser.call (Traits.CommandHandler.startDefineFunsRec
          (found : List (Nodes.Signature (Traits.Handler.«Sort» H))).toArray) >>=
            fun _ => pure found) >>=
        fun found => pure (.more (.defineFunsRecBodies found.toArray (ListState.paren .init))))
      (fun found hfound => by
        cases found with
        | nil => exact absurd (List.length_eq_zero_iff.mp hfound.symm) hne
        | cons => simp [Step.wrap]))
  have hbodiesList : ∀ found : List (Nodes.Signature (Traits.Handler.«Sort» H)),
      found.length = bodies.length →
      Runs points (bodiesStep found.toArray.size version)
        (ListState.paren (TermState.init : Parser.Category.Term.TermStateOf H))
        (.parenOpen :: (bodyInner ++ [.parenClose]))
        (do
          tick points .parenOpen
          adaptRun (Traversal.recursiveBodies points h ((found.map Bridge.signature).zip bodies))
          tick points .parenClose)
        (fun _ => pure (.done (Array.replicate found.length ()))) (bodiesArrive found.toArray) := by
    intro found hfound
    rw [show Input.parenOpen :: (bodyInner ++ [.parenClose]) =
      [.parenOpen] ++ (bodyInner ++ [.parenClose]) by rfl]
    refine (Runs.append (middle := fun _ => bodiesBetween 0)
      (Runs.token_moreA (by simp [bodiesStep, ListState.step, ListState.paren,
          Parser.Category.Token.expectOpen,
        ListState.between])) fun _ =>
      Runs.append (middle := fun _ => bodiesBetween found.toArray.size)
        (bodies_runs hA found.toArray bodies hbodies hbodyInner 0 (by simp [hfound])) fun _ =>
        Runs.tokenA (program := pure ())
          (next := fun _ => pure (.done (Array.replicate found.length ())))
          (by rw [bodiesStep_close]; simp)
          (by simp [bodiesArrive, ListState.between])).congr ?_ rfl
    simp
  have hbodiesPayload : ∀ found : List (Nodes.Signature (Traits.Handler.«Sort» H)),
      found.length = bodies.length →
      PayloadRuns points version (.defineFunsRecBodies found.toArray (ListState.paren .init))
        (.parenOpen :: (bodyInner ++ [.parenClose]))
        (do
          tick points .parenOpen
          adaptRun (Traversal.recursiveBodies points h ((found.map Bridge.signature).zip bodies))
          tick points .parenClose)
        fun _ => pure (.more (.closing .endDefineFunsRec)) := by
    intro found hfound
    exact (Runs.embedA (outer := payloadStep version)
        (outerArrival := Parser.Command.Standard.payloadArrive)
      (Payload.defineFunsRecBodies found.toArray)
      (fun bodies => do
        if bodies.size != found.toArray.size then Parser.syntaxError .expectedFunctionBody
        return .more (.closing .endDefineFunsRec))
      (by
        intro state token
        simp only [payloadStep]
        congr 1
        funext step
        cases step <;> simp [Step.wrap]) (hbodiesList found hfound)).congr rfl
      (by funext; simp [Step.wrap])
  rw [show Input.parenOpen :: (declarationInner ++ [.parenClose]) ++
      Input.parenOpen :: (bodyInner ++ [.parenClose]) ++ [.parenClose] =
    (Input.parenOpen :: (declarationInner ++ [.parenClose])) ++
      ((Input.parenOpen :: (bodyInner ++ [.parenClose])) ++ [.parenClose]) by simp]
  refine (Runs.append_length
    (middle := fun found => .defineFunsRecBodies found.toArray (ListState.paren .init))
    hdeclarationsPayload
    (HasLength.bind_effect (HasLength.after (HasLength.bind_pure hsignaturesLength _) _) _)
    fun found hfound =>
    Runs.append (middle := fun _ => .closing .endDefineFunsRec)
      (hbodiesPayload found (by rw [hfound, hlength])) fun _ =>
      closing_runs (h := h) (request := .endDefineFunsRec) .endDefineFunsRec
        (by simp [finalCall, hA.endDefineFunsRec]) rfl).congr ?_ rfl
  simp only [adaptRun_bind, adaptRun_mapM] at hsignatures ⊢
  rw [← hsignatures]
  simp [takeAll, hA.startDefineFunsRec, adaptRun_take (token := .parenOpen) rfl,
    adaptRun_take (token := .parenClose) rfl]

end

end BSmtLib.Facts.Proofs.Parser.Commands.FunsRec
