module

public import BSmtLib.Facts.Proofs.Parser.TermParts
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.QualifiedIdent
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Token.Reserved

@[expose] public section
open BSmtLib.Parser.Category.Term.Internal

/-!
# The term parser's steps, one construct at a time

The lemmas of the term proof that need no recursion over terms: the steps of `termStep` in the
modes that run another parser (stated once, for `Runs.embed`); identifier terms; the head of an
application; the start of a binder of sorted variables, with its variables. The ones that read a
term inside (a binder's body, a binding, a case) take the run of that term as a hypothesis, so
that the recursive proof (`Facts.Proofs.Parser.Term`) only joins them.
-/

namespace BSmtLib.Facts.Proofs.Parser.TermHelpers

open BSmtLibSpec.Grammar
open BSmtLib.Parser.Internal (PM syntaxError)
open BSmtLib.Parser.Category.Term.Internal
    (TermState TermMode TermLevel TermStateOf TermLevelOf termStep termOpened termComplete startBinder endBinder SortedBinder BinderKind)
open BSmtLib.Parser.Category.QualifiedIdent.Internal (QualIdentState qualIdentStep)
open BSmtLib.Parser.Category.Combinator.Internal (ListState)
open BSmtLib.Parser.Category.SortedVar.Internal (SortedVarState sortedVarStep)
open BSmtLib.Parser.Category.Pattern.Internal (PatternState)
open BSmtLib.Parser.Category.Attribute.Internal (AttributeState attributeStep)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Lemmas
open BSmtLib.Facts.Proofs.Parser.List BSmtLib.Facts.Proofs.Parser.Reserved
open BSmtLib.Facts.Proofs.Parser.«Sort» BSmtLib.Facts.Proofs.Parser.TermParts
open BSmtLib.Facts.Proofs.Parser.Tokens BSmtLib.Facts.Proofs.Parser.Tokens.Stands

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser.Equations (term_identifier)
open BSmtLibSpec.Facts.Proofs.Parser (Program.callScope)

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
variable {points : Points (StateT H m)} {version : Version}

/-! ## The modes that run another parser -/

omit [LawfulMonad m] in
theorem termStep_qualIdent (levels : List (TermLevelOf H))
    (state : QualIdentState (Handler.«Sort» H)) (token : Parser.Internal.Input) :
    termStep version ({ mode := .qualIdent state, levels } : TermStateOf H) token =
      qualIdentStep version state token >>= Parser.Internal.Step.wrap
        (fun state => ({ mode := .qualIdent state, levels } : TermStateOf H))
        (fun r => do
          let term ← Parser.Internal.call (Handler.handleTerm (.qualifiedIdent r.1 r.2))
          termComplete levels term) := by
  simp only [termStep]
  congr 1
  funext step
  cases step <;> rfl

omit [LawfulMonad m] in
theorem termStep_applicationHead (levels : List (TermLevelOf H))
    (state : QualIdentState (Handler.«Sort» H)) (token : Parser.Internal.Input) :
    termStep version ({ mode := .applicationHead state, levels } : TermStateOf H) token =
      qualIdentStep version state token >>= Parser.Internal.Step.wrap
        (fun state => ({ mode := .applicationHead state, levels } : TermStateOf H))
        (fun r =>
          pure (.more { mode := .start, levels := .application r.1 r.2 #[] :: levels })) := by
  simp only [termStep]
  congr 1
  funext step
  cases step <;> rfl

/-- The check that a binder has variables, and its start. -/
def binderScope (binder : SortedBinder)
    (variables : Array (Lexicon.Value.Symbol × Handler.«Sort» H)) :
    PM H (Handler.Scope H) := do
  if variables.isEmpty then
    syntaxError (match binder with
      | .lambda => (.empty .lambdaVars)
      | _ => (.empty .quantifierVars))
  startBinder binder variables

/-- What the term parser does when a binder's variables are complete. -/
def binderStarted (levels : List (TermLevelOf H)) (binder : SortedBinder)
    (variables : Array (Lexicon.Value.Symbol × Handler.«Sort» H)) :
    PM H (Parser.Internal.Step (TermStateOf H) (Handler.Term H)) := do
  if variables.isEmpty then
    syntaxError (match binder with
      | .lambda => (.empty .lambdaVars)
      | _ => (.empty .quantifierVars))
  let scope ← startBinder binder variables
  return .more { mode := .start, levels := .binder (.sorted binder) scope :: levels }

theorem binderStarted_eq (levels : List (TermLevelOf H)) (binder : SortedBinder)
    (variables : Array (Lexicon.Value.Symbol × Handler.«Sort» H)) :
    binderStarted levels binder variables =
      binderScope binder variables >>= fun scope =>
        pure (.more { mode := .start, levels := .binder (.sorted binder) scope :: levels }) := by
  simp only [binderStarted, binderScope]
  split <;> simp only [bind_assoc]

omit [LawfulMonad m] in
theorem termStep_sortedVars (levels : List (TermLevelOf H)) (binder : SortedBinder)
    (state : ListState (SortedVarState (Handler.«Sort» H))
      (Lexicon.Value.Symbol × Handler.«Sort» H)) (token : Parser.Internal.Input) :
    termStep version ({ mode := .sortedVars binder state, levels } : TermStateOf H) token =
      state.step .start (sortedVarStep version) none token >>= Parser.Internal.Step.wrap
        (fun state => ({ mode := .sortedVars binder state, levels } : TermStateOf H))
        (binderStarted levels binder) := by
  simp only [termStep]
  congr 1
  funext step
  cases step <;> rfl

/-- What the term parser does when a case's pattern is complete. -/
def caseStarted (levels : List (TermLevelOf H)) (scrutinee : Handler.Term H)
    (cases : Array (Grammar.Nodes.Pattern × Handler.Term H)) (pattern : Grammar.Nodes.Pattern) :
    PM H (Parser.Internal.Step (TermStateOf H) (Handler.Term H)) := do
  let scope ← Parser.Internal.call (Handler.startMatchCase scrutinee pattern)
  return .more { mode := .start, levels := .matchCase scrutinee cases pattern scope :: levels }

omit [LawfulMonad m] in
theorem termStep_matchPattern (levels : List (TermLevelOf H)) (scrutinee : Handler.Term H)
    (cases : Array (Grammar.Nodes.Pattern × Handler.Term H)) (state : PatternState)
    (token : Parser.Internal.Input) :
    termStep version ({ mode := .matchPattern scrutinee cases state, levels } : TermStateOf H)
        token =
      state.step version token >>= Parser.Internal.Step.wrap
        (fun state => ({ mode := .matchPattern scrutinee cases state, levels } : TermStateOf H))
        (caseStarted levels scrutinee cases) := by
  simp only [termStep]
  congr 1
  funext step
  cases step <;> rfl

/-- What the term parser does when an annotation's attributes are complete. -/
def annotated (levels : List (TermLevelOf H)) (term : Handler.Term H)
    (attributes : Array (Handler.Attribute H)) :
    PM H (Parser.Internal.Step (TermStateOf H) (Handler.Term H)) := do
  if attributes.isEmpty then syntaxError (.empty .annotation)
  let annotated ← Parser.Internal.call (Handler.annotateTerm term (.new attributes))
  termComplete levels annotated

omit [LawfulMonad m] in
theorem termStep_annotating (levels : List (TermLevelOf H)) (term : Handler.Term H)
    (state : AttributeState (Handler.SExpr H) (Handler.Attribute H))
    (token : Parser.Internal.Input) :
    termStep version ({ mode := .annotating term state, levels } : TermStateOf H) token =
      attributeStep false version state token >>= Parser.Internal.Step.wrap
        (fun state => ({ mode := .annotating term state, levels } : TermStateOf H))
        (annotated levels term) := by
  simp only [termStep]
  congr 1
  funext step
  cases step <;> rfl

/-! ## Qualified identifiers -/

/-- The identifier of a qualified identifier. -/
def qualName : Tree.QualIdentifier → Tree.Identifier
  | .plain name => name
  | .as name _ => name

variable {h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H)}

/-- The tokens of a qualified identifier, and its sort if it is qualified. -/
def qualProgram (points : Points (StateT H m))
    (h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H)) :
    Tree.QualIdentifier →
      Run (StateT H m) (Handler.Error H) (Option (Handler.«Sort» H))
  | .plain name => do
    takeAll points name.tokens
    pure none
  | .as name qualification => do
    takeAll points [.parenOpen, word "as"]
    takeAll points name.tokens
    let sort ← Traversal.sort points h qualification
    take points .parenClose
    pure (some sort)

theorem qualIdentifier_eq (qualified : Tree.QualIdentifier) :
    Traversal.qualIdentifier points h qualified =
      (fun sort => (qualName qualified, sort)) <$> qualProgram points h qualified := by
  cases qualified <;> simp [Traversal.qualIdentifier, qualProgram, qualName]

/-- A qualified identifier as a term, with the calls `first` due at its first token's arrival:
the parser handles it at its last token. -/
theorem identifierTerm_runs (hA : TermAgrees h) {qualified : Tree.QualIdentifier}
    (hvalid : qualified.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens qualified.tokens)
    (first : Run (StateT H m) (Handler.Error H) Unit) (levels : List (TermLevelOf H)) :
    RunsFirst points (adaptRun first) (termStep version)
      ({ mode := .start, levels } : TermStateOf H) tokens
      (adaptRun (Traversal.term points h (.identifier qualified) first))
      fun r => termComplete levels r := by
  cases qualified with
  | plain name =>
    match name with
    | ⟨symbolName, []⟩ =>
      obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
      obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
      exact (RunsFirst.token (program := Parser.Internal.call (Handler.handleTerm
        (.qualifiedIdent ⟨symbol, #[]⟩ none))) (by simp [termStep])).congr
        (by simp [term_identifier, Traversal.qualIdentifier, Tree.Identifier.tokens,
          takeAllArriving_cons, adaptRun_receive htoken, adaptRun_takeAll (tokens := []) Stands.nil,
          hA.handleTerm, Bridge.termNode,
          Bridge.identifier]) rfl
    | ⟨symbolName, index :: indices⟩ =>
      obtain ⟨symbolToken, rest, rfl, hsymbol, hrest⟩ :=
        Stands.indexed (List.cons_ne_nil _ _) hs
      obtain ⟨head, hhead, hruns⟩ := qualIndexed_runs (H := H) (points := points) hvalid
        (List.cons_ne_nil _ _) hsymbol hrest
      have hembed := Runs.bind_next
        (following := fun _ =>
          Parser.Internal.call (Handler.handleTerm (.qualifiedIdent head none)))
        (next := termComplete levels)
        ((Runs.embed (outer := termStep version)
          (fun state => ({ mode := .qualIdent state, levels } : TermStateOf H)) _
          (termStep_qualIdent levels) hruns).congr rfl
              (by funext; simp [Parser.Internal.Step.wrap]))
      rw [show Parser.Internal.Input.parenOpen :: Parser.Internal.Input.reserved
          (.general .underscore) :: symbolToken ::
          (rest ++ [.parenClose]) = [.parenOpen] ++ ([.reserved (.general .underscore)] ++
          (symbolToken :: (rest ++ [.parenClose]))) by simp]
      refine (RunsFirst.append (middle := fun _ => ({ mode := .opened, levels } : TermStateOf H))
        (RunsFirst.token_more (by simp [termStep])) fun _ =>
          Runs.append (middle := fun _ =>
              ({ mode := .qualIdent (.indexed .afterUnderscore), levels } : TermStateOf H))
            (Runs.token_more (by simp [termStep, termOpened])) fun _ => hembed).congr ?_ rfl
      have htail : Stands (.reserved (.general .underscore) :: symbolToken ::
          (rest ++ [.parenClose]))
          (word "_" :: .symbol symbolName :: (index.tokens ++
            (indices.flatMap Tree.Index.tokens ++ [.parenClose]))) := by
        have := Stands.cons (token := .reserved (.general .underscore)) (syntaxToken := word "_")
          rfl (Stands.cons hsymbol (Stands.append hrest (Stands.cons (token := .parenClose)
            (syntaxToken := .parenClose) rfl nil)))
        simpa [List.flatMap_cons, List.append_assoc] using this
      simp [term_identifier, Traversal.qualIdentifier,
        identifier_tokens_indexed symbolName (List.cons_ne_nil index indices), paren,
        takeAllArriving_cons, adaptRun_receive (token := .parenOpen) rfl, adaptRun_takeAll htail,
        hA.handleTerm, Bridge.termNode, hhead, ticks_append]
  | as name qualification =>
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    obtain ⟨asToken, rest, rfl, has, hrest⟩ := Stands.split_cons hinner
    obtain ⟨identifierTokens, sortTokens, rfl, hs₁, hs₂⟩ := Stands.split hrest
    rw [Parser.Internal.Input.received_word (word := .general .as) has]
    obtain ⟨head, hhead, hruns⟩ := qualAs_runs (points := points) hA hvalid.1 hvalid.2 hs₁ hs₂
    have hembed := Runs.bind_next
      (following := fun sort =>
        Parser.Internal.call (Handler.handleTerm (.qualifiedIdent head (some sort))))
      (next := termComplete levels)
      ((Runs.embed (outer := termStep version)
        (fun state => ({ mode := .qualIdent state, levels } : TermStateOf H)) _
        (termStep_qualIdent levels) hruns).congr rfl (by funext; simp [Parser.Internal.Step.wrap]))
    rw [show Parser.Internal.Input.parenOpen :: (Parser.Internal.Input.reserved (.general .as) ::
        (identifierTokens ++
        sortTokens) ++ [.parenClose]) = [.parenOpen] ++ ([.reserved (.general .as)] ++
        (identifierTokens ++ (sortTokens ++ [.parenClose]))) by simp]
    refine (RunsFirst.append (middle := fun _ => ({ mode := .opened, levels } : TermStateOf H))
      (RunsFirst.token_more (by simp [termStep])) fun _ =>
        Runs.append (middle := fun _ =>
            ({ mode := .qualIdent (.qualifiedIdent .start), levels } : TermStateOf H))
          (Runs.token_more (by simp [termStep, termOpened])) fun _ => hembed).congr ?_ rfl
    simp [term_identifier, Traversal.qualIdentifier, adaptRun_takeAll hs₁, takeAllArriving_cons,
      adaptRun_receive (token := .parenOpen) rfl,
      adaptRun_takeAll (tokens := [.reserved (.general .as)]) (syntaxTokens := [word "as"])
        (Stands.cons rfl nil),
      adaptRun_take (token := .parenClose) rfl, hA.handleTerm, Bridge.termNode, hhead]

/-- The words that open a parenthesised qualified identifier, told apart. -/
theorem beq_words :
    (Token.Reserved.GeneralReserved.underscore == .underscore) = true ∧
      (Token.Reserved.GeneralReserved.as == .underscore) = false ∧
      (Token.Reserved.GeneralReserved.as == .as) = true := by
  decide

/--
The head of an application, from after the application's `(`: the parser reads a qualified
identifier and opens the application with it.
-/
theorem applicationHead_runs (hA : TermAgrees h) {qualified : Tree.QualIdentifier}
    (hvalid : qualified.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens qualified.tokens) (levels : List (TermLevelOf H)) :
    ∃ head : Grammar.Nodes.Ident, Bridge.identifier head = qualName qualified ∧
      Runs points (termStep version) ({ mode := .opened, levels } : TermStateOf H) tokens
        (adaptRun (qualProgram points h qualified))
        fun sort =>
          pure (.more { mode := .start, levels := .application head sort #[] :: levels }) := by
  cases qualified with
  | plain name =>
    match name with
    | ⟨symbolName, []⟩ =>
      obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
      obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
      refine ⟨⟨symbol, #[]⟩, by simp [Bridge.identifier, qualName], ?_⟩
      exact (Runs.token (program := pure none) (by simp [termStep, termOpened])).congr
        (by simp [qualProgram, Tree.Identifier.tokens,
          adaptRun_takeAll (Stands.cons htoken nil)]) rfl
    | ⟨symbolName, index :: indices⟩ =>
      obtain ⟨symbolToken, rest, rfl, hsymbol, hrest⟩ :=
        Stands.indexed (List.cons_ne_nil _ _) hs
      obtain ⟨head, hhead, hruns⟩ := qualIndexed_runs (H := H) (points := points) hvalid
        (List.cons_ne_nil _ _) hsymbol hrest
      refine ⟨head, hhead, ?_⟩
      have hembed := Runs.map_program (f := fun _ => (none : Option (Handler.«Sort» H)))
        (next := fun sort =>
          pure (.more { mode := .start, levels := .application head sort #[] :: levels }))
        ((Runs.embed (outer := termStep version)
          (fun state => ({ mode := .applicationHead state, levels } : TermStateOf H)) _
          (termStep_applicationHead levels) hruns).congr rfl
              (by funext; simp [Parser.Internal.Step.wrap]))
      rw [show Parser.Internal.Input.parenOpen :: Parser.Internal.Input.reserved
          (.general .underscore) :: symbolToken ::
          (rest ++ [.parenClose]) = [.parenOpen] ++ ([.reserved (.general .underscore)] ++
          (symbolToken :: (rest ++ [.parenClose]))) by simp]
      refine (Runs.append (middle := fun _ =>
          ({ mode := .applicationHead .opened, levels } : TermStateOf H))
        (Runs.token_more (by simp [termStep, termOpened])) fun _ =>
          Runs.append (middle := fun _ =>
              ({ mode := .applicationHead (.indexed .afterUnderscore), levels } :
                TermStateOf H))
            (Runs.token_more (by simp [termStep,
                Parser.Category.QualifiedIdent.Internal.qualIdentStep,
                Parser.Internal.Input.isWord, beq_words]))
            fun _ => hembed).congr ?_ rfl
      simp [qualProgram,
        adaptRun_takeAll (show Stands _ (Tree.Identifier.tokens ⟨symbolName, index :: indices⟩)
          from hs), ticks_append]
  | as name qualification =>
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    obtain ⟨asToken, rest, rfl, has, hrest⟩ := Stands.split_cons hinner
    obtain ⟨identifierTokens, sortTokens, rfl, hs₁, hs₂⟩ := Stands.split hrest
    rw [Parser.Internal.Input.received_word (word := .general .as) has]
    obtain ⟨head, hhead, hruns⟩ := qualAs_runs (points := points) hA hvalid.1 hvalid.2 hs₁ hs₂
    refine ⟨head, hhead, ?_⟩
    have hembed := Runs.map_program (f := some)
      (next := fun sort =>
        pure (.more { mode := .start, levels := .application head sort #[] :: levels }))
      ((Runs.embed (outer := termStep version)
        (fun state => ({ mode := .applicationHead state, levels } : TermStateOf H)) _
        (termStep_applicationHead levels) hruns).congr rfl
            (by funext; simp [Parser.Internal.Step.wrap]))
    rw [show Parser.Internal.Input.parenOpen :: (Parser.Internal.Input.reserved (.general .as) ::
        (identifierTokens ++
        sortTokens) ++ [.parenClose]) = [.parenOpen] ++ ([.reserved (.general .as)] ++
        (identifierTokens ++ (sortTokens ++ [.parenClose]))) by simp]
    refine (Runs.append (middle := fun _ =>
        ({ mode := .applicationHead .opened, levels } : TermStateOf H))
      (Runs.token_more (by simp [termStep, termOpened])) fun _ =>
        Runs.append (middle := fun _ =>
            ({ mode := .applicationHead (.qualifiedIdent .start), levels } : TermStateOf H))
          (Runs.token_more (by simp [termStep,
              Parser.Category.QualifiedIdent.Internal.qualIdentStep,
              Parser.Internal.Input.isWord, beq_words]))
          fun _ => hembed).congr ?_ rfl
    simp [qualProgram, adaptRun_takeAll hs₁,
      adaptRun_takeAll (tokens := [.parenOpen, .reserved (.general .as)])
        (syntaxTokens := [.parenOpen, word "as"]) (Stands.cons rfl (Stands.cons rfl nil)),
      adaptRun_take (token := .parenClose) rfl]

end
/-! ## Binders of sorted variables -/

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
variable {points : Points (StateT H m)} {version : Version}
variable {h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H)}

/-- The sorted variable parser at its start. -/
abbrev start₀ (H : Type) {m : Type → Type} [Handler H m] :
    SortedVarState (Handler.«Sort» H) :=
  .start

/-- The spec's start of a binder of sorted variables. -/
def specStart (h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H)) :
    SortedBinder → List (Tree.Symbol × Handler.«Sort» H) →
      Run (StateT H m) (Handler.Error H) (Handler.Scope H)
  | .quantifier quantifier, handled =>
    Program.callScope h (.startQuantifier (Bridge.quantifier quantifier) handled)
  | .lambda, handled => Program.callScope h (.startLambda handled)

/--
From after a binder's `(`, the parser reads its word and its sorted variables, and starts the
binder with all of them at their `)`.
-/
theorem binderStart_runs (hA : TermAgrees h) (binder : SortedBinder) {word : Parser.Internal.Input}
    {wordToken : BSmtLibSpec.Grammar.SyntaxToken}
    (hwordToken : Bridge.received word = some (.token wordToken))
    (hword : ∀ levels : List (TermLevelOf H),
      termStep version ({ mode := .opened, levels } : TermStateOf H) word =
        pure (.more { mode := .sortedVars binder (ListState.paren .start), levels }))
    (variables : List Tree.SortedVar)
    (hvalid : ∀ var ∈ variables, var.Valid (Bridge.version version)) (hne : variables ≠ [])
    {tokens : List Parser.Internal.Input} (hs : Stands tokens
        (variables.flatMap Tree.SortedVar.tokens))
    (levels : List (TermLevelOf H)) :
    Runs points (termStep version) ({ mode := .opened, levels } : TermStateOf H)
      (word :: .parenOpen :: (tokens ++ [.parenClose]))
      (adaptRun (do
        takeAll points [wordToken, .parenOpen]
        let handled ← Traversal.sortedVars points h variables
        take points .parenClose
        specStart h binder handled))
      fun scope =>
        pure (.more { mode := .start, levels := .binder (.sorted binder) scope :: levels }) := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.flatMap_cons] at hs
  obtain ⟨firstTokens, restTokens, rfl, hs₁, hs₂⟩ := Stands.split hs
  obtain ⟨symbol, sortTokens, rfl, hsymbol, -, hfirstRuns⟩ := sortedVar_runs (points := points)
    hA first (hvalid first (List.mem_cons_self ..)) hs₁
  obtain ⟨program, hprogram, hrestRuns⟩ := sortedVars_runs (points := points) hA rest
    (fun v hv => hvalid v (List.mem_cons_of_mem _ hv)) hs₂
  have hopen := ListState.open_runs (points := points)
    (init := (SortedVarState.start : SortedVarState (Handler.«Sort» H)))
    (inner := sortedVarStep version) (maximum := none)
  have hitem := ListState.item_runs_done (points := points) (maximum := none) #[]
    (by simp) (by simp) hfirstRuns
  have hclose : ∀ items : Array (Lexicon.Value.Symbol × Handler.«Sort» H),
      Runs points (ListState.step .start (sortedVarStep version) none)
        (ListState.between (start₀ H) items) [.parenClose]
        (do tick points .parenClose; pure items) fun items => pure (.done items) :=
    fun items => ListState.close_runs items
  have hlist := Runs.append (middle := fun _ => ListState.between (start₀ H) #[]) hopen fun _ =>
    Runs.append (middle := fun r => ListState.between (start₀ H) (#[].push r)) hitem fun r =>
      Runs.append (middle := fun (others : List (Lexicon.Value.Symbol × Handler.«Sort» H)) =>
          ListState.between (start₀ H) (#[].push r ++ others.toArray))
        (hrestRuns (#[].push r)) fun (others : List (Lexicon.Value.Symbol × Handler.«Sort» H)) =>
          hclose (#[].push r ++ others.toArray)
  have hembed := Runs.bind_next
    (following := binderScope binder)
    (next := fun scope =>
      pure (.more { mode := .start, levels := .binder (.sorted binder) scope :: levels }))
    ((Runs.embed (outer := termStep version)
      (fun state => ({ mode := .sortedVars binder state, levels } : TermStateOf H)) _
      (termStep_sortedVars levels binder) hlist).congr rfl (by
        funext
        simp [Parser.Internal.Step.wrap, binderStarted_eq]))
  rw [show word :: Parser.Internal.Input.parenOpen ::
      (Parser.Internal.Input.parenOpen :: Parser.Internal.Input.symbol symbol ::
      (sortTokens ++ [.parenClose]) ++ restTokens ++ [.parenClose]) =
      [word] ++ (Parser.Internal.Input.parenOpen ::
          (Parser.Internal.Input.parenOpen :: Parser.Internal.Input.symbol symbol ::
      (sortTokens ++ [.parenClose])) ++ (restTokens ++ [.parenClose])) by simp]
  refine (Runs.append (middle := fun _ =>
      ({ mode := .sortedVars binder (ListState.paren .start), levels } : TermStateOf H))
    (Runs.token_more (hword levels)) fun _ => hembed).congr ?_ rfl
  obtain ⟨firstSymbol, firstSort⟩ := first
  have hsymbolToken : Bridge.received (Parser.Internal.Input.symbol symbol) =
      some (.token (.symbol firstSymbol)) := by
    simp only at hsymbol
    simp [Bridge.received, hsymbol]
  cases binder <;>
  simp [binderScope, Traversal.sortedVars, ← hprogram, Bridge.specPairs, hsymbol, startBinder,
    specStart, Bridge.pairs, hA.startQuantifier, hA.startLambda,
    adaptRun_takeAll (tokens := [word, .parenOpen]) (Stands.cons hwordToken
      (Stands.cons (token := .parenOpen) rfl nil)),
    adaptRun_takeAll (tokens := [.parenOpen, .symbol symbol]) (Stands.cons
      (token := .parenOpen) rfl (Stands.cons hsymbolToken nil)),
    adaptRun_take (token := .parenClose) rfl]

/-! ## The parts that read a term inside -/

/-- The run of a term, from any stack, as `term_runs` states it. -/
def TermRuns (points : Points (StateT H m))
    (h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H))
    (version : Version) (tokens : List Parser.Internal.Input) (term : Tree.Term) : Prop :=
  ∀ levels : List (TermLevelOf H),
    Runs points (termStep version) ({ mode := .start, levels } : TermStateOf H) tokens
      (adaptRun (Traversal.term points h term))
      fun r => termComplete levels r

/-- The run of a term, from any stack, with any calls due at its first token's arrival. -/
def TermRunsFirst (points : Points (StateT H m))
    (h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H))
    (version : Version) (tokens : List Parser.Internal.Input) (term : Tree.Term) : Prop :=
  ∀ (first : Run (StateT H m) (Handler.Error H) Unit) (levels : List (TermLevelOf H)),
    RunsFirst points (adaptRun first) (termStep version)
      ({ mode := .start, levels } : TermStateOf H)
      tokens (adaptRun (Traversal.term points h term first))
      fun r => termComplete levels r

/-- With no call due at the first token's arrival, the run of a term as `TermRuns` states it. -/
theorem TermRunsFirst.plain {tokens : List Parser.Internal.Input} {term : Tree.Term}
    (hruns : TermRunsFirst points h version tokens term) : TermRuns points h version tokens term :=
  fun levels => RunsFirst.runs (by
    have := hruns (pure ()) levels
    rwa [adaptRun_pure] at this)

/-- A binder's body and its `)`: the body with the binder's level on top, then the end. -/
theorem binderBody_runs {tokens : List Parser.Internal.Input} {body : Tree.Term}
    (hbody : TermRuns points h version tokens body) (kind : BinderKind)
    (scope : Handler.Scope H) (levels : List (TermLevelOf H)) :
    Runs points (termStep version)
      ({ mode := .start, levels := .binder kind scope :: levels } : TermStateOf H)
      (tokens ++ [.parenClose])
      (do
        let result ← adaptRun (Traversal.term points h body)
        tick points .parenClose
        endBinder kind scope result)
      fun r => termComplete levels r :=
  Runs.append (middle := fun result =>
      ({ mode := .binderClose kind scope result, levels } : TermStateOf H))
    ((hbody (.binder kind scope :: levels)).congr rfl (by funext; simp [termComplete]))
    fun result => Runs.token (by simp [termStep, Parser.Category.Token.Internal.expectClose])

/--
A binding of a `let`, from between bindings: the parser reads `(` ⟨symbol⟩ ⟨term⟩ `)`, and adds
the symbol with the handled term to the bindings.
-/
theorem binding_runs {symbolToken : Parser.Internal.Input} {name : Tree.Symbol}
    {tokens : List Parser.Internal.Input}
    {bound : Tree.Term} (hsymbol : Bridge.received symbolToken = some (.token (.symbol name)))
    (hbound : TermRuns points h version tokens bound) :
    ∃ symbol : Lexicon.Value.Symbol, Bridge.symbol symbol = name ∧ symbolToken = .symbol symbol ∧
      ∀ (found : Array (Lexicon.Value.Symbol × Handler.Term H)) (levels : List (TermLevelOf H)),
      Runs points (termStep version) ({ mode := .letBindingOpen found, levels } : TermStateOf H)
        (.parenOpen :: symbolToken :: (tokens ++ [.parenClose]))
        (do
          tick points .parenOpen
          tick points symbolToken
          let result ← adaptRun (Traversal.term points h bound)
          tick points .parenClose
          pure (symbol, result))
        fun binding => pure (.more { mode := .letBindingOpen (found.push binding), levels }) := by
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbol
  refine ⟨symbol, rfl, rfl, fun found levels => ?_⟩
  rw [show Parser.Internal.Input.parenOpen :: Parser.Internal.Input.symbol symbol ::
      (tokens ++ [.parenClose]) =
    [.parenOpen] ++ ([.symbol symbol] ++ (tokens ++ [.parenClose])) by simp]
  exact Runs.append (middle := fun _ =>
      ({ mode := .letBindingSymbol found, levels } : TermStateOf H))
    (Runs.token_more (by simp [termStep])) fun _ =>
    Runs.append (middle := fun _ =>
        ({ mode := .start, levels := .letBinding found symbol :: levels } : TermStateOf H))
      (Runs.token_more (by simp [termStep, Parser.Category.Token.Internal.expectSymbol])) fun _ =>
      Runs.append (middle := fun result =>
          ({ mode := .letBindingClose (found.push (symbol, result)), levels } : TermStateOf H))
        ((hbound (.letBinding found symbol :: levels)).congr rfl
          (by funext; simp [termComplete])) fun result =>
        Runs.token (by simp [termStep, Parser.Category.Token.Internal.expectClose])

/--
A case of a `match`, from between cases: the parser reads `(` ⟨pattern⟩ ⟨term⟩ `)`, starts the
case with the scrutinee and the pattern at the pattern's last token, and ends it at its `)`.
-/
theorem case_runs {pattern : Tree.Pattern}
    (hpattern : pattern.Valid
        (Bridge.version version)) {patternTokens bodyTokens : List Parser.Internal.Input}
    {body : Tree.Term} (hs : Stands patternTokens pattern.tokens)
    (hbody : TermRuns points h version bodyTokens body) :
    ∃ parsed : Grammar.Nodes.Pattern, Bridge.pattern parsed = pattern ∧
      ∀ (scrutinee : Handler.Term H) (found : Array (Grammar.Nodes.Pattern × Handler.Term H))
        (levels : List (TermLevelOf H)),
      Runs points (termStep version)
        ({ mode := .matchCaseOpen scrutinee found, levels } : TermStateOf H)
        (.parenOpen :: (patternTokens ++ (bodyTokens ++ [.parenClose])))
        (do
          tick points .parenOpen
          ticks points patternTokens
          let scope ← Parser.Internal.call (Handler.startMatchCase scrutinee parsed)
          let result ← adaptRun (Traversal.term points h body)
          tick points .parenClose
          let handled ← Parser.Internal.call (Handler.endMatchCase scope scrutinee result)
          pure (parsed, handled))
        fun handledCase =>
          pure (.more { mode := .matchCaseOpen scrutinee (found.push handledCase), levels }) := by
  obtain ⟨parsed, hparsed, hruns⟩ := pattern_runs (H := H) (points := points) hpattern hs
  refine ⟨parsed, hparsed, fun scrutinee found levels => ?_⟩
  have hembed := Runs.bind_next
    (following := fun _ => Parser.Internal.call (Handler.startMatchCase scrutinee parsed))
    (next := fun scope =>
      pure (.more { mode := .start, levels := .matchCase scrutinee found parsed scope :: levels }))
    ((Runs.embed (outer := termStep version)
      (fun state => ({ mode := .matchPattern scrutinee found state, levels } : TermStateOf H)) _
      (termStep_matchPattern levels scrutinee found) hruns).congr rfl
      (by funext; simp [Parser.Internal.Step.wrap, caseStarted]))
  rw [show Parser.Internal.Input.parenOpen :: (patternTokens ++ (bodyTokens ++ [.parenClose])) =
    [.parenOpen] ++ (patternTokens ++ (bodyTokens ++ [.parenClose])) by simp]
  refine (Runs.append (middle := fun _ =>
      ({ mode := .matchPattern scrutinee found .start, levels } : TermStateOf H))
    (Runs.token_more (by simp [termStep])) fun _ =>
    Runs.append hembed fun scope =>
      Runs.append (middle := fun result =>
          ({ mode := .matchCaseClose scrutinee found parsed scope result, levels } :
            TermStateOf H))
        ((hbody (.matchCase scrutinee found parsed scope :: levels)).congr rfl
          (by funext; simp [termComplete])) fun result =>
        Runs.token (program := do
            let handled ← Parser.Internal.call (Handler.endMatchCase scope scrutinee result)
            pure (parsed, handled))
          (by simp [termStep, Parser.Category.Token.Internal.expectClose])).congr ?_ rfl
  simp

end

end BSmtLib.Facts.Proofs.Parser.TermHelpers
