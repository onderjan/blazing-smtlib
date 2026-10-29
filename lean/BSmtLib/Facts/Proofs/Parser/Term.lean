module

public import BSmtLib.Facts.Proofs.Parser.TermHelpers
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Lexicon.Reserved
import all BSmtLib.Parser.Category.Token

@[expose] public section

/-!
# The term parser against the traversal

The term parser is a stack parser like the sort and S-expression parsers, and its proof has
their shape (see `Facts.Proofs.Parser.SExpr`): `term_runs` holds for every stack of levels, with the
parser's own "a term is complete" step (`termComplete`) as the continuation; the items of a level
are a lemma of their own, from the stack with that level on top (`terms_runs` for the arguments
of an application, `bindings_runs` for the bindings of a `let`, `cases_runs` for the cases of a
`match`); the four go by recursion over the tree. A level whose parser checks that it has a part
has its first part read by `term_runs` or a single-part lemma, so that the check is decided by
the state, and the rest by the list lemma.

The parts that need no recursion over terms are in `Facts.Proofs.Parser.TermHelpers`; here they are
joined.
-/

namespace BSmtLib.Facts.Proofs.Parser.Term

open BSmtLibSpec.Grammar
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.Term.Internal
    (TermState TermMode TermLevel TermStateOf TermLevelOf termStep termOpened termComplete startBinder endBinder SortedBinder BinderKind)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Attribute BSmtLib.Facts.Proofs.Parser.Drive
open BSmtLib.Facts.Proofs.Parser.Lemmas BSmtLib.Facts.Proofs.Parser.Reserved
open BSmtLib.Facts.Proofs.Parser.TermHelpers BSmtLib.Facts.Proofs.Parser.TermParts
open BSmtLib.Facts.Proofs.Parser.Tokens BSmtLib.Facts.Proofs.Parser.Tokens.Stands

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser.Equations (term_constant term_application term_let term_lambda
    term_quantified term_match term_annotated cases_cons)

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
variable {points : Points (StateT H m)} {σ ρ α β : Type}

omit [LawfulMonad m] in
/-- A run over tokens is a run over any list equal to them. -/
theorem _root_.BSmtLib.Facts.Proofs.Parser.Drive.Runs.tokens_eq
    {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)} {state : σ}
    {tokens tokens' : List Parser.Internal.Input} {program : PM H α} {next : α → PM H
        (Parser.Internal.Step σ ρ)}
    (h : Runs points step state tokens program next) (heq : tokens = tokens') :
    Runs points step state tokens' program next :=
  heq ▸ h

/-- A run whose program is a pure function of another's is a run of that other. -/
theorem _root_.BSmtLib.Facts.Proofs.Parser.Drive.Runs.of_map_program
    {step : σ → Parser.Internal.Input → PM H (Parser.Internal.Step σ ρ)} {state : σ}
    {tokens : List Parser.Internal.Input} {program : PM H α} {f : α → β} {next : β → PM H
        (Parser.Internal.Step σ ρ)}
    (h : Runs points step state tokens (f <$> program) next) :
    Runs points step state tokens program fun a => next (f a) := by
  intro rest
  rw [h rest, map_eq_pure_bind, bind_assoc]
  simp

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Handler H m]
variable {points : Points (StateT H m)} {version : Version}
variable {h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H)}

/-- The token after the first of the attributes: the next keyword, or the `)` after them. -/
def followingOf : List Tree.Attribute → BSmtLibSpec.Grammar.SyntaxToken
  | [] => .parenClose
  | next :: _ => .keyword next.keyword

/-- The attributes after the first. -/
def othersOf (points : Points (StateT H m))
    (h : Traversal.Handler (StateT H m) (Handler.Error H) (valuesOf H)) :
    List Tree.Attribute →
      Run (StateT H m) (Handler.Error H) (List (Handler.Attribute H))
  | [] => pure []
  | next :: rest => attributesThen points h next.keyword next.value rest

/-- The attributes of an annotation: the first, then the others. -/
theorem attributesThen_eq (keyword : BSmtLibSpec.Regex.Chars) (value : Option Tree.AttributeValue)
    (rest : List Tree.Attribute) :
    attributesThen points h keyword value rest =
      (fun (pair : Handler.Attribute H × List (Handler.Attribute H)) =>
        pair.1 :: pair.2) <$> (do
        let first ← attributeThen points h keyword (followingOf rest) value
        let others ← othersOf points h rest
        pure (first, others)) := by
  cases rest <;> simp [attributesThen, followingOf, othersOf]

/--
An annotation, from after its `(`: the parser reads `!`, the term with the annotation's level on
top, then its attributes up to the `)`, and handles the annotation there.
-/
theorem annotation_runs
    (hA : TermAgrees h) {termTokens : List Parser.Internal.Input} {annotatedTerm : Tree.Term}
    (hterm : TermRuns points h version termTokens annotatedTerm) (first : Tree.Attribute)
    (rest : List Tree.Attribute)
    (hvalid : ∀ attr ∈ first :: rest, attr.Valid (Bridge.version version))
    {attributeTokens : List Parser.Internal.Input}
    (hs : Stands attributeTokens ((first :: rest).flatMap Tree.Attribute.tokens ++ [.parenClose]))
    (levels : List (TermLevelOf H)) :
    Runs points (termStep version) ({ mode := .opened, levels } : TermStateOf H)
      (.reserved (.general .exclamationMark) :: (termTokens ++ attributeTokens))
      (do
        tick points (.reserved (.general .exclamationMark))
        let handled ← adaptRun (Traversal.term points h annotatedTerm)
        let attributes ← adaptRun (do
          take points (.keyword first.keyword)
          attributesThen points h first.keyword first.value rest)
        Parser.Internal.call (Handler.annotateTerm handled (.new attributes.toArray)))
      fun r => termComplete levels r := by
  obtain ⟨name, value⟩ := first
  have hinner := attributes_runs_init (points := points) hA ⟨name, value⟩ rest hvalid hs
  have hsplit : adaptRun (do
        take points (.keyword name)
        attributesThen points h name value rest) =
      (fun (pair : Handler.Attribute H × List (Handler.Attribute H)) =>
        pair.1 :: pair.2) <$> adaptRun (do
        take points (.keyword name)
        let first ← attributeThen points h name (followingOf rest) value
        let others ← othersOf points h rest
        pure (first, others)) := by
    rw [attributesThen_eq]
    simp
  have hembed := fun (term : Handler.Term H) => Runs.bind_next
    (following := fun (pair : Handler.Attribute H × List (Handler.Attribute H)) =>
      Parser.Internal.call
        (Handler.annotateTerm term (.new (pair.1 :: pair.2 : List _).toArray)))
    (next := termComplete levels)
    (Runs.of_map_program
      (f := fun (pair : Handler.Attribute H × List (Handler.Attribute H)) =>
        pair.1 :: pair.2)
      ((Runs.embed (outer := termStep version)
        (fun state => ({ mode := .annotating term state, levels } : TermStateOf H)) _
        (termStep_annotating levels term) (hsplit ▸ hinner)).congr rfl rfl) |>.congr rfl (by
          funext
          simp [Parser.Internal.Step.wrap, annotated]))
  refine (Runs.tokens_eq (Runs.append (middle := fun _ =>
      ({ mode := .start, levels := .annotation :: levels } : TermStateOf H))
    (Runs.token_more (token := .reserved (.general .exclamationMark))
      (by simp [termStep, termOpened])) fun _ =>
    Runs.append (middle := fun term =>
        ({ mode := .annotating term .init, levels } : TermStateOf H))
      ((hterm (.annotation :: levels)).congr rfl (by funext; simp [termComplete])) fun term =>
      hembed term) (by simp)).congr ?_ rfl
  rw [hsplit]
  simp

/-- The cases of a `match` as the formalism hands them over, from the parser's. -/
def specCases {T : Type} (cases : List (Grammar.Nodes.Pattern × T)) : List (Tree.Pattern × T) :=
  cases.map fun (pattern, body) => (Bridge.pattern pattern, body)

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

mutual

/--
From any stack of levels, the term parser reads the tokens of a term with the traversal's
effects, then completes the term on that stack.
-/
theorem term_runs' (hA : TermAgrees h) : (term : Tree.Term) →
    term.Valid (Bridge.version version) →
    ∀ {tokens : List Parser.Internal.Input},
        Stands tokens term.tokens → TermRunsFirst points h version tokens term
  | .constant constant, _, _, hs, atArrival, levels => by
    obtain ⟨constant', rfl, rfl⟩ := Stands.constant hs
    exact (RunsFirst.token (program := Parser.Internal.call (Handler.handleTerm
      (.specialConstant constant'))) (by simp [termStep])).congr (by simp [term_constant,
        adaptRun_receive (token := .constant constant') rfl, hA.handleTerm, Bridge.termNode]) rfl
  | .identifier qualified, hvalid, _, hs, atArrival, levels =>
    identifierTerm_runs hA hvalid hs atArrival levels
  | .application function arguments, hvalid, _, hs, atArrival, levels => by
    obtain ⟨hne, hfunction, harguments⟩ := hvalid
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    obtain ⟨headTokens, argumentTokens, rfl, hsHead, hsArguments⟩ := Stands.split hinner
    obtain ⟨head, hheadName, hheadRuns⟩ := applicationHead_runs (points := points) hA hfunction
      hsHead levels
    obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨firstTokens, restTokens, rfl, hs₁, hs₂⟩ := Stands.split hsArguments
    have hclose : ∀ (sort : Option (Handler.«Sort» H)) (r : Handler.Term H)
        (handled : List (Handler.Term H)),
        Runs points (termStep version)
          ({ mode := .start, levels := .application head sort (#[].push r ++ handled.toArray) ::
            levels } : TermStateOf H) [.parenClose]
          (do
            tick points .parenClose
            Parser.Internal.call (Handler.handleTerm
              (.application head sort (.new (#[].push r ++ handled.toArray))
                (Grammar.Multiple.len_pos_new (by simp)))))
          fun r => termComplete levels r :=
      fun _ _ _ => Runs.token (by simp [termStep])
    have harguments' := fun sort => Runs.append (middle := fun r =>
        ({ mode := .start, levels := .application head sort (#[].push r) :: levels } :
          TermStateOf H))
      (((term_runs' hA first harguments.1 hs₁).plain
        (.application head sort #[] :: levels)).congr rfl
        (by funext; simp [termComplete])) fun r =>
        Runs.append (middle := fun handled =>
            ({ mode := .start,
               levels := .application head sort (#[].push r ++ handled.toArray) :: levels } :
              TermStateOf H))
          (terms_runs hA rest harguments.2 hs₂ head sort (#[].push r) levels) fun handled =>
            hclose sort r handled
    refine (RunsFirst.tokens_eq (RunsFirst.append
        (middle := fun _ => ({ mode := .opened, levels } :
        TermStateOf H))
      (RunsFirst.token_more (token := .parenOpen) (by simp [termStep])) fun _ =>
        Runs.append hheadRuns fun sort => harguments' sort) (by simp)).congr ?_ rfl
    simp [term_application, adaptRun_receive (token := .parenOpen) rfl,
      Traversal.terms, qualIdentifier_eq, hA.handleTerm, Bridge.termNode,
      hheadName, adaptRun_take (token := .parenClose) rfl]
  | .«let» bindingList body, hvalid, _, hs, atArrival, levels => by
    obtain ⟨hne, hbindings, hbody⟩ := hvalid
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    obtain ⟨letToken, rest, rfl, hlet, hrest⟩ := Stands.split_cons hinner
    rw [Parser.Internal.Input.received_word (word := .general .let) hlet]
    obtain ⟨bindingTokens, bodyTokens, rfl, hsBindings, hsBody⟩ := Stands.split hrest
    obtain ⟨bindingInner, rfl, hbindingInner⟩ := Stands.split_paren hsBindings
    obtain ⟨⟨name, bound⟩, others, rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨hbound, hothers⟩ := hbindings
    obtain ⟨firstTokens, restTokens, rfl, hs₁, hs₂⟩ := Stands.split hbindingInner
    obtain ⟨firstInner, rfl, hfirstInner⟩ := Stands.split_paren hs₁
    obtain ⟨symbolToken, boundTokens, rfl, hsymbol, hsBound⟩ := Stands.split_cons hfirstInner
    obtain ⟨symbol, hsymbolName, rfl, hbinding⟩ := binding_runs (points := points) hsymbol
      (term_runs' hA bound hbound hsBound).plain
    obtain ⟨program, hprogram, hothersRuns⟩ := bindings_runs hA others hothers hs₂
    have hstart : ∀ (b : Lexicon.Value.Symbol × Handler.Term H)
        (handled : List (Lexicon.Value.Symbol × Handler.Term H)),
        Runs points (termStep version)
          ({ mode := .letBindingOpen (#[].push b ++ handled.toArray), levels } : TermStateOf H)
          [.parenClose]
          (do
            tick points .parenClose
            Parser.Internal.call (Handler.startLet (Grammar.Multiple.NamedValues.Internal.new
              (#[].push b ++ handled.toArray))))
          fun scope => pure (.more { mode := .start, levels := .binder .let scope :: levels }) :=
      fun _ _ => Runs.token (by simp [termStep])
    refine (RunsFirst.tokens_eq (RunsFirst.append
        (middle := fun _ => ({ mode := .opened, levels } :
        TermStateOf H))
      (RunsFirst.token_more (token := .parenOpen) (by simp [termStep])) fun _ =>
      Runs.append (middle := fun _ => ({ mode := .letBindingsOpen, levels } : TermStateOf H))
        (Runs.token_more (token := .reserved (.general .let)) (by simp [termStep, termOpened]))
        fun _ =>
      Runs.append (middle := fun _ => ({ mode := .letBindingOpen #[], levels } : TermStateOf H))
        (Runs.token_more (token := .parenOpen) (by
            simp [termStep, Parser.Category.Token.Internal.expectOpen])) fun _ =>
      Runs.append (middle := fun b => ({ mode := .letBindingOpen (#[].push b), levels } :
          TermStateOf H)) (hbinding #[] levels) fun b =>
      Runs.append (middle := fun handled =>
          ({ mode := .letBindingOpen (#[].push b ++ handled.toArray), levels } : TermStateOf H))
        (hothersRuns (#[].push b) levels) fun handled =>
      Runs.append (middle := fun scope => ({ mode := .start, levels := .binder .let scope ::
          levels } : TermStateOf H)) (hstart b handled) fun scope =>
      binderBody_runs (term_runs' hA body hbody hsBody).plain .let scope levels)
      (by simp)).congr ?_ rfl
    have hsymbolToken : Bridge.received (Parser.Internal.Input.symbol symbol) = some (.token
        (.symbol name)) := by
      simp [Bridge.received, hsymbolName]
    simp [term_let, takeAllArriving_cons, adaptRun_receive (token := .parenOpen) rfl,
      Traversal.bindings, ← hprogram, Bridge.specPairs, hsymbolName,
      hA.startLet, hA.endLet, Bridge.pairs, endBinder,
      adaptRun_takeAll (tokens := [.reserved (.general .let), .parenOpen])
        (syntaxTokens := [word "let", .parenOpen])
        (Stands.cons rfl (Stands.cons rfl nil)),
      adaptRun_takeAll (tokens := [.parenOpen, .symbol symbol])
        (Stands.cons (token := .parenOpen) rfl (Stands.cons hsymbolToken nil)),
      adaptRun_take (token := .parenClose) rfl]
  | .lambda variables body, hvalid, _, hs, atArrival, levels => by
    obtain ⟨-, hne, hvariables, hbody⟩ := hvalid
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    obtain ⟨wordToken, rest, rfl, hword, hrest⟩ := Stands.split_cons hinner
    obtain ⟨variableTokens, bodyTokens, rfl, hsVariables, hsBody⟩ := Stands.split hrest
    obtain ⟨variableInner, rfl, hvariableInner⟩ := Stands.split_paren hsVariables
    obtain rfl := Parser.Internal.Input.received_word (word := .general .lambda) hword
    have hstart := binderStart_runs (points := points) hA .lambda hword
      (fun levels => by simp [termStep, termOpened]) variables hvariables hne hvariableInner
      levels
    refine (RunsFirst.tokens_eq (RunsFirst.append
        (middle := fun _ => ({ mode := .opened, levels } :
        TermStateOf H))
      (RunsFirst.token_more (token := .parenOpen) (by simp [termStep])) fun _ =>
      Runs.append hstart fun scope =>
        binderBody_runs (term_runs' hA body hbody hsBody).plain (.sorted .lambda) scope levels)
      (by simp)).congr ?_ rfl
    simp [term_lambda, takeAllArriving_cons, adaptRun_receive (token := .parenOpen) rfl,
      specStart, endBinder, hA.endLambda, takeAll,
      adaptRun_take (token := .parenOpen) rfl, adaptRun_take (token := .parenClose) rfl]
  | .quantified quantifier variables body, hvalid, _, hs, atArrival, levels => by
    obtain ⟨hne, hvariables, hbody⟩ := hvalid
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    obtain ⟨wordToken, rest, rfl, hword, hrest⟩ := Stands.split_cons hinner
    obtain ⟨variableTokens, bodyTokens, rfl, hsVariables, hsBody⟩ := Stands.split hrest
    obtain ⟨variableInner, rfl, hvariableInner⟩ := Stands.split_paren hsVariables
    cases quantifier with
    | «forall» =>
      obtain rfl := Parser.Internal.Input.received_word (word := .general .forall) hword
      have hstart := binderStart_runs (points := points) hA (.quantifier .forall) hword
        (fun levels => by simp [termStep, termOpened]) variables hvariables hne hvariableInner
        levels
      refine (RunsFirst.tokens_eq (RunsFirst.append
          (middle := fun _ => ({ mode := .opened, levels } :
          TermStateOf H))
        (RunsFirst.token_more (token := .parenOpen) (by simp [termStep])) fun _ =>
        Runs.append hstart fun scope =>
          binderBody_runs (term_runs' hA body hbody hsBody).plain (.sorted (.quantifier .forall))
            scope levels) (by simp)).congr ?_ rfl
      simp [term_quantified, takeAllArriving_cons, adaptRun_receive (token := .parenOpen) rfl,
        specStart, endBinder, hA.endQuantifier, Bridge.quantifier,
        Tree.Quantifier.word, takeAll, adaptRun_take (token := .parenOpen) rfl,
        adaptRun_take (token := .parenClose) rfl]
    | «exists» =>
      obtain rfl := Parser.Internal.Input.received_word (word := .general .exists) hword
      have hstart := binderStart_runs (points := points) hA (.quantifier .exists) hword
        (fun levels => by simp [termStep, termOpened]) variables hvariables hne hvariableInner
        levels
      refine (RunsFirst.tokens_eq (RunsFirst.append
          (middle := fun _ => ({ mode := .opened, levels } :
          TermStateOf H))
        (RunsFirst.token_more (token := .parenOpen) (by simp [termStep])) fun _ =>
        Runs.append hstart fun scope =>
          binderBody_runs (term_runs' hA body hbody hsBody).plain (.sorted (.quantifier .exists))
            scope levels) (by simp)).congr ?_ rfl
      simp [term_quantified, takeAllArriving_cons, adaptRun_receive (token := .parenOpen) rfl,
        specStart, endBinder, hA.endQuantifier, Bridge.quantifier,
        Tree.Quantifier.word, takeAll, adaptRun_take (token := .parenOpen) rfl,
        adaptRun_take (token := .parenClose) rfl]
  | .«match» scrutinee caseList, hvalid, _, hs, atArrival, levels => by
    obtain ⟨-, hne, hscrutinee, hcases⟩ := hvalid
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    obtain ⟨matchToken, rest, rfl, hmatch, hrest⟩ := Stands.split_cons hinner
    rw [Parser.Internal.Input.received_word (word := .general .match) hmatch]
    obtain ⟨scrutineeTokens, casesTokens, rfl, hsScrutinee, hsCases⟩ := Stands.split hrest
    obtain ⟨casesInner, rfl, hcasesInner⟩ := Stands.split_paren hsCases
    obtain ⟨⟨firstPattern, firstBody⟩, others, rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨hpattern, hbody, hothers⟩ := hcases
    obtain ⟨firstTokens, restTokens, rfl, hs₁, hs₂⟩ := Stands.split hcasesInner
    obtain ⟨firstInner, rfl, hfirstInner⟩ := Stands.split_paren hs₁
    obtain ⟨patternTokens, bodyTokens, rfl, hsPattern, hsBody⟩ := Stands.split hfirstInner
    obtain ⟨parsed, hparsed, hcase⟩ := case_runs (points := points) hpattern hsPattern
      (term_runs' hA firstBody hbody hsBody).plain
    obtain ⟨program, hprogram, hothersRuns⟩ := cases_runs hA others hothers hs₂
    have hscrutineeRuns := Runs.bind_next
      (following := fun r => do Parser.Internal.call (Handler.startMatch r); pure r)
      (next := fun r => pure (.more ({ mode := .matchCasesOpen r, levels } : TermStateOf H)))
      (((term_runs' hA scrutinee hscrutinee hsScrutinee).plain
        (.matchScrutinee :: levels)).congr rfl
        (by funext; simp [termComplete]))
    have hclose : ∀ (scrutinee : Handler.Term H)
        (c : Grammar.Nodes.Pattern × Handler.Term H)
        (handled : List (Grammar.Nodes.Pattern × Handler.Term H)),
        Runs points (termStep version)
          ({ mode := .matchCaseOpen scrutinee (#[].push c ++ handled.toArray), levels } :
            TermStateOf H) [.parenClose, .parenClose]
          (do
            tick points .parenClose
            tick points .parenClose
            Parser.Internal.call
                (Handler.endMatch scrutinee (Grammar.Multiple.MatchCases.Internal.new
                  (#[].push c ++ handled.toArray))))
          fun r => termComplete levels r := fun scrutinee c handled =>
      Runs.append (middle := fun _ =>
          ({ mode := .matchClose scrutinee (#[].push c ++ handled.toArray), levels } :
            TermStateOf H))
        (Runs.token_more (token := .parenClose) (by simp [termStep])) fun _ =>
        Runs.token (by simp [termStep, Parser.Category.Token.Internal.expectClose])
    refine (RunsFirst.tokens_eq (RunsFirst.append
        (middle := fun _ => ({ mode := .opened, levels } :
        TermStateOf H))
      (RunsFirst.token_more (token := .parenOpen) (by simp [termStep])) fun _ =>
      Runs.append (middle := fun _ => ({ mode := .start, levels := .matchScrutinee :: levels } :
          TermStateOf H))
        (Runs.token_more (token := .reserved (.general .match)) (by simp [termStep, termOpened]))
        fun _ =>
      Runs.append hscrutineeRuns fun scrutinee =>
      Runs.append (middle := fun _ => ({ mode := .matchCaseOpen scrutinee #[], levels } :
          TermStateOf H))
        (Runs.token_more (token := .parenOpen) (by
            simp [termStep, Parser.Category.Token.Internal.expectOpen])) fun _ =>
      Runs.append (middle := fun c => ({ mode := .matchCaseOpen scrutinee (#[].push c), levels } :
          TermStateOf H)) (hcase scrutinee #[] levels) fun c =>
      Runs.append (middle := fun handled =>
          ({ mode := .matchCaseOpen scrutinee (#[].push c ++ handled.toArray), levels } :
            TermStateOf H))
        (hothersRuns scrutinee (#[].push c) levels) fun handled =>
      hclose scrutinee c handled) (by simp)).congr ?_ rfl
    simp [term_match, takeAllArriving_cons, adaptRun_receive (token := .parenOpen) rfl,
      cases_cons, ← hprogram, specCases, hparsed, hA.startMatch,
      hA.startMatchCase, hA.endMatchCase, hA.endMatch,
      adaptRun_takeAll (tokens := [.reserved (.general .match)])
        (syntaxTokens := [word "match"]) (Stands.cons rfl nil),
      adaptRun_takeAll (tokens := [.parenClose, .parenClose])
        (syntaxTokens := [.parenClose, .parenClose]) (Stands.cons rfl (Stands.cons rfl nil)),
      adaptRun_takeAll hsPattern, adaptRun_take (token := .parenOpen) rfl,
      adaptRun_take (token := .parenClose) rfl]
  | .annotated annotatedTerm attributeList, hvalid, _, hs, atArrival, levels => by
    obtain ⟨hne, hterm, hattributes⟩ := hvalid
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    obtain ⟨bangToken, rest, rfl, hbang, hrest⟩ := Stands.split_cons hinner
    rw [Parser.Internal.Input.received_word (word := .general .exclamationMark) hbang]
    obtain ⟨termTokens, attributeTokens, rfl, hsTerm, hsAttributes⟩ := Stands.split hrest
    obtain ⟨first, others, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hannotation := annotation_runs (points := points) hA
      ((term_runs' hA annotatedTerm hterm hsTerm).plain) first others hattributes
      (Stands.append hsAttributes (Stands.cons (token := .parenClose) rfl nil)) levels
    refine (RunsFirst.tokens_eq (RunsFirst.append
        (middle := fun _ => ({ mode := .opened, levels } :
        TermStateOf H))
      (RunsFirst.token_more (token := .parenOpen) (by simp [termStep])) fun _ => hannotation)
      (by simp)).congr ?_ rfl
    simp [term_annotated, takeAllArriving_cons, adaptRun_receive (token := .parenOpen) rfl,
      hA.annotateTerm,
      adaptRun_takeAll (tokens := [.reserved (.general .exclamationMark)])
        (syntaxTokens := [word "!"]) (Stands.cons rfl nil)]

/--
From a stack whose innermost application has the arguments found so far, the term parser reads
the tokens of terms with the traversal's effects, and appends them to those arguments.
-/
theorem terms_runs (hA : TermAgrees h) : (terms : List Tree.Term) →
    Tree.Term.ValidAll (Bridge.version version) terms →
    ∀ {tokens : List Parser.Internal.Input}, Stands tokens (Tree.Term.tokensAll terms) →
    ∀ (head : Grammar.Nodes.Ident) (sort : Option (Handler.«Sort» H))
      (found : Array (Handler.Term H)) (levels : List (TermLevelOf H)),
    Runs points (termStep version)
      ({ mode := .start, levels := .application head sort found :: levels } : TermStateOf H)
      tokens
      (adaptRun (Traversal.terms points h terms))
      fun handled => pure (.more
        { mode := .start, levels := .application head sort (found ++ handled.toArray) :: levels })
  | [], _, _, hs, head, sort, found, levels => by
    have := Stands.eq_nil hs
    subst this
    exact (Runs.nil [] (by simp)).congr (by simp [Traversal.terms]) rfl
  | first :: rest, hvalid, _, hs, head, sort, found, levels => by
    obtain ⟨tokens₁, tokens₂, rfl, hs₁, hs₂⟩ := Stands.split hs
    have htail : ∀ r, Runs points (termStep version)
        ({ mode := .start, levels := .application head sort (found.push r) :: levels } :
          TermStateOf H) tokens₂
        ((r :: ·) <$> adaptRun (Traversal.terms points h rest))
        fun handled => pure (.more
          { mode := .start,
            levels := .application head sort (found ++ handled.toArray) :: levels }) :=
      fun r => Runs.map_program ((terms_runs hA rest hvalid.2 hs₂ head sort (found.push r)
        levels).congr rfl (by funext handled; simp))
    refine (Runs.append (middle := fun r =>
        ({ mode := .start, levels := .application head sort (found.push r) :: levels } :
          TermStateOf H))
      (((term_runs' hA first hvalid.1 hs₁).plain (.application head sort found :: levels)).congr rfl
        (by funext; simp [termComplete])) htail).congr ?_ rfl
    simp [Traversal.terms]

/--
From between the bindings of a `let`, the term parser reads the tokens of bindings with the
effects of a program whose bindings are the traversal's, through the bridge, and appends them to
those found so far.
-/
theorem bindings_runs (hA : TermAgrees h) : (bindings : List (Tree.Symbol × Tree.Term)) →
    Tree.Term.ValidBindings (Bridge.version version) bindings →
    ∀ {tokens : List Parser.Internal.Input}, Stands tokens (Tree.Term.bindingTokens bindings) →
    ∃ program : PM H (List (Lexicon.Value.Symbol × Handler.Term H)),
      Bridge.specPairs <$> program = adaptRun (Traversal.bindings points h bindings) ∧
      ∀ (found : Array (Lexicon.Value.Symbol × Handler.Term H)) (levels : List (TermLevelOf H)),
      Runs points (termStep version) ({ mode := .letBindingOpen found, levels } : TermStateOf H)
        tokens program
        fun handled => pure (.more { mode := .letBindingOpen (found ++ handled.toArray), levels })
  | [], _, _, hs => by
    have := Stands.eq_nil hs
    subst this
    exact ⟨pure [], by simp [Traversal.bindings, Bridge.specPairs],
      fun found levels => (Runs.nil [] (by simp)).congr rfl rfl⟩
  | (name, bound) :: rest, hvalid, _, hs => by
    obtain ⟨first, others, rfl, hs₁, hs₂⟩ := Stands.split hs
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs₁
    obtain ⟨symbolToken, boundTokens, rfl, hsymbol, hsBound⟩ := Stands.split_cons hinner
    obtain ⟨symbol, hsymbolName, rfl, hbinding⟩ := binding_runs (points := points) hsymbol
      (term_runs' hA bound hvalid.1 hsBound).plain
    obtain ⟨program, hprogram, hrestRuns⟩ := bindings_runs hA rest hvalid.2 hs₂
    refine ⟨do
      tick points .parenOpen
      tick points (.symbol symbol)
      let result ← adaptRun (Traversal.term points h bound)
      tick points .parenClose
      let others ← program
      pure ((symbol, result) :: others), ?_, fun found levels => ?_⟩
    · have hsymbolToken : Bridge.received (Parser.Internal.Input.symbol symbol) =
          some (.token (.symbol name)) := by
        simp [Bridge.received, hsymbolName]
      simp [Traversal.bindings, ← hprogram, Bridge.specPairs, hsymbolName,
        adaptRun_takeAll (tokens := [.parenOpen, .symbol symbol])
          (Stands.cons (token := .parenOpen) rfl (Stands.cons hsymbolToken nil)),
        adaptRun_take (token := .parenClose) rfl]
    · refine (Runs.tokens_eq (Runs.append (middle := fun b =>
          ({ mode := .letBindingOpen (found.push b), levels } : TermStateOf H))
        (hbinding found levels) fun b =>
          Runs.map_program (f := (b :: ·)) ((hrestRuns (found.push b) levels).congr rfl
            (by funext; simp))) (by simp)).congr ?_ rfl
      simp

/--
From between the cases of a `match`, the term parser reads the tokens of cases with the effects
of a program whose cases are the traversal's, through the bridge, and appends them to those
found so far.
-/
theorem cases_runs (hA : TermAgrees h) : (cases : List (Tree.Pattern × Tree.Term)) →
    Tree.Term.ValidCases (Bridge.version version) cases →
    ∀ {tokens : List Parser.Internal.Input}, Stands tokens (Tree.Term.caseTokens cases) →
    ∃ program : Handler.Term H → PM H (List (Grammar.Nodes.Pattern × Handler.Term H)),
      (∀ scrutinee, specCases <$> program scrutinee =
        adaptRun (Traversal.cases points h scrutinee cases)) ∧
      ∀ (scrutinee : Handler.Term H)
        (found : Array (Grammar.Nodes.Pattern × Handler.Term H)) (levels : List (TermLevelOf H)),
      Runs points (termStep version)
        ({ mode := .matchCaseOpen scrutinee found, levels } : TermStateOf H) tokens
        (program scrutinee)
        fun handled =>
          pure (.more { mode := .matchCaseOpen scrutinee (found ++ handled.toArray), levels })
  | [], _, _, hs => by
    have := Stands.eq_nil hs
    subst this
    exact ⟨fun _ => pure [], by simp [Traversal.cases, specCases],
      fun scrutinee found levels => (Runs.nil [] (by simp)).congr rfl rfl⟩
  | (pattern, body) :: rest, hvalid, _, hs => by
    obtain ⟨first, others, rfl, hs₁, hs₂⟩ := Stands.split hs
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs₁
    obtain ⟨patternTokens, bodyTokens, rfl, hsPattern, hsBody⟩ := Stands.split hinner
    obtain ⟨parsed, hparsed, hcase⟩ := case_runs (points := points) hvalid.1 hsPattern
      (term_runs' hA body hvalid.2.1 hsBody).plain
    obtain ⟨program, hprogram, hrestRuns⟩ := cases_runs hA rest hvalid.2.2 hs₂
    refine ⟨fun scrutinee => do
      tick points .parenOpen
      ticks points patternTokens
      let scope ← Parser.Internal.call (Handler.startMatchCase scrutinee parsed)
      let result ← adaptRun (Traversal.term points h body)
      tick points .parenClose
      let handled ← Parser.Internal.call (Handler.endMatchCase scope scrutinee result)
      let others ← program scrutinee
      pure ((parsed, handled) :: others), fun scrutinee => ?_, fun scrutinee found levels => ?_⟩
    · simp [cases_cons, ← hprogram scrutinee, specCases, hparsed, hA.startMatchCase,
        hA.endMatchCase, adaptRun_takeAll hsPattern, adaptRun_take (token := .parenOpen) rfl,
        adaptRun_take (token := .parenClose) rfl]
    · refine (Runs.tokens_eq (Runs.append (middle := fun c =>
          ({ mode := .matchCaseOpen scrutinee (found.push c), levels } : TermStateOf H))
        (hcase scrutinee found levels) fun c =>
          Runs.map_program (f := (c :: ·)) ((hrestRuns scrutinee (found.push c) levels).congr rfl
            (by funext; simp))) (by simp)).congr ?_ rfl
      simp

end

/--
From any stack of open constructs, the term parser reads the tokens of a term with the
traversal's effects, then completes the term on that stack.
-/
theorem term_runs (hA : TermAgrees h) (term : Tree.Term)
    (hvalid : term.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens term.tokens) (levels : List (TermLevelOf H)) :
    Runs points (termStep version) { mode := .start, levels } tokens
      (adaptRun (Traversal.term points h term))
      fun r => termComplete levels r :=
  (term_runs' hA term hvalid hs).plain levels

/-- From its start, the term parser reads the tokens of a term and ends with it. -/
theorem term_runs_init (hA : TermAgrees h) (term : Tree.Term)
    (hvalid : term.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens term.tokens) :
    Runs points (termStep version) Parser.Category.Term.Internal.TermState.init tokens
      (adaptRun (Traversal.term points h term))
      fun r => pure (.done r) :=
  (term_runs hA term hvalid hs []).congr rfl (by funext; simp [termComplete])

/-- From its start, the term parser reads the tokens of a term, with the calls due at its first
token's arrival, and ends with it. -/
theorem term_runs_first_init (hA : TermAgrees h) (term : Tree.Term)
    (hvalid : term.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens term.tokens) (first : Run (StateT H m) (Handler.Error H) Unit) :
    RunsFirst points (adaptRun first)
        (termStep version) Parser.Category.Term.Internal.TermState.init tokens
      (adaptRun (Traversal.term points h term first))
      fun r => pure (.done r) :=
  (term_runs' hA term hvalid hs first []).congr rfl (by funext; simp [termComplete])

end

end BSmtLib.Facts.Proofs.Parser.Term
