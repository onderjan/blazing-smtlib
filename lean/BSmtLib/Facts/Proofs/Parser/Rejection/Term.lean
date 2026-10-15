module

public import BSmtLib.Facts.Proofs.Parser.Rejection.Parts
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Attribute
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Token.Reserved
import all BSmtLib.Parser.Category.Token

@[expose] public section

/-!
# What terms can still take

The term parser's state is a mode and the constructs whose inner term it reads, innermost first
(levels). When the inner term of a level is complete, what follows is the rest of that construct
(`termAfter`), and then the rest of the constructs outside it (`termAfterAll`). A mode reads part
of the innermost construct; its remainder (`modeRem`) ends where a term is complete and goes to
the levels. In the start mode, an open application on top takes its further arguments or its
`)` (`startRem`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Rejection.Term

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser.Category.Term.Internal
    (TermState TermMode TermLevel termStep termComplete termOpened startBinder endBinder BinderKind SortedBinder)
open BSmtLib.Parser.Category.Combinator.Internal (ListState)
open BSmtLib.Parser.Category.Attribute.Internal (AttributeState)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Proofs.Parser.Rejection.Basic
open BSmtLib.Facts.Proofs.Parser.Rejection.Parts BSmtLib.Facts.Proofs.Parser.Rejection.SExpr
open BSmtLib.Facts.Proofs.Parser.Rejection.«Sort»

open BSmtLib.Facts.Proofs.Parser.Rejection.Basic.Lang

/-! ## Terms, bindings and cases -/

section

variable (version : BSmtLibSpec.Lexicon.Version)

/-- A term of the version. -/
def TermLang : Lang := fun u => ∃ term : Tree.Term, term.Valid version ∧ u = toks term.tokens

/-- What follows the `(` of a term of the version. -/
def OpenedLang : Lang :=
  fun u => ∃ term : Tree.Term, term.Valid version ∧ toks term.tokens = openItem :: u

/-- A binding of a `let`, of the version. -/
def BindingLang : Lang := fun u => ∃ (symbol : Tree.Symbol) (term : Tree.Term),
  term.Valid version ∧ u = toks (paren (.symbol symbol :: term.tokens))

/-- A case of a `match`, of the version. -/
def CaseLang : Lang := fun u => ∃ (pattern : Tree.Pattern) (term : Tree.Term),
  pattern.Valid version ∧ term.Valid version ∧ u = toks (paren (pattern.tokens ++ term.tokens))

/-- After the bindings of a `let`: their `)`, the body, the `let`'s `)`. -/
def letTail : Lang := cat (tok closeItem) (cat (TermLang version) (tok closeItem))

/-- After the cases of a `match`: their `)` and the `match`'s `)`. -/
def caseTail : Lang := cat (tok closeItem) (tok closeItem)

/-- What follows when the inner term of the construct is complete, up to the construct's end. -/
def termAfter : TermLevel Nat Nat Nat → Lang
  | .application .. => cat (star (TermLang version)) (tok closeItem)
  | .letBinding .. =>
    cat (tok closeItem) (cat (star (BindingLang version)) (letTail version))
  | .binder .. => tok closeItem
  | .annotation => cat (plus (AttrLang version)) (tok closeItem)
  | .matchScrutinee => cat (tok openItem) (cat (plus (CaseLang version)) caseTail)
  | .matchCase .. => cat (tok closeItem) (cat (star (CaseLang version)) caseTail)

/-- What follows when the inner term of the innermost construct is complete, outwards. -/
def termAfterAll : List (TermLevel Nat Nat Nat) → Lang
  | [] => eps
  | level :: outer => cat (termAfter version level) (termAfterAll outer)

/-- The remainders in the start mode: an open application's further arguments and `)`, or a
term, then what follows. -/
def startRem : List (TermLevel Nat Nat Nat) → Lang
  | .application _ _ arguments :: outer =>
    cat (rep (TermLang version) (if arguments.isEmpty then 1 else 0) none)
      (cat (tok closeItem) (termAfterAll version outer))
  | levels => cat (TermLang version) (termAfterAll version levels)

/-- The remainders of the modes other than the start, up to the end of the innermost term. -/
def modeRem : TermMode Nat Nat Nat Nat Nat → Lang
  | .start => TermLang version
  | .opened => OpenedLang version
  | .qualIdent state => qualRem version state
  | .applicationHead state =>
    cat (qualRem version state) (cat (plus (TermLang version)) (tok closeItem))
  | .letBindingsOpen => cat (tok openItem) (cat (plus (BindingLang version)) (letTail version))
  | .letBindingOpen bindings =>
    cat (rep (BindingLang version) (if bindings.isEmpty then 1 else 0) none) (letTail version)
  | .letBindingSymbol _ =>
    cat SymbolLang (cat (TermLang version) (cat (tok closeItem)
      (cat (star (BindingLang version)) (letTail version))))
  | .letBindingClose _ => cat (tok closeItem) (cat (star (BindingLang version)) (letTail version))
  | .sortedVars _ state =>
    cat (listRem (sortedVarRem version) (SortedVarLang version) .start 1 none state)
      (cat (TermLang version) (tok closeItem))
  | .binderClose .. => tok closeItem
  | .matchCasesOpen _ => cat (tok openItem) (cat (plus (CaseLang version)) caseTail)
  | .matchCaseOpen _ cases =>
    cat (rep (CaseLang version) (if cases.isEmpty then 1 else 0) none) caseTail
  | .matchPattern _ _ state =>
    cat (patternRem version state) (cat (TermLang version) (cat (tok closeItem)
      (cat (star (CaseLang version)) caseTail)))
  | .matchCaseClose .. => cat (tok closeItem) (cat (star (CaseLang version)) caseTail)
  | .matchClose .. => tok closeItem
  | .annotating _ state => attrRem version false true state

/-- The remainders of the term parser's states. -/
def termRem (state : TermState Nat Nat Nat Nat Nat) : Lang :=
  match state.mode with
  | .start => startRem version state.levels
  | mode => cat (modeRem version mode) (termAfterAll version state.levels)

end

/-! ## Lists of trees -/

section

variable {version : BSmtLibSpec.Lexicon.Version}

theorem termTokensAll_eq (terms : List Tree.Term) :
    Tree.Term.tokensAll terms = (terms.map Tree.Term.tokens).flatten := by
  induction terms with
  | nil => rfl
  | cons first rest ih => simp [Tree.Term.tokensAll, ih]

theorem termValidAll_of {terms : List Tree.Term} (h : ∀ term ∈ terms, term.Valid version) :
    Tree.Term.ValidAll version terms := by
  induction terms with
  | nil => trivial
  | cons first rest ih => exact ⟨h first (by simp), ih fun t ht => h t (by simp [ht])⟩

theorem bindingTokens_eq' (bindings : List (Tree.Symbol × Tree.Term)) :
    Tree.Term.bindingTokens bindings =
      (bindings.map fun (s, t) => paren (.symbol s :: t.tokens)).flatten := by
  induction bindings with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨s, t⟩ := first
    simp [Tree.Term.bindingTokens, ih]

theorem validBindings_of {bindings : List (Tree.Symbol × Tree.Term)}
    (h : ∀ b ∈ bindings, b.2.Valid version) : Tree.Term.ValidBindings version bindings := by
  induction bindings with
  | nil => trivial
  | cons first rest ih =>
    obtain ⟨s, t⟩ := first
    exact ⟨h (s, t) (by simp), ih fun b hb => h b (by simp [hb])⟩

theorem caseTokens_eq' (cases : List (Tree.Pattern × Tree.Term)) :
    Tree.Term.caseTokens cases =
      (cases.map fun (p, t) => paren (p.tokens ++ t.tokens)).flatten := by
  induction cases with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨p, t⟩ := first
    simp [Tree.Term.caseTokens, ih]

theorem validCases_of {cases : List (Tree.Pattern × Tree.Term)}
    (h : ∀ c ∈ cases, c.1.Valid version ∧ c.2.Valid version) :
    Tree.Term.ValidCases version cases := by
  induction cases with
  | nil => trivial
  | cons first rest ih =>
    obtain ⟨p, t⟩ := first
    exact ⟨(h (p, t) (by simp)).1, (h (p, t) (by simp)).2, ih fun c hc => h c (by simp [hc])⟩

theorem terms_rep {lo : Nat} {hi : Option Nat} {u : List Received}
    (h : rep (TermLang version) lo hi u) :
    ∃ terms : List Tree.Term, Tree.Term.ValidAll version terms ∧ lo ≤ terms.length ∧
      u = toks (Tree.Term.tokensAll terms) := by
  obtain ⟨terms, hvalid, hlo, -, rfl⟩ := rep_trees h
  exact ⟨terms, termValidAll_of hvalid, hlo, by simp [termTokensAll_eq, Function.comp_def]⟩

theorem bindings_rep {lo : Nat} {hi : Option Nat} {u : List Received}
    (h : rep (BindingLang version) lo hi u) :
    ∃ bindings : List (Tree.Symbol × Tree.Term), Tree.Term.ValidBindings version bindings ∧
      lo ≤ bindings.length ∧ u = toks (Tree.Term.bindingTokens bindings) := by
  have h' : rep (fun w => ∃ b : Tree.Symbol × Tree.Term, b.2.Valid version ∧
      w = toks (paren (.symbol b.1 :: b.2.tokens))) lo hi u := by
    obtain ⟨ws, hws, hlo, hhi, rfl⟩ := h
    refine ⟨ws, fun w hw => ?_, hlo, hhi, rfl⟩
    obtain ⟨s, t, ht, rfl⟩ := hws w hw
    exact ⟨(s, t), ht, rfl⟩
  obtain ⟨bindings, hvalid, hlo, -, rfl⟩ := rep_trees h'
  exact ⟨bindings, validBindings_of hvalid, hlo, by simp [bindingTokens_eq', Function.comp_def]⟩

theorem cases_rep {lo : Nat} {hi : Option Nat} {u : List Received}
    (h : rep (CaseLang version) lo hi u) :
    ∃ cases : List (Tree.Pattern × Tree.Term), Tree.Term.ValidCases version cases ∧
      lo ≤ cases.length ∧ u = toks (Tree.Term.caseTokens cases) := by
  have h' : rep (fun w => ∃ c : Tree.Pattern × Tree.Term, (c.1.Valid version ∧
      c.2.Valid version) ∧ w = toks (paren (c.1.tokens ++ c.2.tokens))) lo hi u := by
    obtain ⟨ws, hws, hlo, hhi, rfl⟩ := h
    refine ⟨ws, fun w hw => ?_, hlo, hhi, rfl⟩
    obtain ⟨p, t, hp, ht, rfl⟩ := hws w hw
    exact ⟨(p, t), ⟨hp, ht⟩, rfl⟩
  obtain ⟨cases, hvalid, hlo, -, rfl⟩ := rep_trees h'
  exact ⟨cases, validCases_of hvalid, hlo, by simp [caseTokens_eq', Function.comp_def]⟩

theorem attrs_rep {lo : Nat} {hi : Option Nat} {u : List Received}
    (h : rep (AttrLang version) lo hi u) :
    ∃ attributes : List Tree.Attribute, (∀ a ∈ attributes, a.Valid version) ∧
      lo ≤ attributes.length ∧ u = toks (attributes.flatMap Tree.Attribute.tokens) := by
  obtain ⟨attributes, hvalid, hlo, -, rfl⟩ := rep_trees h
  exact ⟨attributes, hvalid, hlo, by simp [List.flatMap, Function.comp_def]⟩

theorem sortedVars_rep {lo : Nat} {hi : Option Nat} {u : List Received}
    (h : rep (SortedVarLang version) lo hi u) :
    ∃ vars : List Tree.SortedVar, (∀ v ∈ vars, v.Valid version) ∧
      lo ≤ vars.length ∧ u = toks (vars.flatMap Tree.SortedVar.tokens) := by
  obtain ⟨vars, hvalid, hlo, -, rfl⟩ := rep_trees h
  exact ⟨vars, hvalid, hlo, by simp [List.flatMap, Function.comp_def]⟩

end

/-! ## Non-empty remainders -/

section

variable (version : BSmtLibSpec.Lexicon.Version)

/-- A term written as one numeral. -/
def zeroTerm : Tree.Term := .constant (.numeral [])

/-- A term written with parentheses: an application. -/
def appTerm : Tree.Term := .application (.plain ⟨⟨[], false⟩, []⟩) [zeroTerm]

theorem appTerm_valid : appTerm.Valid version := by
  simp [appTerm, zeroTerm, Tree.Term.Valid, Tree.Term.ValidAll, Tree.QualIdentifier.Valid,
    Tree.Identifier.Valid]

theorem termLang_nonempty : ∃ u, TermLang version u := ⟨_, ⟨zeroTerm, trivial, rfl⟩⟩

theorem bindingLang_nonempty : ∃ u, BindingLang version u :=
  ⟨_, ⟨⟨[], false⟩, zeroTerm, trivial, rfl⟩⟩

theorem caseLang_nonempty : ∃ u, CaseLang version u :=
  ⟨_, ⟨.single (.symbol ⟨[], false⟩), zeroTerm, trivial, trivial, rfl⟩⟩

theorem letTail_nonempty : ∃ u, letTail version u :=
  cat_nonempty ⟨_, tok_intro _⟩ (cat_nonempty (termLang_nonempty version) ⟨_, tok_intro _⟩)

theorem caseTail_nonempty : ∃ u, caseTail u :=
  cat_nonempty ⟨_, tok_intro _⟩ ⟨_, tok_intro _⟩

theorem termAfter_nonempty (level : TermLevel Nat Nat Nat) : ∃ u, termAfter version level u := by
  cases level with
  | application => exact cat_nonempty ⟨[], rep_nil⟩ ⟨_, tok_intro _⟩
  | letBinding =>
    exact cat_nonempty ⟨_, tok_intro _⟩ (cat_nonempty ⟨[], rep_nil⟩ (letTail_nonempty version))
  | binder => exact ⟨_, tok_intro _⟩
  | annotation =>
    exact cat_nonempty (rep_nonempty (attrLang_nonempty version) 1 none (by simp))
      ⟨_, tok_intro _⟩
  | matchScrutinee =>
    exact cat_nonempty ⟨_, tok_intro _⟩ (cat_nonempty
      (rep_nonempty (caseLang_nonempty version) 1 none (by simp)) caseTail_nonempty)
  | matchCase =>
    exact cat_nonempty ⟨_, tok_intro _⟩ (cat_nonempty ⟨[], rep_nil⟩ caseTail_nonempty)

theorem termAfterAll_nonempty (levels : List (TermLevel Nat Nat Nat)) :
    ∃ u, termAfterAll version levels u := by
  induction levels with
  | nil => exact ⟨[], rfl⟩
  | cons level outer ih => exact cat_nonempty (termAfter_nonempty version level) ih

theorem startRem_nonempty (levels : List (TermLevel Nat Nat Nat)) :
    ∃ u, startRem version levels u := by
  match levels with
  | .application _ _ arguments :: outer =>
    exact cat_nonempty (rep_nonempty (termLang_nonempty version) _ none (by simp))
      (cat_nonempty ⟨_, tok_intro _⟩ (termAfterAll_nonempty version outer))
  | [] => exact cat_nonempty (termLang_nonempty version) (termAfterAll_nonempty version _)
  | .letBinding .. :: _ =>
    exact cat_nonempty (termLang_nonempty version) (termAfterAll_nonempty version _)
  | .binder .. :: _ =>
    exact cat_nonempty (termLang_nonempty version) (termAfterAll_nonempty version _)
  | .annotation :: _ =>
    exact cat_nonempty (termLang_nonempty version) (termAfterAll_nonempty version _)
  | .matchScrutinee :: _ =>
    exact cat_nonempty (termLang_nonempty version) (termAfterAll_nonempty version _)
  | .matchCase .. :: _ =>
    exact cat_nonempty (termLang_nonempty version) (termAfterAll_nonempty version _)

/-- The mode has a remainder where it reads a list that has one: the sorted variables of a
binder. -/
def modeFine : TermMode Nat Nat Nat Nat Nat → Prop
  | .sortedVars _ state =>
    ∃ u, listRem (sortedVarRem version) (SortedVarLang version) .start 1 none state u
  | _ => True

theorem modeRem_nonempty (mode : TermMode Nat Nat Nat Nat Nat) (hfine : modeFine version mode) :
    ∃ u, modeRem version mode u := by
  have hterm := termLang_nonempty version
  have hplus : ∀ {A : Lang}, (∃ u, A u) → ∃ u, plus A u := fun h => rep_nonempty h 1 none (by simp)
  have hrep : ∀ {A : Lang} (lo : Nat), (∃ u, A u) → ∃ u, rep A lo none u :=
    fun lo h => rep_nonempty h lo none (by simp)
  have htok : ∀ x, ∃ u, tok x u := fun x => ⟨_, tok_intro x⟩
  cases mode with
  | start => exact hterm
  | opened => exact ⟨_, ⟨appTerm, appTerm_valid version, rfl⟩⟩
  | qualIdent state => exact qualRem_nonempty version state
  | applicationHead state =>
    exact cat_nonempty (qualRem_nonempty version state) (cat_nonempty (hplus hterm) (htok _))
  | letBindingsOpen =>
    exact cat_nonempty (htok _) (cat_nonempty (hplus (bindingLang_nonempty version))
      (letTail_nonempty version))
  | letBindingOpen bindings =>
    exact cat_nonempty (hrep _ (bindingLang_nonempty version)) (letTail_nonempty version)
  | letBindingSymbol _ =>
    exact cat_nonempty symbolLang_nonempty (cat_nonempty hterm (cat_nonempty (htok _)
      (cat_nonempty (hrep _ (bindingLang_nonempty version)) (letTail_nonempty version))))
  | letBindingClose _ =>
    exact cat_nonempty (htok _) (cat_nonempty (hrep _ (bindingLang_nonempty version))
      (letTail_nonempty version))
  | sortedVars _ state =>
    exact cat_nonempty hfine (cat_nonempty hterm (htok _))
  | binderClose => exact htok _
  | matchCasesOpen _ =>
    exact cat_nonempty (htok _) (cat_nonempty (hplus (caseLang_nonempty version))
      caseTail_nonempty)
  | matchCaseOpen _ cases =>
    exact cat_nonempty (hrep _ (caseLang_nonempty version)) caseTail_nonempty
  | matchPattern _ _ state =>
    exact cat_nonempty (patternRem_nonempty version state) (cat_nonempty hterm
      (cat_nonempty (htok _) (cat_nonempty (hrep _ (caseLang_nonempty version))
        caseTail_nonempty)))
  | matchCaseClose =>
    exact cat_nonempty (htok _) (cat_nonempty (hrep _ (caseLang_nonempty version))
      caseTail_nonempty)
  | matchClose => exact htok _
  | annotating _ state => exact attrRem_nonempty version false true state

theorem termRem_nonempty (state : TermState Nat Nat Nat Nat Nat)
    (hfine : modeFine version state.mode) : ∃ u, termRem version state u := by
  obtain ⟨mode, levels⟩ := state
  cases mode with
  | start => exact startRem_nonempty version levels
  | _ =>
    exact cat_nonempty (modeRem_nonempty version _ hfine) (termAfterAll_nonempty version levels)

end

/-- A term, then what follows it, is a remainder in the start mode. -/
theorem startRem_term {version : BSmtLibSpec.Lexicon.Version}
    {levels : List (TermLevel Nat Nat Nat)}
    {w v : List Received} (hw : TermLang version w) (hv : termAfterAll version levels v) :
    startRem version levels (w ++ v) := by
  match levels, hv with
  | .application _ _ arguments :: outer, hv =>
    obtain ⟨_, r, ⟨a, c, ha, hc, rfl⟩, hr, rfl⟩ := hv
    simp only [startRem]
    rw [List.append_assoc, ← List.append_assoc]
    exact cat_intro (rep_cons hw (by split <;> simpa using ha) (by simp)) (cat_intro hc hr)
  | [], hv => exact cat_intro hw hv
  | .letBinding .. :: _, hv => exact cat_intro hw hv
  | .binder .. :: _, hv => exact cat_intro hw hv
  | .annotation :: _, hv => exact cat_intro hw hv
  | .matchScrutinee :: _, hv => exact cat_intro hw hv
  | .matchCase .. :: _, hv => exact cat_intro hw hv

/-! ## Reserved words a lexer hands over -/

theorem lambda_lexical {version : Token.Version}
    (h : (Received.token (.reserved (Bridge.reserved (.general .lambda)))).OfVersion
      (Bridge.version version)) :
    versionAtLeast (Bridge.version version) .v2_7 := by
  simp only [Received.OfVersion] at h
  simp only [versionAtLeast]
  revert h
  cases version <;> decide

theorem match_lexical {version : Token.Version}
    (h : (Received.token (.reserved (Bridge.reserved (.general .match)))).OfVersion
      (Bridge.version version)) :
    versionAtLeast (Bridge.version version) .v2_6 := by
  simp only [Received.OfVersion] at h
  simp only [versionAtLeast]
  revert h
  cases version <;> decide

section

variable {version : BSmtLibSpec.Lexicon.Version}

theorem opened_app {w p : List Received} (hw : QualLang version w)
    (hp : plus (TermLang version) p) : OpenedLang version (w ++ (p ++ [closeItem])) := by
  obtain ⟨q, hq, rfl⟩ := hw
  obtain ⟨arguments, hvalid, hlen, rfl⟩ := terms_rep hp
  refine ⟨.application q arguments, ⟨by rintro rfl; simp at hlen, hq, hvalid⟩, ?_⟩
  simp [Tree.Term.tokens, paren, toks]

theorem opened_let {b t : List Received} (hb : plus (BindingLang version) b)
    (ht : TermLang version t) :
    OpenedLang version (wordItem "let" :: openItem :: (b ++ closeItem :: (t ++ [closeItem]))) := by
  obtain ⟨bindings, hvalid, hlen, rfl⟩ := bindings_rep hb
  obtain ⟨body, hbody, rfl⟩ := ht
  refine ⟨.let bindings body, ⟨by rintro rfl; simp at hlen, hvalid, hbody⟩, ?_⟩
  simp [Tree.Term.tokens, paren, toks, word]

theorem opened_sorted (binder : BSmtLibSpec.Grammar.SyntaxToken) {vars t : List Received}
    (hvars : plus (SortedVarLang version) vars) (ht : TermLang version t)
    (hterm : ∀ (variables : List Tree.SortedVar) (body : Tree.Term), variables ≠ [] →
      (∀ v ∈ variables, v.Valid version) → body.Valid version →
      ∃ term : Tree.Term, term.Valid version ∧ term.tokens =
        paren (binder :: paren (variables.flatMap Tree.SortedVar.tokens) ++ body.tokens)) :
    OpenedLang version
      (.token binder :: openItem :: (vars ++ closeItem :: (t ++ [closeItem]))) := by
  obtain ⟨variables, hvalid, hlen, rfl⟩ := sortedVars_rep hvars
  obtain ⟨body, hbody, rfl⟩ := ht
  obtain ⟨term, hterm, htokens⟩ := hterm variables body (by rintro rfl; simp at hlen) hvalid hbody
  exact ⟨term, hterm, by simp [htokens, paren, toks]⟩

theorem opened_match {t c : List Received} (hversion : versionAtLeast version .v2_6)
    (ht : TermLang version t) (hc : plus (CaseLang version) c) :
    OpenedLang version (wordItem "match" :: (t ++ openItem :: (c ++ [closeItem, closeItem]))) := by
  obtain ⟨scrutinee, hscrutinee, rfl⟩ := ht
  obtain ⟨cases, hvalid, hlen, rfl⟩ := cases_rep hc
  refine ⟨.match scrutinee cases, ⟨hversion, by rintro rfl; simp at hlen, hscrutinee, hvalid⟩, ?_⟩
  simp [Tree.Term.tokens, paren, toks, word]

theorem opened_annotated {t a : List Received} (ht : TermLang version t)
    (ha : plus (AttrLang version) a) :
    OpenedLang version (wordItem "!" :: (t ++ (a ++ [closeItem]))) := by
  obtain ⟨term, hterm, rfl⟩ := ht
  obtain ⟨attributes, hvalid, hlen, rfl⟩ := attrs_rep ha
  refine ⟨.annotated term attributes, ⟨by rintro rfl; simp at hlen, hterm, hvalid⟩, ?_⟩
  simp [Tree.Term.tokens, paren, toks, word]

theorem binding_of {s : Tree.Symbol} {t : List Received} (ht : TermLang version t) :
    BindingLang version (.token (.symbol s) :: (t ++ [closeItem]) |>.cons openItem) := by
  obtain ⟨term, hterm, rfl⟩ := ht
  exact ⟨s, term, hterm, by simp [paren, toks]⟩

theorem case_of {p t : List Received} (hp : PatternLang version p) (ht : TermLang version t) :
    CaseLang version (openItem :: (p ++ (t ++ [closeItem]))) := by
  obtain ⟨pattern, hpattern, rfl⟩ := hp
  obtain ⟨term, hterm, rfl⟩ := ht
  exact ⟨pattern, term, hpattern, hterm, by simp [paren, toks]⟩

end

/-! ## The end of a term -/

/-- The term parser's step at the end of a term: it is the result, or goes to the innermost
construct. -/
theorem termComplete_advances {version : BSmtLibSpec.Lexicon.Version}
    {state : TermState Nat Nat Nat Nat Nat} {item : Received}
    (levels : List (TermLevel Nat Nat Nat)) (term : Nat) {Q : Parser.ParseErrorCause Unit → Prop}
    (h : ∀ v, termAfterAll version levels v → termRem version state (item :: v)) :
    Sound (Advances (termRem version) (fun state _ => termRem version state) state item) Q
      (termComplete (H := List Event) levels term) := by
  match levels with
  | [] => exact Sound.pure fun _ => h [] rfl
  | .application f s arguments :: outer =>
    refine Sound.pure fun _ => ⟨fun u hu => h u ?_, termRem_nonempty _ _ trivial⟩
    simp only [termRem, startRem, push_isEmpty, Bool.false_eq_true, ite_false] at hu
    exact cat_assoc.mpr hu
  | .letBinding bindings symbol :: outer =>
    exact Sound.pure fun _ => ⟨fun u hu => h u hu, termRem_nonempty _ _ trivial⟩
  | .binder kind scope :: outer =>
    exact Sound.pure fun _ => ⟨fun u hu => h u hu, termRem_nonempty _ _ trivial⟩
  | .annotation :: outer =>
    refine Sound.pure fun _ => ⟨fun u hu => h u ?_, termRem_nonempty _ _ trivial⟩
    simpa [termRem, modeRem, attrRem, Parser.Category.Attribute.Internal.AttributeState.init,
        termAfterAll,
        termAfter]
      using hu
  | .matchScrutinee :: outer =>
    simp only [termComplete]
    call_step
    exact Sound.pure fun _ => ⟨fun u hu => h u hu, termRem_nonempty _ _ trivial⟩
  | .matchCase scrutinee cases pattern scope :: outer =>
    exact Sound.pure fun _ => ⟨fun u hu => h u hu, termRem_nonempty _ _ trivial⟩

/-! ## The steps of the term parser -/

theorem startBinder_sound {Q : Parser.ParseErrorCause Unit → Prop} (binder : SortedBinder)
    (variables : Array (Nodes.Symbol × Nat)) :
    Sound (fun _ => True) Q (startBinder (H := List Event) binder variables) := by
  cases binder <;> exact Sound.ofCall fun _ => ⟨_, _, rfl⟩

theorem endBinder_sound {Q : Parser.ParseErrorCause Unit → Prop} (kind : BinderKind)
    (scope body : Nat) :
    Sound (fun _ => True) Q (endBinder (H := List Event) kind scope body) := by
  rcases kind with _ | (_ | _) <;> exact Sound.ofCall fun _ => ⟨_, _, rfl⟩

section

variable (version : Token.Version) (levels : List
    (TermLevel Nat Nat Nat)) {token : Parser.Internal.Input}
  {item : Received} (hitem : Bridge.received token = some item)
  (hlex : item.OfVersion (Bridge.version version))

/-- The advance of a term parser's step from the state. -/
abbrev TermAdvance (state : TermState Nat Nat Nat Nat Nat) (item : Received)
    (x : Quiet.RPM (Parser.Internal.Step (TermState Nat Nat Nat Nat Nat) Nat)) : Prop :=
  Sound (Advances (termRem (Bridge.version version))
    (fun state _ => termRem (Bridge.version version) state) state item) Benign x

include hitem in
theorem termStep_start :
    TermAdvance version ⟨.start, levels⟩ item
      (termStep (H := List Event) version ⟨.start, levels⟩ token) := by
  cases token <;> simp only [termStep] <;> try fail_step
  · item_of hitem
    refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
    obtain ⟨o, r, ⟨t, ht, htokens⟩, hr, rfl⟩ := hu
    exact startRem_term (w := openItem :: o) ⟨t, ht, htokens.symm⟩ hr
  · match levels with
    | .application f s arguments :: outer =>
      simp only
      split
      · fail_step
      · rename_i hne
        item_of hitem
        call_step
        refine termComplete_advances outer _ fun v hv => ?_
        simp only [termRem, startRem, hne, Bool.false_eq_true, ite_false]
        exact cat_intro' rep_nil (cat_intro (tok_intro _) hv) rfl
    | [] => fail_step
    | .letBinding .. :: _ => fail_step
    | .binder .. :: _ => fail_step
    | .annotation :: _ => fail_step
    | .matchScrutinee :: _ => fail_step
    | .matchCase .. :: _ => fail_step
  · item_of hitem
    call_step
    exact termComplete_advances levels _ fun v hv => startRem_term ⟨.constant _, trivial, rfl⟩ hv
  · item_of hitem
    call_step
    exact termComplete_advances levels _ fun v hv =>
      startRem_term ⟨.identifier (.plain ⟨_, []⟩), by
        simp [Tree.Term.Valid, Tree.QualIdentifier.Valid, Tree.Identifier.Valid], rfl⟩ hv

include hitem hlex in
theorem termStep_opened :
    TermAdvance version ⟨.opened, levels⟩ item
      (termStep (H := List Event) version ⟨.opened, levels⟩ token) := by
  cases token <;> simp only [termStep, termOpened] <;> try fail_step
  · -- `(`: the head of an application in parentheses
    item_of hitem
    refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
    obtain ⟨_, r, ⟨q, _, hq, ⟨p, c, hp, rfl, rfl⟩, rfl⟩, hr, rfl⟩ := hu
    exact cat_intro' (opened_app (qualLang_of_opened _ hq) hp) hr (by simp <;> rfl)
  · -- a symbol: the function of an application
    rename_i function
    item_of hitem
    refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
    simp only [termRem, startRem, Array.isEmpty_empty, ite_true] at hu
    obtain ⟨p, _, hp, ⟨c, r, rfl, hr, rfl⟩, rfl⟩ := hu
    have hhead : QualLang (Bridge.version version) [.token (.symbol (Bridge.symbol function))] :=
      ⟨.plain ⟨_, []⟩, by simp [Tree.QualIdentifier.Valid, Tree.Identifier.Valid], rfl⟩
    exact cat_intro' (opened_app hhead hp) hr (by simp <;> rfl)
  · rename_i reserved
    cases reserved with
    | commandName => fail_step
    | general w =>
      cases w <;> simp only <;> try fail_step
      · -- `_`
        item_of hitem
        refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
        obtain ⟨i, r, hi, hr, rfl⟩ := hu
        obtain ⟨identifier, hident, htokens⟩ := identLang_indexed (cat_tok (x := wordItem "_") hi)
        have hopened : OpenedLang (Bridge.version version) (wordItem "_" :: i) :=
          ⟨.identifier (.plain identifier), hident, by
            simpa [Tree.Term.tokens, Tree.QualIdentifier.tokens] using htokens.symm⟩
        exact cat_intro' hopened hr rfl
      · -- `!`
        item_of hitem
        refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
        obtain ⟨t, _, ht, ⟨_, r, ⟨a, c, ha, rfl, rfl⟩, hr, rfl⟩, rfl⟩ := hu
        exact cat_intro' (opened_annotated ht ha) hr (by simp <;> rfl)
      · -- `as`
        item_of hitem
        refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
        obtain ⟨_, r, ⟨i, _, ⟨identifier, hident, rfl⟩, ⟨s, _, ⟨sort, hsort, rfl⟩, rfl, rfl⟩,
          rfl⟩, hr, rfl⟩ := hu
        have hopened : OpenedLang (Bridge.version version)
            (wordItem "as" :: (toks identifier.tokens ++ (toks sort.tokens ++ [closeItem]))) :=
          ⟨.identifier (.as identifier sort), ⟨hident, hsort⟩, by
            simp [Tree.Term.tokens, Tree.QualIdentifier.tokens, paren, toks, word]⟩
        exact cat_intro' hopened hr (by simp <;> rfl)
      · -- `lambda`
        item_of hitem
        refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _
          (listRem_paren_nonempty (sortedVarRem_nonempty _ .start) (sortedVarRem_nonempty _ .start)
            (by simp))⟩
        obtain ⟨_, r, ⟨l, _, hl, ⟨t, _, ht, rfl, rfl⟩, rfl⟩, hr, rfl⟩ := hu
        obtain ⟨vars, hvars, rfl⟩ := listRem_paren (fun _ h => h) hl
        exact cat_intro' (opened_sorted (word "lambda") hvars ht
          fun variables body hne hv hb => ⟨.lambda variables body,
            ⟨lambda_lexical hlex, hne, hv, hb⟩, rfl⟩) hr (by simp <;> rfl)
      · -- `let`
        item_of hitem
        refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
        obtain ⟨_, r, ⟨_, _, rfl, ⟨b, _, hb, ⟨_, _, rfl, ⟨t, _, ht, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩,
          hr, rfl⟩ := hu
        exact cat_intro' (opened_let hb ht) hr (by simp <;> rfl)
      · -- `exists`
        item_of hitem
        refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _
          (listRem_paren_nonempty (sortedVarRem_nonempty _ .start) (sortedVarRem_nonempty _ .start)
            (by simp))⟩
        obtain ⟨_, r, ⟨l, _, hl, ⟨t, _, ht, rfl, rfl⟩, rfl⟩, hr, rfl⟩ := hu
        obtain ⟨vars, hvars, rfl⟩ := listRem_paren (fun _ h => h) hl
        exact cat_intro' (opened_sorted (word "exists") hvars ht
          fun variables body hne hv hb => ⟨.quantified .exists variables body,
            ⟨hne, hv, hb⟩, rfl⟩) hr (by simp <;> rfl)
      · -- `forall`
        item_of hitem
        refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _
          (listRem_paren_nonempty (sortedVarRem_nonempty _ .start) (sortedVarRem_nonempty _ .start)
            (by simp))⟩
        obtain ⟨_, r, ⟨l, _, hl, ⟨t, _, ht, rfl, rfl⟩, rfl⟩, hr, rfl⟩ := hu
        obtain ⟨vars, hvars, rfl⟩ := listRem_paren (fun _ h => h) hl
        exact cat_intro' (opened_sorted (word "forall") hvars ht
          fun variables body hne hv hb => ⟨.quantified .forall variables body,
            ⟨hne, hv, hb⟩, rfl⟩) hr (by simp <;> rfl)
      · -- `match`
        item_of hitem
        refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
        obtain ⟨t, _, ht, ⟨_, r, ⟨_, _, rfl, ⟨c, _, hc, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩, rfl⟩, hr,
          rfl⟩, rfl⟩ := hu
        exact cat_intro' (opened_match (match_lexical hlex) ht hc) hr (by simp <;> rfl)

include hitem hlex in
theorem termStep_qualIdent (state : Parser.Category.QualifiedIdent.Internal.QualIdentState Nat) :
    TermAdvance version ⟨.qualIdent state, levels⟩ item
      (termStep (H := List Event) version ⟨.qualIdent state, levels⟩ token) := by
  simp only [termStep]
  refine Sound.bind (qualIdentStep_advances version state token item hitem hlex) fun r hr => ?_
  replace hr := hr.from (qualRem_nonempty _ _)
  cases r with
  | more state' =>
    exact Sound.pure fun _ => ⟨fun u hu => cat_left hr.1 hu, termRem_nonempty _ _ trivial⟩
  | done result =>
    call_step
    exact termComplete_advances levels _ fun v hv => cat_intro' hr hv rfl

include hitem hlex in
theorem termStep_applicationHead (state : Parser.Category.QualifiedIdent.Internal.QualIdentState
    Nat) :
    TermAdvance version ⟨.applicationHead state, levels⟩ item
      (termStep (H := List Event) version ⟨.applicationHead state, levels⟩ token) := by
  simp only [termStep]
  refine Sound.bind (qualIdentStep_advances version state token item hitem hlex) fun r hr => ?_
  replace hr := hr.from (qualRem_nonempty _ _)
  cases r with
  | more state' =>
    exact Sound.pure fun _ => ⟨fun u hu => cat_left (fun _ h => cat_left hr.1 h) hu,
      termRem_nonempty _ _ trivial⟩
  | done result =>
    refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
    simp only [termRem, startRem, Array.isEmpty_empty, ite_true] at hu
    obtain ⟨p, _, hp, ⟨c, r, hc, hr', rfl⟩, rfl⟩ := hu
    exact cat_intro' (cat_intro' hr (cat_intro hp hc) rfl) hr' (by simp)

include hitem in
theorem termStep_letBindingsOpen :
    TermAdvance version ⟨.letBindingsOpen, levels⟩ item
      (termStep (H := List Event) version ⟨.letBindingsOpen, levels⟩ token) := by
  cases token <;> simp only [termStep, Parser.Category.Token.Internal.expectOpen, pure_bind] <;> try
      fail_step
  item_of hitem
  refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
  simp only [termRem, modeRem, Array.isEmpty_empty, ite_true] at hu
  exact cat_left (fun _ h => cat_tok h) hu

include hitem in
theorem termStep_letBindingOpen (bindings : Array (Nodes.Symbol × Nat)) :
    TermAdvance version ⟨.letBindingOpen bindings, levels⟩ item
      (termStep (H := List Event) version ⟨.letBindingOpen bindings, levels⟩ token) := by
  cases token <;> simp only [termStep] <;> try fail_step
  · item_of hitem
    refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
    obtain ⟨_, r, ⟨_, _, ⟨s, rfl⟩, ⟨t, _, ht, ⟨_, _, rfl, ⟨b, l, hb, hl, rfl⟩, rfl⟩, rfl⟩, rfl⟩,
      hr, rfl⟩ := hu
    refine cat_intro' (cat_intro' (rep_cons (binding_of (s := s) ht) (by split <;> simpa using hb)
      (by simp)) hl rfl) hr (by simp)
  · split
    · fail_step
    · rename_i hne
      item_of hitem
      call_step
      refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
      obtain ⟨t, _, ht, ⟨_, r, rfl, hr, rfl⟩, rfl⟩ := hu
      simp only [termRem, modeRem, hne, Bool.false_eq_true, ite_false]
      exact cat_intro' (cat_intro' rep_nil (cat_intro' (tok_intro _) (cat_intro ht (tok_intro _))
        rfl) rfl) hr (by simp)

include hitem in
theorem termStep_letBindingSymbol (bindings : Array (Nodes.Symbol × Nat)) :
    TermAdvance version ⟨.letBindingSymbol bindings, levels⟩ item
      (termStep (H := List Event) version ⟨.letBindingSymbol bindings, levels⟩ token) := by
  cases token <;> simp only [termStep, Parser.Category.Token.Internal.expectSymbol,
      bind_pure_comp] <;>
    try fail_step
  item_of hitem
  refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
  obtain ⟨t, _, ht, ⟨a, r, ha, hr, rfl⟩, rfl⟩ := hu
  rename_i symbol _
  exact cat_intro' (cat_intro' (symbolLang_intro (Bridge.symbol symbol)) (cat_intro ht ha) rfl) hr
    (by simp)

include hitem in
theorem termStep_letBindingClose (bindings : Array (Nodes.Symbol × Nat)) :
    TermAdvance version ⟨.letBindingClose bindings, levels⟩ item
      (termStep (H := List Event) version ⟨.letBindingClose bindings, levels⟩ token) := by
  cases token <;> simp only [termStep, Parser.Category.Token.Internal.expectClose,
      pure_bind] <;> try
      fail_step
  item_of hitem
  refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
  exact cat_left (fun _ h => cat_tok (cat_mono (fun _ h => star_of_rep h) (fun _ h => h) h)) hu

include hitem hlex in
theorem termStep_sortedVars (binder : SortedBinder)
    (state : ListState (Parser.Category.SortedVar.Internal.SortedVarState Nat)
    (Nodes.Symbol × Nat)) :
    TermAdvance version ⟨.sortedVars binder state, levels⟩ item
      (termStep (H := List Event) version ⟨.sortedVars binder state, levels⟩ token) := by
  simp only [termStep]
  refine Sound.bindOn (listStep_advances version .start (sortedVarStep_advances version)
    (fun _ h => h) (sortedVarRem_nonempty _ .start) (sortedVarRem_nonempty _ .start) 1 none
    (by simp) state token item hitem hlex) (fun r => ∃ v, r = .done v)
    (fun _ _ _ hrun ⟨_, hv⟩ => by subst hv; exact listStep_done_silent _ _ _ _ _ _ _ _ hrun)
    fun r hr => ?_
  have hlist : (∃ u, termRem (Bridge.version version) ⟨.sortedVars binder state, levels⟩ u) →
      ∃ u, listRem (sortedVarRem (Bridge.version version))
        (SortedVarLang (Bridge.version version)) .start 1 none state u := by
    intro ⟨_, _, _, ⟨l, _, hl, _, rfl⟩, _, rfl⟩
    exact ⟨l, hl⟩
  cases r with
  | more state' =>
    refine Sound.pure fun hne => ?_
    have hr := hr (hlist hne)
    exact ⟨fun u hu => cat_left (fun _ h => cat_left hr.1 h) hu, termRem_nonempty _ _ hr.2⟩
  | done variables =>
    refine Sound.quietly ?_ ⟨variables, rfl⟩
    simp only
    split
    · fail_step
    · rename_i hne
      refine Sound.bind (startBinder_sound binder variables) fun _ _ => ?_
      refine Sound.pure fun hstate => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
      obtain ⟨t, _, ht, ⟨_, r, rfl, hr', rfl⟩, rfl⟩ := hu
      have hlen : 1 ≤ variables.size := by
        cases variables using Array.casesOn with
        | mk l => cases l <;> simp_all
      exact cat_intro' (cat_intro' (hr (hlist hstate) hlen (by simp))
        (cat_intro ht (tok_intro _)) rfl) hr' (by simp)

include hitem in
theorem termStep_binderClose (kind : BinderKind) (scope body : Nat) :
    TermAdvance version ⟨.binderClose kind scope body, levels⟩ item
      (termStep (H := List Event) version ⟨.binderClose kind scope body, levels⟩ token) := by
  cases token <;> simp only [termStep, Parser.Category.Token.Internal.expectClose,
      pure_bind] <;> try
      fail_step
  item_of hitem
  refine Sound.bind (endBinder_sound kind scope body) fun _ _ => ?_
  exact termComplete_advances levels _ fun v hv => cat_intro' (tok_intro _) hv rfl

include hitem in
theorem termStep_matchCasesOpen (scrutinee : Nat) :
    TermAdvance version ⟨.matchCasesOpen scrutinee, levels⟩ item
      (termStep (H := List Event) version ⟨.matchCasesOpen scrutinee, levels⟩ token) := by
  cases token <;> simp only [termStep, Parser.Category.Token.Internal.expectOpen, pure_bind] <;> try
      fail_step
  item_of hitem
  refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
  simp only [termRem, modeRem, Array.isEmpty_empty, ite_true] at hu
  exact cat_left (fun _ h => cat_tok h) hu

include hitem in
theorem termStep_matchCaseOpen (scrutinee : Nat) (cases : Array (Nodes.Pattern × Nat)) :
    TermAdvance version ⟨.matchCaseOpen scrutinee cases, levels⟩ item
      (termStep (H := List Event) version ⟨.matchCaseOpen scrutinee cases, levels⟩ token) := by
  cases token <;> simp only [termStep] <;> try fail_step
  · item_of hitem
    refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
    obtain ⟨_, r, ⟨p, _, hp, ⟨t, _, ht, ⟨_, _, rfl, ⟨c, l, hc, hl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hr,
      rfl⟩ := hu
    refine cat_intro' (cat_intro' (rep_cons (case_of hp ht) (by split <;> simpa using hc)
      (by simp)) hl rfl) hr (by simp)
  · split
    · fail_step
    · rename_i hne
      item_of hitem
      refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
      obtain ⟨_, r, rfl, hr, rfl⟩ := hu
      simp only [termRem, modeRem, hne, Bool.false_eq_true, ite_false]
      exact cat_intro' (cat_intro' rep_nil (cat_intro (tok_intro _) (tok_intro _)) rfl) hr
        (by simp)

include hitem hlex in
theorem termStep_matchPattern (scrutinee : Nat) (cases : Array (Nodes.Pattern × Nat))
    (state : Parser.Category.Pattern.Internal.PatternState) :
    TermAdvance version ⟨.matchPattern scrutinee cases state, levels⟩ item
      (termStep (H := List Event) version ⟨.matchPattern scrutinee cases state, levels⟩ token) := by
  simp only [termStep]
  refine Sound.bind (patternStep_advances version state token item hitem hlex) fun r hr => ?_
  replace hr := hr.from (patternRem_nonempty _ _)
  cases r with
  | more state' =>
    exact Sound.pure fun _ => ⟨fun u hu => cat_left (fun _ h => cat_left hr.1 h) hu,
      termRem_nonempty _ _ trivial⟩
  | done pattern =>
    call_step
    refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
    obtain ⟨t, _, ht, ⟨a, r, ha, hr', rfl⟩, rfl⟩ := hu
    exact cat_intro' (cat_intro' hr (cat_intro ht ha) rfl) hr' (by simp)

include hitem in
theorem termStep_matchCaseClose (scrutinee : Nat) (cases : Array (Nodes.Pattern × Nat))
    (pattern : Nodes.Pattern) (scope body : Nat) :
    TermAdvance version ⟨.matchCaseClose scrutinee cases pattern scope body, levels⟩ item
      (termStep (H := List Event) version
        ⟨.matchCaseClose scrutinee cases pattern scope body, levels⟩ token) := by
  cases token <;> simp only [termStep, Parser.Category.Token.Internal.expectClose,
      pure_bind] <;> try
      fail_step
  item_of hitem
  call_step
  refine Sound.pure fun _ => ⟨fun u hu => ?_, termRem_nonempty _ _ trivial⟩
  exact cat_left (fun _ h => cat_tok (cat_mono (fun _ h => star_of_rep h) (fun _ h => h) h)) hu

include hitem in
theorem termStep_matchClose (scrutinee : Nat) (cases : Array (Nodes.Pattern × Nat)) :
    TermAdvance version ⟨.matchClose scrutinee cases, levels⟩ item
      (termStep (H := List Event) version ⟨.matchClose scrutinee cases, levels⟩ token) := by
  cases token <;> simp only [termStep, Parser.Category.Token.Internal.expectClose,
      pure_bind] <;> try
      fail_step
  item_of hitem
  call_step
  exact termComplete_advances levels _ fun v hv => cat_intro' (tok_intro _) hv rfl

include hitem hlex in
theorem termStep_annotating (term : Nat) (state : AttributeState Nat Nat) :
    TermAdvance version ⟨.annotating term state, levels⟩ item
      (termStep (H := List Event) version ⟨.annotating term state, levels⟩ token) := by
  simp only [termStep]
  refine Sound.bindOn (attributeStep_advances version false true state token item hitem hlex)
    (fun r => ∃ a, r = .done a ∧ a.isEmpty = true)
    (fun _ _ _ hrun ⟨_, hv, he⟩ => by
      subst hv; exact attributeStep_done_silent _ _ _ _ _ _ _ hrun he)
    fun r hr => ?_
  replace hr := hr.from (attrRem_nonempty _ _ _ _)
  cases r with
  | more state' =>
    exact Sound.pure fun _ => ⟨fun u hu => cat_left hr.1 hu, termRem_nonempty _ _ trivial⟩
  | done attributes =>
    simp only
    split
    · rename_i hempty
      exact Sound.quietly (Sound.syntaxError trivial) ⟨attributes, rfl, hempty⟩
    · rename_i hne
      refine Sound.loudly ?_
      call_step
      exact termComplete_advances levels _ fun v hv =>
        cat_intro' (hr fun _ => by simpa using hne) hv rfl

end

/-- Every step of the term parser advances. -/
theorem termStep_advances (version : Token.Version) :
    StepsAdvance version (termStep (H := List Event) version)
      (termRem (Bridge.version version)) fun state _ => termRem (Bridge.version version) state := by
  intro ⟨mode, levels⟩ token item hitem hlex
  cases mode with
  | start => exact termStep_start version levels hitem
  | opened => exact termStep_opened version levels hitem hlex
  | qualIdent state => exact termStep_qualIdent version levels hitem hlex state
  | applicationHead state => exact termStep_applicationHead version levels hitem hlex state
  | letBindingsOpen => exact termStep_letBindingsOpen version levels hitem
  | letBindingOpen bindings => exact termStep_letBindingOpen version levels hitem bindings
  | letBindingSymbol bindings => exact termStep_letBindingSymbol version levels hitem bindings
  | letBindingClose bindings => exact termStep_letBindingClose version levels hitem bindings
  | sortedVars binder state => exact termStep_sortedVars version levels hitem hlex binder state
  | binderClose kind scope body => exact termStep_binderClose version levels hitem kind scope body
  | matchCasesOpen scrutinee => exact termStep_matchCasesOpen version levels hitem scrutinee
  | matchCaseOpen scrutinee cases =>
    exact termStep_matchCaseOpen version levels hitem scrutinee cases
  | matchPattern scrutinee cases state =>
    exact termStep_matchPattern version levels hitem hlex scrutinee cases state
  | matchCaseClose scrutinee cases pattern scope body =>
    exact termStep_matchCaseClose version levels hitem scrutinee cases pattern scope body
  | matchClose scrutinee cases => exact termStep_matchClose version levels hitem scrutinee cases
  | annotating term state => exact termStep_annotating version levels hitem hlex term state

end BSmtLib.Facts.Proofs.Parser.Rejection.Term
