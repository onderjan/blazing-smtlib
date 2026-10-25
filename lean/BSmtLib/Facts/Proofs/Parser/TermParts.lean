module

public import BSmtLib.Facts.Proofs.Parser.Attribute
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Ident
import all BSmtLib.Parser.Category.Pattern
import all BSmtLib.Parser.Category.QualifiedIdent
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Category.SortedVar
import all BSmtLib.Parser.Category.Token
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# The parts of terms against the traversal

The parsers that the term parser runs inside its modes: the parenthesised forms of a qualified
identifier from the state after their word (`_` or `as`), patterns, and sorted variables, one
and as a list. None of them has a stack of its own; each lemma reads one part and ends.

A part whose value the parser holds as its own syntax (an identifier, a pattern, a symbol) is
related to the spec's through the bridge: the lemma gives the parser's value, and says that the
bridge maps it to the tree's.
-/

namespace BSmtLib.Facts.Proofs.Parser.TermParts

open BSmtLibSpec.Grammar
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.Ident.Internal (IdentState)
open BSmtLib.Parser.Category.Sort.Internal (SortState sortStep)
open BSmtLib.Parser.Category.SortedVar.Internal (SortedVarState sortedVarStep)
open BSmtLib.Parser.Category.Pattern.Internal (PatternState)
open BSmtLib.Parser.Category.QualifiedIdent.Internal (QualIdentState qualIdentStep)
open BSmtLib.Parser.Category.Combinator.Internal (ListState)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Lemmas
open BSmtLib.Facts.Proofs.Parser.List BSmtLib.Facts.Proofs.Parser.Reserved
open BSmtLib.Facts.Proofs.Parser.SExpr BSmtLib.Facts.Proofs.Parser.«Sort»
open BSmtLib.Facts.Proofs.Parser.Tokens BSmtLib.Facts.Proofs.Parser.Tokens.Stands

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal

/-- The sorted variables as the spec hands them over, from the parser's. -/
def Bridge.specPairs {S : Type} (variables : List (Plain.Symbol × S)) :
    List (Tree.Symbol × S) :=
  variables.map fun (symbol, sort) => (Bridge.symbol symbol, sort)

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {points : Points (StateT H m)} {version : Token.Version}

/-! ## Qualified identifiers in parentheses -/

/--
After `(` `_`, the qualified identifier parser reads the rest of an indexed identifier and ends
with it, unqualified.
-/
theorem qualIndexed_runs {name : Tree.Symbol} {indices : List Tree.Index}
    (hvalid : ∀ index ∈ indices, index.Valid (Bridge.version version)) (hne : indices ≠ [])
    {symbolToken : Parser.Internal.Input} {tokens : List Parser.Internal.Input}
    (hsymbol : Bridge.received symbolToken = some (.token (.symbol name)))
    (hs : Stands tokens (indices.flatMap Tree.Index.tokens)) :
    ∃ head : Nodes.Ident, Bridge.identifier head = ⟨name, indices⟩ ∧
      Runs points (qualIdentStep (H := H) version) (.indexed .afterUnderscore)
        (symbolToken :: (tokens ++ [.parenClose]))
        (ticks points (symbolToken :: (tokens ++ [.parenClose])))
        fun _ => pure (.done (head, none)) := by
  obtain ⟨head, hhead, hruns⟩ := indexed_runs (H := H) (points := points) hvalid hne hsymbol hs
  refine ⟨head, hhead, ?_⟩
  exact (Runs.embed (outer := qualIdentStep version) QualIdentState.indexed
    (fun head => pure (.done (head, none)))
    (fun state token => by
      simp only [Parser.Category.QualifiedIdent.Internal.qualIdentStep]
      congr 1
      funext step
      cases step <;> rfl)
    hruns).congr rfl (by funext; simp [Parser.Internal.Step.wrap])

/-- The tokens of an identifier start with a token other than `)`. -/
theorem identifier_first {name : Tree.Identifier} {tokens : List Parser.Internal.Input}
    (hs : Stands tokens name.tokens) :
    ∃ token rest, tokens = token :: rest ∧ token ≠ .parenClose := by
  match name with
  | ⟨_, []⟩ =>
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨_, rfl, _⟩ := Parser.Internal.Input.received_symbol htoken
    exact ⟨_, _, rfl, by simp⟩
  | ⟨_, _ :: _⟩ =>
    obtain ⟨_, _, rfl, _, _⟩ := Stands.indexed (List.cons_ne_nil _ _) hs
    exact ⟨_, _, rfl, by simp⟩

/-- From its start, the identifier parser reads an identifier and ends with it. -/
theorem ident_runs {name : Tree.Identifier} (hname : name.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input} (hs : Stands tokens name.tokens) :
    ∃ head : Nodes.Ident, Bridge.identifier head = name ∧
      Runs points (IdentState.step (H := H) version) .start tokens (ticks points tokens)
        fun _ => pure (.done head) := by
  match name with
  | ⟨symbolName, []⟩ =>
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
    refine ⟨⟨symbol, #[]⟩, by simp [Bridge.identifier], ?_⟩
    exact (Runs.token (program := pure ()) (by simp [IdentState.step])).congr (by simp) rfl
  | ⟨symbolName, index :: indices⟩ =>
    obtain ⟨symbolToken, rest, rfl, hsymbol, hrest⟩ := Stands.indexed (List.cons_ne_nil _ _) hs
    obtain ⟨head, hhead, hruns⟩ := indexed_runs (H := H) (points := points) hname
      (List.cons_ne_nil _ _) hsymbol hrest
    refine ⟨head, hhead, ?_⟩
    rw [show Parser.Internal.Input.parenOpen :: Parser.Internal.Input.reserved
        (.general .underscore) :: symbolToken ::
        (rest ++ [.parenClose]) = [.parenOpen] ++ ([.reserved (.general .underscore)] ++
        (symbolToken :: (rest ++ [.parenClose]))) by simp]
    refine (Runs.append (middle := fun _ => IdentState.opened)
      (Runs.token_more (step := IdentState.step (H := H) version) (state := .start)
        (token := .parenOpen) (by simp [IdentState.step])) fun _ =>
      Runs.append (middle := fun _ => IdentState.afterUnderscore)
        (Runs.token_more (step := IdentState.step (H := H) version) (state := .opened)
          (token := .reserved (.general .underscore)) (by simp [IdentState.step])) fun _ =>
        hruns).congr ?_ rfl
    simp

variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

/--
After `(` `as`, the qualified identifier parser reads the identifier, the sort and the `)`, and
ends with the identifier qualified by the sort.
-/
theorem qualAs_runs (hA : TermAgrees h) {name : Tree.Identifier} {qualification : Tree.«Sort»}
    (hname : name.Valid (Bridge.version version))
    (hsort : qualification.Valid (Bridge.version version))
    {identifierTokens sortTokens : List Parser.Internal.Input}
        (hs₁ : Stands identifierTokens name.tokens)
    (hs₂ : Stands sortTokens qualification.tokens) :
    ∃ head : Nodes.Ident, Bridge.identifier head = name ∧
      Runs points (qualIdentStep version) (.qualifiedIdent .start)
        (identifierTokens ++ (sortTokens ++ [.parenClose]))
        (do
          ticks points identifierTokens
          let sort ← adaptRun (Traversal.sort points h qualification)
          tick points .parenClose
          pure sort)
        fun sort => pure (.done (head, some sort)) := by
  obtain ⟨head, hhead, hident⟩ := ident_runs (H := H) (points := points) hname hs₁
  refine ⟨head, hhead, ?_⟩
  have hidentEmbed := Runs.embed (outer := qualIdentStep (H := H) version)
    QualIdentState.qualifiedIdent (fun identifier => pure (.more (.sort identifier .init)))
    (fun state token => by
      simp only [Parser.Category.QualifiedIdent.Internal.qualIdentStep]
      congr 1
      funext step
      cases step <;> rfl)
    hident
  have hsortEmbed := Runs.embed (outer := qualIdentStep version)
    (QualIdentState.sort head) (fun sort => pure (.more (.close head sort)))
    (fun state token => by
      simp only [Parser.Category.QualifiedIdent.Internal.qualIdentStep]
      congr 1
      funext step
      cases step <;> rfl)
    (sort_runs (points := points) hA qualification hsort hs₂ [])
  have hclose : ∀ sort, Runs points (qualIdentStep version) (.close head sort) [.parenClose]
      (do tick points .parenClose; pure sort) fun sort => pure (.done (head, some sort)) :=
    fun _ => Runs.token (by simp [Parser.Category.QualifiedIdent.Internal.qualIdentStep,
        Parser.Category.Token.Internal.expectClose])
  exact Runs.append (middle := fun _ => QualIdentState.sort head .init)
    (hidentEmbed.congr rfl (by funext; simp [Parser.Internal.Step.wrap])) fun _ =>
      Runs.append (middle := fun sort => QualIdentState.close head sort)
        ((show (SortState.init : SortState (Traits.Handler.«Sort» H)) =
                ({ mode := .start, levels := [] } : SortState (Traits.Handler.«Sort» H)) from rfl) ▸
          hsortEmbed.congr rfl (by funext; simp [Parser.Internal.Step.wrap, sortPush])) hclose

end

/-! ## Patterns -/

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {points : Points (StateT H m)} {version : Token.Version}

theorem versionAtLeast_wildcard (h : versionAtLeast (Bridge.version version) .v2_7) :
    PatternState.wildcardAllowed version = true := by
  simp [PatternState.wildcardAllowed, versionAtLeast_v2_7 h]

/-- The token standing for a symbol or the wildcard of the version, as the pattern parser
reads it. -/
theorem symbolOrWildcard_runs {item : Tree.SymbolOrWildcard}
    (hvalid : item.Valid (Bridge.version version)) {token : Parser.Internal.Input}
    (htoken : Bridge.received token = some (.token item.token)) :
    ∃ parsed, PatternState.symbolOrWildcard? version token = some parsed ∧
      Bridge.symbolOrWildcard parsed = item ∧ token ≠ .parenClose := by
  cases item with
  | symbol name =>
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
    exact ⟨.symbol symbol, by simp [PatternState.symbolOrWildcard?], rfl, by simp⟩
  | wildcard =>
    have := Parser.Internal.Input.received_word (word := .general .underscore) htoken
    subst this
    exact ⟨.wildcard, by simp [PatternState.symbolOrWildcard?,
      versionAtLeast_wildcard (by simpa [Tree.SymbolOrWildcard.Valid] using hvalid)], rfl,
      by simp⟩

/-- The arguments of a constructor pattern, appended to those found so far. -/
theorem patternArguments_runs : (arguments : List Tree.SymbolOrWildcard) →
    (∀ argument ∈ arguments, argument.Valid (Bridge.version version)) →
    ∀ {tokens : List Parser.Internal.Input},
        Stands tokens (arguments.map Tree.SymbolOrWildcard.token) →
    ∀ (constructor : Plain.Symbol) (found : Array Nodes.SimplePattern),
    ∃ parsed : Array Nodes.SimplePattern,
      parsed.toList.map Bridge.symbolOrWildcard = arguments ∧
      Runs points (PatternState.step (H := H) version) (.arguments constructor found) tokens
        (ticks points tokens) fun _ => pure (.more (.arguments constructor (found ++ parsed)))
  | [], _, _, hs, constructor, found => by
    have := Stands.eq_nil hs
    subst this
    exact ⟨#[], rfl, (Runs.nil () (by simp)).congr (by simp) rfl⟩
  | first :: rest, hvalid, _, hs, constructor, found => by
    obtain ⟨token, tokens, rfl, htoken, hrest⟩ := Stands.split_cons hs
    obtain ⟨parsed, hparsed, hfirst, hne⟩ := symbolOrWildcard_runs
      (hvalid first (List.mem_cons_self ..)) htoken
    obtain ⟨others, hothers, hruns⟩ := patternArguments_runs rest
      (fun a ha => hvalid a (List.mem_cons_of_mem _ ha)) hrest constructor (found.push parsed)
    refine ⟨#[parsed] ++ others, by simp [hothers, hfirst], ?_⟩
    rw [show token :: tokens = [token] ++ tokens by rfl]
    refine (Runs.append (middle := fun _ => .arguments constructor (found.push parsed))
      (Runs.token_more (by
        cases token <;> simp_all [PatternState.step])) fun _ => hruns).congr ?_ ?_
    · simp
    · funext
      simp

/-- From its start, the pattern parser reads a pattern and ends with it. -/
theorem pattern_runs {pattern : Tree.Pattern} (hvalid : pattern.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input} (hs : Stands tokens pattern.tokens) :
    ∃ parsed : Nodes.Pattern, Bridge.pattern parsed = pattern ∧
      Runs points (PatternState.step (H := H) version) .start tokens (ticks points tokens)
        fun _ => pure (.done parsed) := by
  cases pattern with
  | single item =>
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨parsed, hparsed, hitem, hne⟩ := symbolOrWildcard_runs hvalid htoken
    refine ⟨.simple parsed, by simp [Bridge.pattern, hitem], ?_⟩
    refine (Runs.token (program := pure ()) ?_).congr (by simp) rfl
    cases token <;> simp_all [PatternState.step, PatternState.symbolOrWildcard?,
        Parser.Internal.Input.isWord]
  | constructor name arguments =>
    obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
    obtain ⟨symbolToken, argumentTokens, rfl, hsymbol, hargumentTokens⟩ :=
      Stands.split_cons hinner
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbol
    obtain ⟨parsed, hmap, hruns⟩ := patternArguments_runs (H := H) (points := points) arguments
      hvalid.2 hargumentTokens symbol #[]
    have hparsed : parsed.isEmpty = false := by
      cases parsed using Array.recOn with
      | mk list => cases list <;> simp_all [Tree.Pattern.Valid]
    have hpos : 0 < (#[] ++ parsed).size :=
      Nodes.PatternApplication.Internal.size_pos (by simp [hparsed])
    refine ⟨.application ⟨symbol, #[] ++ parsed, hpos⟩, by simp [Bridge.pattern, hmap], ?_⟩
    have hclose : Runs points (PatternState.step (H := H) version)
        (.arguments symbol (#[] ++ parsed)) [.parenClose] (do tick points .parenClose; pure ())
        fun _ => pure (.done (.application ⟨symbol, #[] ++ parsed, hpos⟩)) :=
      Runs.token (by simp [PatternState.step, hparsed])
    rw [show Parser.Internal.Input.parenOpen ::
        (Parser.Internal.Input.symbol symbol :: argumentTokens ++ [.parenClose]) =
      [.parenOpen] ++ ([.symbol symbol] ++ (argumentTokens ++ [.parenClose])) by simp]
    refine (Runs.append (middle := fun _ => PatternState.opened)
      (Runs.token_more (by simp [PatternState.step])) fun _ =>
        Runs.append (middle := fun _ => PatternState.arguments symbol #[])
          (Runs.token_more (by simp [PatternState.step])) fun _ =>
            Runs.append hruns fun _ => hclose).congr ?_ rfl
    simp [ticks_append]

end

/-! ## Sorted variables -/

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {points : Points (StateT H m)} {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

/-- From its start, the sorted variable parser reads `(` ⟨symbol⟩ ⟨sort⟩ `)` and ends with it. -/
theorem sortedVar_runs (hA : TermAgrees h) (var : Tree.SortedVar)
    (hvalid : var.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens var.tokens) :
    ∃ (symbol : Plain.Symbol) (sortTokens : List Parser.Internal.Input),
      tokens = .parenOpen :: .symbol symbol :: (sortTokens ++ [.parenClose]) ∧
      Bridge.symbol symbol = var.symbol ∧ Stands sortTokens var.sort.tokens ∧
      Runs points (sortedVarStep version) .start tokens
        (do
          tick points .parenOpen
          tick points (.symbol symbol)
          let sort ← adaptRun (Traversal.sort points h var.sort)
          tick points .parenClose
          pure (symbol, sort))
        fun result => pure (.done result) := by
  obtain ⟨varSymbol, varSort⟩ := var
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
  obtain ⟨symbolToken, sortTokens, rfl, hsymbol, hsortTokens⟩ := Stands.split_cons hinner
  obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol hsymbol
  refine ⟨symbol, sortTokens, rfl, rfl, hsortTokens, ?_⟩
  have hsortEmbed := Runs.embed (outer := sortedVarStep version)
    (SortedVarState.sort symbol) (fun sort => pure (.more (.close symbol sort)))
    (fun state token => by
      simp only [Parser.Category.SortedVar.Internal.sortedVarStep]
      congr 1
      funext step
      cases step <;> rfl)
    (sort_runs (points := points) hA varSort hvalid hsortTokens [])
  have hclose : ∀ sort, Runs points (sortedVarStep version) (.close symbol sort) [.parenClose]
      (do tick points .parenClose; pure (symbol, sort)) fun result => pure (.done result) :=
    fun _ => Runs.token (by simp [Parser.Category.SortedVar.Internal.sortedVarStep,
        Parser.Category.Token.Internal.expectClose])
  rw [show Parser.Internal.Input.parenOpen ::
      (Parser.Internal.Input.symbol symbol :: sortTokens ++ [.parenClose]) =
    [.parenOpen] ++ ([.symbol symbol] ++ (sortTokens ++ [.parenClose])) by simp]
  exact (Runs.append (middle := fun _ => SortedVarState.opened)
    (Runs.token_more (by simp [Parser.Category.SortedVar.Internal.sortedVarStep,
    Parser.Category.Token.Internal.expectOpen])) fun _ =>
      Runs.append (middle := fun _ => SortedVarState.sort symbol .init)
        (Runs.token_more (by simp [Parser.Category.SortedVar.Internal.sortedVarStep,
            Parser.Category.Token.Internal.expectSymbol])) fun _ =>
          Runs.append (middle := fun sort => SortedVarState.close symbol sort)
            ((show (SortState.init : SortState (Traits.Handler.«Sort» H)) =
                ({ mode := .start, levels := [] } : SortState (Traits.Handler.«Sort» H)) from rfl) ▸
              hsortEmbed.congr rfl (by funext; simp [Parser.Internal.Step.wrap,
                  sortPush])) hclose).congr
    (by simp) rfl

/--
From between elements, the list of sorted variables reads the tokens of sorted variables with
the effects of a program whose variables are the traversal's, through the bridge, and appends
them to those found so far.
-/
theorem sortedVars_runs (hA : TermAgrees h) (variables : List Tree.SortedVar)
    (hvalid : ∀ var ∈ variables,
        var.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (variables.flatMap Tree.SortedVar.tokens)) :
    ∃ program : PM H (List (Plain.Symbol × Traits.Handler.«Sort» H)),
      Bridge.specPairs <$> program = adaptRun (Traversal.sortedVars points h variables) ∧
      ∀ found : Array (Plain.Symbol × Traits.Handler.«Sort» H),
      Runs points (ListState.step .start (sortedVarStep version) none)
        (ListState.between .start found) tokens program
        fun handled => pure (.more (ListState.between .start (found ++ handled.toArray))) := by
  induction variables generalizing tokens with
  | nil =>
    have := Stands.eq_nil hs
    subst this
    exact ⟨pure [], by simp [Traversal.sortedVars, Bridge.specPairs],
      fun found => (Runs.nil [] (by simp)).congr rfl rfl⟩
  | cons var rest ih =>
    simp only [List.flatMap_cons] at hs
    obtain ⟨first, others, rfl, hs₁, hs₂⟩ := Stands.split hs
    obtain ⟨symbol, sortTokens, rfl, hsymbol, -, hruns⟩ := sortedVar_runs (points := points) hA
      var (hvalid var (List.mem_cons_self ..)) hs₁
    obtain ⟨program, hprogram, hrest⟩ := ih (fun v hv => hvalid v (List.mem_cons_of_mem _ hv)) hs₂
    refine ⟨do
      tick points .parenOpen
      tick points (.symbol symbol)
      let sort ← adaptRun (Traversal.sort points h var.sort)
      tick points .parenClose
      let others ← program
      pure ((symbol, sort) :: others), ?_, fun found => ?_⟩
    · obtain ⟨varSymbol, varSort⟩ := var
      have hsymbolToken : Bridge.received (Parser.Internal.Input.symbol symbol) =
          some (.token (.symbol varSymbol)) := by
        simp only at hsymbol
        simp [Bridge.received, hsymbol]
      simp [Traversal.sortedVars, ← hprogram, Bridge.specPairs, hsymbol,
        adaptRun_takeAll (Stands.cons (token := .parenOpen) rfl (Stands.cons hsymbolToken nil)),
        adaptRun_take (token := .parenClose) rfl]
    · refine (Runs.append (middle := fun r => ListState.between .start (found.push r))
        (ListState.item_runs_done found (by simp) (by simp) hruns) fun r =>
          Runs.map_program (f := (r :: ·)) ((hrest (found.push r)).congr rfl
            (by funext; simp))).congr ?_ rfl
      simp

end

end BSmtLib.Facts.Proofs.Parser.TermParts
