module

public import BSmtLibSpec.Parser
public import BSmtLibSpec.Grammar.Properties
public import BSmtLibSpec.Facts.Proofs.Lexicon.Lemmas

@[expose] public section

/-!
# The reserved words that a parser takes

Every reserved word among the items that a parser takes for commands, a script's or those that a
declaration of a version that is not supported ends, is reserved in 2.7, which reserves the
words that every version reserves (`takes_reserved`).

The tokens of a tree hold a reserved word only as one of the fixed words of its productions,
all of which 2.7 reserves, or as a reserved s-expression, which a valid tree has only with a
word that its version reserves. The proof follows the token functions of each category.

Not trusted: everything here is proved.
-/

namespace BSmtLibSpec.Facts.Proofs.Reader.Words

open BSmtLibSpec.Lexicon BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Regex (Chars chars)
open BSmtLibSpec.Parser.Traversal

/-- The words that 2.7 reserves. -/
private abbrev words27 : List String := basicReservedWords .v2_7 ++ commandNames .v2_7

/-- The token is no reserved word, or reserved in 2.7. -/
private def Ok : SyntaxToken → Prop
  | .reserved w => w ∈ words27.map chars
  | _ => True

/-- Each of the tokens is no reserved word, or reserved in 2.7. -/
private def Good (tokens : List SyntaxToken) : Prop := ∀ t ∈ tokens, Ok t

private theorem good_nil : Good [] := by simp [Good]

private theorem good_cons {t : SyntaxToken} {ts : List SyntaxToken} (ht : Ok t) (h : Good ts) :
    Good (t :: ts) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ht
  · exact h x hx

private theorem good_append {a b : List SyntaxToken} (ha : Good a) (hb : Good b) :
    Good (a ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact ha x hx
  · exact hb x hx

private theorem good_paren {ts : List SyntaxToken} (h : Good ts) : Good (paren ts) :=
  good_cons trivial (good_append h (good_cons trivial good_nil))

private theorem good_flatMap {α : Type} {l : List α} {f : α → List SyntaxToken}
    (h : ∀ x ∈ l, Good (f x)) : Good (l.flatMap f) := by
  intro t ht
  obtain ⟨x, hx, ht⟩ := List.mem_flatMap.mp ht
  exact h x hx t ht

private theorem good_map {α : Type} {l : List α} {f : α → SyntaxToken} (h : ∀ x ∈ l, Ok (f x)) :
    Good (l.map f) := by
  intro t ht
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
  exact h x hx

private theorem ok_word {w : String} (h : w ∈ words27) : Ok (word w) :=
  List.mem_map_of_mem h

/-- 2.7 reserves every word that a version reserves. -/
private theorem version_words {version : Version} {w : Chars}
    (h : w ∈ (basicReservedWords version ++ commandNames version).map chars) :
    w ∈ words27.map chars := by
  have hv : ∀ x ∈ version.upTo, x ∈ Version.v2_7.upTo := by
    cases version <;> decide
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
  refine List.mem_map_of_mem ?_
  simp only [words27, basicReservedWords, commandNames, List.mem_append, List.mem_flatMap] at hs ⊢
  rcases hs with ⟨x, hx, hs⟩ | ⟨x, hx, hs⟩
  · exact .inl ⟨x, hv x hx, hs⟩
  · exact .inr ⟨x, hv x hx, hs⟩

/--
Proves `Good` of tokens built with `paren`, `::` and `++` from parts whose facts are hypotheses,
from tokens that are no reserved word, and from fixed words that 2.7 reserves.
-/
local macro "good" : tactic =>
  `(tactic| repeat' (first
    | assumption
    | exact good_nil
    | exact ok_word (by decide)
    | exact trivial
    | apply good_paren
    | apply good_cons
    | apply good_append))

private theorem spec_good (c : Tree.SpecConstant) : Ok c.token := by
  cases c <;> trivial

mutual

private theorem sexpr_good {version : Version} :
    (e : Tree.SExpr) → e.Valid version → Good e.tokens
  | .constant c, _ => by
    have := spec_good c
    rw [Tree.SExpr.tokens]
    good
  | .symbol _, _ => by
    rw [Tree.SExpr.tokens]
    good
  | .reserved _, h => by
    have : Ok (.reserved _) := version_words h.2
    rw [Tree.SExpr.tokens]
    good
  | .keyword _, _ => by
    rw [Tree.SExpr.tokens]
    good
  | .list items, h => by
    have := sexprAll_good items h
    rw [Tree.SExpr.tokens]
    good

private theorem sexprAll_good {version : Version} :
    (es : List Tree.SExpr) → Tree.SExpr.ValidAll version es → Good (Tree.SExpr.tokensAll es)
  | [], _ => good_nil
  | e :: es, h => by
    have := sexpr_good e h.1
    have := sexprAll_good es h.2
    rw [Tree.SExpr.tokensAll]
    good

end

private theorem identifier_good (i : Tree.Identifier) : Good i.tokens := by
  obtain ⟨symbol, indices⟩ := i
  cases indices with
  | nil =>
    rw [Tree.Identifier.tokens]
    good
  | cons index rest =>
    have : Good ((index :: rest).flatMap Tree.Index.tokens) := good_flatMap fun x _ => by
      cases x <;> (rw [Tree.Index.tokens]; good)
    rw [Tree.Identifier.tokens]
    · good
    · simp

mutual

private theorem sort_good : (s : Tree.«Sort») → Good s.tokens
  | .mk identifier [] => by
    rw [Tree.«Sort».tokens]
    exact identifier_good identifier
  | .mk identifier (a :: as) => by
    have := identifier_good identifier
    have := sortAll_good (a :: as)
    rw [Tree.«Sort».tokens]
    · good
    · simp

private theorem sortAll_good : (ss : List Tree.«Sort») → Good (Tree.«Sort».tokensAll ss)
  | [] => good_nil
  | s :: ss => by
    have := sort_good s
    have := sortAll_good ss
    rw [Tree.«Sort».tokensAll]
    good

end

private theorem attribute_good {version : Version} (a : Tree.Attribute) (h : a.Valid version) :
    Good a.tokens := by
  obtain ⟨keyword, value⟩ := a
  cases value with
  | none =>
    rw [Tree.Attribute.tokens]
    good
  | some value =>
    have hv : Good value.tokens := by
      cases value with
      | constant c =>
        have := spec_good c
        rw [Tree.AttributeValue.tokens]
        good
      | symbol _ =>
        rw [Tree.AttributeValue.tokens]
        good
      | list items =>
        have := sexprAll_good items h
        rw [Tree.AttributeValue.tokens]
        good
    rw [Tree.Attribute.tokens]
    good

private theorem qualIdentifier_good (q : Tree.QualIdentifier) : Good q.tokens := by
  have := identifier_good
  have := sort_good
  cases q <;> (rw [Tree.QualIdentifier.tokens]; good)
  all_goals apply_assumption

private theorem sortedVars_good (vs : List Tree.SortedVar) :
    Good (vs.flatMap Tree.SortedVar.tokens) := by
  refine good_flatMap fun ⟨_, s⟩ _ => ?_
  have := sort_good s
  rw [Tree.SortedVar.tokens]
  good

private theorem symbolOrWildcard_good (s : Tree.SymbolOrWildcard) : Ok s.token := by
  cases s <;> (rw [Tree.SymbolOrWildcard.token]; good)

private theorem pattern_good (p : Tree.Pattern) : Good p.tokens := by
  cases p with
  | single s =>
    have := symbolOrWildcard_good s
    rw [Tree.Pattern.tokens]
    good
  | constructor _ arguments =>
    have : Good (arguments.map Tree.SymbolOrWildcard.token) :=
      good_map fun s _ => symbolOrWildcard_good s
    rw [Tree.Pattern.tokens]
    good

mutual

private theorem term_good {version : Version} :
    (t : Tree.Term) → t.Valid version → Good t.tokens
  | .constant c, _ => by
    have := spec_good c
    rw [Tree.Term.tokens]
    good
  | .identifier q, _ => by
    rw [Tree.Term.tokens]
    exact qualIdentifier_good q
  | .application f arguments, h => by
    have := qualIdentifier_good f
    have := termAll_good arguments h.2.2
    rw [Tree.Term.tokens]
    good
  | .«let» bindings body, h => by
    have := bindings_good bindings h.2.1
    have := term_good body h.2.2
    rw [Tree.Term.tokens]
    good
  | .lambda variables body, h => by
    have := sortedVars_good variables
    have := term_good body h.2.2.2
    rw [Tree.Term.tokens]
    good
  | .quantified quantifier variables body, h => by
    have := sortedVars_good variables
    have := term_good body h.2.2
    have : Ok quantifier.word := by
      cases quantifier <;> (rw [Tree.Quantifier.word]; good)
    rw [Tree.Term.tokens]
    good
  | .«match» scrutinee cases, h => by
    have := term_good scrutinee h.2.2.1
    have := cases_good cases h.2.2.2
    rw [Tree.Term.tokens]
    good
  | .annotated term attributes, h => by
    have := term_good term h.2.1
    have : Good (attributes.flatMap Tree.Attribute.tokens) :=
      good_flatMap fun a ha => attribute_good a (h.2.2 a ha)
    rw [Tree.Term.tokens]
    good

private theorem termAll_good {version : Version} :
    (ts : List Tree.Term) → Tree.Term.ValidAll version ts → Good (Tree.Term.tokensAll ts)
  | [], _ => good_nil
  | t :: ts, h => by
    have := term_good t h.1
    have := termAll_good ts h.2
    rw [Tree.Term.tokensAll]
    good

private theorem bindings_good {version : Version} :
    (bs : List (Tree.Symbol × Tree.Term)) → Tree.Term.ValidBindings version bs →
      Good (Tree.Term.bindingTokens bs)
  | [], _ => good_nil
  | (_, t) :: bs, h => by
    have := term_good t h.1
    have := bindings_good bs h.2
    rw [Tree.Term.bindingTokens]
    good

private theorem cases_good {version : Version} :
    (cs : List (Tree.Pattern × Tree.Term)) → Tree.Term.ValidCases version cs →
      Good (Tree.Term.caseTokens cs)
  | [], _ => good_nil
  | (p, t) :: cs, h => by
    have := pattern_good p
    have := term_good t h.2.1
    have := cases_good cs h.2.2
    rw [Tree.Term.caseTokens]
    good

end

private theorem datatype_good (d : Tree.DatatypeDec) : Good d.tokens := by
  have hc : Good (d.constructors.flatMap Tree.ConstructorDec.tokens) := by
    refine good_flatMap fun ⟨_, selectors⟩ _ => ?_
    have : Good (selectors.flatMap Tree.SelectorDec.tokens) := good_flatMap fun ⟨_, s⟩ _ => by
      have := sort_good s
      rw [Tree.SelectorDec.tokens]
      good
    rw [Tree.ConstructorDec.tokens]
    good
  obtain ⟨parameters, constructors⟩ := d
  cases parameters with
  | nil =>
    rw [Tree.DatatypeDec.tokens]
    good
  | cons p ps =>
    have : Good (ps.map SyntaxToken.symbol) := good_map fun _ _ => trivial
    rw [Tree.DatatypeDec.tokens]
    · good
    · simp

private theorem functionDef_good {version : Version} (d : Tree.FunctionDef)
    (h : d.Valid version) : Good d.tokens := by
  obtain ⟨_, parameters, result, body⟩ := d
  have := sortedVars_good parameters
  have := sort_good result
  have := term_good body h.2.2
  rw [Tree.FunctionDef.tokens]
  good

private theorem command_good {version : Version} (c : Tree.Command) (h : c.Valid version) :
    Good c.tokens := by
  cases c
  case assert term =>
    have := term_good term h
    rw [Tree.Command.tokens, commandTokens]
    good
  case checkSatAssuming terms =>
    have := termAll_good terms h.2
    rw [Tree.Command.tokens, commandTokens]
    good
  case checkSatAssumingLiterals literals =>
    have : Good (literals.flatMap Tree.PropLiteral.tokens) := good_flatMap fun l _ => by
      cases l <;> (rw [Tree.PropLiteral.tokens]; good)
    rw [Tree.Command.tokens, commandTokens]
    good
  case declareConst sort =>
    have := sort_good sort
    rw [Tree.Command.tokens, commandTokens]
    good
  case declareDatatype datatype =>
    have := datatype_good datatype
    rw [Tree.Command.tokens, commandTokens]
    good
  case declareDatatypes sorts datatypes =>
    have : Good (sorts.flatMap Tree.SortDec.tokens) := good_flatMap fun _ _ => by
      rw [Tree.SortDec.tokens]
      good
    have : Good (datatypes.flatMap Tree.DatatypeDec.tokens) :=
      good_flatMap fun d _ => datatype_good d
    rw [Tree.Command.tokens, commandTokens]
    good
  case declareFun parameters result =>
    have := sortAll_good parameters
    have := sort_good result
    rw [Tree.Command.tokens, commandTokens]
    good
  case defineConst sort term =>
    have := sort_good sort
    have := term_good term h.2.2
    rw [Tree.Command.tokens, commandTokens]
    good
  case defineFun definition =>
    have := functionDef_good definition h
    rw [Tree.Command.tokens, commandTokens]
    good
  case defineFunRec definition =>
    have := functionDef_good definition h.2
    rw [Tree.Command.tokens, commandTokens]
    good
  case defineFunsRec declarations bodies =>
    have : Good (declarations.flatMap Tree.FunctionDec.tokens) :=
      good_flatMap fun ⟨_, parameters, result⟩ _ => by
        have := sortedVars_good parameters
        have := sort_good result
        rw [Tree.FunctionDec.tokens]
        good
    have := termAll_good bodies h.2.2.2.2
    rw [Tree.Command.tokens, commandTokens]
    good
  case defineSort parameters sort =>
    have : Good (parameters.map SyntaxToken.symbol) := good_map fun _ _ => trivial
    have := sort_good sort
    rw [Tree.Command.tokens, commandTokens]
    good
  case getValue terms =>
    have := termAll_good terms h.2
    rw [Tree.Command.tokens, commandTokens]
    good
  case setInfo info =>
    have := attribute_good info h
    rw [Tree.Command.tokens, commandTokens]
    good
  case setOption option =>
    have := attribute_good option h
    rw [Tree.Command.tokens, commandTokens]
    good
  all_goals (rw [Tree.Command.tokens, commandTokens]; good)

private theorem received_good {version : Version} {c : Tree.Command} (h : c.Valid version)
    {word : Chars} (hw : Received.token (.reserved word) ∈ c.tokens.map .token) :
    word ∈ words27.map chars := by
  obtain ⟨t, ht, he⟩ := List.mem_map.mp hw
  cases he
  exact command_good c h _ ht

/-- 2.7 reserves every reserved word that a parser takes. -/
theorem takes_reserved {version : Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (h : Takes version commands taken ending)
    {word : Chars} (hw : Received.token (.reserved word) ∈ taken) :
    word ∈ (basicReservedWords .v2_7 ++ commandNames .v2_7).map chars := by
  induction h with
  | done => simp at hw
  | command hv _ _ ih =>
    rcases List.mem_append.mp hw with hw | hw
    · exact received_good hv hw
    · exact ih hw
  | stop hv _ =>
    rcases List.mem_append.mp hw with hw | hw
    · exact received_good hv hw
    · simp at hw
  | refused hv _ => exact received_good hv hw

end BSmtLibSpec.Facts.Proofs.Reader.Words
