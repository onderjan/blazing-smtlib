module

public import BSmtLib.Facts.Proofs.Parser.Category.QualifiedIdent
public import BSmtLib.Facts.Proofs.Parser.Category.Multiple
public import BSmtLib.Parser.Category
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.SortedVar
import all BSmtLib.Parser.Category
import all BSmtLib.Parser.Category.Combinator

@[expose] public section

/-!
# The parser of sorted variables in parentheses on a cursor

`ParenSortedVarsParser` is the list parser enclosed in `(` and `)` of the sorted variable
parser; its lemma is the list parser's (`Category.Multiple`) with the sorted variable parser's
(`Category.SortedVar`) for each variable.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.SortedVars

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category BSmtLib.Parser.Category.Combinator BSmtLib.Parser.Category.SortedVar
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Parser.Adapters.Cursor (Takes Reads noPoints)
open BSmtLib.Facts.Parser.Adapters.Outcome (Finishes)
open BSmtLib.Facts.Proofs.Parser.Category.Multiple BSmtLib.Facts.Proofs.Parser.Category.SortedVar
open BSmtLib.Facts.Proofs.Parser.Category.QualifiedIdent
open BSmtLib.Facts.Proofs.Parser.Lemmas BSmtLib.Facts.Proofs.Parser.Tokens

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {version : Token.Version}
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

/-- The sorted variables as values of the sorted variable parser. -/
theorem sortedVars_values (hA : TermAgrees h) : (variables : List Tree.SortedVar) →
    (∀ variable_ ∈ variables, variable_.Valid (Bridge.version version)) →
    ∀ {tokens : List Parser.Internal.Input},
      Stands tokens (variables.flatMap Tree.SortedVar.tokens) →
    ∃ (values :
        List (List Parser.Internal.Input × PM H (Plain.SymbolBuf × Traits.Handler.«Sort» H)))
      (symbols : List Plain.Symbol),
      ValuesParse version (SortedVarParser.new (H := H)) values ∧ valuesTokens values = tokens ∧
      symbols.map Bridge.symbol = variables.map (·.symbol) ∧
      (values.mapM fun value => value.2) =
        (fun pairs => (symbols.map Plain.Symbol.intoOwned).zip (pairs.map (·.2))) <$>
          adaptRun (Traversal.sortedVars noPoints h variables)
  | [], _, _, hs => by
    have := Stands.eq_nil hs
    subst this
    exact ⟨[], [], fun _ hv => absurd hv (List.not_mem_nil), rfl, rfl, by
      simp [Traversal.sortedVars]⟩
  | first :: rest, hvalid, _, hs => by
    simp only [List.flatMap_cons] at hs
    obtain ⟨firstTokens, restTokens, rfl, hfirst, hrest⟩ := Stands.split hs
    obtain ⟨symbol, hsymbol, hparses⟩ := sortedVar_parses (H := H) hA first
      (hvalid first (List.mem_cons_self ..)) hfirst
    obtain ⟨values, symbols, hvalues, htokens, hsymbols, hprogram⟩ := sortedVars_values hA rest
      (fun v hv => hvalid v (List.mem_cons_of_mem _ hv)) hrest
    obtain ⟨name, sort⟩ := first
    obtain ⟨inner, rfl, _⟩ := Stands.split_paren hfirst
    refine ⟨(.parenOpen :: (inner ++ [.parenClose]),
      (fun sort => (symbol.intoOwned, sort)) <$> adaptRun (Traversal.sort noPoints h sort)) ::
      values, symbol :: symbols, ?_, ?_, ?_, ?_⟩
    · intro value hvalue
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact ⟨hparses, _, _, rfl, by simp⟩
      · exact hvalues value hvalue
    · simp [valuesTokens, htokens]
    · simp [hsymbols, hsymbol]
    · rw [List.mapM_cons, hprogram]
      simp only [Traversal.sortedVars, takeAll_noPoints, take_noPoints, pure_bind,
        adaptRun_bind, adaptRun_pure, map_bind, bind_map_left, map_pure]
      rfl

/-- The parser of sorted variables in parentheses on the tokens of valid sorted variables in
parentheses: it finishes with their symbols, through the bridge, and their handled sorts, making
the traversal's calls for the sorts. -/
theorem parenSortedVars_parses (hA : TermAgrees h) (variables : List Tree.SortedVar)
    (hvalid : ∀ variable_ ∈ variables, variable_.Valid (Bridge.version version))
    {tokens : List Parser.Internal.Input}
    (hs : Stands tokens (paren (variables.flatMap Tree.SortedVar.tokens))) :
    ∃ symbols : List Plain.Symbol, symbols.map Bridge.symbol = variables.map (·.symbol) ∧
      Finishes version
        (ParenSortedVarsParser.new (ClosedMultipleParser.new (SortedVarParser.new (H := H))) :
          ParenSortedVarsParser H) tokens
        ((fun pairs => ((symbols.map Plain.Symbol.intoOwned).zip (pairs.map (·.2))).toArray) <$>
          adaptRun (Traversal.sortedVars noPoints h variables))
        (ParenSortedVarsParser.new (ClosedMultipleParser.new SortedVarParser.new)) := by
  obtain ⟨inner, rfl, hinner⟩ := Stands.split_paren hs
  obtain ⟨values, symbols, hvalues, htokens, hsymbols, hprogram⟩ :=
    sortedVars_values hA variables hvalid hinner
  refine ⟨symbols, hsymbols, ?_⟩
  have hparses := parenMultiple_parses (H := H) hvalues
  rw [htokens, hprogram, Functor.map_map] at hparses
  exact hparses

end

end BSmtLib.Facts.Proofs.Parser.Category.SortedVars
