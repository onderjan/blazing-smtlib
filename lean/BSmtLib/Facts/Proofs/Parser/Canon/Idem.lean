module

public import BSmtLib.Facts.Proofs.Parser.Canon.Loop
import all BSmtLib.Lexicon.Value
import all BSmtLib.Grammar.Multiple
import all BSmtLib.Grammar.Multiple.MatchCases

@[expose] public section

/-!
# Canonicalising twice

The view of a view's content is its own content's view (`Loop.canonSlice_canonSlice`), so
canonicalising a state of the parser twice is canonicalising it once.
-/

namespace BSmtLib.Facts.Proofs.Parser.Canon.Idem

open BSmtLib.Grammar.Multiple (FunctionSignature)
open BSmtLib.Grammar (Multiple)
open BSmtLib.Parser BSmtLib.Grammar.Nodes
open BSmtLib.Lexicon.Value (Symbol Numeral Decimal HexDigits BinDigits
  StringContent Keyword)
open Basic States Simp Loop
open BSmtLib.Parser.Category.Attribute BSmtLib.Parser.Category.Combinator
open BSmtLib.Parser.Category.Ident BSmtLib.Parser.Category.Pattern
open BSmtLib.Parser.Category.QualifiedIdent BSmtLib.Parser.Category.SExpr
open BSmtLib.Parser.Category.«Sort» BSmtLib.Parser.Category.SortedVar
open BSmtLib.Parser.Category.Term BSmtLib.Parser.Command BSmtLib.Parser.Command.Internal.Datatype
open BSmtLib.Parser.Command.Internal.Definition BSmtLib.Parser.Command.Internal.Function
open BSmtLib.Parser.Command.Internal.Standard BSmtLib.Parser.Script
open BSmtLibSpec.Parser.Properties (Event)
open BSmtLib.Parser.Category.Attribute.Internal
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Parser.Category.Ident.Internal
open BSmtLib.Parser.Category.Pattern.Internal
open BSmtLib.Parser.Category.QualifiedIdent.Internal
open BSmtLib.Parser.Category.SExpr.Internal
open BSmtLib.Parser.Category.«Sort».Internal
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.Term.Internal
open BSmtLib.Parser.Command.Internal

/-- Canonicalising a value twice is canonicalising it once. -/
class CanonIdem (α : Type) [Canon α] : Prop where
  idem : ∀ a : α, canon (canon a) = canon a

attribute [simp] CanonIdem.idem

instance {α : Type} [Canon α] [CanonId α] : CanonIdem α :=
  ⟨fun a => by rw [CanonId.canon_id, CanonId.canon_id]⟩

instance {α : Type} [Canon α] [CanonIdem α] : CanonIdem (Array α) := ⟨fun xs => by
  show (xs.map canon).map canon = xs.map canon
  rw [Array.map_map]; congr 1; funext a; exact CanonIdem.idem a⟩

instance {α : Type} [Canon α] [CanonIdem α] : CanonIdem (List α) := ⟨fun xs => by
  show (xs.map canon).map canon = xs.map canon
  rw [List.map_map]; congr 1; funext a; exact CanonIdem.idem a⟩

instance {α : Type} [Canon α] [CanonIdem α] : CanonIdem (Option α) := ⟨fun o => by
  show (o.map canon).map canon = o.map canon
  cases o <;> simp⟩

instance {α : Type} [Canon α] [CanonIdem α] : CanonIdem (Multiple α) := ⟨fun m => by
  show Grammar.Multiple.new (canon (canon m.asSlice)) = Grammar.Multiple.new (canon m.asSlice)
  rw [CanonIdem.idem]⟩

instance {α β : Type} [Canon α] [Canon β] [CanonIdem α] [CanonIdem β] : CanonIdem (α × β) :=
  ⟨fun p => by show (canon (canon p.1), canon (canon p.2)) = (canon p.1, canon p.2); simp⟩

/-- A view type: canonicalising twice gives the view of the same content. -/
macro "view_idem" : tactic => `(tactic|
  (intro v; simp only [Canon.canon, canon_simps, canonSlice_canonSlice]))

instance : CanonIdem Symbol := ⟨fun v => by
  show canonSymbol (canonSymbol v) = canonSymbol v
  simp only [canonSymbol, canon_simps, canonSlice_canonSlice]⟩
instance : CanonIdem Numeral := ⟨by view_idem⟩
instance : CanonIdem Decimal := ⟨by view_idem⟩
instance : CanonIdem HexDigits := ⟨by view_idem⟩
instance : CanonIdem BinDigits := ⟨by view_idem⟩
instance : CanonIdem StringContent := ⟨by view_idem⟩
instance : CanonIdem Keyword := ⟨by view_idem⟩
instance : CanonIdem Lexicon.Reserved := ⟨fun _ => rfl⟩
instance : CanonIdem QuantifierKind := ⟨fun _ => rfl⟩

/-- Canonicalising twice by `canonX` is canonicalising once, by the components. -/
macro "idem_by" f:ident : tactic => `(tactic|
  (intro x; show $f ($f x) = $f x; cases x <;> simp only [$f:ident, CanonIdem.idem]))

instance : CanonIdem Index := ⟨by idem_by canonIndex⟩
instance : CanonIdem Ident := ⟨by idem_by canonIdentifier⟩
instance : CanonIdem SpecialConstant := ⟨by idem_by canonConstant⟩
instance : CanonIdem SimplePattern := ⟨by idem_by canonSymbolOrWildcard⟩
instance : CanonIdem Pattern := ⟨by idem_by canonPattern⟩
instance : CanonIdem IdentState := ⟨by idem_by canonIdentState⟩
instance : CanonIdem SortMode := ⟨by idem_by canonSortMode⟩
instance : CanonIdem PatternState := ⟨by idem_by canonPatternState⟩
instance : CanonIdem SortDecState := ⟨by idem_by canonSortDecState⟩
instance : CanonIdem SortedBinder := ⟨fun _ => rfl⟩
instance : CanonIdem BinderKind := ⟨fun _ => rfl⟩
instance : CanonIdem LiteralShape := ⟨fun _ => rfl⟩
instance : CanonIdem NamedCommand := ⟨fun _ => rfl⟩
instance : CanonIdem Declaration := ⟨fun _ => rfl⟩

section

variable {SE A S T Sc : Type} [Canon SE] [Canon A] [Canon S] [Canon T] [Canon Sc]
  [CanonIdem SE] [CanonIdem A] [CanonIdem S] [CanonIdem T] [CanonIdem Sc]

instance : CanonIdem (AttributeMode SE) := ⟨by idem_by canonAttributeMode⟩
instance : CanonIdem (AttributeState SE A) := ⟨by idem_by canonAttributeState⟩
instance : CanonIdem (SortLevel S) := ⟨by idem_by canonSortLevel⟩
instance : CanonIdem (SortState S) := ⟨by idem_by canonSortState⟩
instance : CanonIdem (SortedVarState S) := ⟨by idem_by canonSortedVarState⟩
instance : CanonIdem (QualIdentState S) := ⟨by idem_by canonQualIdentState⟩
instance {σ ρ : Type} [Canon σ] [Canon ρ] [CanonIdem σ] [CanonIdem ρ] :
    CanonIdem (ListState σ ρ) := ⟨by idem_by canonListState⟩
instance : CanonIdem (TermLevel S T Sc) := ⟨by idem_by canonTermLevel⟩
instance : CanonIdem (TermMode SE A S T Sc) := ⟨by idem_by canonTermMode⟩
instance : CanonIdem (TermState SE A S T Sc) := ⟨by idem_by canonTermState⟩
instance : CanonIdem (FunctionSignature S) := ⟨fun s => by
  show canonSignature (canonSignature s) = canonSignature s
  simp only [canonSignature, FunctionSignature.Internal.name_new,
    FunctionSignature.Internal.params_new, FunctionSignature.Internal.resultSort_new,
    CanonIdem.idem]⟩
instance {V : Type} [Canon V] [CanonIdem V] : CanonIdem (Grammar.Multiple.NamedValues V) := ⟨fun v => by
  show Grammar.Multiple.NamedValues.Internal.new (canon (canon v.toArray)) =
    Grammar.Multiple.NamedValues.Internal.new (canon v.toArray)
  rw [CanonIdem.idem]⟩
instance : CanonIdem (ConstructorState S) := ⟨by idem_by canonConstructorState⟩
instance : CanonIdem (DatatypeState S) := ⟨by idem_by canonDatatypeState⟩
instance : CanonIdem (DefinitionEnd S) := ⟨by idem_by canonDefinitionEnd⟩
instance : CanonIdem (SignatureState S) := ⟨by idem_by canonSignatureState⟩
instance : CanonIdem (FunctionDecState S) := ⟨by idem_by canonFunctionDecState⟩
instance : CanonIdem (LiteralState SE A S T Sc) := ⟨by idem_by canonLiteralState⟩
instance : CanonIdem (FinalCall A S T) := ⟨by idem_by canonFinalCall⟩
instance : CanonIdem (Payload SE A S T Sc) := ⟨by idem_by canonPayload⟩
instance {N : Type} : CanonIdem (CommandState SE A S T Sc N) := ⟨by idem_by canonCommandState⟩

end

instance : CanonIdem (CommandStateOf (List Event)) :=
  inferInstanceAs (CanonIdem (CommandState RSExpr RAttribute RSort RTerm RScope Empty))

instance : CanonIdem (ScriptParser (List Event)) := ⟨fun p => by
  show canonScriptParser (canonScriptParser p) = canonScriptParser p
  simp only [canonScriptParser, ScriptParser.Internal.posture_mk, ScriptParser.Internal.command_mk,
    ScriptParser.Internal.declarations_mk, CanonIdem.idem]⟩

end BSmtLib.Facts.Proofs.Parser.Canon.Idem
