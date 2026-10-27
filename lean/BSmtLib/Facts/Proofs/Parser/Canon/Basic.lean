module

public import BSmtLib.Facts.Proofs.Parser.Quiet
public import BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
public import BSmtLib.Facts.Proofs.Parser.Canon.Attr
import all BSmtLib.Parser
import all BSmtLib.Lexicon.Value
import all BSmtLib.Grammar.Multiple
import all BSmtLib.Grammar.Multiple.MatchCases

@[expose] public section

/-!
# Views replaced by their contents

A view of the parser points into some storage: the slice the lexer was fed, or its buffer. Two
lexers that hold the same tokens may hand over views of the same contents in different storage.
`canonSlice` is the view of a view's content in storage of its own, and `Canon.canon` replaces
every view in a value of the parser by that view: in its tokens, its nodes and its states.

A run of the parser that canonicalises its token and its state relates to the run that does not
(`CSim`): the same log and the canonical result. A step of the parser does with a view nothing
but pass it on, hand its content to the handler or compare its content, so the steps are so
related; Lean does not give that free theorem, so it is proved for each step from how it is
built, by the closure lemmas below.
-/

namespace BSmtLib.Facts.Proofs.Parser.Canon.Basic

open BSmtLib.Grammar (Multiple)
open BSmtLib.Parser BSmtLib.Grammar.Nodes
open BSmtLib.Lexicon.Value (Symbol Numeral Decimal HexDigits BinDigits
  StringContent Keyword)
open BSmtLib.Facts.Proofs.Parser.Quiet (RPM)
open BSmtLibSpec.Parser.Properties (Event)

/-! ## Canonical views -/

/-- The view of the content of the view, in storage of its own. -/
def canonSlice (s : ByteSlice) : ByteSlice := s.toByteArray.toByteSlice

theorem toByteArray_canonSlice (s : ByteSlice) : (canonSlice s).toByteArray = s.toByteArray :=
  BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes.toByteArray_toByteSlice _

/-- Replaces every view in a value by the view of its content in storage of its own. -/
class Canon (α : Type) where
  canon : α → α

export Canon (canon)

/-- A type that holds no view: replacing views changes nothing. -/
class CanonId (α : Type) [Canon α] : Prop where
  canon_id : ∀ a : α, canon a = a

instance : Canon Nat := ⟨id⟩
instance : Canon Bool := ⟨id⟩
instance : Canon Unit := ⟨id⟩
instance : Canon Version := ⟨id⟩
instance : Canon Lexicon.Reserved := ⟨id⟩
instance : Canon QuantifierKind := ⟨id⟩
instance : CanonId Nat := ⟨fun _ => rfl⟩
instance : CanonId Bool := ⟨fun _ => rfl⟩
instance : CanonId Unit := ⟨fun _ => rfl⟩
instance : CanonId Version := ⟨fun _ => rfl⟩

instance {α : Type} [Canon α] : Canon (Array α) := ⟨Array.map canon⟩
instance {α : Type} [Canon α] : Canon (List α) := ⟨List.map canon⟩
instance {α : Type} [Canon α] : Canon (Option α) := ⟨Option.map canon⟩
instance {α β : Type} [Canon α] [Canon β] : Canon (α × β) := ⟨fun p => (canon p.1, canon p.2)⟩

instance {α : Type} [Canon α] [CanonId α] : CanonId (Array α) :=
  ⟨fun a => by show a.map canon = a; exact Array.map_id'' CanonId.canon_id a⟩
instance {α : Type} [Canon α] [CanonId α] : CanonId (List α) :=
  ⟨fun a => by show a.map canon = a; exact List.map_id'' CanonId.canon_id a⟩
instance {α : Type} [Canon α] [CanonId α] : CanonId (Option α) :=
  ⟨fun a => by show a.map canon = a; cases a <;> simp [CanonId.canon_id]⟩
instance {α β : Type} [Canon α] [Canon β] [CanonId α] [CanonId β] : CanonId (α × β) :=
  ⟨fun a => by show (canon a.1, canon a.2) = a; simp [CanonId.canon_id]⟩
instance {α : Type} [Canon α] : Canon (Multiple α) := ⟨fun m => .new (canon m.asSlice)⟩
instance {α : Type} [Canon α] [CanonId α] : CanonId (Multiple α) :=
  ⟨fun m => by show Grammar.Multiple.new (canon m.asSlice) = m; rw [CanonId.canon_id]; rfl⟩

def canonSymbol (v : Symbol) : Symbol :=
  Symbol.Internal.newUnchecked v.isQuoted (canonSlice v.asSlice)

instance : Canon Symbol := ⟨canonSymbol⟩
instance : Canon Numeral :=
  ⟨fun v => Numeral.Internal.newUnchecked (canonSlice v.asSlice)⟩
instance : Canon Decimal :=
  ⟨fun v => Decimal.Internal.newUnchecked (canonSlice v.asSlice)⟩
instance : Canon HexDigits :=
  ⟨fun v => HexDigits.Internal.newUnchecked (canonSlice v.asSlice)⟩
instance : Canon BinDigits :=
  ⟨fun v => BinDigits.Internal.newUnchecked (canonSlice v.asSlice)⟩
instance : Canon StringContent :=
  ⟨fun v => StringContent.Internal.newUnchecked (canonSlice v.asSlice)⟩
instance : Canon Keyword :=
  ⟨fun v => Keyword.Internal.newUnchecked (canonSlice v.asSlice)⟩

@[canon_simps] theorem asSlice_canonSymbol (v : Symbol) :
    (canonSymbol v).asSlice = canonSlice v.asSlice := (rfl)
@[canon_simps] theorem isQuoted_canonSymbol (v : Symbol) :
    (canonSymbol v).isQuoted = v.isQuoted := (rfl)
@[canon_simps] theorem isQuoted_canon_symbolView (v : Symbol) :
    (canon v).isQuoted = v.isQuoted := (rfl)
@[canon_simps] theorem asSlice_canon_symbolView (v : Symbol) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)
@[canon_simps] theorem asSlice_canon_numeralView (v : Numeral) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)
@[canon_simps] theorem asSlice_canon_decimalView (v : Decimal) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)
@[canon_simps] theorem asSlice_canon_hexDigitsView (v : HexDigits) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)
@[canon_simps] theorem asSlice_canon_binDigitsView (v : BinDigits) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)
@[canon_simps] theorem asSlice_canon_stringContentView (v : StringContent) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)
@[canon_simps] theorem asSlice_canon_keywordView (v : Keyword) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)

instance {V : Type} [Canon V] : Canon (Grammar.Multiple.NamedValues V) :=
  ⟨fun v => Grammar.Multiple.NamedValues.Internal.new (canon v.toArray)⟩

attribute [canon_simps] Grammar.Multiple.asSlice_new Grammar.Multiple.NamedValues.Internal.toArray_new
  Grammar.Multiple.Symbols.Internal.toArray_new Grammar.Multiple.SortArities.Internal.toArray_new
  Grammar.Multiple.Constructors.Internal.toArray_new Grammar.Multiple.MatchCases.Internal.toArray_new
  Grammar.Multiple.FunctionSignatures.Internal.toArray_new Grammar.Multiple.FunctionSignature.Internal.name_new
  Grammar.Multiple.FunctionSignature.Internal.params_new Grammar.Multiple.FunctionSignature.Internal.resultSort_new

/-! ## Nodes and tokens -/

def canonIndex : Index → Index
  | .numeral digits => .numeral (canon digits)
  | .symbol s => .symbol (canon s)

instance : Canon Index := ⟨canonIndex⟩

def canonIdentifier : Ident → Ident
  | ⟨symbol, indices⟩ => ⟨canon symbol, canon indices⟩

instance : Canon Ident := ⟨canonIdentifier⟩

def canonConstant : SpecialConstant → SpecialConstant
  | .numeral d => .numeral (canon d)
  | .decimal d => .decimal (canon d)
  | .hexadecimal d => .hexadecimal (canon d)
  | .binary d => .binary (canon d)
  | .string c => .string (canon c)

instance : Canon SpecialConstant := ⟨canonConstant⟩

def canonSymbolOrWildcard : SimplePattern → SimplePattern
  | .symbol s => .symbol (canon s)
  | .wildcard => .wildcard

instance : Canon SimplePattern := ⟨canonSymbolOrWildcard⟩

def canonPattern : Pattern → Pattern
  | .simple s => .simple (canon s)
  | .application ⟨c, args, h⟩ => .application ⟨canon c, canon args, by
    rw [show canon args = args.map canon from rfl, Array.size_map]
    exact h⟩

instance : Canon Pattern := ⟨canonPattern⟩

instance : Canon Grammar.Multiple.Symbols :=
  ⟨fun v => Grammar.Multiple.Symbols.Internal.new (canon v.toArray)⟩
instance : Canon Grammar.Multiple.SortArities :=
  ⟨fun v => Grammar.Multiple.SortArities.Internal.new (canon v.toArray)⟩
instance {S : Type} [Canon S] : Canon (Grammar.Multiple.Constructors S) :=
  ⟨fun v => Grammar.Multiple.Constructors.Internal.new (canon v.toArray)⟩
instance {T : Type} [Canon T] : Canon (Grammar.Multiple.MatchCases T) :=
  ⟨fun v => Grammar.Multiple.MatchCases.Internal.new (canon v.toArray)⟩

def canonTermNode {S T : Type} [Canon S] [Canon T] : Grammar.Nodes.Term S T → Grammar.Nodes.Term S T
  | .specialConstant c => .specialConstant (canon c)
  | .qualifiedIdent i s => .qualifiedIdent (canon i) (canon s)
  | .application i s args h => .application (canon i) (canon s) (canon args) (by
    rw [show canon args = Grammar.Multiple.new (args.asSlice.map canon) from rfl, Grammar.Multiple.len_new,
      Array.size_map, Grammar.Multiple.size_asSlice]
    exact h)

instance {S T : Type} [Canon S] [Canon T] : Canon (Grammar.Nodes.Term S T) := ⟨canonTermNode⟩

def canonSExprNode {X : Type} [Canon X] : Grammar.Nodes.SExpr X → Grammar.Nodes.SExpr X
  | .specialConstant c => .specialConstant (canon c)
  | .symbol s => .symbol (canon s)
  | .reserved w => .reserved w
  | .keyword k => .keyword (canon k)
  | .sExprs items => .sExprs (canon items)

instance {X : Type} [Canon X] : Canon (Grammar.Nodes.SExpr X) := ⟨canonSExprNode⟩

def canonAttributeValueNode {X : Type} [Canon X] : AttributeValue X → AttributeValue X
  | .specialConstant c => .specialConstant (canon c)
  | .symbol s => .symbol (canon s)
  | .sExprs items => .sExprs (canon items)

instance {X : Type} [Canon X] : Canon (AttributeValue X) := ⟨canonAttributeValueNode⟩

def canonInput : Internal.Input → Internal.Input
  | .constant c => .constant (canon c)
  | .symbol s => .symbol (canon s)
  | .keyword k => .keyword (canon k)
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .reserved word => .reserved word
  | .endOfInput => .endOfInput
  | .layout => .layout

instance : Canon Internal.Input := ⟨canonInput⟩

def canonStep {σ ρ : Type} [Canon σ] [Canon ρ] : Internal.Step σ ρ → Internal.Step σ ρ
  | .more s => .more (canon s)
  | .done r => .done (canon r)

instance {σ ρ : Type} [Canon σ] [Canon ρ] : Canon (Internal.Step σ ρ) := ⟨canonStep⟩

/-! ## Runs related by canonicalisation -/

/-- `CSim x y`: from every log, `y` makes the log `x` makes, and gives `x`'s result with its views
replaced by their contents; errors hold no views. -/
structure CSim {α : Type} [Canon α] (x y : RPM α) : Prop where
  run : ∀ log : List Event, y.run.run log = ((x.run.run log).1.map canon, (x.run.run log).2)

section

variable {α β : Type} [Canon α] [Canon β]

theorem CSim.pure {a : α} {b : α} (h : b = canon a) : CSim (Pure.pure a : RPM α) (Pure.pure b) :=
  ⟨fun _ => by rw [h]; rfl⟩

theorem CSim.throw (e : ParseErrorKind Unit) :
    CSim (MonadExcept.throw e : RPM α) (MonadExcept.throw e) := ⟨fun _ => rfl⟩

theorem CSim.bind {x y : RPM α} {f g : α → RPM β} (hx : CSim x y)
    (hf : ∀ a, CSim (f a) (g (canon a))) : CSim (x >>= f) (y >>= g) := by
  constructor
  intro log
  simp only [ExceptT.run_bind, StateT.run_bind]
  rw [hx.run log]
  rcases x.run.run log with ⟨_ | a, log'⟩
  · rfl
  · exact (hf a).run log'

/-- An action that does not depend on views, run on both sides, with a result that holds none. -/
theorem CSim.same [CanonId α] {x y : RPM α} (h : y = x) : CSim x y := by
  constructor
  intro log
  rw [h]
  rcases x.run.run log with ⟨_ | a, log'⟩
  · rfl
  · simp only [Except.map, CanonId.canon_id]

theorem CSim.ite {c c' : Prop} [Decidable c] [Decidable c'] {x₁ x₂ y₁ y₂ : RPM α}
    (hc : c' = c) (h₁ : c → CSim x₁ y₁) (h₂ : ¬ c → CSim x₂ y₂) :
    CSim (if c then x₁ else x₂) (if c' then y₁ else y₂) := by
  subst hc
  by_cases h : c'
  · simp only [h, ↓reduceIte]; exact h₁ h
  · simp only [h, ↓reduceIte]; exact h₂ h

theorem CSim.dite {c c' : Prop} [Decidable c] [Decidable c'] {x₁ : c → RPM α} {x₂ : ¬ c → RPM α}
    {y₁ : c' → RPM α} {y₂ : ¬ c' → RPM α} (hc : c' = c)
    (h₁ : ∀ (h : c) (h' : c'), CSim (x₁ h) (y₁ h'))
    (h₂ : ∀ (h : ¬ c) (h' : ¬ c'), CSim (x₂ h) (y₂ h')) :
    CSim (dite c x₁ x₂) (dite c' y₁ y₂) := by
  subst hc
  by_cases h : c'
  · simp only [h, ↓reduceDIte]; exact h₁ h h
  · simp only [h, ↓reduceDIte]; exact h₂ h h

end

end BSmtLib.Facts.Proofs.Parser.Canon.Basic
