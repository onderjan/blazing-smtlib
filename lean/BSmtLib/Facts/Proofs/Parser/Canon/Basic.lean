module

public import BSmtLib.Facts.Proofs.Parser.Quiet
public import BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
public import BSmtLib.Facts.Proofs.Parser.Canon.Attr
import all BSmtLib.Parser
import all BSmtLib.Plain

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

open BSmtLib.Parser BSmtLib.Nodes
open BSmtLib.Plain (SymbolView NumeralView DecimalView HexDigitsView BinDigitsView
  StringContentView KeywordView)
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
instance : Canon Token.Version := ⟨id⟩
instance : Canon Token.Reserved := ⟨id⟩
instance : Canon Quantifier := ⟨id⟩
instance : CanonId Nat := ⟨fun _ => rfl⟩
instance : CanonId Bool := ⟨fun _ => rfl⟩
instance : CanonId Unit := ⟨fun _ => rfl⟩
instance : CanonId Token.Version := ⟨fun _ => rfl⟩

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

instance : Canon SymbolView :=
  ⟨fun v => SymbolView.Internal.newUnchecked (canonSlice v.asSlice)⟩
instance : Canon NumeralView :=
  ⟨fun v => NumeralView.Internal.newUnchecked (canonSlice v.asSlice)⟩
instance : Canon DecimalView :=
  ⟨fun v => DecimalView.Internal.newUnchecked (canonSlice v.asSlice)⟩
instance : Canon HexDigitsView :=
  ⟨fun v => HexDigitsView.Internal.newUnchecked (canonSlice v.asSlice)⟩
instance : Canon BinDigitsView :=
  ⟨fun v => BinDigitsView.Internal.newUnchecked (canonSlice v.asSlice)⟩
instance : Canon StringContentView :=
  ⟨fun v => StringContentView.Internal.newUnchecked (canonSlice v.asSlice)⟩
instance : Canon KeywordView :=
  ⟨fun v => KeywordView.Internal.newUnchecked (canonSlice v.asSlice)⟩

@[canon_simps] theorem asSlice_canon_symbolView (v : SymbolView) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)
@[canon_simps] theorem asSlice_canon_numeralView (v : NumeralView) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)
@[canon_simps] theorem asSlice_canon_decimalView (v : DecimalView) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)
@[canon_simps] theorem asSlice_canon_hexDigitsView (v : HexDigitsView) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)
@[canon_simps] theorem asSlice_canon_binDigitsView (v : BinDigitsView) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)
@[canon_simps] theorem asSlice_canon_stringContentView (v : StringContentView) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)
@[canon_simps] theorem asSlice_canon_keywordView (v : KeywordView) :
    (canon v).asSlice = canonSlice v.asSlice := (rfl)

/-! ## Nodes and tokens -/

def canonSymbol : Symbol → Symbol
  | ⟨content, quoted⟩ => ⟨canon content, quoted⟩

instance : Canon Symbol := ⟨canonSymbol⟩

def canonIndex : Index → Index
  | .numeral digits => .numeral (canon digits)
  | .symbol s => .symbol (canon s)

instance : Canon Index := ⟨canonIndex⟩

def canonIdentifier : Identifier → Identifier
  | ⟨symbol, indices⟩ => ⟨canon symbol, canon indices⟩

instance : Canon Identifier := ⟨canonIdentifier⟩

def canonConstant : SpecConstant → SpecConstant
  | .numeral d => .numeral (canon d)
  | .decimal d => .decimal (canon d)
  | .hexadecimal d => .hexadecimal (canon d)
  | .binary d => .binary (canon d)
  | .string c => .string (canon c)

instance : Canon SpecConstant := ⟨canonConstant⟩

def canonSymbolOrWildcard : SymbolOrWildcard → SymbolOrWildcard
  | .symbol s => .symbol (canon s)
  | .wildcard => .wildcard

instance : Canon SymbolOrWildcard := ⟨canonSymbolOrWildcard⟩

def canonPattern : Pattern → Pattern
  | .single s => .single (canon s)
  | .constructor c args => .constructor (canon c) (canon args)

instance : Canon Pattern := ⟨canonPattern⟩

def canonTermNode {S T : Type} [Canon S] [Canon T] : TermNode S T → TermNode S T
  | .constant c => .constant (canon c)
  | .identifier i s => .identifier (canon i) (canon s)
  | .application i s args => .application (canon i) (canon s) (canon args)

instance {S T : Type} [Canon S] [Canon T] : Canon (TermNode S T) := ⟨canonTermNode⟩

def canonSExprNode {X : Type} [Canon X] : SExprNode X → SExprNode X
  | .constant c => .constant (canon c)
  | .symbol s => .symbol (canon s)
  | .reserved w => .reserved w
  | .keyword k => .keyword (canon k)
  | .list items => .list (canon items)

instance {X : Type} [Canon X] : Canon (SExprNode X) := ⟨canonSExprNode⟩

def canonAttributeValueNode {X : Type} [Canon X] : AttributeValueNode X → AttributeValueNode X
  | .constant c => .constant (canon c)
  | .symbol s => .symbol (canon s)
  | .list items => .list (canon items)

instance {X : Type} [Canon X] : Canon (AttributeValueNode X) := ⟨canonAttributeValueNode⟩

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

theorem CSim.throw (e : ParseErrorCause Unit) :
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

end

end BSmtLib.Facts.Proofs.Parser.Canon.Basic
