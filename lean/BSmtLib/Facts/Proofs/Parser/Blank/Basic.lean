module

public import BSmtLib.Parser
public import BSmtLib.Traits.CommandHandler
public import BSmtLib.Facts.Proofs.Parser.Blank.Attr
import all BSmtLib.Parser

@[expose] public section

/-!
# The handler's values blanked

A step of the parser passes the handler's values on, from the handler's results into its state
and back into the handler's calls, and never looks at them; it branches only on its tokens, on
the parts of its state that are no values of the handler, and on whether a call failed. So a
handler whose calls never fail (`NoFails`) is, for the parser's control, the handler `Shell`,
whose state and values are all `()`: the step run with the handler gives what the step run with
`Shell` on the state with every value of the handler replaced by `()` gives, with the values
replaced (`BSim`). Lean does not give that free theorem, so it is proved for each step from how
it is built, by the closure lemmas below.

Two handlers whose calls never fail therefore run the parser alike: the same answers, the same
cursors, the same failures, and states that are the same up to the values.
-/

namespace BSmtLib.Facts.Proofs.Parser.Blank.Basic

open BSmtLib.Multiple (FunctionSignature)
open BSmtLib.Parser BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Parser.Internal (PM)

/-! ## The blank handler -/

/-- The handler whose state is nothing and whose values are all `()`. -/
structure Shell where

instance : Inhabited Shell := ⟨{}⟩

/-- Every call of the blank handler gives `()` and leaves it as it is. -/
instance shellTerms : Traits.Handler Shell Id where
  Error := Unit
  SExpr := Unit
  Attribute := Unit
  «Sort» := Unit
  Term := Unit
  Scope := Unit
  setVersion _ := pure ()
  handleSort _ _ := pure ()
  handleTerm _ := pure ()
  handleSExpr _ := pure ()
  handleAttribute _ _ := pure ()
  annotateTerm _ _ := pure ()
  startLet _ := pure ()
  endLet _ _ := pure ()
  startQuantifier _ _ := pure ()
  endQuantifier _ _ _ := pure ()
  startLambda _ := pure ()
  endLambda _ _ := pure ()
  startMatch _ := pure ()
  startMatchCase _ _ := pure ()
  endMatchCase _ _ _ := pure ()
  endMatch _ _ := pure ()

/-- Every command call of the blank handler gives `()`; a command that is no standard one fails
with `()`. -/
instance shellCommands : Traits.CommandHandler Shell Id where
  NonstandardParser := Empty
  nonstandardCommand _ := throw ()
  commandAssert _ := pure ()
  commandCheckSat := pure ()
  commandCheckSatAssuming _ := pure ()
  commandDeclareConst _ _ := pure ()
  startDeclareDatatype _ _ := pure ()
  endDeclareDatatype _ := pure ()
  startDeclareDatatypes _ := pure ()
  startDatatypeDeclaration _ := pure ()
  endDatatypeDeclaration _ := pure ()
  endDeclareDatatypes := pure ()
  commandDeclareFun _ _ _ := pure ()
  commandDeclareSort _ _ := pure ()
  commandDeclareSortParameter _ := pure ()
  commandDefineConst _ _ _ := pure ()
  startDefineFun _ := pure ()
  endDefineFun _ := pure ()
  startDefineFunRec _ := pure ()
  endDefineFunRec _ := pure ()
  startDefineFunsRec _ := pure ()
  startRecursiveBody _ := pure ()
  endRecursiveBody _ := pure ()
  endDefineFunsRec := pure ()
  startDefineSort _ _ := pure ()
  endDefineSort _ := pure ()
  commandEcho _ := pure ()
  commandExit := pure ()
  commandGetAssertions := pure ()
  commandGetAssignment := pure ()
  commandGetInfo _ := pure ()
  commandGetModel := pure ()
  commandGetOption _ := pure ()
  commandGetProof := pure ()
  commandGetUnsatAssumptions := pure ()
  commandGetUnsatCore := pure ()
  commandGetValue _ := pure ()
  commandPop _ := pure ()
  commandPush _ := pure ()
  commandReset := pure ()
  commandResetAssertions := pure ()
  commandSetInfo _ := pure ()
  commandSetLogic _ := pure ()
  commandSetOption _ := pure ()

/-! ## Blanking -/

/-- Replaces every value of the handler in a value of the parser by `()`; `β` is the type the
parser has for it with the blank handler. -/
class Blanks (α : Type) (β : outParam Type) where
  blank : α → β

export Blanks (blank)

/-- What holds no value of the handler stays as it is. -/
instance (priority := low) blanksId {α : Type} : Blanks α α := ⟨id⟩

instance {α β : Type} [Blanks α β] : Blanks (Array α) (Array β) := ⟨Array.map blank⟩
instance {α β : Type} [Blanks α β] : Blanks (List α) (List β) := ⟨List.map blank⟩
instance {α β : Type} [Blanks α β] : Blanks (Option α) (Option β) := ⟨Option.map blank⟩
instance {α α' β β' : Type} [Blanks α α'] [Blanks β β'] : Blanks (α × β) (α' × β') :=
  ⟨fun p => (blank p.1, blank p.2)⟩

section

variable {H : Type} [Handler H Id]

instance : Blanks (Handler.SExpr H) Unit := ⟨fun _ => ()⟩
instance : Blanks (Handler.Attribute H) Unit := ⟨fun _ => ()⟩
instance : Blanks (Handler.«Sort» H) Unit := ⟨fun _ => ()⟩
instance : Blanks (Handler.Term H) Unit := ⟨fun _ => ()⟩
instance : Blanks (Handler.Scope H) Unit := ⟨fun _ => ()⟩

end

/-! ## The nodes -/

instance {α β : Type} [Blanks α β] : Blanks (Multiple α) (Multiple β) :=
  ⟨fun m => .new (blank m.asSlice)⟩

instance {V V' : Type} [Blanks V V'] : Blanks (Multiple.Named V) (Multiple.Named V') :=
  ⟨fun v => Multiple.Named.Internal.new (blank v.toArray)⟩

instance {T T' : Type} [Blanks T T'] : Blanks (Multiple.MatchCases T) (Multiple.MatchCases T') :=
  ⟨fun v => Multiple.MatchCases.Internal.new (blank v.toArray)⟩

instance {S S' : Type} [Blanks S S'] :
    Blanks (Multiple.Constructors S) (Multiple.Constructors S') :=
  ⟨fun v => Multiple.Constructors.Internal.new (blank v.toArray)⟩

def blankQualifiedIdent {S S' : Type} [Blanks S S'] : QualifiedIdent S → QualifiedIdent S'
  | ⟨identifier, sort⟩ => ⟨identifier, blank sort⟩

instance {S S' : Type} [Blanks S S'] : Blanks (QualifiedIdent S) (QualifiedIdent S') :=
  ⟨blankQualifiedIdent⟩

def blankTermNode {S S' T T' : Type} [Blanks S S'] [Blanks T T'] :
    Nodes.Term S T → Nodes.Term S' T'
  | .specialConstant c => .specialConstant c
  | .qualifiedIdent i s => .qualifiedIdent i (blank s)
  | .application i s args h => .application i (blank s) (blank args) (by
    rw [show blank args = Multiple.new (args.asSlice.map blank) from rfl, Multiple.len_new,
      Array.size_map, Multiple.size_asSlice]
    exact h)

instance {S S' T T' : Type} [Blanks S S'] [Blanks T T'] :
    Blanks (Nodes.Term S T) (Nodes.Term S' T') :=
  ⟨blankTermNode⟩

def blankSExprNode {X X' : Type} [Blanks X X'] : Nodes.SExpr X → Nodes.SExpr X'
  | .specialConstant c => .specialConstant c
  | .symbol s => .symbol s
  | .reserved w => .reserved w
  | .keyword k => .keyword k
  | .sExprs items => .sExprs (blank items)

instance {X X' : Type} [Blanks X X'] : Blanks (Nodes.SExpr X) (Nodes.SExpr X') := ⟨blankSExprNode⟩

def blankAttributeValueNode {X X' : Type} [Blanks X X'] :
    AttributeValue X → AttributeValue X'
  | .specialConstant c => .specialConstant c
  | .symbol s => .symbol s
  | .sExprs items => .sExprs (blank items)

instance {X X' : Type} [Blanks X X'] : Blanks (AttributeValue X) (AttributeValue X') :=
  ⟨blankAttributeValueNode⟩

def blankSignature {S S' : Type} [Blanks S S'] (s : FunctionSignature S) :
    FunctionSignature S' :=
  FunctionSignature.Internal.new s.name (blank s.params) (blank s.resultSort)

instance {S S' : Type} [Blanks S S'] : Blanks (FunctionSignature S) (FunctionSignature S') :=
  ⟨blankSignature⟩

instance {S S' : Type} [Blanks S S'] :
    Blanks (Multiple.FunctionSignatures S) (Multiple.FunctionSignatures S') :=
  ⟨fun v => Multiple.FunctionSignatures.Internal.new (blank v.toArray)⟩

def blankStep {σ σ' ρ ρ' : Type} [Blanks σ σ'] [Blanks ρ ρ'] :
    Internal.Step σ ρ → Internal.Step σ' ρ'
  | .more s => .more (blank s)
  | .done r => .done (blank r)

instance {σ σ' ρ ρ' : Type} [Blanks σ σ'] [Blanks ρ ρ'] :
    Blanks (Internal.Step σ ρ) (Internal.Step σ' ρ') := ⟨blankStep⟩

/-! ## Runs related by blanking -/

/-- The cause of a failure with the handler's error replaced by `()`. -/
def blankCause {ε : Type} : ParseErrorCause ε → ParseErrorCause Unit
  | .syntax kind => .syntax kind
  | .version kind => .version kind
  | .handler _ => .handler ()

/-- A result of a run, blanked. -/
def blankResult {ε α β : Type} [Blanks α β] :
    Except (ParseErrorCause ε) α → Except (ParseErrorCause Unit) β
  | .ok a => .ok (blank a)
  | .error e => .error (blankCause e)

/-- A parse error with the handler's error replaced by `()`. -/
def blankError {ε : Type} (e : ParseError ε) : ParseError Unit :=
  ParseError.Internal.new (blankCause e.cause)

/-- An answer of a parse, its error blanked. -/
def blankAnswer {ε α : Type} : Except (ParseError ε) α → Except (ParseError Unit) α
  | .ok a => .ok a
  | .error e => .error (blankError e)

variable {H : Type} [Handler H Id]

/-- `BSim x y`: from every state of the handler, `x` ends as `y` does with the blank handler,
blanked: `y` gives `x`'s result with the handler's values replaced by `()`, and fails where `x`
fails, with the same syntax error, or a handler error where `x` has one. -/
structure BSim {α β : Type} [Blanks α β] (x : PM H α) (y : PM Shell β) : Prop where
  run : ∀ h : H, (y.run.run {}).1 = blankResult (x.run.run h).1

section

variable {α β γ δ : Type} [Blanks α β] [Blanks γ δ]

theorem BSim.pure {a : α} {b : β} (h : b = blank a) :
    BSim (Pure.pure a : PM H α) (Pure.pure b : PM Shell β) :=
  ⟨fun _ => by rw [h]; rfl⟩

theorem BSim.throw (e : ParseErrorCause (Handler.Error H)) (e' : ParseErrorCause Unit)
    (h : e' = blankCause e) :
    BSim (MonadExcept.throw e : PM H α) (MonadExcept.throw e' : PM Shell β) :=
  ⟨fun _ => by rw [h]; rfl⟩

theorem BSim.bind {x : PM H α} {y : PM Shell β} {f : α → PM H γ} {g : β → PM Shell δ}
    (hx : BSim x y) (hf : ∀ a, BSim (f a) (g (blank a))) : BSim (x >>= f) (y >>= g) := by
  constructor
  intro h
  simp only [ExceptT.run_bind, StateT.run_bind]
  have e := hx.run h
  generalize y.run.run {} = Y at e ⊢
  obtain ⟨ry, sy⟩ := Y
  dsimp only at e
  rcases hxr : x.run.run h with ⟨_ | a, h'⟩ <;> rw [hxr] at e <;> subst e
  · rfl
  · show ((g (blank a)).run.run sy).1 = _
    have : sy = {} := rfl
    rw [this]
    exact (hf a).run h'

theorem BSim.ite {c c' : Prop} [Decidable c] [Decidable c'] {x₁ x₂ : PM H α}
    {y₁ y₂ : PM Shell β} (hc : c' = c) (h₁ : c → BSim x₁ y₁) (h₂ : ¬ c → BSim x₂ y₂) :
    BSim (if c then x₁ else x₂) (if c' then y₁ else y₂) := by
  subst hc
  by_cases h : c'
  · simp only [h, ↓reduceIte]; exact h₁ h
  · simp only [h, ↓reduceIte]; exact h₂ h

theorem BSim.dite {c c' : Prop} [Decidable c] [Decidable c'] {x₁ : c → PM H α}
    {x₂ : ¬ c → PM H α} {y₁ : c' → PM Shell β} {y₂ : ¬ c' → PM Shell β} (hc : c' = c)
    (h₁ : ∀ (h : c) (h' : c'), BSim (x₁ h) (y₁ h'))
    (h₂ : ∀ (h : ¬ c) (h' : ¬ c'), BSim (x₂ h) (y₂ h')) :
    BSim (dite c x₁ x₂) (dite c' y₁ y₂) := by
  subst hc
  by_cases h : c'
  · simp only [h, ↓reduceDIte]; exact h₁ h h
  · simp only [h, ↓reduceDIte]; exact h₂ h h

end

theorem BSim.syntaxError {α β : Type} [Blanks α β] (kind : SyntaxErrorKind) :
    BSim (Parser.Internal.syntaxError kind : PM H α)
      (Parser.Internal.syntaxError kind : PM Shell β) :=
  ⟨fun _ => rfl⟩

/-! ## Handlers whose calls never fail -/

/-- The action fails from no state. -/
structure NeverFails {ε α : Type} (x : ExceptT ε (StateT H Id) α) : Prop where
  run : ∀ s, ∃ a s', x.run.run s = (.ok a, s')

/-- A call of the handler that never fails, in a parse, against any call of the blank handler
that gives `()` and leaves it as it is. -/
theorem BSim.call {α β : Type} [Blanks α β] {x : ExceptT (Handler.Error H) (StateT H Id) α}
    {y : ExceptT Unit (StateT Shell Id) β} (hx : NeverFails x) {b : β}
    (hy : y = Pure.pure b) (hb : ∀ a : α, blank a = b) :
    BSim (Parser.Internal.call x) (Parser.Internal.call y) := by
  constructor
  intro h
  obtain ⟨a, h', e⟩ := hx.run h
  subst hy
  simp only [Parser.Internal.call, ExceptT.adapt, ExceptT.run_mk, StateT.run_map]
  show _ = blankResult (Except.mapError _ (x.run.run h).1)
  rw [e]
  simp only [Except.mapError, blankResult, hb]
  rfl

/-- A call of the handler that gives a value of a type that has none, against a call of the blank
handler that fails: both fail with a handler error, whatever comes after. -/
theorem BSim.callNone {α β γ δ : Type} [Blanks γ δ]
    {x : ExceptT (Handler.Error H) (StateT H Id) α} (hα : α → False)
    {y : ExceptT Unit (StateT Shell Id) β} (hy : y = MonadExcept.throw ())
    {f : α → PM H γ} {g : β → PM Shell δ} :
    BSim (Parser.Internal.call x >>= f) (Parser.Internal.call y >>= g) := by
  constructor
  intro h
  subst hy
  simp only [Parser.Internal.call, ExceptT.adapt, ExceptT.run_bind, ExceptT.run_mk,
    StateT.run_bind, StateT.run_map]
  simp only [StateT.run, ExceptT.run]
  rcases hx : x h with ⟨_ | a, h'⟩
  · rfl
  · exact (hα a).elim

/-! ## Handlers whose calls never fail, by method -/

section

open Traits.Handler Traits.CommandHandler

variable (H : Type) [CommandHandler H Id]

/-- Every call of the handler fails from no state, and the handler names no parser of
non-standard commands: there is none of its type, so its `nonstandardCommand` always fails. -/
class NoFails : Prop where
  noNonstandard : CommandHandler.NonstandardParser H → False
  handleSort : ∀ i args, NeverFails (handleSort (H := H) i args)
  handleTerm : ∀ node, NeverFails (handleTerm (H := H) node)
  handleSExpr : ∀ node, NeverFails (handleSExpr (H := H) node)
  handleAttribute : ∀ k v, NeverFails (handleAttribute (H := H) k v)
  annotateTerm : ∀ t attrs, NeverFails (annotateTerm (H := H) t attrs)
  startLet : ∀ bs, NeverFails (startLet (H := H) bs)
  endLet : ∀ s t, NeverFails (endLet (H := H) s t)
  startQuantifier : ∀ q vs, NeverFails (startQuantifier (H := H) q vs)
  endQuantifier : ∀ q s t, NeverFails (endQuantifier (H := H) q s t)
  startLambda : ∀ vs, NeverFails (startLambda (H := H) vs)
  endLambda : ∀ s t, NeverFails (endLambda (H := H) s t)
  startMatch : ∀ t, NeverFails (startMatch (H := H) t)
  startMatchCase : ∀ t p, NeverFails (startMatchCase (H := H) t p)
  endMatchCase : ∀ s t b, NeverFails (endMatchCase (H := H) s t b)
  endMatch : ∀ t cs, NeverFails (endMatch (H := H) t cs)
  commandAssert : ∀ t, NeverFails (commandAssert (H := H) t)
  commandCheckSat : NeverFails (commandCheckSat (H := H))
  commandCheckSatAssuming : ∀ ts, NeverFails (commandCheckSatAssuming (H := H) ts)
  commandDeclareConst : ∀ s t, NeverFails (commandDeclareConst (H := H) s t)
  startDeclareDatatype : ∀ s ps, NeverFails (startDeclareDatatype (H := H) s ps)
  endDeclareDatatype : ∀ cs, NeverFails (endDeclareDatatype (H := H) cs)
  startDeclareDatatypes : ∀ ss, NeverFails (startDeclareDatatypes (H := H) ss)
  startDatatypeDeclaration : ∀ ps, NeverFails (startDatatypeDeclaration (H := H) ps)
  endDatatypeDeclaration : ∀ cs, NeverFails (endDatatypeDeclaration (H := H) cs)
  endDeclareDatatypes : NeverFails (endDeclareDatatypes (H := H))
  commandDeclareFun : ∀ s ps r, NeverFails (commandDeclareFun (H := H) s ps r)
  commandDeclareSort : ∀ s n, NeverFails (commandDeclareSort (H := H) s n)
  commandDeclareSortParameter : ∀ s, NeverFails (commandDeclareSortParameter (H := H) s)
  commandDefineConst : ∀ s t b, NeverFails (commandDefineConst (H := H) s t b)
  startDefineFun : ∀ sig, NeverFails (startDefineFun (H := H) sig)
  endDefineFun : ∀ b, NeverFails (endDefineFun (H := H) b)
  startDefineFunRec : ∀ sig, NeverFails (startDefineFunRec (H := H) sig)
  endDefineFunRec : ∀ b, NeverFails (endDefineFunRec (H := H) b)
  startDefineFunsRec : ∀ sigs, NeverFails (startDefineFunsRec (H := H) sigs)
  startRecursiveBody : ∀ sig, NeverFails (startRecursiveBody (H := H) sig)
  endRecursiveBody : ∀ b, NeverFails (endRecursiveBody (H := H) b)
  endDefineFunsRec : NeverFails (endDefineFunsRec (H := H))
  startDefineSort : ∀ s ps, NeverFails (startDefineSort (H := H) s ps)
  endDefineSort : ∀ t, NeverFails (endDefineSort (H := H) t)
  commandEcho : ∀ c, NeverFails (commandEcho (H := H) c)
  commandExit : NeverFails (commandExit (H := H))
  commandGetAssertions : NeverFails (commandGetAssertions (H := H))
  commandGetAssignment : NeverFails (commandGetAssignment (H := H))
  commandGetInfo : ∀ k, NeverFails (commandGetInfo (H := H) k)
  commandGetModel : NeverFails (commandGetModel (H := H))
  commandGetOption : ∀ k, NeverFails (commandGetOption (H := H) k)
  commandGetProof : NeverFails (commandGetProof (H := H))
  commandGetUnsatAssumptions : NeverFails (commandGetUnsatAssumptions (H := H))
  commandGetUnsatCore : NeverFails (commandGetUnsatCore (H := H))
  commandGetValue : ∀ ts, NeverFails (commandGetValue (H := H) ts)
  commandPop : ∀ n, NeverFails (commandPop (H := H) n)
  commandPush : ∀ n, NeverFails (commandPush (H := H) n)
  commandReset : NeverFails (commandReset (H := H))
  commandResetAssertions : NeverFails (commandResetAssertions (H := H))
  commandSetInfo : ∀ a, NeverFails (commandSetInfo (H := H) a)
  commandSetLogic : ∀ s, NeverFails (commandSetLogic (H := H) s)
  commandSetOption : ∀ a, NeverFails (commandSetOption (H := H) a)

end

end BSmtLib.Facts.Proofs.Parser.Blank.Basic
