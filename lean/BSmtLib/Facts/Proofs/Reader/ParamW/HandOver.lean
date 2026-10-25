module

public import BSmtLib.Facts.Proofs.Reader.ParamW.Walk
public import BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The Rust port's handover to two consumers

The Rust port's code calls the consumer only where it hands a new cursor over
(`Rust.flushCursor`); where the two handovers of the same new cursor are related as the link
says (`ConsumersW`), so are the operations of the Rust port that hand over (`Rust.ops`). Here are
the lemmas for the helpers of the lexer's state and for these operations.
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Reader.ParamW.HandOver

open BSmtLib.Lexer
open BSmtLib.Lexer.Cursor.LexerCursor.Internal (EndsAfter)
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Lexer.Internal.WRustPort

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂]

/-- The Rust port's handovers of the same new cursor to the two consumers are related as the
link says. Both consumers take whitespace and comments, or neither does. -/
structure ConsumersW [∀ b, Token.ConsumeFrom H₁ (LexerCursor b) m₁]
    [∀ b, Token.ConsumeFrom H₂ (LexerCursor b) m₂]
    (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂) : Prop where
  concrete : Token.Consume.isConcrete (H := H₁) = Token.Consume.isConcrete (H := H₂)
  flushNew {floor : Option Nat} {low : Nat} (version : Version)
    (batch : Token.Internal.TokenBatch)
    (hfloor : ∀ p, floor = some p → EndsAfter (Lexer.Cursor.LexerCursor.Internal.new version batch) p) :
    LSim L (· = ·) (Rust.flushCursor (H := H₁) (m := m₁) (R := R₁) (E := E₁) (low := low)
        (Lexer.Cursor.LexerCursor.Internal.new version batch) hfloor)
      (Rust.flushCursor (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        (Lexer.Cursor.LexerCursor.Internal.new version batch) hfloor)

end

section State

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂} {floor : Option Nat} {low : Nat}

/-! ## The helpers of the lexer's state -/

theorem getCore_sim : LSim L (· = ·) (getCore (H := H₁) (m := m₁) (R := R₁) (E := E₁)
    (floor := floor) (low := low)) (getCore (H := H₂) (m := m₂) (R := R₂) (E := E₂)) := by
  unfold getCore; lsimW

theorem modifyCore_sim (f : Lexer.Internal.WRustPort.LexerCore → Lexer.Internal.WRustPort.LexerCore)
    (h) :
    LSim L (· = ·) (modifyCore (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) f h) (modifyCore (H := H₂) (m := m₂) (R := R₂) (E := E₂) f h) := by
  unfold modifyCore; lsimW

theorem modifyBound_sim (f) :
    LSim L (· = ·) (modifyBound (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) f) (modifyBound (H := H₂) (m := m₂) (R := R₂) (E := E₂) f) := by
  unfold modifyBound; lsimW

theorem setNormal_sim : LSim L (· = ·) (setNormal (H := H₁) (m := m₁) (R := R₁) (E := E₁)
    (floor := floor) (low := low)) (setNormal (H := H₂) (m := m₂) (R := R₂) (E := E₂)) := by
  unfold setNormal; lsimW

theorem setTokenState_sim (state start h) :
    LSim L (· = ·) (setTokenState (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) state start h)
      (setTokenState (H := H₂) (m := m₂) (R := R₂) (E := E₂) state start h) := by
  unfold setTokenState; lsimW

theorem modifyContent_sim (f) :
    LSim L (· = ·) (modifyContent (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) f) (modifyContent (H := H₂) (m := m₂) (R := R₂) (E := E₂) f) := by
  unfold modifyContent; lsimW

theorem extendContent_sim (input start stop) :
    LSim L (· = ·) (extendContent (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) input start stop)
      (extendContent (H := H₂) (m := m₂) (R := R₂) (E := E₂) input start stop) := by
  unfold extendContent; lsimW

theorem pushContent_sim (c) :
    LSim L (· = ·) (pushContent (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) c) (pushContent (H := H₂) (m := m₂) (R := R₂) (E := E₂) c) := by
  unfold pushContent; lsimW

theorem startToken_sim (offset base position hframe) :
    LSim L (· = ·) (startToken (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) offset base position hframe)
      (startToken (H := H₂) (m := m₂) (R := R₂) (E := E₂) offset base position hframe) := by
  unfold startToken; lsimW

theorem markLineFeedAt_sim (position) :
    LSim L (· = ·) (markLineFeedAt (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) position)
      (markLineFeedAt (H := H₂) (m := m₂) (R := R₂) (E := E₂) position) := by
  unfold markLineFeedAt; lsimW

theorem errorWith_sim (kind position failure) :
    LSim L (IRel L.rr L.re) (errorWith (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) kind position failure)
      (errorWith (H := H₂) (m := m₂) (R := R₂) (E := E₂) kind position failure) := by
  unfold errorWith
  exact XSim.bind_eq getCore_sim fun c => XSim.pure ⟨rfl, rfl, rfl⟩

theorem errorAt_sim (kind position) :
    LSim L (IRel L.rr L.re) (errorAt (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) kind position)
      (errorAt (H := H₂) (m := m₂) (R := R₂) (E := E₂) kind position) := by
  unfold errorAt; exact errorWith_sim _ _ _

theorem error_sim (kind tokenEnd) :
    LSim L (IRel L.rr L.re) (error (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) kind tokenEnd)
      (error (H := H₂) (m := m₂) (R := R₂) (E := E₂) kind tokenEnd) := by
  unfold error; exact errorWith_sim _ _ _

theorem bind_errorWith {S₁ S₂ : Type} {Q : S₁ → S₂ → Prop} {kind position failure}
    {f : Interrupted R₁ E₁ floor → Lexer.Internal.WRustPort.LexM H₁ m₁ R₁ E₁ floor low S₁}
    {g : Interrupted R₂ E₂ floor → Lexer.Internal.WRustPort.LexM H₂ m₂ R₂ E₂ floor low S₂}
    (hk : ∀ a b, IRel L.rr L.re a b → LSim L Q (f a) (g b)) :
    LSim L Q (errorWith kind position failure >>= f) (errorWith kind position failure >>= g) :=
  XSim.bind (errorWith_sim kind position failure) hk

theorem bind_errorAt {S₁ S₂ : Type} {Q : S₁ → S₂ → Prop} {kind position}
    {f : Interrupted R₁ E₁ floor → Lexer.Internal.WRustPort.LexM H₁ m₁ R₁ E₁ floor low S₁}
    {g : Interrupted R₂ E₂ floor → Lexer.Internal.WRustPort.LexM H₂ m₂ R₂ E₂ floor low S₂}
    (hk : ∀ a b, IRel L.rr L.re a b → LSim L Q (f a) (g b)) :
    LSim L Q (errorAt kind position >>= f) (errorAt kind position >>= g) :=
  XSim.bind (errorAt_sim kind position) hk

theorem bind_error {S₁ S₂ : Type} {Q : S₁ → S₂ → Prop} {kind tokenEnd}
    {f : Interrupted R₁ E₁ floor → Lexer.Internal.WRustPort.LexM H₁ m₁ R₁ E₁ floor low S₁}
    {g : Interrupted R₂ E₂ floor → Lexer.Internal.WRustPort.LexM H₂ m₂ R₂ E₂ floor low S₂}
    (hk : ∀ a b, IRel L.rr L.re a b → LSim L Q (f a) (g b)) :
    LSim L Q (error kind tokenEnd >>= f) (error kind tokenEnd >>= g) :=
  XSim.bind (error_sim kind tokenEnd) hk

theorem expectDelimiter_sim (next position) :
    LSim L (· = ·) (expectDelimiter (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) next position)
      (expectDelimiter (H := H₂) (m := m₂) (R := R₂) (E := E₂) next position) := by
  unfold expectDelimiter; lsimW

theorem locationFrom_sim (base position) :
    LSim L (· = ·) (locationFrom (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) base position)
      (locationFrom (H := H₂) (m := m₂) (R := R₂) (E := E₂) base position) := by
  unfold locationFrom; lsimW

theorem load_sim : LSim L (· = ·) (FastState.load (H := H₁) (m := m₁) (R := R₁) (E := E₁)
    (floor := floor) (low := low)) (FastState.load (H := H₂) (m := m₂) (R := R₂) (E := E₂)) := by
  unfold FastState.load; lsimW

theorem store_sim (s : FastState) : LSim L (· = ·) (FastState.store (H := H₁) (m := m₁)
    (R := R₁) (E := E₁) (floor := floor) (low := low) s)
    (FastState.store (H := H₂) (m := m₂) (R := R₂) (E := E₂) s) := by
  unfold FastState.store; lsimW

end State

section Consumer

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂] [∀ b, Token.ConsumeFrom H₁
      (LexerCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (LexerCursor b) m₂]
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂} {floor : Option Nat} {low : Nat}

/-! ## The handover -/

theorem consumesWhitespaceAndComments_sim (hc : ConsumersW L) :
    LSim L (· = ·) (consumesWhitespaceAndComments (H := H₁) (m := m₁) (R := R₁) (E := E₁)
        (floor := floor) (low := low))
      (consumesWhitespaceAndComments (H := H₂) (m := m₂) (R := R₂) (E := E₂)) := by
  unfold consumesWhitespaceAndComments
  rw [hc.concrete]
  exact XSim.pure_eq _

theorem flushCursor_sim (hc : ConsumersW L) (version batch hfloor) :
    LSim L (· = ·) (Rust.flushCursor (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) (Lexer.Cursor.LexerCursor.Internal.new version batch) hfloor)
      (Rust.flushCursor (H := H₂) (m := m₂) (R := R₂) (E := E₂)
        (Lexer.Cursor.LexerCursor.Internal.new version batch) hfloor) :=
  hc.flushNew version batch hfloor

theorem flushBatch_sim (hc : ConsumersW L) :
    LSim L (· = ·) (Rust.flushBatch (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low)) (Rust.flushBatch (H := H₂) (m := m₂) (R := R₂) (E := E₂)) := by
  unfold Rust.flushBatch; lsimW

theorem sinkStoredAt_sim (hc : ConsumersW L) (ty start «end» hend hfloor) :
    LSim L (· = ·) (Rust.sinkStoredAt (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) ty start «end» hend hfloor)
      (Rust.sinkStoredAt (H := H₂) (m := m₂) (R := R₂) (E := E₂) ty start «end» hend hfloor) := by
  unfold Rust.sinkStoredAt; lsimW

theorem sinkEof_sim (hc : ConsumersW L) (location) :
    LSim L (· = ·) (Rust.sinkEof (H := H₁) (m := m₁) (R := R₁) (E := E₁) (low := low) location)
      (Rust.sinkEof (H := H₂) (m := m₂) (R := R₂) (E := E₂) location) := by
  unfold Rust.sinkEof; lsimW

theorem flushHeld_sim (hc : ConsumersW L) (batch origin hbatch) :
    LSim L (· = ·) (Rust.flushHeld (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor)
        (low := low) batch origin hbatch)
      (Rust.flushHeld (H := H₂) (m := m₂) (R := R₂) (E := E₂) batch origin hbatch) := by
  unfold Rust.flushHeld; lsimW

theorem pushFast_sim (hc : ConsumersW L) (input batch locals offset base ty contentStart
    contentStop start «end» emit hty hstart hend hframe hbatch) :
    LSim L (· = ·)
      (Rust.pushFast (H := H₁) (m := m₁) (R := R₁) (E := E₁) (floor := floor) (low := low) input
        batch locals offset base ty contentStart contentStop start «end» emit hty hstart hend
        hframe hbatch)
      (Rust.pushFast (H := H₂) (m := m₂) (R := R₂) (E := E₂) input batch locals offset base ty
        contentStart contentStop start «end» emit hty hstart hend hframe hbatch) := by
  unfold Rust.pushFast; lsimW

end Consumer

end BSmtLib.Facts.Proofs.Reader.ParamW.HandOver
