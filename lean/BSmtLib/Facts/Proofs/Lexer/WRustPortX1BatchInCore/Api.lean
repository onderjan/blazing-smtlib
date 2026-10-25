module

public import BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Calls
public import BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Instance
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.X1BatchInCore

@[expose] public section

/-!
# The calls of the Rust port and of the lexer with the batch in its state

The two lexers have the same type (`WRustPort.Lexer`); each call runs the step of the call over
the lexer's operations on it (`Lexer.run`) and gives back the result with the lexer, or with
what remains of it after a failure. Their operations simulate each other
(`opsSim_rust_x1BatchInCore`), so the steps of their calls on lexers that correspond give the same
results with lexers that correspond again (`run_lexSliceStep_x1BatchInCore`,
`run_lexEofStep_x1BatchInCore`), and so do their calls (`lexSlice_couple`, `lexEof_couple`,
`pendingLexEof_couple`).
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Api

open BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Calls
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Instance BSmtLib.Lexer.Error
open BSmtLib.Lexer.Recovery (Recovers)

/-- What the two lexers give back after a failed call on a slice corresponds, by whether the
lexers recover. -/
def AfterRelOf {H R E : Type} [Token.Consume H R E] (recovery : Type) : (recovers : Bool) →
    Lexer.Internal.WRustPort.Lexer.AfterErrorOf H recovery recovers →
    Lexer.Internal.WRustPort.Lexer.AfterErrorOf H recovery recovers → Prop
  | false, a, b => a = b
  | true, a, b => LexRel a b

/-- What the two lexers give back after a failed call on a slice corresponds. -/
def AfterRel {H R E : Type} [Token.Consume H R E] (recovery : Type) [Recovers recovery]
    (a b : Lexer.Internal.WRustPort.Lexer.AfterError H recovery) : Prop :=
  AfterRelOf recovery (Recovers.recovers recovery) a b

/-- What the two lexers give back after a failed call at the end of the input corresponds, by
whether the lexers recover. -/
def AfterEofRelOf {H R E : Type} [Token.Consume H R E] (recovery : Type) : (recovers : Bool) →
    Lexer.Internal.WRustPort.Lexer.AfterEofErrorOf H recovery recovers →
    Lexer.Internal.WRustPort.Lexer.AfterEofErrorOf H recovery recovers → Prop
  | false, a, b => a = b
  | true, a, b =>
    match (a : Lexer.Internal.WRustPort.Lexer.AfterEof H recovery),
        (b : Lexer.Internal.WRustPort.Lexer.AfterEof H recovery) with
    | .lexer a, .lexer b => LexRel a b
    | .pending a, .pending b => LexRel a.lexer b.lexer
    | _, _ => False

/-- What the two lexers give back after a failed call at the end of the input corresponds. -/
def AfterEofRel {H R E : Type} [Token.Consume H R E] (recovery : Type) [Recovers recovery]
    (a b : Lexer.Internal.WRustPort.Lexer.AfterEofError H recovery) : Prop :=
  AfterEofRelOf recovery (Recovers.recovers recovery) a b

/-- The results of the calls of the two lexers correspond: results related by `OK`, or the same
error, with what the lexers give back related by `AR`. -/
def ResRel {E A B α : Type} (OK : α → α → Prop) (AR : A → B → Prop) :
    Except (LexerError E × A) α → Except (LexerError E × B) α → Prop
  | .ok a, .ok b => OK a b
  | .error (e, a), .error (e', b) => e = e' ∧ AR a b
  | _, _ => False

/-- The results of the calls at the end of the input correspond: the same result, with lexers
that correspond. -/
def EofRel {H R E : Type} [Token.Consume H R E] {recovery : Type}
    (a b : Option (Span.Located R) × Lexer.Internal.WRustPort.Lexer H recovery) : Prop :=
  a.1 = b.1 ∧ LexRel a.2 b.2

theorem afterErrorOf_rel {H R E : Type} [Token.Consume H R E] (recovery : Type)
    (recovers : Bool) (a b : Lexer.Internal.WRustPort.Lexer H recovery) (h : LexRel a b) :
    AfterRelOf recovery recovers (Lexer.Internal.WRustPort.Lexer.afterErrorOf recovers a)
      (Lexer.Internal.WRustPort.Lexer.afterErrorOf recovers b) := by
  cases recovers
  · exact h.1
  · exact h

theorem afterError_rel {H R E : Type} [Token.Consume H R E] (recovery : Type) [Recovers recovery]
    (a b : Lexer.Internal.WRustPort.Lexer H recovery) (h : LexRel a b) :
    AfterRel recovery (Lexer.Internal.WRustPort.Lexer.afterError a)
      (Lexer.Internal.WRustPort.Lexer.afterError b) :=
  afterErrorOf_rel recovery (Recovers.recovers recovery) a b h

theorem afterEofErrorOf_rel {H R E : Type} [Token.Consume H R E] (recovery : Type)
    (recovers : Bool) (a b : Lexer.Internal.WRustPort.Lexer H recovery) (h : LexRel a b)
    (continues : Bool) :
    AfterEofRelOf recovery recovers
      (Lexer.Internal.WRustPort.Lexer.afterEofErrorOf recovers a continues)
      (Lexer.Internal.WRustPort.Lexer.afterEofErrorOf recovers b continues) := by
  cases recovers
  · exact h.1
  · cases continues
    · exact h
    · exact h

theorem afterEofError_rel {H R E : Type} [Token.Consume H R E] (recovery : Type)
    [Recovers recovery] (a b : Lexer.Internal.WRustPort.Lexer H recovery) (h : LexRel a b)
    (continues : Bool) :
    AfterEofRel recovery (Lexer.Internal.WRustPort.Lexer.afterEofError a continues)
      (Lexer.Internal.WRustPort.Lexer.afterEofError b continues) :=
  afterEofErrorOf_rel recovery (Recovers.recovers recovery) a b h continues

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (LexerCursor batch) m]
  {recovery : Type}

/-- The step of a call on a slice of the Rust port and of the lexer with the batch in its state,
run on lexers that correspond, gives the same result with lexers that correspond again. -/
theorem run_lexSliceStep_x1BatchInCore (hcons : ConsumesAlike H m R E)
    (abandon recover : Span.Location → StateT H m Unit) (slice : ByteSlice)
    (self self' : Lexer.Internal.WRustPort.Lexer H recovery) (h : LexRel self self') :
    Simulation.Couple.MCouple RunRel
      (self.run (Lexer.Internal.WRustPort.lexSliceStep (ops := Lexer.Internal.WRustPort.Rust.ops)
          (R := R) (E := E)
        abandon recover slice))
      (self'.run (Lexer.Internal.WRustPort.lexSliceStep
          (ops := Lexer.Internal.X1BatchInCore.ops) abandon recover
        slice)) :=
  run_lexSliceStep_sim (opsSim_rust_x1BatchInCore hcons) abandon recover slice self self' h

/-- The step of a call at the end of the input of the Rust port and of the lexer with the batch
in its state, run on lexers that correspond, gives the same result with lexers that correspond
again. -/
theorem run_lexEofStep_x1BatchInCore (hcons : ConsumesAlike H m R E)
    (abandon recover : Span.Location → StateT H m Unit)
    (self self' : Lexer.Internal.WRustPort.Lexer H recovery) (h : LexRel self self') :
    Simulation.Couple.MCouple RunRel
      (self.run (Lexer.Internal.WRustPort.lexEofStep (ops := Lexer.Internal.WRustPort.Rust.ops)
          (R := R) (E := E)
        abandon recover))
      (self'.run (Lexer.Internal.WRustPort.lexEofStep
          (ops := Lexer.Internal.X1BatchInCore.ops) abandon recover)) :=
  run_lexEofStep_sim (opsSim_rust_x1BatchInCore hcons) abandon recover self self' h

theorem lexSlice_couple (hcons : ConsumesAlike H m R E) [Recovers recovery]
    [Lexer.Recovery.LexerRecovery recovery H m]
    (self self' : Lexer.Internal.WRustPort.Lexer H recovery) (h : LexRel self self')
    (slice : ByteSlice) :
    Simulation.Couple.MCouple (ResRel LexRel (AfterRel recovery))
      (Lexer.Internal.WRustPort.Lexer.lexSlice self slice)
      (Lexer.Internal.X1BatchInCore.Lexer.lexSlice self' slice) := by
  unfold Lexer.Internal.WRustPort.Lexer.lexSlice Lexer.Internal.X1BatchInCore.Lexer.lexSlice
  refine Simulation.Couple.MCouple.bind (run_lexSliceStep_x1BatchInCore hcons _ _ slice self self'
      h)
    fun a b hab => ?_
  obtain ⟨r, l⟩ := a
  obtain ⟨r', l'⟩ := b
  obtain ⟨e, hl⟩ := hab
  dsimp only at e hl ⊢
  subst e
  cases r
  · exact Simulation.Couple.MCouple.pure ⟨rfl, afterError_rel _ { l with held := none }
      { l' with held := none }
      ⟨hl.1, hl.2.1, rfl⟩⟩
  · exact Simulation.Couple.MCouple.pure ⟨hl.1, hl.2.1, by rw [hl.2.2]⟩

theorem lexEof_couple (hcons : ConsumesAlike H m R E) [Recovers recovery]
    [Lexer.Recovery.LexerRecovery recovery H m]
    (self self' : Lexer.Internal.WRustPort.Lexer H recovery) (h : LexRel self self') :
    Simulation.Couple.MCouple (ResRel EofRel (AfterEofRel recovery))
        (Lexer.Internal.WRustPort.Lexer.lexEof self)
      (Lexer.Internal.X1BatchInCore.Lexer.lexEof self') := by
  unfold Lexer.Internal.WRustPort.Lexer.lexEof Lexer.Internal.X1BatchInCore.Lexer.lexEof
  refine Simulation.Couple.MCouple.bind (run_lexEofStep_x1BatchInCore hcons _ _ self self' h) fun a
      b hab => ?_
  obtain ⟨r, l⟩ := a
  obtain ⟨r', l'⟩ := b
  obtain ⟨e, hl⟩ := hab
  dsimp only at e hl ⊢
  subst e
  cases r
  · exact Simulation.Couple.MCouple.pure ⟨rfl, afterEofError_rel _ { l with held := none }
      { l' with held := none }
      ⟨hl.1, hl.2.1, rfl⟩ _⟩
  · exact Simulation.Couple.MCouple.pure ⟨by rw [hl.2.2], hl.1, hl.2.1, rfl⟩

theorem pendingLexEof_couple (hcons : ConsumesAlike H m R E) [Lexer.Recovery.Recover H m]
    (self self' : Lexer.Internal.WRustPort.Lexer.PendingEof H) (h : LexRel self.lexer self'.lexer) :
    Simulation.Couple.MCouple (ResRel (EofRel (recovery := Lexer.Recovery.Recovering)) LexRel)
      (Lexer.Internal.WRustPort.Lexer.PendingEof.lexEof self)
      (Lexer.Internal.X1BatchInCore.Lexer.PendingEof.lexEof self') := by
  unfold Lexer.Internal.WRustPort.Lexer.PendingEof.lexEof
      Lexer.Internal.X1BatchInCore.Lexer.PendingEof.lexEof
  refine Simulation.Couple.MCouple.bind (run_lexEofStep_x1BatchInCore hcons _ _ self.lexer
      self'.lexer h)
    fun a b hab => ?_
  obtain ⟨r, l⟩ := a
  obtain ⟨r', l'⟩ := b
  obtain ⟨e, hl⟩ := hab
  dsimp only at e hl ⊢
  subst e
  cases r
  · exact Simulation.Couple.MCouple.pure ⟨rfl, hl.1, hl.2.1, rfl⟩
  · exact Simulation.Couple.MCouple.pure ⟨by rw [hl.2.2], hl.1, hl.2.1, rfl⟩

end

end BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Api
