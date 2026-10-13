import BSmtLib.Proofs.WRustPortX1BatchInCore.Calls
import BSmtLib.Proofs.WRustPortX1BatchInCore.Instance

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

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation

/-- What the two lexers give back after a failed call on a slice corresponds. -/
def AfterRel {H R E : Type} [Consume H R E] : (recovery : Recovery) →
    Lexer.WRustPort.Lexer.AfterError H recovery →
    Lexer.WRustPort.Lexer.AfterError H recovery → Prop
  | .failFast, _, _ => True
  | .recovering, a, b => LexRel (recovery := .recovering) a b

/-- What the two lexers give back after a failed call at the end of the input corresponds. -/
def AfterEofRel {H R E : Type} [Consume H R E] : (recovery : Recovery) →
    Lexer.WRustPort.Lexer.AfterEofError H recovery →
    Lexer.WRustPort.Lexer.AfterEofError H recovery → Prop
  | .failFast, _, _ => True
  | .recovering, a, b =>
    match (a : Lexer.WRustPort.Lexer.AfterEof H), (b : Lexer.WRustPort.Lexer.AfterEof H) with
    | .lexer a, .lexer b => LexRel a b
    | .pending a, .pending b => LexRel a.lexer b.lexer
    | _, _ => False

/-- The results of the calls of the two lexers correspond: results related by `OK`, or the same
error, with what the lexers give back related by `AR`. -/
def ResRel {E A B α : Type} (OK : α → α → Prop) (AR : A → B → Prop) :
    Except (LexError E × A) α → Except (LexError E × B) α → Prop
  | .ok a, .ok b => OK a b
  | .error (e, a), .error (e', b) => e = e' ∧ AR a b
  | _, _ => False

/-- The results of the calls at the end of the input correspond: the same result, with lexers
that correspond. -/
def EofRel {H R E : Type} [Consume H R E] {recovery : Recovery}
    (a b : Option (Located R) × Lexer.WRustPort.Lexer H recovery) : Prop :=
  a.1 = b.1 ∧ LexRel a.2 b.2

theorem afterError_rel {H R E : Type} [Consume H R E] (recovery : Recovery)
    (a b : Lexer.WRustPort.Lexer H recovery) (h : LexRel a b) :
    AfterRel recovery (Lexer.WRustPort.Lexer.afterError a)
      (Lexer.WRustPort.Lexer.afterError b) := by
  cases recovery
  · trivial
  · exact h

theorem afterEofError_rel {H R E : Type} [Consume H R E] (recovery : Recovery)
    (a b : Lexer.WRustPort.Lexer H recovery) (h : LexRel a b) (continues : Bool) :
    AfterEofRel recovery (Lexer.WRustPort.Lexer.afterEofError a continues)
      (Lexer.WRustPort.Lexer.afterEofError b continues) := by
  cases recovery
  · trivial
  · cases continues
    · exact h
    · exact h

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H R E]
  [∀ batch, ConsumeFrom H (BatchCursor batch) m]
  {recovery : Recovery}

/-- The step of a call on a slice of the Rust port and of the lexer with the batch in its state,
run on lexers that correspond, gives the same result with lexers that correspond again. -/
theorem run_lexSliceStep_x1BatchInCore (hcons : ConsumesAlike H m R E)
    (abandon recover : Location → StateT H m Unit) (slice : ByteSlice)
    (self self' : Lexer.WRustPort.Lexer H recovery) (h : LexRel self self') :
    MCouple RunRel
      (self.run (Lexer.WRustPort.lexSliceStep (ops := Lexer.WRustPort.Rust.ops) (R := R) (E := E)
        abandon recover slice))
      (self'.run (Lexer.WRustPort.lexSliceStep (ops := Lexer.X1BatchInCore.ops) abandon recover
        slice)) :=
  run_lexSliceStep_sim (opsSim_rust_x1BatchInCore hcons) abandon recover slice self self' h

/-- The step of a call at the end of the input of the Rust port and of the lexer with the batch
in its state, run on lexers that correspond, gives the same result with lexers that correspond
again. -/
theorem run_lexEofStep_x1BatchInCore (hcons : ConsumesAlike H m R E)
    (abandon recover : Location → StateT H m Unit)
    (self self' : Lexer.WRustPort.Lexer H recovery) (h : LexRel self self') :
    MCouple RunRel
      (self.run (Lexer.WRustPort.lexEofStep (ops := Lexer.WRustPort.Rust.ops) (R := R) (E := E)
        abandon recover))
      (self'.run (Lexer.WRustPort.lexEofStep (ops := Lexer.X1BatchInCore.ops) abandon recover)) :=
  run_lexEofStep_sim (opsSim_rust_x1BatchInCore hcons) abandon recover self self' h

theorem lexSlice_couple (hcons : ConsumesAlike H m R E) [LexRecovery recovery H m]
    (self self' : Lexer.WRustPort.Lexer H recovery) (h : LexRel self self') (slice : ByteSlice) :
    MCouple (ResRel LexRel (AfterRel recovery))
      (Lexer.WRustPort.Lexer.lexSlice self slice)
      (Lexer.X1BatchInCore.Lexer.lexSlice self' slice) := by
  unfold Lexer.WRustPort.Lexer.lexSlice Lexer.X1BatchInCore.Lexer.lexSlice
  refine MCouple.bind (run_lexSliceStep_x1BatchInCore hcons _ _ slice self self' h)
    fun a b hab => ?_
  obtain ⟨r, l⟩ := a
  obtain ⟨r', l'⟩ := b
  obtain ⟨e, hl⟩ := hab
  dsimp only at e hl ⊢
  subst e
  cases r
  · exact MCouple.pure ⟨rfl, afterError_rel _ { l with held := none } { l' with held := none }
      ⟨hl.1, hl.2.1, rfl⟩⟩
  · exact MCouple.pure ⟨hl.1, hl.2.1, by rw [hl.2.2]⟩

theorem lexEof_couple (hcons : ConsumesAlike H m R E) [LexRecovery recovery H m]
    (self self' : Lexer.WRustPort.Lexer H recovery) (h : LexRel self self') :
    MCouple (ResRel EofRel (AfterEofRel recovery)) (Lexer.WRustPort.Lexer.lexEof self)
      (Lexer.X1BatchInCore.Lexer.lexEof self') := by
  unfold Lexer.WRustPort.Lexer.lexEof Lexer.X1BatchInCore.Lexer.lexEof
  refine MCouple.bind (run_lexEofStep_x1BatchInCore hcons _ _ self self' h) fun a b hab => ?_
  obtain ⟨r, l⟩ := a
  obtain ⟨r', l'⟩ := b
  obtain ⟨e, hl⟩ := hab
  dsimp only at e hl ⊢
  subst e
  cases r
  · exact MCouple.pure ⟨rfl, afterEofError_rel _ { l with held := none } { l' with held := none }
      ⟨hl.1, hl.2.1, rfl⟩ _⟩
  · exact MCouple.pure ⟨by rw [hl.2.2], hl.1, hl.2.1, rfl⟩

theorem pendingLexEof_couple (hcons : ConsumesAlike H m R E) [Recover H m]
    (self self' : Lexer.WRustPort.Lexer.PendingEof H) (h : LexRel self.lexer self'.lexer) :
    MCouple (ResRel (EofRel (recovery := .recovering)) LexRel)
      (Lexer.WRustPort.Lexer.PendingEof.lexEof self)
      (Lexer.X1BatchInCore.Lexer.PendingEof.lexEof self') := by
  unfold Lexer.WRustPort.Lexer.PendingEof.lexEof Lexer.X1BatchInCore.Lexer.PendingEof.lexEof
  refine MCouple.bind (run_lexEofStep_x1BatchInCore hcons _ _ self.lexer self'.lexer h)
    fun a b hab => ?_
  obtain ⟨r, l⟩ := a
  obtain ⟨r', l'⟩ := b
  obtain ⟨e, hl⟩ := hab
  dsimp only at e hl ⊢
  subst e
  cases r
  · exact MCouple.pure ⟨rfl, hl.1, hl.2.1, rfl⟩
  · exact MCouple.pure ⟨by rw [hl.2.2], hl.1, hl.2.1, rfl⟩

end

end BSmtLib.Proofs.WRustPortX1BatchInCore
