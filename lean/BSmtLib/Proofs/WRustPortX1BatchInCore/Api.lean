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
def AfterRel {H : Type} : (recovery : Recovery) → Lexer.WRustPort.Lexer.AfterError H recovery →
    Lexer.WRustPort.Lexer.AfterError H recovery → Prop
  | .failFast, _, _ => True
  | .recovering, a, b => LexRel (recovery := .recovering) a b

/-- What the two lexers give back after a failed call at the end of the input corresponds. -/
def AfterEofRel {H : Type} : (recovery : Recovery) →
    Lexer.WRustPort.Lexer.AfterEofError H recovery →
    Lexer.WRustPort.Lexer.AfterEofError H recovery → Prop
  | .failFast, _, _ => True
  | .recovering, a, b =>
    match (a : Lexer.WRustPort.Lexer.AfterEof H), (b : Lexer.WRustPort.Lexer.AfterEof H) with
    | .lexer a, .lexer b => LexRel a b
    | .pending a, .pending b => LexRel a.lexer b.lexer
    | _, _ => False

/-- The results of the calls of the two lexers correspond: the same result, with lexers that
correspond, or the same error, with what the lexers give back related by `AR`. -/
def ResRel {H R E A B : Type} {recovery : Recovery} (AR : A → B → Prop) :
    Except (LexError E × A) (ControlFlow (Located R) × Lexer.WRustPort.Lexer H recovery) →
      Except (LexError E × B) (ControlFlow (Located R) × Lexer.WRustPort.Lexer H recovery) →
      Prop
  | .ok (f, a), .ok (g, b) => f = g ∧ LexRel a b
  | .error (e, a), .error (e', b) => e = e' ∧ AR a b
  | _, _ => False

theorem afterError_rel {H : Type} (recovery : Recovery) (a b : Lexer.WRustPort.Lexer H recovery)
    (h : LexRel a b) :
    AfterRel recovery (Lexer.WRustPort.Lexer.afterError a)
      (Lexer.WRustPort.Lexer.afterError b) := by
  cases recovery
  · trivial
  · exact h

theorem afterEofError_rel {H : Type} (recovery : Recovery) (a b : Lexer.WRustPort.Lexer H recovery)
    (h : LexRel a b) (continues : Bool) :
    AfterEofRel recovery (Lexer.WRustPort.Lexer.afterEofError a continues)
      (Lexer.WRustPort.Lexer.afterEofError b continues) := by
  cases recovery
  · trivial
  · cases continues
    · exact h
    · exact h

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
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
    MCouple (ResRel (AfterRel recovery))
      (Lexer.WRustPort.Lexer.lexSlice (R := R) (E := E) self slice)
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
  · exact MCouple.pure ⟨rfl, afterError_rel _ _ _ hl⟩
  · exact MCouple.pure ⟨rfl, hl⟩

theorem lexEof_couple (hcons : ConsumesAlike H m R E) [LexRecovery recovery H m]
    (self self' : Lexer.WRustPort.Lexer H recovery) (h : LexRel self self') :
    MCouple (ResRel (AfterEofRel recovery)) (Lexer.WRustPort.Lexer.lexEof (R := R) (E := E) self)
      (Lexer.X1BatchInCore.Lexer.lexEof self') := by
  unfold Lexer.WRustPort.Lexer.lexEof Lexer.X1BatchInCore.Lexer.lexEof
  refine MCouple.bind (run_lexEofStep_x1BatchInCore hcons _ _ self self' h) fun a b hab => ?_
  obtain ⟨r, l⟩ := a
  obtain ⟨r', l'⟩ := b
  obtain ⟨e, hl⟩ := hab
  dsimp only at e hl ⊢
  subst e
  cases r
  · exact MCouple.pure ⟨rfl, afterEofError_rel _ _ _ hl _⟩
  · exact MCouple.pure ⟨rfl, hl⟩

theorem pendingLexEof_couple (hcons : ConsumesAlike H m R E) [Recover H m]
    (self self' : Lexer.WRustPort.Lexer.PendingEof H) (h : LexRel self.lexer self'.lexer) :
    MCouple (ResRel (recovery := .recovering) LexRel)
      (Lexer.WRustPort.Lexer.PendingEof.lexEof (R := R) (E := E) self)
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
  · exact MCouple.pure ⟨rfl, hl⟩
  · exact MCouple.pure ⟨rfl, hl⟩

end

end BSmtLib.Proofs.WRustPortX1BatchInCore
