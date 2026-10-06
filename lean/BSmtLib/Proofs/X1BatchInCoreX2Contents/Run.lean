import BSmtLib.Proofs.X1BatchInCoreX2Contents.Inner

/-!
# The lexers' calls, in both lexers

The lexer with the content buffer is mapped to the lexer with the batch kept in the lexer's state
by its state (`lexerMap`), and so are the lexers that the calls give back. Each call of the first,
from a lexer whose content buffer fits its array, gives back lexers whose buffers fit, and the
second's call on the mapped lexer gives the same results, mapped.
-/

namespace BSmtLib.Proofs.X1BatchInCoreX2Contents

open BSmtLib.Proofs.Simulation

section Maps

variable {H : Type}

/-- The lexer with the batch kept in the lexer's state for the lexer with the content buffer. -/
def lexerMap {recovery : Recovery} (l : Lexer.X2Contents.Lexer H recovery) :
    Lexer.X1BatchInCore.Lexer H recovery :=
  { handler := l.handler, core := coreMap l.core }

/-- The content buffer of the lexer fits its array. -/
abbrev LexerFits {recovery : Recovery} (l : Lexer.X2Contents.Lexer H recovery) : Prop :=
  Fits l.core.tokenContent

/-- What a failed lexing of a slice gives back, mapped. -/
def afterErrorMap : {recovery : Recovery} → Lexer.X2Contents.Lexer.AfterError H recovery →
    Lexer.X1BatchInCore.Lexer.AfterError H recovery
  | .failFast, u => u
  | .recovering, l => lexerMap l

/-- What a failed lexing of a slice gives back has its content buffer fit, if it is a lexer. -/
def AfterErrorFits : {recovery : Recovery} → Lexer.X2Contents.Lexer.AfterError H recovery → Prop
  | .failFast, _ => True
  | .recovering, l => LexerFits l

/-- What a failed lexing of the end of the input gives back, mapped. -/
def afterEofErrorMap : {recovery : Recovery} → Lexer.X2Contents.Lexer.AfterEofError H recovery →
    Lexer.X1BatchInCore.Lexer.AfterEofError H recovery
  | .failFast, u => u
  | .recovering, .lexer l => .lexer (lexerMap l)
  | .recovering, .pending p => .pending ⟨lexerMap p.lexer⟩

/-- What a failed lexing of the end of the input gives back has its content buffer fit. -/
def AfterEofErrorFits : {recovery : Recovery} → Lexer.X2Contents.Lexer.AfterEofError H recovery →
    Prop
  | .failFast, _ => True
  | .recovering, .lexer l => LexerFits l
  | .recovering, .pending p => LexerFits p.lexer

variable {R E : Type} {recovery : Recovery}

/-- The result of a call that gives back a lexer or what a failure gives back, mapped. -/
def resultMap {A A' : Type} (f : A → A') :
    Except (LexError E × A) (ControlFlow (Located R) × Lexer.X2Contents.Lexer H recovery) →
      Except (LexError E × A') (ControlFlow (Located R) × Lexer.X1BatchInCore.Lexer H recovery)
  | .ok (flow, l) => .ok (flow, lexerMap l)
  | .error (err, a) => .error (err, f a)

/-- The lexer that a call gives back has its content buffer fit, and so has what a failure gives
back. -/
def ResultFits {A : Type} (F : A → Prop) :
    Except (LexError E × A) (ControlFlow (Located R) × Lexer.X2Contents.Lexer H recovery) → Prop
  | .ok (_, l) => LexerFits l
  | .error (_, a) => F a

end Maps

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  (hblind : ContentBlind H m R E)
include hblind

theorem lexSlice_sim {recovery : Recovery} [LexRecovery recovery H m]
    (l : Lexer.X2Contents.Lexer H recovery) (hl : LexerFits l) (slice : ByteSlice) :
    ∃ y : m {r // ResultFits AfterErrorFits r},
      Lexer.X2Contents.Lexer.lexSlice l slice = Subtype.val <$> y ∧
        Lexer.X1BatchInCore.Lexer.lexSlice (lexerMap l) slice =
          (fun r => resultMap afterErrorMap r.val) <$> y := by
  obtain ⟨handler, core⟩ := l
  obtain ⟨y, h1, h2⟩ := lexSliceStep_sim hblind (LexRecovery.abandon recovery)
    (LexRecovery.recover recovery) slice core hl handler
  refine ⟨(fun z => ⟨match z.val.1.1 with
      | .ok flow => .ok (flow, { handler := z.val.2, core := z.val.1.2 })
      | .error err => .error (err, Lexer.X2Contents.Lexer.afterError
          { handler := z.val.2, core := z.val.1.2 }), ?_⟩) <$> y, ?_, ?_⟩
  · obtain ⟨⟨⟨r, c⟩, h⟩, _, hc⟩ := z
    cases r with
    | ok flow => exact hc
    | error err => cases recovery <;> first | trivial | exact hc
  · simp only [Lexer.X2Contents.Lexer.lexSlice, Lexer.X2Contents.Lexer.run]
    rw [h1]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    rfl
  · simp only [Lexer.X1BatchInCore.Lexer.lexSlice, Lexer.X1BatchInCore.Lexer.run, lexerMap]
    rw [h2]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    refine congrArg (y >>= ·) (funext fun z => ?_)
    obtain ⟨⟨⟨r, c⟩, h⟩, _, hc⟩ := z
    cases r <;> cases recovery <;> rfl

theorem lexEof_sim {recovery : Recovery} [LexRecovery recovery H m]
    (l : Lexer.X2Contents.Lexer H recovery) (hl : LexerFits l) :
    ∃ y : m {r // ResultFits AfterEofErrorFits r},
      Lexer.X2Contents.Lexer.lexEof l = Subtype.val <$> y ∧
        Lexer.X1BatchInCore.Lexer.lexEof (lexerMap l) =
          (fun r => resultMap afterEofErrorMap r.val) <$> y := by
  obtain ⟨handler, core⟩ := l
  obtain ⟨y, h1, h2⟩ := lexEofStep_sim hblind (LexRecovery.abandon recovery)
    (LexRecovery.recover recovery) core hl handler
  refine ⟨(fun z => ⟨match z.val.1.1 with
      | .ok flow => .ok (flow, { handler := z.val.2, core := z.val.1.2 })
      | .error err => .error (err, Lexer.X2Contents.Lexer.afterEofError
          { handler := z.val.2, core := z.val.1.2 } err.continuesFrom.isSome), ?_⟩) <$> y, ?_,
    ?_⟩
  · obtain ⟨⟨⟨r, c⟩, h⟩, _, hc⟩ := z
    cases r with
    | ok flow => exact hc
    | error err =>
      cases recovery
      · trivial
      · dsimp only
        cases err.continuesFrom.isSome <;> exact hc
  · simp only [Lexer.X2Contents.Lexer.lexEof, Lexer.X2Contents.Lexer.run]
    rw [h1]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    rfl
  · simp only [Lexer.X1BatchInCore.Lexer.lexEof, Lexer.X1BatchInCore.Lexer.run, lexerMap]
    rw [h2]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    refine congrArg (y >>= ·) (funext fun z => ?_)
    obtain ⟨⟨⟨r, c⟩, h⟩, _, hc⟩ := z
    cases r with
    | ok flow => rfl
    | error err =>
      cases recovery
      · rfl
      · dsimp only [id]
        cases err.continuesFrom.isSome <;> rfl

theorem pendingLexEof_sim [Recover H m] (l : Lexer.X2Contents.Lexer H .recovering)
    (hl : LexerFits l) :
    ∃ y : m {r // ResultFits LexerFits r},
      Lexer.X2Contents.Lexer.PendingEof.lexEof ⟨l⟩ = Subtype.val <$> y ∧
        Lexer.X1BatchInCore.Lexer.PendingEof.lexEof ⟨lexerMap l⟩ =
          (fun r => resultMap lexerMap r.val) <$> y := by
  obtain ⟨handler, core⟩ := l
  obtain ⟨y, h1, h2⟩ := lexEofStep_sim hblind (Recover.abandon (H := H))
    (Recover.recover (H := H)) core hl handler
  refine ⟨(fun z => ⟨match z.val.1.1 with
      | .ok flow => .ok (flow, { handler := z.val.2, core := z.val.1.2 })
      | .error err => .error (err, { handler := z.val.2, core := z.val.1.2 }), ?_⟩) <$> y, ?_,
    ?_⟩
  · obtain ⟨⟨⟨r, c⟩, h⟩, _, hc⟩ := z
    cases r <;> exact hc
  · simp only [Lexer.X2Contents.Lexer.PendingEof.lexEof, Lexer.X2Contents.Lexer.run]
    rw [h1]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    rfl
  · simp only [Lexer.X1BatchInCore.Lexer.PendingEof.lexEof, Lexer.X1BatchInCore.Lexer.run,
      lexerMap]
    rw [h2]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    refine congrArg (y >>= ·) (funext fun z => ?_)
    obtain ⟨⟨⟨r, c⟩, h⟩, _, hc⟩ := z
    cases r <;> rfl

end

theorem lexerMap_new {H : Type} (consumer : H) (version : Version) :
    lexerMap (Lexer.X2Contents.Lexer.new consumer version) =
      Lexer.X1BatchInCore.Lexer.new consumer version := rfl

theorem fits_new {H : Type} (consumer : H) (version : Version) :
    LexerFits (Lexer.X2Contents.Lexer.new consumer version) := fits_empty

theorem lexerMap_newRecovering {H : Type} {m : Type → Type} [Recover H m] (consumer : H)
    (version : Version) :
    lexerMap (Lexer.X2Contents.Lexer.newRecovering (m := m) consumer version) =
      Lexer.X1BatchInCore.Lexer.newRecovering (m := m) consumer version := rfl

theorem fits_newRecovering {H : Type} {m : Type → Type} [Recover H m] (consumer : H)
    (version : Version) :
    LexerFits (Lexer.X2Contents.Lexer.newRecovering (m := m) consumer version) := fits_empty

end BSmtLib.Proofs.X1BatchInCoreX2Contents
