module

public import BSmtLib.Facts.Lexer.Adapters
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.X1BatchInCore

@[expose] public section

/-!
# The adapter's steps and the public calls

`Adapters.lexing` feeds a lexer by the steps of its public calls `lexSlice` and `lexEof`
(`LexOps.lexSliceStep`, `LexOps.lexEofStep`), and keeps the held result as they do. For each
lexer of the chain, each public call is its step followed by keeping the held result as `lexing`
keeps it, and fails with the step's error where the step fails (`LexOps.SliceCallAgrees`,
`LexOps.EofCallAgrees`); the lexer, which stops at its first error, is then not given back.
-/

namespace BSmtLib.Facts.Proofs.Lexer.AdapterSteps

open BSmtLib.Facts.Lexer.Adapters

/-- The public call on a slice is its step followed by keeping the held result: the one of the
step, else the one the lexer held; where the step fails, the call fails with its error. -/
def LexOps.SliceCallAgrees (ops : LexOps) : Prop :=
  ∀ (consumer : BSmtLibSpec.Lexer.Consumer) (lexer : ops.Lexer consumer) (slice : ByteSlice),
    Except.mapError Prod.fst <$> ops.lexSlice lexer slice =
      (fun r => match r with
        | (.ok held, lexer) => .ok (ops.withHeld lexer (held.or (ops.held lexer)))
        | (.error e, _) => .error e) <$> ops.lexSliceStep lexer slice

/-- The public call at the end of the input is its step followed by returning the held result,
else the one the consumer broke with (`eofResult`), with the lexer holding none; where the step
fails, the call fails with its error. -/
def LexOps.EofCallAgrees (ops : LexOps) : Prop :=
  ∀ (consumer : BSmtLibSpec.Lexer.Consumer) (lexer : ops.Lexer consumer),
    Except.mapError Prod.fst <$> ops.lexEof lexer =
      (fun r => match r with
        | (.ok flow, lexer) => .ok (eofResult (ops.held lexer) flow, ops.withHeld lexer none)
        | (.error e, _) => .error e) <$> ops.lexEofStep lexer

theorem VNaive.sliceCallAgrees : (LexOps.SliceCallAgrees VNaive.lexOps) := by
  intro consumer lexer slice
  show Except.mapError Prod.fst <$> Lexer.Internal.VNaive.Lexer.lexSlice lexer slice = _
  unfold Lexer.Internal.VNaive.Lexer.lexSlice
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | _, _⟩ <;> rfl

theorem WRustPort.sliceCallAgrees : (LexOps.SliceCallAgrees WRustPort.lexOps) := by
  intro consumer lexer slice
  show Except.mapError Prod.fst <$> Lexer.Internal.WRustPort.Lexer.lexSlice lexer slice = _
  unfold Lexer.Internal.WRustPort.Lexer.lexSlice
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | _, _⟩ <;> rfl

theorem X1BatchInCore.sliceCallAgrees : (LexOps.SliceCallAgrees X1BatchInCore.lexOps) := by
  intro consumer lexer slice
  show Except.mapError Prod.fst <$> Lexer.Internal.X1BatchInCore.Lexer.lexSlice lexer slice = _
  unfold Lexer.Internal.X1BatchInCore.Lexer.lexSlice
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | _, _⟩ <;> rfl

theorem Lexer.sliceCallAgrees : (LexOps.SliceCallAgrees Lexer.lexOps) := by
  intro consumer lexer slice
  show Except.mapError Prod.fst <$> BSmtLib.Lexer.lexSlice lexer slice = _
  unfold BSmtLib.Lexer.lexSlice
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | _, _⟩ <;> rfl

theorem VNaive.eofCallAgrees : (LexOps.EofCallAgrees VNaive.lexOps) := by
  intro consumer lexer
  show Except.mapError Prod.fst <$> Lexer.Internal.VNaive.Lexer.lexEof lexer = _
  unfold Lexer.Internal.VNaive.Lexer.lexEof
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | flow, l⟩
  · rfl
  · rcases l with ⟨_, _, held⟩
    cases held <;> cases flow <;> rfl

theorem WRustPort.eofCallAgrees : (LexOps.EofCallAgrees WRustPort.lexOps) := by
  intro consumer lexer
  show Except.mapError Prod.fst <$> Lexer.Internal.WRustPort.Lexer.lexEof lexer = _
  unfold Lexer.Internal.WRustPort.Lexer.lexEof
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | flow, l⟩
  · rfl
  · rcases l with ⟨_, _, held⟩
    cases held <;> cases flow <;> rfl

theorem X1BatchInCore.eofCallAgrees : (LexOps.EofCallAgrees X1BatchInCore.lexOps) := by
  intro consumer lexer
  show Except.mapError Prod.fst <$> Lexer.Internal.X1BatchInCore.Lexer.lexEof lexer = _
  unfold Lexer.Internal.X1BatchInCore.Lexer.lexEof
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | flow, l⟩
  · rfl
  · rcases l with ⟨_, _, held⟩
    cases held <;> cases flow <;> rfl

theorem Lexer.eofCallAgrees : (LexOps.EofCallAgrees Lexer.lexOps) := by
  intro consumer lexer
  show Except.mapError Prod.fst <$> BSmtLib.Lexer.lexEof lexer = _
  unfold BSmtLib.Lexer.lexEof
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | flow, l⟩
  · rfl
  · cases h : BSmtLib.Lexer.Internal.held l <;> cases flow <;> rfl

end BSmtLib.Facts.Proofs.Lexer.AdapterSteps
