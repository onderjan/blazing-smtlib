import BSmtLib.Proofs.Adapters

/-!
# The adapter's steps and the public calls

`Adapter.lexing` feeds a lexer by the steps of its public calls `lexSlice` and `lexEof`
(`LexOps.lexSliceStep`, `LexOps.lexEofStep`), and keeps the held result as they do. For each
lexer of the chain, each public call is its step followed by keeping the held result as `lexing`
keeps it, and fails with the step's error where the step fails (`LexOps.SliceCallAgrees`,
`LexOps.EofCallAgrees`); the lexer, which stops at its first error, is then not given back.
-/

namespace BSmtLib.Proofs.Adapter

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

theorem VNaive.sliceCallAgrees : VNaive.lexOps.SliceCallAgrees := by
  intro consumer lexer slice
  show Except.mapError Prod.fst <$> Lexer.VNaive.Lexer.lexSlice lexer slice = _
  unfold Lexer.VNaive.Lexer.lexSlice
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | _, _⟩ <;> rfl

theorem WRustPort.sliceCallAgrees : WRustPort.lexOps.SliceCallAgrees := by
  intro consumer lexer slice
  show Except.mapError Prod.fst <$> Lexer.WRustPort.Lexer.lexSlice lexer slice = _
  unfold Lexer.WRustPort.Lexer.lexSlice
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | _, _⟩ <;> rfl

theorem X1BatchInCore.sliceCallAgrees : X1BatchInCore.lexOps.SliceCallAgrees := by
  intro consumer lexer slice
  show Except.mapError Prod.fst <$> Lexer.X1BatchInCore.Lexer.lexSlice lexer slice = _
  unfold Lexer.X1BatchInCore.Lexer.lexSlice
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | _, _⟩ <;> rfl

theorem Lexer.sliceCallAgrees : Lexer.lexOps.SliceCallAgrees := by
  intro consumer lexer slice
  show Except.mapError Prod.fst <$> BSmtLib.Lexer.lexSlice lexer slice = _
  unfold BSmtLib.Lexer.lexSlice
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | _, _⟩ <;> rfl

theorem VNaive.eofCallAgrees : VNaive.lexOps.EofCallAgrees := by
  intro consumer lexer
  show Except.mapError Prod.fst <$> Lexer.VNaive.Lexer.lexEof lexer = _
  unfold Lexer.VNaive.Lexer.lexEof
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | flow, l⟩
  · rfl
  · rcases l with ⟨_, _, held⟩
    cases held <;> cases flow <;> rfl

theorem WRustPort.eofCallAgrees : WRustPort.lexOps.EofCallAgrees := by
  intro consumer lexer
  show Except.mapError Prod.fst <$> Lexer.WRustPort.Lexer.lexEof lexer = _
  unfold Lexer.WRustPort.Lexer.lexEof
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | flow, l⟩
  · rfl
  · rcases l with ⟨_, _, held⟩
    cases held <;> cases flow <;> rfl

theorem X1BatchInCore.eofCallAgrees : X1BatchInCore.lexOps.EofCallAgrees := by
  intro consumer lexer
  show Except.mapError Prod.fst <$> Lexer.X1BatchInCore.Lexer.lexEof lexer = _
  unfold Lexer.X1BatchInCore.Lexer.lexEof
  simp only [map_bind, map_pure]
  rw [map_eq_pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | flow, l⟩
  · rfl
  · rcases l with ⟨_, _, held⟩
    cases held <;> cases flow <;> rfl

theorem Lexer.eofCallAgrees : Lexer.lexOps.EofCallAgrees := by
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

end BSmtLib.Proofs.Adapter
