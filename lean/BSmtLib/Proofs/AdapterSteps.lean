import BSmtLib.Proofs.Adapter

/-!
# The adapter's steps and the public calls

`Adapter.fed` feeds a lexer by the step of its public call `lexSlice` (`Ops.lexSliceStep`). For
each lexer of the chain, the public call is that step followed by dropping the lexer when the
call fails: the lexer stops at its first error and is not given back.
-/

namespace BSmtLib.Proofs.Adapter

theorem VNaive.lexSlice_eq_lexSliceStep (lexer : VNaive.ops.Lexer) (slice : ByteSlice) :
    VNaive.ops.lexSlice lexer slice =
      match VNaive.ops.lexSliceStep lexer slice with
      | (.ok flow, lexer) => .ok (flow, lexer)
      | (.error e, _) => .error (e, ()) := by
  show Lexer.VNaive.Lexer.lexSlice lexer slice = _
  unfold Lexer.VNaive.Lexer.lexSlice
  simp only [VNaive.ops, bind, pure]
  split
  next result self heq =>
    rw [heq]
    cases result <;> rfl

theorem WRustPort.lexSlice_eq_lexSliceStep (lexer : WRustPort.ops.Lexer) (slice : ByteSlice) :
    WRustPort.ops.lexSlice lexer slice =
      match WRustPort.ops.lexSliceStep lexer slice with
      | (.ok flow, lexer) => .ok (flow, lexer)
      | (.error e, _) => .error (e, ()) := by
  show Lexer.WRustPort.Lexer.lexSlice lexer slice = _
  unfold Lexer.WRustPort.Lexer.lexSlice
  simp only [WRustPort.ops, bind, pure]
  split
  next result self heq =>
    rw [heq]
    cases result <;> rfl

theorem X1BatchInCore.lexSlice_eq_lexSliceStep (lexer : X1BatchInCore.ops.Lexer)
    (slice : ByteSlice) :
    X1BatchInCore.ops.lexSlice lexer slice =
      match X1BatchInCore.ops.lexSliceStep lexer slice with
      | (.ok flow, lexer) => .ok (flow, lexer)
      | (.error e, _) => .error (e, ()) := by
  show Lexer.X1BatchInCore.Lexer.lexSlice lexer slice = _
  unfold Lexer.X1BatchInCore.Lexer.lexSlice
  simp only [X1BatchInCore.ops, bind, pure]
  split
  next result self heq =>
    rw [heq]
    cases result <;> rfl

theorem Lexer.lexSlice_eq_lexSliceStep (lexer : Lexer.ops.Lexer) (slice : ByteSlice) :
    Lexer.ops.lexSlice lexer slice =
      match Lexer.ops.lexSliceStep lexer slice with
      | (.ok flow, lexer) => .ok (flow, lexer)
      | (.error e, _) => .error (e, ()) := by
  show BSmtLib.Lexer.lexSlice lexer slice = _
  unfold BSmtLib.Lexer.lexSlice
  simp only [Lexer.ops, bind, pure]
  split
  next result self heq =>
    rw [heq]
    cases result <;> rfl

end BSmtLib.Proofs.Adapter
