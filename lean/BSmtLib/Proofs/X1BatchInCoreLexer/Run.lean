import BSmtLib.Proofs.Adapter

/-!
# The calls of the lexers on slices, one after another

The adapter's consumer is fed slices by calls of a lexer, each of which runs the lexer's step on a
slice (`lexSliceStep`) by `run`, which gives back the lexer after the call even where the call
failed. `runSlices` makes these calls for a list of slices, one after another, until a call does
not continue, and gives the result of the last call made and the lexer after it: what a lexer
has done after being fed the slices, before the end of the input. `lexerStep` and `x1Step` are the
calls of the library's lexer and of `X1BatchInCore`.

What the adapter records when it feeds the slices and then the end of the input is what the
end of the input gives after `runSlices` (`feed_eq_afterRun`).
-/

namespace BSmtLib.Proofs.X1BatchInCoreLexer

open BSmtLib.Proofs.Adapter (Collector feed)

/-- What a call of a lexer with the adapter's consumer gives: its result, and the lexer after
it, which a failed call gives back too. -/
abbrev Called (L : Type) := Except (LexError Unit) (ControlFlow (Located Empty)) × L

/-- Feeds the slices to the lexer one call after another, until a call does not continue, and
gives what the last call made gives; the lexer itself if there are no slices. -/
def runSlices {L : Type} (step : L → ByteSlice → Called L) :
    L → List Spec.Lexicon.Chars → Called L
  | l, [] => (.ok .continue, l)
  | l, s :: rest =>
    match step l s.toByteArray.toByteSlice with
    | (.ok .continue, l') => runSlices step l' rest
    | called => called

/-- A call of the library's lexer, which stops at its first error, on a slice. -/
def lexerStep (l : BSmtLib.Lexer Collector) (slice : ByteSlice) :
    Called (BSmtLib.Lexer Collector) :=
  BSmtLib.Lexer.Internal.run (m := Id) l
    (BSmtLib.Lexer.Internal.lexSliceStep (R := Empty) (E := Unit)
      (LexRecovery.abandon .failFast) (LexRecovery.recover .failFast) slice)

/-- A call of `X1BatchInCore`, which stops at its first error, on a
slice. -/
def x1Step (x : Lexer.WRustPort.Lexer Collector) (slice : ByteSlice) :
    Called (Lexer.WRustPort.Lexer Collector) :=
  Lexer.WRustPort.Lexer.run (m := Id) x
    (Lexer.WRustPort.lexSliceStep (ops := Lexer.X1BatchInCore.ops) (R := Empty) (E := Unit)
      (LexRecovery.abandon .failFast) (LexRecovery.recover .failFast) slice)

/-- What the adapter records after the calls on the slices: what the end of the input gives
if the last call continued, and none if it failed. -/
def afterRun (ops : Adapter.Ops) : Called ops.Lexer → Option (List BSmtLib.Spec.Lexer.Handed)
  | (.ok .continue, l) => feed ops l []
  | (.ok (.break finished), _) => finished.value.elim
  | (.error _, _) => none

/-- The adapter feeds the slices by the calls of a lexer whose `lexSlice` gives what the call
gives, with what is left after a failed call mapped by `after`. -/
theorem feed_eq_afterRun (ops : Adapter.Ops) (step : ops.Lexer → ByteSlice → Called ops.Lexer)
    (after : ops.Lexer → ops.AfterError)
    (hstep : ∀ l slice, ops.lexSlice l slice =
      match step l slice with
      | (.ok flow, l') => .ok (flow, l')
      | (.error e, l') => .error (e, after l')) :
    ∀ (slices : List Spec.Lexicon.Chars) (l : ops.Lexer),
      feed ops l slices = afterRun ops (runSlices step l slices)
  | [], l => by
    simp only [runSlices, afterRun]
  | s :: rest, l => by
    simp only [feed, runSlices, hstep]
    rcases step l s.toByteArray.toByteSlice with ⟨e | flow, l'⟩
    · rfl
    · cases flow with
      | «continue» => exact feed_eq_afterRun ops step after hstep rest l'
      | «break» finished => exact finished.value.elim

theorem feed_lexer (slices : List Spec.Lexicon.Chars) (l : BSmtLib.Lexer Collector) :
    feed Adapter.Lexer.ops l slices = afterRun Adapter.Lexer.ops (runSlices lexerStep l slices) :=
  feed_eq_afterRun Adapter.Lexer.ops lexerStep (fun _ => ()) (fun l slice => by
    simp only [Adapter.Lexer.ops, BSmtLib.Lexer.lexSlice, lexerStep]
    rcases BSmtLib.Lexer.Internal.run (m := Id) l
      (BSmtLib.Lexer.Internal.lexSliceStep (R := Empty) (E := Unit)
        (LexRecovery.abandon .failFast) (LexRecovery.recover .failFast) slice) with ⟨_ | _, _⟩ <;>
      rfl) slices l

theorem feed_x1 (slices : List Spec.Lexicon.Chars) (x : Lexer.WRustPort.Lexer Collector) :
    feed Adapter.X1BatchInCore.ops x slices =
      afterRun Adapter.X1BatchInCore.ops (runSlices x1Step x slices) :=
  feed_eq_afterRun Adapter.X1BatchInCore.ops x1Step (fun _ => ()) (fun x slice => by
    simp only [Adapter.X1BatchInCore.ops, Lexer.X1BatchInCore.Lexer.lexSlice, x1Step]
    rcases Lexer.WRustPort.Lexer.run (m := Id) x
      (Lexer.WRustPort.lexSliceStep (ops := Lexer.X1BatchInCore.ops) (R := Empty) (E := Unit)
        (LexRecovery.abandon .failFast) (LexRecovery.recover .failFast) slice) with
      ⟨_ | _, _⟩ <;> rfl) slices x

end BSmtLib.Proofs.X1BatchInCoreLexer
