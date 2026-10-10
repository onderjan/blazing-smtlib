import BSmtLib.Proofs.Adapter

/-!
# The calls of the lexers on slices, one after another

The adapter's consumer is fed slices by calls of a lexer, each of which runs the lexer's step on a
slice (`lexSliceStep`) by `run`, which gives back the lexer after the call even where the call
failed. `runSlices` makes these calls for a list of slices, one after another, until a call does
not continue, and gives the result of the last call made and the lexer after it: what a lexer
has done after being fed the slices, before the end of the input. `lexerStep` and `x1Step` are the
calls of the library's lexer and of `X1BatchInCore`.

What the adapter records when it feeds the slices and then, if the input has ended, the end of
the input is what it records after `runSlices` (`feedInput_eq_afterRun`).
-/

namespace BSmtLib.Proofs.X1BatchInCoreLexer

open BSmtLib.Proofs.Adapter (Collector feedInput)

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

/-- What the adapter records after the calls on the slices: what it feeds then, if the last call
continued, and that a call failed, with the consumer as the last call left it, if it failed. -/
def afterRun (ops : Adapter.Ops) (ended : Bool) : Called ops.Lexer → Collector × Bool
  | (.ok .continue, l) => feedInput ops l ended []
  | (.ok (.break finished), _) => finished.value.elim
  | (.error _, l) => (ops.handler l, true)

/-- The adapter feeds the slices by the calls of `runSlices`, when its step is the lexer's
call. -/
theorem feedInput_eq_afterRun (ops : Adapter.Ops) (ended : Bool)
    (step : ops.Lexer → ByteSlice → Called ops.Lexer)
    (hstep : ∀ l slice, ops.lexSliceStep l slice = step l slice) :
    ∀ (slices : List Spec.Lexicon.Chars) (l : ops.Lexer),
      feedInput ops l ended slices = afterRun ops ended (runSlices step l slices)
  | [], l => rfl
  | s :: rest, l => by
    simp only [feedInput, runSlices, hstep]
    rcases step l s.toByteArray.toByteSlice with ⟨e | flow, l'⟩
    · rfl
    · cases flow with
      | «continue» => exact feedInput_eq_afterRun ops ended step hstep rest l'
      | «break» finished => exact finished.value.elim

end BSmtLib.Proofs.X1BatchInCoreLexer
