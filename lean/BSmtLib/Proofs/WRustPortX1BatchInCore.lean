import BSmtLib.Proofs.WRustPortX1BatchInCore.Handed

/-!
# The Rust port and the lexer with the batch in its state lex alike

The lexer with the batch in its state `X1BatchInCore` is the Rust port `WRustPort` with one batch
kept in the lexer state and reused from slice to slice, where the Rust port makes a fresh batch
for every slice, at the end of the input and for a token handed over alone. A batch of
`X1BatchInCore` keeps the entries of earlier slices beyond its length; the two lexers' batches
agree (`WRustPortX1BatchInCore.Agree`): the same length, the same entries below it, and the same
array of contents if they have a token. The two lexers do not share their state type: their
states correspond (`WRustPortX1BatchInCore.CoreRel`) when their fields are equal but for the
batches, which agree; between the calls the batches have no tokens
(`WRustPortX1BatchInCore.LexRel`).

A consumer may keep a token from an earlier hand-over and read it through a later cursor; it
then reads the storage beyond the length of the batch, where the two lexers differ. The theorems
hold for consumers that read the cursors they are handed only below the length of their batches
(`WRustPortX1BatchInCore.ConsumesAlike`), as the adapter's consumer does.

- `Lexer.WRustPort.new_sim_x1BatchInCore` and `Lexer.WRustPort.newRecovering_sim_x1BatchInCore`:
  the two lexers are constructed with states that correspond.
- `Lexer.WRustPort.lexSlice_sim_x1BatchInCore`, `Lexer.WRustPort.lexEof_sim_x1BatchInCore` and
  `Lexer.WRustPort.pendingLexEof_sim_x1BatchInCore`: for every such consumer, in every lawful
  monad, with and without recovery, lexers that correspond lex a slice, and the end of the input,
  alike: the two calls are the projections of one computation of the same results, with lexers
  that correspond again (`WRustPortX1BatchInCore.MCouple`).
- `Lexer.WRustPort.handed_eq_handed_x1BatchInCore`: the spec's view.

The proof, in parts:

- `WRustPortX1BatchInCore.Relation`: the relational simulation (`SimR`) of two steps run from
  related states, as the projections of one computation of related outcomes, and its rules;
  the coupling (`Couple`) of two actions of the consumer's monad;
- `WRustPortX1BatchInCore.Batch`: batches and cursors that agree, the operations and reads that
  respect it, and the consumers that read only below the length;
- `WRustPortX1BatchInCore.Core`, `HandOver`, `Flush`, `Finish`, `Held`, `Whitespace`: the helpers
  of the steps, simulated from states that correspond, with the Rust port's line and line start
  given where it keeps them in the locals of its fast path; where a step pushes tokens the two
  batches have the same array of contents, the slice's;
- `WRustPortX1BatchInCore.Normal` and `WRustPortX1BatchInCore.Steps`: the loop of the normal
  state and the steps per state, each by induction on the bytes left where it loops;
- `WRustPortX1BatchInCore.Slice` and `WRustPortX1BatchInCore.Eof`: the loops over a slice and
  the end of the input, coupled, which return with the batches handed over;
- `WRustPortX1BatchInCore.Top` and `WRustPortX1BatchInCore.Calls`: the steps between the calls
  and the calls themselves;
- `WRustPortX1BatchInCore.Collector` and `WRustPortX1BatchInCore.Handed`: the adapter's consumer
  reads only below the length, and what the adapter records.
-/

namespace BSmtLib.Proofs.Lexer

open WRustPortX1BatchInCore

/-- The Rust port and the lexer with the batch in its state are constructed with states that
correspond. -/
theorem WRustPort.new_sim_x1BatchInCore {H : Type} (consumer : H) (version : Version) :
    LexRel (WRustPort.Lexer.new consumer version) (X1BatchInCore.Lexer.new consumer version) :=
  new_rel consumer version

/-- The Rust port and the lexer with the batch in its state that recover are constructed with
states that correspond. -/
theorem WRustPort.newRecovering_sim_x1BatchInCore {H : Type} {m : Type → Type} [Recover H m]
    (consumer : H) (version : Version) :
    LexRel (WRustPort.Lexer.newRecovering (m := m) consumer version)
      (X1BatchInCore.Lexer.newRecovering (m := m) consumer version) :=
  newRecovering_rel consumer version

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {recovery : Recovery}

/-- The Rust port and the lexer with the batch in its state, with the same consumer, which reads
the cursors only below the length of their batches, and states that correspond, lex a slice
alike: the same result, with lexers that correspond again. -/
theorem WRustPort.lexSlice_sim_x1BatchInCore (hcons : ConsumesAlike H m R E)
    [LexRecovery recovery H m] (w : WRustPort.Lexer H recovery)
    (x : X1BatchInCore.Lexer H recovery) (h : LexRel w x) (slice : ByteSlice) :
    MCouple (ResRel (AfterRel recovery)) (WRustPort.Lexer.lexSlice (R := R) (E := E) w slice)
      (X1BatchInCore.Lexer.lexSlice x slice) :=
  lexSlice_couple hcons w x h slice

/-- The Rust port and the lexer with the batch in its state, with the same consumer, which reads
the cursors only below the length of their batches, and states that correspond, lex the end of
the input alike: the same result, with lexers that correspond again. -/
theorem WRustPort.lexEof_sim_x1BatchInCore (hcons : ConsumesAlike H m R E)
    [LexRecovery recovery H m] (w : WRustPort.Lexer H recovery)
    (x : X1BatchInCore.Lexer H recovery) (h : LexRel w x) :
    MCouple (ResRel (AfterEofRel recovery)) (WRustPort.Lexer.lexEof (R := R) (E := E) w)
      (X1BatchInCore.Lexer.lexEof x) :=
  lexEof_couple hcons w x h

/-- The Rust port and the lexer with the batch in its state, recovering at the end of the input,
lex the end of the input again alike. -/
theorem WRustPort.pendingLexEof_sim_x1BatchInCore (hcons : ConsumesAlike H m R E) [Recover H m]
    (w : WRustPort.Lexer.PendingEof H) (x : X1BatchInCore.Lexer.PendingEof H)
    (h : LexRel w.lexer x.lexer) :
    MCouple (ResRel (recovery := .recovering) LexRel)
      (WRustPort.Lexer.PendingEof.lexEof (R := R) (E := E) w)
      (X1BatchInCore.Lexer.PendingEof.lexEof x) :=
  pendingLexEof_couple hcons w x h

end

/-- The Rust port and the lexer with the batch in its state, run by the adapter, hand over the
same tokens. -/
theorem WRustPort.handed_eq_handed_x1BatchInCore (version : Spec.Lexicon.Version)
    (slices : List Spec.Lexicon.Chars) :
    Adapter.handed Adapter.WRustPort.ops version slices =
      Adapter.handed Adapter.X1BatchInCore.ops version slices :=
  handed_eq version slices

end BSmtLib.Proofs.Lexer
