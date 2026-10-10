import BSmtLib.Proofs.WRustPortX1BatchInCore.Fed

/-!
# The Rust port and the lexer with the batch in its state lex alike

The lexer with the batch in its state `X1BatchInCore` is the code of the Rust port `WRustPort`
over operations of its own (`WRustPort.Ops`): one batch kept in the lexer state and reused from
slice to slice, where the Rust port makes a fresh batch for every slice, at the end of the input
and for a token handed over alone, and the line counters read from the lexer state, where the
Rust port keeps them in locals of its fast path. The two lexers have the same type.

A batch of `X1BatchInCore` keeps the entries of earlier slices beyond its length; the two
lexers' batches agree (`Simulation.Agree`): the same length, the same entries below it, and the
same array of contents if they have a token. Two lexer states correspond
(`WRustPortX1BatchInCore.CoreRel`) when their fields are equal but for the batches, which agree;
between the calls the batches have no tokens, and two lexers correspond
(`WRustPortX1BatchInCore.LexRel`) when they also have the same consumer.

A consumer may keep a token from an earlier hand-over and read it through a later cursor; it
then reads the storage beyond the length of the batch, where the two lexers differ. The theorems
about the two lexers hold for consumers that read the cursors they are handed only below the
length of their batches (`Simulation.ConsumesAlike`), as the adapter's consumer does.

- `Lexer.WRustPort.run_sim_of_opsSim`: the code of the Rust port over two structures of
  operations that simulate each other (`WRustPortX1BatchInCore.OpsSim`) runs alike: in every
  lawful monad, with and without recovery, the step of a call on a slice and at the end of the
  input, run on lexers that correspond (`Lexer.run`), are the projections of one computation of
  the same results, with lexers that correspond again (`Simulation.MCouple`), also where the call
  fails.
- `Lexer.WRustPort.opsSim_x1BatchInCore`: the operations of the Rust port and of the lexer with
  the batch in its state simulate each other, for every such consumer.
- `Lexer.WRustPort.run_lexSliceStep_sim_x1BatchInCore` and
  `Lexer.WRustPort.run_lexEofStep_sim_x1BatchInCore`: the two together, for the two lexers. They
  relate the lexers after every call, so that what the lexers have done after a prefix of the
  slices is related too.
- `Lexer.WRustPort.new_sim_x1BatchInCore`, `Lexer.WRustPort.newRecovering_sim_x1BatchInCore`,
  `Lexer.WRustPort.lexSlice_sim_x1BatchInCore`, `Lexer.WRustPort.lexEof_sim_x1BatchInCore` and
  `Lexer.WRustPort.pendingLexEof_sim_x1BatchInCore`: the constructed lexers correspond, and the
  calls of the two lexers on lexers that correspond give the same results with lexers that
  correspond again.
- `Lexer.WRustPort.fedInput_eq_fedInput_x1BatchInCore`: the spec's view, of slices and then, if
  the input has ended, the end of the input.

The proof, in parts:

- `WRustPortX1BatchInCore.Core`: the states that correspond, and the helpers of the code that do
  not use the operations, simulated under `Simulation.SimR`;
- `WRustPortX1BatchInCore.Ops`: operations that simulate each other;
- `WRustPortX1BatchInCore.Held`, `Finish`, `Whitespace`, `Normal`, `Steps`, `Slice`, `Eof`,
  `Top`, `Calls`: the code over two structures of operations that simulate each other, from the
  batch held by the loop of the normal state up to the calls, each loop by induction on the bytes
  left;
- `WRustPortX1BatchInCore.HandOver`, `Flush`, `Instance`: the operations of the two lexers
  simulate each other;
- `WRustPortX1BatchInCore.Api`: the calls of the two lexers;
- `WRustPortX1BatchInCore.Collector`, `WRustPortX1BatchInCore.Handed` and
  `WRustPortX1BatchInCore.Fed`: the adapter's consumer reads only below the length, the
  constructed lexers, and what the adapter records.
-/

namespace BSmtLib.Proofs.Lexer

open WRustPortX1BatchInCore
open BSmtLib.Proofs.Simulation (ConsumesAlike MCouple)

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {recovery : Recovery}

/-- The code of the Rust port over two structures of operations that simulate each other runs
alike: the step of a call on a slice and the step of a call at the end of the input, run on
lexers that correspond, give the same result with lexers that correspond again, whether the call
succeeds or fails. -/
theorem WRustPort.run_sim_of_opsSim {o₁ o₂ : WRustPort.Ops H m R E}
    {LRel : WRustPort.Ops.Locals H m R E (self := o₁) → WRustPort.Ops.Locals H m R E (self := o₂) →
      Nat → Nat → Prop}
    (ho : OpsSim o₁ o₂ LRel) (abandon recover : Location → StateT H m Unit)
    (self self' : WRustPort.Lexer H recovery) (h : LexRel self self') :
    (∀ slice, MCouple RunRel
      (self.run (WRustPort.lexSliceStep (ops := o₁) (R := R) (E := E) abandon recover slice))
      (self'.run (WRustPort.lexSliceStep (ops := o₂) abandon recover slice))) ∧
    MCouple RunRel
      (self.run (WRustPort.lexEofStep (ops := o₁) (R := R) (E := E) abandon recover))
      (self'.run (WRustPort.lexEofStep (ops := o₂) abandon recover)) :=
  ⟨fun slice => run_lexSliceStep_sim ho abandon recover slice self self' h,
    run_lexEofStep_sim ho abandon recover self self' h⟩

/-- The operations of the Rust port and of the lexer with the batch in its state simulate each
other, for a consumer that reads the cursors only below the length of their batches; the Rust
port's locals are the line and the line start. -/
theorem WRustPort.opsSim_x1BatchInCore (hcons : ConsumesAlike H m R E) :
    OpsSim (WRustPort.Rust.ops (H := H) (m := m) (R := R) (E := E)) X1BatchInCore.ops FastRel :=
  opsSim_rust_x1BatchInCore hcons

/-- The Rust port and the lexer with the batch in its state, with the same consumer, which reads
the cursors only below the length of their batches, run the step of a call on a slice on lexers
that correspond to the same result, with lexers that correspond again, also where it fails. -/
theorem WRustPort.run_lexSliceStep_sim_x1BatchInCore (hcons : ConsumesAlike H m R E)
    (abandon recover : Location → StateT H m Unit) (slice : ByteSlice)
    (self self' : WRustPort.Lexer H recovery) (h : LexRel self self') :
    MCouple RunRel
      (self.run (WRustPort.lexSliceStep (ops := WRustPort.Rust.ops) (R := R) (E := E) abandon
        recover slice))
      (self'.run (WRustPort.lexSliceStep (ops := X1BatchInCore.ops) abandon recover slice)) :=
  ((WRustPort.run_sim_of_opsSim (WRustPort.opsSim_x1BatchInCore hcons) abandon recover self
    self' h).1 slice)

/-- The Rust port and the lexer with the batch in its state, with the same consumer, which reads
the cursors only below the length of their batches, run the step of a call at the end of the
input on lexers that correspond to the same result, with lexers that correspond again, also
where it fails. -/
theorem WRustPort.run_lexEofStep_sim_x1BatchInCore (hcons : ConsumesAlike H m R E)
    (abandon recover : Location → StateT H m Unit)
    (self self' : WRustPort.Lexer H recovery) (h : LexRel self self') :
    MCouple RunRel
      (self.run (WRustPort.lexEofStep (ops := WRustPort.Rust.ops) (R := R) (E := E) abandon
        recover))
      (self'.run (WRustPort.lexEofStep (ops := X1BatchInCore.ops) abandon recover)) :=
  (WRustPort.run_sim_of_opsSim (WRustPort.opsSim_x1BatchInCore hcons) abandon recover self
    self' h).2

end

/-- A lexer constructed for the Rust port and the lexer with the batch in its state, which have
the same constructor, corresponds to itself. -/
theorem WRustPort.new_sim_x1BatchInCore {H : Type} (consumer : H) (version : Version) :
    LexRel (WRustPort.Lexer.new consumer version) (WRustPort.Lexer.new consumer version) :=
  new_rel consumer version

/-- A lexer that recovers constructed for the Rust port and the lexer with the batch in its
state corresponds to itself. -/
theorem WRustPort.newRecovering_sim_x1BatchInCore {H : Type} {m : Type → Type} [Recover H m]
    (consumer : H) (version : Version) :
    LexRel (WRustPort.Lexer.newRecovering (m := m) consumer version)
      (WRustPort.Lexer.newRecovering (m := m) consumer version) :=
  newRecovering_rel consumer version

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {recovery : Recovery}

/-- The Rust port and the lexer with the batch in its state, with the same consumer, which reads
the cursors only below the length of their batches, lex a slice alike from lexers that
correspond: the same result, with lexers that correspond again. -/
theorem WRustPort.lexSlice_sim_x1BatchInCore (hcons : ConsumesAlike H m R E)
    [LexRecovery recovery H m] (w x : WRustPort.Lexer H recovery) (h : LexRel w x)
    (slice : ByteSlice) :
    MCouple (ResRel (AfterRel recovery)) (WRustPort.Lexer.lexSlice (R := R) (E := E) w slice)
      (X1BatchInCore.Lexer.lexSlice x slice) :=
  lexSlice_couple hcons w x h slice

/-- The Rust port and the lexer with the batch in its state, with the same consumer, which reads
the cursors only below the length of their batches, lex the end of the input alike from lexers
that correspond: the same result, with lexers that correspond again. -/
theorem WRustPort.lexEof_sim_x1BatchInCore (hcons : ConsumesAlike H m R E)
    [LexRecovery recovery H m] (w x : WRustPort.Lexer H recovery) (h : LexRel w x) :
    MCouple (ResRel (AfterEofRel recovery)) (WRustPort.Lexer.lexEof (R := R) (E := E) w)
      (X1BatchInCore.Lexer.lexEof x) :=
  lexEof_couple hcons w x h

/-- The Rust port and the lexer with the batch in its state, recovering at the end of the input,
lex the end of the input again alike. -/
theorem WRustPort.pendingLexEof_sim_x1BatchInCore (hcons : ConsumesAlike H m R E) [Recover H m]
    (w x : WRustPort.Lexer.PendingEof H) (h : LexRel w.lexer x.lexer) :
    MCouple (ResRel (recovery := .recovering) LexRel)
      (WRustPort.Lexer.PendingEof.lexEof (R := R) (E := E) w)
      (X1BatchInCore.Lexer.PendingEof.lexEof x) :=
  pendingLexEof_couple hcons w x h

end

/-- The Rust port and the lexer with the batch in its state, fed by the adapter slices and then,
if the input has ended, the end of the input, hand over the same tokens and fail alike. -/
theorem WRustPort.fedInput_eq_fedInput_x1BatchInCore (version : Spec.Lexicon.Version)
    (slices : List Spec.Lexicon.Chars) (ended : Bool) :
    Adapter.fedInput Adapter.WRustPort.ops version slices ended =
      Adapter.fedInput Adapter.X1BatchInCore.ops version slices ended :=
  fedInput_eq version slices ended

end BSmtLib.Proofs.Lexer
