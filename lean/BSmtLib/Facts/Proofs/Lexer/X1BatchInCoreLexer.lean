module

public import BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Handed

@[expose] public section

/-!
# The lexer with the batch kept in its state and the library's lexer lex alike

The library's lexer `BSmtLib.Lexer` is the lexer with the batch kept in its state
`X1BatchInCore` with `USize` positions in the whole array of the slice, where `X1BatchInCore`,
which runs the code of the Rust port `WRustPort`, has `Nat` indices into the slice; and it has
the library's forms of what the Rust port writes as Rust does: it throws an error where it finds
it, reads the byte after a closing quote only once it has found the quote, reads whether the
consumer takes whitespace and comments where it needs it, and has no locals of the loop of the
normal state. The two do not share their state type: a state of the library's lexer is one of
the lexer with the batch kept in its state with its `base`, the position of the byte at the
lexer's offset, mapped to the index of that position (`X1BatchInCoreLexer.coreMap`). Between the
calls the base means nothing, so the lexers are related by `X1BatchInCoreLexer.LexerRel`: they
have the same consumer, and their states are equal once the base is forgotten.

- `Lexer.X1BatchInCore.new_eq_new_lexer`: the lexer with the batch kept in its state is
  constructed as the library's lexer is, with its state mapped.
- `Lexer.X1BatchInCore.lexSliceStep_sim_lexer` and `Lexer.X1BatchInCore.lexEofStep_sim_lexer`:
  for every consumer, in every lawful monad, with and without recovery, the step of a call on a
  slice, and on the end of the input, run on related lexers by `run`, gives the same result and
  related lexers, also where the call fails. For a slice, this holds where its end is below
  `USize.size`; the library's lexer lexes a larger slice in chunks, which the lexer with the
  batch kept in its state does not. `lexSlice_sim_lexer` and `lexEof_sim_lexer` are the same of
  the calls themselves.

The library's lexer lexes a slice too large for its positions in chunks: `Chunks.cutAll` cuts
every such slice of a list into the chunks it lexes it by, with the same bytes
(`Chunks.flatten_cutAll`).

The proof, in parts:

- `X1BatchInCoreLexer.Positions`: the reads and the run scans at a position are those at its
  index;
- `X1BatchInCoreLexer.Core`, `HandOver`, `Finish`, `Batch`, `Whitespace`: the helpers of the
  steps, simulated (`Simulation.SimP`) under `coreMap` of the start of the slice, from the states
  with a given base, with the errors of the library's lexer thrown where the Rust port's are
  formed and then thrown;
- `X1BatchInCoreLexer.Steps` and `X1BatchInCoreLexer.Normal`: the steps per state and the loop of
  the normal state, each by induction on the bytes left where it loops;
- `X1BatchInCoreLexer.Step`: the step of the loop over a slice, which leaves the base between the
  start of the slice and the position it returns;
- `X1BatchInCoreLexer.Slice`: the loop over a slice, simulated up to the first stop of the
  consumer and coupled over the stops, where a stop at the end of the slice goes back to a
  position that only the base records;
- `X1BatchInCoreLexer.Outer`, `Recovery`, `Eof`, `Calls`: the steps between the calls, coupled
  from related states;
- `X1BatchInCoreLexer.Top`: the calls, and their steps run by `run`;
- `X1BatchInCoreLexer.Chunks`: the chunks of a slice too large for the positions of the library's
  lexer;
- `X1BatchInCoreLexer.Handed`: the constructed lexers.
-/

namespace BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer

open BSmtLib.Facts.Proofs.Lexer.Simulation.Couple (MCouple)

/-- The lexer with the batch kept in its state is constructed as the library's lexer is, with
its state mapped. -/
theorem X1BatchInCore.new_eq_new_lexer {H R E : Type} [Token.Consume H R E] (consumer : H)
    (version : Token.Version) :
    Lexer.Internal.WRustPort.Lexer.new consumer version =
      { handler := BSmtLib.Lexer.Internal.handler (BSmtLib.Lexer.new consumer version)
        core := Core.coreMap 0 (BSmtLib.Lexer.Internal.core (BSmtLib.Lexer.new consumer version))
        held := BSmtLib.Lexer.Internal.held (BSmtLib.Lexer.new consumer version) } :=
  Handed.new_eq consumer version

/-- The lexer with the batch kept in its state that recovers is constructed as the library's
lexer that recovers is, with its state mapped. -/
theorem X1BatchInCore.newRecovering_eq_newRecovering_lexer {H R E : Type} [Token.Consume H R E]
    {m : Type → Type} [Token.Recover H m] (consumer : H) (version : Token.Version) :
    Lexer.Internal.WRustPort.Lexer.newRecovering (m := m) consumer version =
      { handler := BSmtLib.Lexer.Internal.handler (BSmtLib.Lexer.newRecovering
          (m := m) consumer version)
        core := Core.coreMap 0 (BSmtLib.Lexer.Internal.core
            (BSmtLib.Lexer.newRecovering (m := m) consumer version))
        held := BSmtLib.Lexer.Internal.held
          (BSmtLib.Lexer.newRecovering (m := m) consumer version) } :=
  Handed.newRecovering_eq consumer version

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]

/-- The step of a call on a slice that ends below `USize.size`, run by `run` on related lexers
(`LexerRel`), gives the same result in the library's lexer and in the lexer with the batch kept
in its state, and related lexers, also where the call fails: the two runs are the projections
of one run of such pairs. -/
theorem X1BatchInCore.lexSliceStep_sim_lexer (abandon recover : Span.Location → StateT H m Unit)
    {recovery : Lexer.Recovery} (l : BSmtLib.Lexer H recovery)
    (x : Lexer.Internal.WRustPort.Lexer H recovery)
    (hlx : Top.LexerRel l x) (slice : ByteSlice) (hs : slice.stop < USize.size) :
    MCouple (fun a b => a.1 = b.1 ∧ Top.LexerRel a.2 b.2)
      (BSmtLib.Lexer.Internal.run l
        (BSmtLib.Lexer.Internal.lexSliceStep (R := R) (E := E) abandon recover slice))
      (x.run (Lexer.Internal.WRustPort.lexSliceStep
          (ops := Lexer.Internal.X1BatchInCore.ops) abandon recover slice)) :=
  Top.run_lexSliceStep abandon recover l x hlx slice hs

/-- The step of a call on the end of the input, run by `run` on related lexers, gives the same
result in the library's lexer and in the lexer with the batch kept in its state, and related
lexers, also where the call fails. -/
theorem X1BatchInCore.lexEofStep_sim_lexer (abandon recover : Span.Location → StateT H m Unit)
    {recovery : Lexer.Recovery} (l : BSmtLib.Lexer H recovery)
    (x : Lexer.Internal.WRustPort.Lexer H recovery)
    (hlx : Top.LexerRel l x) :
    MCouple (fun a b => a.1 = b.1 ∧ Top.LexerRel a.2 b.2)
      (BSmtLib.Lexer.Internal.run l
        (BSmtLib.Lexer.Internal.lexEofStep (R := R) (E := E) abandon recover))
      (x.run (Lexer.Internal.WRustPort.lexEofStep (ops := Lexer.Internal.X1BatchInCore.ops) abandon
          recover)) :=
  Top.run_lexEofStep abandon recover l x hlx

/-- The lexer with the batch kept in its state and the library's lexer, with the same consumer,
the same held result and states equal but for the base, lex a slice that ends below
`USize.size` alike: the results are equal once the base is forgotten. -/
theorem X1BatchInCore.lexSlice_sim_lexer {recovery : Lexer.Recovery} [Lexer.Recovery.LexRecovery
    recovery H m]
    (x : Lexer.Internal.WRustPort.Lexer H recovery) (l : BSmtLib.Lexer H recovery)
    (hh : x.handler = BSmtLib.Lexer.Internal.handler l)
    (hx : Outer.Rel (BSmtLib.Lexer.Internal.core l) x.core)
    (hd : x.held = BSmtLib.Lexer.Internal.held l) (slice : ByteSlice)
    (hs : slice.stop < USize.size) :
    Top.resultMap Top.afterErrorZb Top.lexerZb <$> Lexer.Internal.X1BatchInCore.Lexer.lexSlice x
        slice =
      Top.resultMap Top.afterErrorMap Top.lexerMap <$> BSmtLib.Lexer.lexSlice l slice :=
  Top.lexSlice_sim l x hh hx hd slice hs

/-- The lexer with the batch kept in its state and the library's lexer, with the same consumer,
the same held result and states equal but for the base, lex the end of the input alike: the
results are equal once the base is forgotten. -/
theorem X1BatchInCore.lexEof_sim_lexer {recovery : Lexer.Recovery} [Lexer.Recovery.LexRecovery
    recovery H m]
    (x : Lexer.Internal.WRustPort.Lexer H recovery) (l : BSmtLib.Lexer H recovery)
    (hh : x.handler = BSmtLib.Lexer.Internal.handler l)
    (hx : Outer.Rel (BSmtLib.Lexer.Internal.core l) x.core)
    (hd : x.held = BSmtLib.Lexer.Internal.held l) :
    Top.resultMap Top.afterEofZb (fun p => (p.1, Top.lexerZb p.2)) <$>
        Lexer.Internal.X1BatchInCore.Lexer.lexEof x =
      Top.resultMap Top.afterEofMap (fun p => (p.1, Top.lexerMap p.2)) <$> BSmtLib.Lexer.lexEof l :=
  Top.lexEof_sim l x hh hx hd

end

end BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer
