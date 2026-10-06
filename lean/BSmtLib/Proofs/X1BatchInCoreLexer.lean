import BSmtLib.Proofs.X1BatchInCoreLexer.Handed

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
- `Lexer.X1BatchInCore.runSlices_cutAll_lexer`: the library's lexer, fed slices one call after
  another with the adapter's consumer, gives the result that the lexer with the batch kept in its
  state gives fed the slices with each slice too large for the positions cut into the chunks it
  lexes such a slice by (`X1BatchInCoreLexer.Chunks.cutAll`), and a lexer related to it, also
  after a failed call; the cut slices have the same bytes and end below `USize.size`.
- `Lexer.handed_eq_handed_x1BatchInCore`: the spec's view of the whole input, run by the
  adapter: the library's lexer hands over for the slices what the lexer with the batch kept in
  its state hands over for their cut.

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
- `X1BatchInCoreLexer.Run`: the calls on slices one after another (`runSlices`), and what the
  adapter records of them;
- `X1BatchInCoreLexer.Chunks`: the library's lexer on a slice too large for its positions;
- `X1BatchInCoreLexer.Handed`: the calls on slices one after another, and what the adapter
  records.
-/

namespace BSmtLib.Proofs.Lexer

open X1BatchInCoreLexer
open BSmtLib.Proofs.Simulation (MCouple)
open BSmtLib.Lexer.Internal (handler core)

/-- The lexer with the batch kept in its state is constructed as the library's lexer is, with
its state mapped. -/
theorem X1BatchInCore.new_eq_new_lexer {H : Type} (consumer : H) (version : Version) :
    WRustPort.Lexer.new consumer version =
      { handler := handler (BSmtLib.Lexer.new consumer version)
        core := coreMap 0 (core (BSmtLib.Lexer.new consumer version)) } :=
  new_eq consumer version

/-- The lexer with the batch kept in its state that recovers is constructed as the library's
lexer that recovers is, with its state mapped. -/
theorem X1BatchInCore.newRecovering_eq_newRecovering_lexer {H : Type} {m : Type → Type}
    [Recover H m] (consumer : H) (version : Version) :
    WRustPort.Lexer.newRecovering (m := m) consumer version =
      { handler := handler (BSmtLib.Lexer.newRecovering (m := m) consumer version)
        core := coreMap 0 (core (BSmtLib.Lexer.newRecovering (m := m) consumer version)) } :=
  newRecovering_eq consumer version

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]

/-- The step of a call on a slice that ends below `USize.size`, run by `run` on related lexers
(`LexerRel`), gives the same result in the library's lexer and in the lexer with the batch kept
in its state, and related lexers, also where the call fails: the two runs are the projections
of one run of such pairs. -/
theorem X1BatchInCore.lexSliceStep_sim_lexer (abandon recover : Location → StateT H m Unit)
    {recovery : Recovery} (l : BSmtLib.Lexer H recovery) (x : WRustPort.Lexer H recovery)
    (hlx : LexerRel l x) (slice : ByteSlice) (hs : slice.stop < USize.size) :
    MCouple (fun a b => a.1 = b.1 ∧ LexerRel a.2 b.2)
      (BSmtLib.Lexer.Internal.run l
        (BSmtLib.Lexer.Internal.lexSliceStep (R := R) (E := E) abandon recover slice))
      (x.run (WRustPort.lexSliceStep (ops := X1BatchInCore.ops) abandon recover slice)) :=
  run_lexSliceStep abandon recover l x hlx slice hs

/-- The step of a call on the end of the input, run by `run` on related lexers, gives the same
result in the library's lexer and in the lexer with the batch kept in its state, and related
lexers, also where the call fails. -/
theorem X1BatchInCore.lexEofStep_sim_lexer (abandon recover : Location → StateT H m Unit)
    {recovery : Recovery} (l : BSmtLib.Lexer H recovery) (x : WRustPort.Lexer H recovery)
    (hlx : LexerRel l x) :
    MCouple (fun a b => a.1 = b.1 ∧ LexerRel a.2 b.2)
      (BSmtLib.Lexer.Internal.run l
        (BSmtLib.Lexer.Internal.lexEofStep (R := R) (E := E) abandon recover))
      (x.run (WRustPort.lexEofStep (ops := X1BatchInCore.ops) abandon recover)) :=
  run_lexEofStep abandon recover l x hlx

/-- The lexer with the batch kept in its state and the library's lexer, with the same consumer
and states equal but for the base, lex a slice that ends below `USize.size` alike: the results
are equal once the base is forgotten. -/
theorem X1BatchInCore.lexSlice_sim_lexer {recovery : Recovery} [LexRecovery recovery H m]
    (x : WRustPort.Lexer H recovery) (l : BSmtLib.Lexer H recovery)
    (hh : x.handler = handler l) (hx : Rel (core l) x.core) (slice : ByteSlice)
    (hs : slice.stop < USize.size) :
    resultZb afterErrorZb <$> X1BatchInCore.Lexer.lexSlice (R := R) (E := E) x slice =
      resultMap afterErrorMap <$> BSmtLib.Lexer.lexSlice l slice :=
  lexSlice_sim l x hh hx slice hs

/-- The lexer with the batch kept in its state and the library's lexer, with the same consumer
and states equal but for the base, lex the end of the input alike: the results are equal once
the base is forgotten. -/
theorem X1BatchInCore.lexEof_sim_lexer {recovery : Recovery} [LexRecovery recovery H m]
    (x : WRustPort.Lexer H recovery) (l : BSmtLib.Lexer H recovery)
    (hh : x.handler = handler l) (hx : Rel (core l) x.core) :
    resultZb afterEofZb <$> X1BatchInCore.Lexer.lexEof (R := R) (E := E) x =
      resultMap afterEofMap <$> BSmtLib.Lexer.lexEof l :=
  lexEof_sim l x hh hx

end

/-- The library's lexer, fed the slices one call after another with the adapter's consumer,
gives the result that the lexer with the batch kept in its state gives fed their cut, and a
lexer related to it, also after a failed call, from related lexers that neither discard nor
recover, as the constructed ones do; the cut slices have the same bytes and end below
`USize.size`. -/
theorem X1BatchInCore.runSlices_cutAll_lexer (slices : List Spec.Lexicon.Chars)
    (l : BSmtLib.Lexer Adapter.Collector) (x : WRustPort.Lexer Adapter.Collector)
    (hlx : LexerRel l x) (hl : Chunks.Inv (core l)) :
    ((runSlices lexerStep l slices).1 = (runSlices x1Step x (Chunks.cutAll slices)).1 ∧
      LexerRel (runSlices lexerStep l slices).2 (runSlices x1Step x (Chunks.cutAll slices)).2) ∧
      (Chunks.cutAll slices).flatten = slices.flatten ∧
      ∀ s ∈ Chunks.cutAll slices, s.length < USize.size :=
  ⟨runSlices_cutAll slices l x hlx hl, Chunks.flatten_cutAll slices,
    fun _ h => Chunks.mem_cutAll h⟩

/-- The library's lexer, run by the adapter, hands over for the slices what the lexer with the
batch kept in its state hands over for them with each slice too large for the positions of the
library's lexer cut into its chunks; the cut slices have the same bytes. -/
theorem handed_eq_handed_x1BatchInCore (version : Spec.Lexicon.Version)
    (slices : List Spec.Lexicon.Chars) :
    Adapter.handed Adapter.Lexer.ops version slices =
        Adapter.handed Adapter.X1BatchInCore.ops version (Chunks.cutAll slices) ∧
      (Chunks.cutAll slices).flatten = slices.flatten :=
  ⟨handed_eq_cutAll version slices, Chunks.flatten_cutAll slices⟩

end BSmtLib.Proofs.Lexer
