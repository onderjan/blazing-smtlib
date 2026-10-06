import BSmtLib.Proofs.X2ContentsLexer.Handed
import BSmtLib.Proofs.X2ContentsLexer.Chunks

/-!
# The lexer with the content buffer and the library's lexer lex alike

The library's lexer `BSmtLib.Lexer` is the lexer with the content buffer `X2Contents` with
`USize` positions in the whole array of the slice, where `X2Contents` has `Nat` indices into the
slice. The two do not share their state type: a state of the library's lexer is one of the lexer
with the content buffer with its `base`, the position of the byte at the lexer's offset, mapped
to the index of that position (`X2ContentsLexer.coreMap`). Between the calls the base means
nothing, so the lexers are related by `X2ContentsLexer.Rel`: their states are equal once the
base is forgotten.

- `Lexer.X2Contents.new_eq_new_lexer`: the lexer with the content buffer is constructed as the
  library's lexer is, with its state mapped.
- `Lexer.X2Contents.lexSlice_sim_lexer` and `Lexer.X2Contents.lexEof_sim_lexer`: for every
  consumer, in every lawful monad, with and without recovery, lexers with the same consumer and
  related states lex a slice, and the end of the input, alike: the results are equal once the
  base is forgotten. For a slice, this holds where its end is below `USize.size`; the library's
  lexer lexes a larger slice in chunks, which the lexer with the content buffer does not.
- `Lexer.X2Contents.handed_eq_handed_lexer`: the spec's view, for slices that end below
  `USize.size`.
- `Lexer.handed_eq_handed_cutAll`: of the library's lexer alone, run by the adapter, it hands
  over for the slices what it hands over for them with each slice too large for its positions cut
  into the chunks it lexes such a slice by (`X2ContentsLexer.Chunks.cutAll`); the cut slices have
  the same bytes and end below `USize.size`.

The proof, in parts:

- `X2ContentsLexer.Positions`: the reads and the run scans at a position are those at its index;
- `X2ContentsLexer.Core`, `HandOver`, `Finish`, `Batch`, `Whitespace`: the helpers of the steps,
  simulated (`Simulation.SimP`) under `coreMap` of the start of the slice, from the states with a
  given base;
- `X2ContentsLexer.Steps` and `X2ContentsLexer.Normal`: the steps per state and the loop of the
  normal state, each by induction on the bytes left where it loops;
- `X2ContentsLexer.Step`: the step of the loop over a slice, which leaves the base between the
  start of the slice and the position it returns;
- `X2ContentsLexer.Slice`: the loop over a slice, simulated up to the first stop of the consumer
  and coupled (`X2ContentsLexer.Couple`) over the stops, where a stop at the end of the slice
  goes back to a position that only the base records;
- `X2ContentsLexer.Outer`, `Recovery`, `Eof`, `Calls`: the steps between the calls, coupled from
  related states;
- `X2ContentsLexer.Top` and `X2ContentsLexer.Handed`: the calls, and what the adapter records;
- `X2ContentsLexer.Chunks`: the library's lexer on a slice too large for its positions.
-/

namespace BSmtLib.Proofs.Lexer

open X2ContentsLexer
open BSmtLib.Lexer.Internal (handler core)

/-- The lexer with the content buffer is constructed as the library's lexer is, with its state
mapped. -/
theorem X2Contents.new_eq_new_lexer {H : Type} (consumer : H) (version : Version) :
    X2Contents.Lexer.new consumer version =
      { handler := handler (BSmtLib.Lexer.new consumer version)
        core := coreMap 0 (core (BSmtLib.Lexer.new consumer version)) } :=
  new_eq consumer version

/-- The lexer with the content buffer that recovers is constructed as the library's lexer that
recovers is, with its state mapped. -/
theorem X2Contents.newRecovering_eq_newRecovering_lexer {H : Type} {m : Type → Type}
    [Recover H m] (consumer : H) (version : Version) :
    X2Contents.Lexer.newRecovering (m := m) consumer version =
      { handler := handler (BSmtLib.Lexer.newRecovering (m := m) consumer version)
        core := coreMap 0 (core (BSmtLib.Lexer.newRecovering (m := m) consumer version)) } :=
  newRecovering_eq consumer version

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]

/-- The lexer with the content buffer and the library's lexer, with the same consumer and states
equal but for the base, lex a slice that ends below `USize.size` alike: the results are equal
once the base is forgotten. -/
theorem X2Contents.lexSlice_sim_lexer {recovery : Recovery} [LexRecovery recovery H m]
    (x : X2Contents.Lexer H recovery) (l : BSmtLib.Lexer H recovery)
    (hh : x.handler = handler l) (hx : Rel (core l) x.core) (slice : ByteSlice)
    (hs : slice.stop < USize.size) :
    resultZb afterErrorZb <$> X2Contents.Lexer.lexSlice (R := R) (E := E) x slice =
      resultMap afterErrorMap <$> BSmtLib.Lexer.lexSlice l slice :=
  lexSlice_sim l x hh hx slice hs

/-- The lexer with the content buffer and the library's lexer, with the same consumer and states
equal but for the base, lex the end of the input alike: the results are equal once the base is
forgotten. -/
theorem X2Contents.lexEof_sim_lexer {recovery : Recovery} [LexRecovery recovery H m]
    (x : X2Contents.Lexer H recovery) (l : BSmtLib.Lexer H recovery)
    (hh : x.handler = handler l) (hx : Rel (core l) x.core) :
    resultZb afterEofZb <$> X2Contents.Lexer.lexEof (R := R) (E := E) x =
      resultMap afterEofMap <$> BSmtLib.Lexer.lexEof l :=
  lexEof_sim l x hh hx

end

/-- The lexer with the content buffer and the library's lexer, run by the adapter, hand over the
same tokens, for slices that end below `USize.size`. -/
theorem X2Contents.handed_eq_handed_lexer (version : Spec.Lexicon.Version)
    (slices : List Spec.Lexicon.Chars) (hb : ∀ s ∈ slices, s.length < USize.size) :
    Adapter.handed Adapter.X2Contents.ops version slices =
      Adapter.handed Adapter.Lexer.ops version slices :=
  feed_eq slices hb _ _ rfl rfl

/-- The library's lexer, run by the adapter, hands over for the slices what it hands over for them
with each slice too large for its positions cut into its chunks; the cut slices have the same
bytes and end below `USize.size`. -/
theorem handed_eq_handed_cutAll (version : Spec.Lexicon.Version)
    (slices : List Spec.Lexicon.Chars) :
    Adapter.handed Adapter.Lexer.ops version slices =
        Adapter.handed Adapter.Lexer.ops version (Chunks.cutAll slices) ∧
      (Chunks.cutAll slices).flatten = slices.flatten ∧
      ∀ s ∈ Chunks.cutAll slices, s.length < USize.size :=
  ⟨Chunks.handed_cutAll version slices, Chunks.flatten_cutAll slices,
    fun _ h => Chunks.mem_cutAll h⟩

end BSmtLib.Proofs.Lexer
