module

public import BSmtLib.Facts.Proofs.PublicApi.Slicing
public import BSmtLib.Facts.Proofs.PublicApi.Tiling
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Error
import all BSmtLib.Span

@[expose] public section

/-!
# The library's lexer with the collector loses no byte

The collector writes down the lexemes of the naive lexer's pure run over the input joined
(`Lexing.collect_stream`), which with whitespace and comments tile the input (`Tiling`). Where the
collector's run fails, it fails as the naive lexer with the concrete collector fed the input as
one slice does (`Slicing.collect_naive`, `VFlattenE`), with the span of the pure run's failure
(`VCollector`), which starts no earlier than where the lexemes reach (`lossless`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.Lossless

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Facts.PublicApi.Adapters
open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.PublicApi.Collector BSmtLib.Facts.Proofs.PublicApi.Lexing
open BSmtLib.Facts.Proofs.PublicApi.Slicing BSmtLib.Facts.Proofs.PublicApi.Tiling
open BSmtLib.Facts.Proofs.PublicApi.VCollector
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.Consumers.Stream
open BSmtLib.Facts.Proofs.Lexer.Consumers.RunE BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps
open BSmtLib.Facts.Proofs.Lexer.Consumers.VEnd BSmtLib.Facts.Proofs.Lexer.Consumers.VSession
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel
open BSmtLib.Lexer.Internal.VNaive
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer

/-- The naive lexer with the concrete collector, fed the bytes as one slice and then the end of
the input, fails with the span of the pure run's failure: at a byte, or where finishing the token
in progress at the end fails. -/
theorem single_error (version : Version) (bs : List UInt8)
    (e : LexerError (Option concreteCollector.Error))
    (he : ((runInputE VOps (VOps.new concreteCollector {} version) true [bs]).run []).1.1 =
      .error e) :
    match lexBytesF version true .idle Span.Location.initial bs with
    | .error (_, f) => e.span = f.span
    | .ok (st', location', _) =>
      finishLs true st' location' = none ∧ e.span = (finishFail true st' location').span := by
  have hx := vBytes_cc_exact (Core.initial version) .idle rfl rfl bs []
  rw [show (Core.initial version).version = version from rfl,
    show (Core.initial version).location = Span.Location.initial from rfl] at hx
  have hp : (Core.Plain (Core.initial version)) := trivial
  rw [runInputE_cons] at he
  rw [show VOps.new concreteCollector {} version = ⟨{}, Core.initial version, none⟩ from rfl,
    BSmtLib.Facts.Proofs.Lexer.Consumers.VFlatten.lexSliceStep_ops concreteCollector
      (Core.initial version) hp none bs []] at he
  generalize vBytes concreteCollector (Core.initial version) none bs [] = R at hx he
  obtain ⟨⟨res, core'⟩, taken'⟩ := R
  dsimp only at hx
  generalize lexBytesF version true .idle Span.Location.initial bs = L at hx ⊢
  cases L with
  | error x =>
    obtain ⟨ls, f⟩ := x
    dsimp only at hx ⊢
    subst hx
    dsimp only at he
    cases he
    rfl
  | ok x =>
    obtain ⟨st', loc', ls⟩ := x
    obtain ⟨rfl, h2, h3, h4, -⟩ := hx
    dsimp only at he ⊢
    rw [runInputE_nil_true] at he
    simp only [BSmtLib.Facts.Proofs.Lexer.Consumers.VFlatten.withHeld_v,
      BSmtLib.Facts.Proofs.Lexer.Consumers.VFlatten.held_v, Option.or_self] at he
    rw [lexOps_lexEofStep] at he
    have hc := vEnd_cc_span core' st' h3 h2 taken'
    generalize vEnd concreteCollector core' taken' = R at hc he
    obtain ⟨⟨r, c''⟩, t''⟩ := R
    dsimp only at he
    cases r with
    | ok _ => cases he
    | error e' =>
      cases he
      have := hc e rfl
      rw [h4] at this
      exact this

/-- The collector's run on slices hands over entries that tile the input, ending at its end; or,
where it fails, entries that tile it from its start up to at most where the error starts. -/
theorem lossless (version : Version) (slices : List ByteList) :
    match collect version slices with
    | (.ok _, entries) => Tiles entries 0 slices.flatten.length
    | (.error error, entries) => ∃ stop, Tiles entries 0 stop ∧ stop ≤ error.span.start.offset := by
  obtain ⟨hs1, hs2⟩ := collect_stream version slices
  have hm := (collect_naive version slices).2
  have hF := BSmtLib.Facts.Proofs.Lexer.Consumers.VFlattenE.runInputE_flatten concreteCollector
    true (X1BatchInCoreLexer.Chunks.cutAll slices) (Core.initial version) none [] trivial
  rw [X1BatchInCoreLexer.Chunks.flatten_cutAll] at hF
  rw [show (⟨{}, Core.initial version, none⟩ : VOps.Lexer concreteCollector) =
    VOps.new concreteCollector {} version from rfl] at hF
  rw [hF.1] at hm
  rw [stream_zero] at hs1 hs2
  have hT := lexBytesF_tiles version slices.flatten .idle Span.Location.initial
  have hplain := plain_lexBytesF version true slices.flatten .idle Span.Location.initial
  generalize hc : collect version slices = C at hs1 hs2 hm
  obtain ⟨res, entries⟩ := C
  dsimp only at hs1 hs2 hm ⊢
  subst hs1
  unfold streamFrom at hs2 ⊢
  rw [← hplain] at hs2 ⊢
  generalize hR : lexBytesF version true .idle Span.Location.initial slices.flatten = R at hT hs2 ⊢
  rcases R with ⟨ls, f⟩ | ⟨st', loc', ls⟩
  · -- the pure run fails at a byte
    dsimp only [RunF.plain, Except.mapError] at hs2 ⊢
    cases res with
    | ok _ => cases hs2
    | error err =>
      generalize hv : ((runInputE VOps (VOps.new concreteCollector {} version) true
        [slices.flatten]).run []).1.1 = v at hm
      cases v with
      | ok _ => exact hm.elim
      | error ev =>
        obtain ⟨-, hsp, -⟩ := hm
        have := single_error version slices.flatten ev hv
        rw [hR] at this
        obtain ⟨X, h1, h2⟩ := hT
        exact ⟨X, h1, by rw [hsp, this]; exact h2⟩
  · obtain ⟨hT, hloc⟩ := hT
    dsimp only [RunF.plain, Except.mapError] at hs2 ⊢
    simp only [ite_true] at hs2 ⊢
    cases hE : endStepW true st' loc' with
    | some ls' =>
      rw [hE] at hs2
      dsimp only at hs2 ⊢
      cases res with
      | error _ => cases hs2
      | ok _ =>
        dsimp only
        rw [List.map_append]
        have h2 := endStep_tiles hE
        have hlen : loc'.offset = slices.flatten.length := by
          rw [hloc, advanceLoc_offset]; exact Nat.zero_add _
        rw [← hlen]
        exact tiles_trans hT h2
    | none =>
      rw [hE] at hs2
      dsimp only at hs2 ⊢
      cases res with
      | ok _ => cases hs2
      | error err =>
        generalize hv : ((runInputE VOps (VOps.new concreteCollector {} version) true
          [slices.flatten]).run []).1.1 = v at hm
        cases v with
        | ok _ => exact hm.elim
        | error ev =>
          obtain ⟨-, hsp, -⟩ := hm
          have := single_error version slices.flatten ev hv
          rw [hR] at this
          obtain ⟨-, hs⟩ := this
          refine ⟨front st' loc', hT, ?_⟩
          rw [hsp, hs]
          cases st' with
          | idle => simp [endStepW] at hE
          | token p =>
            simp only [endStepW] at hE
            cases hf : finish true p loc' with
            | error f' =>
              simp only [finishFail, hf, front]
              exact Nat.le_of_eq (finish_error_start hf).symm
            | none => rw [hf] at hE; cases hE
            | token _ => rw [hf] at hE; cases hE

end BSmtLib.Facts.Proofs.PublicApi.Lossless
