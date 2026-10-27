module

public import BSmtLib.Facts.Proofs.PublicApi.Slicing
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Error
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# The library's lexer with any consumer of the formalism does not tell how its input is cut

`z_naive`: the run of the library's lexer with the adapter's consumer for a consumer of the
specification formalism (`BSmtLibSpec`) ends as the naive lexer fed the cut of the slices ends:
- the two take the same tokens, and their results are alike as `preciseOf` says;
- an error of the library's lexer does not go on, and a consumer's error has the span of the last
  token taken;
- where the library's lexer does not fail, it discards from where the naive lexer does.

The naive lexer does not tell how its input is cut (`VFlattenE`), so neither does the library's
lexer (`slicing`): it takes the same tokens and gives results alike as `preciseOf` says, so the
same result, and the same error but for trailing input and the adapter's error `none`.
-/

namespace BSmtLib.Facts.Proofs.PublicApi.SlicingC

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Lexer.Consumers.RunE
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer
open BSmtLib.Facts.Proofs.PublicApi.Slicing (ZOps XOps WOps VOps)
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls (WVRel WVWeak)

section

variable (C : BSmtLibSpec.Lexer.Consumer)

/-- What an error of the Rust port's run keeps, with the tokens taken: a consumer's error has the
span of the last token taken, and the adapter's error `none` comes only with a consumer that
takes whitespace and comments. -/
def WErr (e : LexerError (Option C.Error)) (t : List Handed) : Prop :=
  (∀ x, e.kind = .consumer (some x) → e.span = VNaiveWRustPort.Cursor.handedSpan t) ∧
    (C.concrete = false → e.kind ≠ .consumer none)

theorem w_run_err (ended : Bool) : ∀ (slices : List BSmtLibSpec.Regex.Chars)
    (a : WOps.Lexer C) (taken : List Handed) (b : VOps.Lexer C), WVRel C a b →
    ∀ e, ((runInputE WOps a ended slices).run taken).1.1 = .error e →
      WErr C e ((runInputE WOps a ended slices).run taken).2
  | [], a, taken, b, h, e, he => by
    cases ended with
    | false => rw [runInputE_nil_false] at he; cases he
    | true =>
      rw [runInputE_nil_true] at he ⊢
      have hs := VNaiveWRustPort.Calls.wv_eof_span C a b taken h
      generalize (WOps.lexEofStep a).run taken = r at hs he ⊢
      obtain ⟨⟨r, l⟩, t⟩ := r
      cases r with
      | ok _ => cases he
      | error e' => cases he; exact ⟨hs.1 e rfl, fun hc => hs.2 hc e rfl⟩
  | slice :: slices, a, taken, b, h, e, he => by
    rw [runInputE_cons] at he ⊢
    have hs := VNaiveWRustPort.Calls.wv_slice_span C slice a b taken h
    have hp := VNaiveWRustPort.Calls.wv_sliceP C slice a b taken h
    generalize (WOps.lexSliceStep a slice.toByteArray.toByteSlice).run taken = r at hs hp he ⊢
    obtain ⟨⟨r, l⟩, t⟩ := r
    cases r with
    | ok held =>
      have hrel := (hp.2.2.1 rfl)
      dsimp only at he ⊢
      exact w_run_err ended slices (WOps.withHeld l (held.or (WOps.held l))) t
        (VOps.withHeld ((VOps.lexSliceStep b slice.toByteArray.toByteSlice).run taken).1.2
          (held.or (WOps.held l))) ⟨rfl, hrel.2⟩ e he
    | error e' => cases he; exact ⟨hs.1 e rfl, fun hc => hs.2 hc e rfl⟩

/-- The library's lexer with the adapter's consumer for `C` ends as the naive lexer fed the cut of
the slices ends: the same tokens taken, results alike as `preciseOf` says, an error that does not
go on and keeps `WErr`, and where it does not fail, discarding from where the naive lexer does. -/
theorem z_naive (version : Version) (ended : Bool) (slices : List BSmtLibSpec.Regex.Chars) :
    ((runInputE ZOps (ZOps.new C {} version) ended slices).run []).2 =
        ((runInputE VOps (VOps.new C {} version) ended
          (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).2 ∧
      ((runInputE ZOps (ZOps.new C {} version) ended slices).run []).1.1.mapError preciseOf =
        ((runInputE VOps (VOps.new C {} version) ended
          (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).1.1.mapError preciseOf ∧
      (∀ e, ((runInputE ZOps (ZOps.new C {} version) ended slices).run []).1.1 = .error e →
        e.continuesFrom = none ∧
          WErr C e ((runInputE ZOps (ZOps.new C {} version) ended slices).run []).2) ∧
      (((runInputE ZOps (ZOps.new C {} version) ended slices).run []).1.1.isOk = true →
        (Internal.core ((runInputE ZOps (ZOps.new C {} version) ended slices).run []).1.2
          ).discardedFrom =
          Lexer.Consumers.VSession.discardedOf ((runInputE VOps (VOps.new C {} version) ended
            (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).1.2.core) := by
  -- the library's lexer and the lexer with the batch in its state, fed the cut
  obtain ⟨z1, z2, -, z4⟩ := Lexer.Consumers.ChainZE.runInput_cutE ended slices
    (ZOps.new C {} version) (XOps.new C {} version) []
    (X1BatchInCoreLexer.Handed.lexerRel_new _ _)
  -- the Rust port and the lexer with the batch in its state
  obtain ⟨x1, x2, x3⟩ := runInputE_alike WOps XOps WRustPortX1BatchInCore.Calls.LexRel
    (fun slice => Lexer.Consumers.ChainX1.slice_alike C slice.toByteArray.toByteSlice)
    (Lexer.Consumers.ChainX1.eof_alike C)
    (fun _ _ h => h.2.2) (fun _ _ _ h => ⟨h.1, h.2.1, rfl⟩) ended
    (X1BatchInCoreLexer.Chunks.cutAll slices)
    (WOps.new C {} version) (XOps.new C {} version) []
    (WRustPortX1BatchInCore.Handed.new_rel _ _)
  -- the Rust port and the naive lexer
  obtain ⟨v1, v2, -, v4⟩ := runInputE_alikeG WOps VOps (WVRel C) (WVWeak C) preciseOf
    (VNaiveWRustPort.Calls.wv_sliceP C) (VNaiveWRustPort.Calls.wv_eofP C)
    (fun _ _ h => h.1) (fun _ _ _ h => ⟨rfl, h.2⟩)
    (fun _ _ h => ⟨h.2.version, VNaiveWRustPort.Calls.cr_weak h.2⟩)
    ended (X1BatchInCoreLexer.Chunks.cutAll slices)
    (WOps.new C {} version) (VOps.new C {} version) []
    (VNaiveWRustPort.Calls.wvRel_new _ _)
  -- the Rust port's errors do not go on
  have hW := runInputE_error_inv WOps (fun a => ∃ b, WVRel C a b)
    (fun e => e.continuesFrom = none)
    (fun slice a taken ⟨b, hab⟩ =>
      ⟨fun held hok held' =>
        ⟨VOps.withHeld ((VOps.lexSliceStep b slice.toByteArray.toByteSlice).run taken).1.2 held',
          rfl, ((VNaiveWRustPort.Calls.wv_sliceP C slice a b taken hab).2.2.1
            (by rw [hok]; rfl)).2⟩,
        fun e he => VNaiveWRustPort.Calls.wv_slice_none C slice a b taken hab e he⟩)
    (fun a taken ⟨b, hab⟩ e he => VNaiveWRustPort.Calls.wv_eof_none C a b taken hab e he)
    ended (X1BatchInCoreLexer.Chunks.cutAll slices) (WOps.new C {} version) []
    ⟨_, VNaiveWRustPort.Calls.wvRel_new _ version⟩
  have hS := w_run_err C ended (X1BatchInCoreLexer.Chunks.cutAll slices) (WOps.new C {} version) []
    _ (VNaiveWRustPort.Calls.wvRel_new C version)
  refine ⟨z2.trans (x2.symm.trans v2), by rw [z1, ← x1]; exact v1, fun e he => ?_, fun hok => ?_⟩
  · rw [z1, ← x1] at he
    rw [z2, ← x2]
    exact ⟨hW e he, hS e he⟩
  · have hl := z4 hok
    have hok' : ((runInputE WOps (WOps.new C {} version) ended
        (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).1.1.isOk = true := by
      rw [x1, ← z1]; exact hok
    have e₁ := congrArg (fun x => x.discardedFrom) (hl.2.1 : X1BatchInCoreLexer.Outer.zb _ = _)
    have e₂ := x3.2.1.1.discardedFrom
    have e₃ := v4.2
    exact e₁.symm.trans (e₂.symm.trans e₃)

/-- Two errors alike as `preciseOf` says, neither going on, with the same spans for consumer's
errors, and neither trailing input nor the adapter's error `none`, are the same. -/
theorem error_eq {e₁ e₂ : LexerError (Option C.Error)} (h : preciseOf e₁ = preciseOf e₂)
    (hc₁ : e₁.continuesFrom = none) (hc₂ : e₂.continuesFrom = none)
    (hs : ∀ x, e₁.kind = .consumer (some x) → e₂.kind = .consumer (some x) → e₁.span = e₂.span)
    (hn₁ : e₁.kind ≠ .consumer none) (hn₂ : e₂.kind ≠ .consumer none)
    (ht : e₁.kind ≠ .lexical .unexpectedTrailingToken) : e₁ = e₂ := by
  obtain ⟨c₁, s₁, f₁⟩ := e₁
  obtain ⟨c₂, s₂, f₂⟩ := e₂
  simp only at hc₁ hc₂ hs hn₁ hn₂ ht
  subst hc₁ hc₂
  rcases c₁ with k | (_ | x)
  · have hv : VCollector.IsLexicalNT (⟨.lexical k, s₁, none⟩ : LexerError (Option C.Error)) :=
      ⟨k, rfl, fun hk => ht (by rw [hk])⟩
    obtain ⟨hc, hsp⟩ := Slicing.precise_lexical h.symm hv
    simp only at hc hsp
    rw [hc, hsp]
  · exact absurd rfl hn₁
  · have h1 := congrArg Prod.fst h
    simp only [preciseOf, preciseFailure, causeFailure, failureOf,
      Lexer.Error.LexerError.Internal.kind_new] at h1
    rcases c₂ with k | (_ | y)
    · simp only at h1
      split at h1 <;> cases h1
    · exact absurd rfl hn₂
    · simp only [BSmtLibSpec.Lexer.Failure.consumer.injEq] at h1
      subst h1
      rw [hs x rfl rfl]

/-- The library's lexer with the adapter's consumer for a consumer of the formalism that does not
take whitespace and comments takes the same tokens however its input is cut into slices, and gives
the same result, or the same error where neither is trailing input; where both do not fail, they
discard from the same location. -/
theorem slicing (hc : C.concrete = false) (version : Version) (ended : Bool)
    (slices : List BSmtLibSpec.Regex.Chars) :
    ((runInputE ZOps (ZOps.new C {} version) ended slices).run []).2 =
        ((runInputE ZOps (ZOps.new C {} version) ended [slices.flatten]).run []).2 ∧
      ((∀ e, ((runInputE ZOps (ZOps.new C {} version) ended slices).run []).1.1 = .error e →
          e.kind ≠ .lexical .unexpectedTrailingToken) →
        ((runInputE ZOps (ZOps.new C {} version) ended slices).run []).1.1 =
          ((runInputE ZOps (ZOps.new C {} version) ended [slices.flatten]).run []).1.1) ∧
      (((runInputE ZOps (ZOps.new C {} version) ended slices).run []).1.1.isOk = true →
        ((runInputE ZOps (ZOps.new C {} version) ended [slices.flatten]).run []).1.1.isOk =
          true →
        (Internal.core ((runInputE ZOps (ZOps.new C {} version) ended slices).run []).1.2
          ).discardedFrom =
        (Internal.core ((runInputE ZOps (ZOps.new C {} version) ended [slices.flatten]).run
          []).1.2).discardedFrom) := by
  obtain ⟨a1, a2, a3, a4⟩ := z_naive C version ended slices
  obtain ⟨b1, b2, b3, b4⟩ := z_naive C version ended [slices.flatten]
  have hS := Lexer.Consumers.VFlattenE.runInputE_flatten C ended
    (X1BatchInCoreLexer.Chunks.cutAll slices) (Lexer.Internal.VNaive.Core.initial version) none
    [] trivial
  have hF := Lexer.Consumers.VFlattenE.runInputE_flatten C ended
    (X1BatchInCoreLexer.Chunks.cutAll [slices.flatten])
    (Lexer.Internal.VNaive.Core.initial version) none [] trivial
  rw [X1BatchInCoreLexer.Chunks.flatten_cutAll] at hS hF
  rw [List.flatten_singleton] at hF
  obtain ⟨s1, s2, s3, -⟩ := hS
  obtain ⟨f1, f2, f3, -⟩ := hF
  have hv1 : ((runInputE VOps (VOps.new C {} version) ended
      (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).1.1 =
      ((runInputE VOps (VOps.new C {} version) ended
        (X1BatchInCoreLexer.Chunks.cutAll [slices.flatten])).run []).1.1 := s1.trans f1.symm
  have hv2 : ((runInputE VOps (VOps.new C {} version) ended
      (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).2 =
      ((runInputE VOps (VOps.new C {} version) ended
        (X1BatchInCoreLexer.Chunks.cutAll [slices.flatten])).run []).2 := s2.trans f2.symm
  have hv3 : ((runInputE VOps (VOps.new C {} version) ended
      (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).1.2.core =
      ((runInputE VOps (VOps.new C {} version) ended
        (X1BatchInCoreLexer.Chunks.cutAll [slices.flatten])).run []).1.2.core := s3.trans f3.symm
  have ht : ((runInputE ZOps (ZOps.new C {} version) ended slices).run []).2 =
      ((runInputE ZOps (ZOps.new C {} version) ended [slices.flatten]).run []).2 :=
    a1.trans (hv2.trans b1.symm)
  refine ⟨ht, fun hnt => ?_, fun hok₁ hok₂ => ?_⟩
  · rw [hv1] at a2
    have hp := a2.trans b2.symm
    generalize hA : ((runInputE ZOps (ZOps.new C {} version) ended slices).run []).1.1 = A
      at hp hnt a3
    generalize hB : ((runInputE ZOps (ZOps.new C {} version) ended [slices.flatten]).run []).1.1 = B
      at hp b3
    rcases A with e₁ | o₁ <;> rcases B with e₂ | o₂ <;>
      simp only [Except.mapError, Except.error.injEq, Except.ok.injEq, reduceCtorEq] at hp
    · obtain ⟨c₁, w₁⟩ := a3 e₁ rfl
      obtain ⟨c₂, w₂⟩ := b3 e₂ rfl
      rw [error_eq C hp c₁ c₂ (fun x h₁ h₂ => (w₁.1 x h₁).trans (ht ▸ (w₂.1 x h₂).symm))
        (w₁.2 hc) (w₂.2 hc) (hnt e₁ rfl)]
    · rw [hp]
  · rw [a4 hok₁, b4 hok₂, hv3]

end

end BSmtLib.Facts.Proofs.PublicApi.SlicingC
