module

public import BSmtLib.Facts.Proofs.PublicApi.CollectE
public import BSmtLib.Facts.Proofs.PublicApi.VCollector
public import BSmtLib.Facts.Proofs.Lexer.Consumers.ChainZE
public import BSmtLib.Facts.Proofs.Lexer.Consumers.VFlattenE
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Error
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# The library's lexer with the collector does not tell how its input is cut into slices

The collector's run (`collect`) ends as the naive lexer with the concrete collector, fed the cut
of the slices, ends (`collect_naive`): with the same result, or with an error of the same lexical
kind and span, that does not go on. The proof chains four links:
- the collector's link (`CollectE`);
- the library's lexer against the lexer with the batch in its state (`ChainZE`);
- that lexer against the Rust port (`RunE.runInputE_alike`);
- the Rust port against the naive lexer (`Calls.wv_sliceP`), which agree on an error exactly
  where the naive lexer's is lexical, as with the concrete collector it always is
  (`VCollector`).

The naive lexer does not tell how its input is cut (`VFlattenE`), so neither does the collector's
run (`slicing`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.Slicing

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Facts.PublicApi.Adapters
open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Facts.Proofs.PublicApi.Collector BSmtLib.Facts.Proofs.PublicApi.CollectE
open BSmtLib.Facts.Proofs.PublicApi.VCollector
open BSmtLib.Facts.Proofs.Lexer.Consumers.RunE
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer

abbrev ZOps := BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps
abbrev XOps := BSmtLib.Facts.Lexer.Adapters.X1BatchInCore.lexOps
abbrev WOps := BSmtLib.Facts.Lexer.Adapters.WRustPort.lexOps
abbrev VOps := BSmtLib.Facts.Lexer.Adapters.VNaive.lexOps

/-- A result of the collector's run against one of the naive lexer with the concrete collector:
the same result, or errors of the same lexical kind and span, the first not going on. -/
def Matches : Except (LexerError Empty) (Option (Span.Located Unit)) →
    Except (LexerError (Option concreteCollector.Error))
      (Option (Span.Located concreteCollector.Result)) → Prop
  | .ok o, .ok o' => o = o'
  | .error e, .error e' => (∃ kind, e.cause = .lexical kind ∧ e'.cause = .lexical kind) ∧
      e.span = e'.span ∧ e.continuesFrom = none
  | _, _ => False

/-- Two results of the collector's run that match the same one of the naive lexer are the
same. -/
theorem matches_unique {c₁ c₂ : Except (LexerError Empty) (Option (Span.Located Unit))}
    {r : Except (LexerError (Option concreteCollector.Error))
      (Option (Span.Located concreteCollector.Result))}
    (h₁ : Matches c₁ r) (h₂ : Matches c₂ r) : c₁ = c₂ := by
  match c₁, c₂, r, h₁, h₂ with
  | .ok o₁, .ok o₂, .ok o, h₁, h₂ => simp only [Matches] at h₁ h₂; rw [h₁, h₂]
  | .error e₁, .error e₂, .error e, ⟨⟨k₁, a₁, b₁⟩, s₁, n₁⟩, ⟨⟨k₂, a₂, b₂⟩, s₂, n₂⟩ =>
    rw [b₁] at b₂
    cases b₂
    obtain ⟨c₁, sp₁, cf₁⟩ := e₁
    obtain ⟨c₂, sp₂, cf₂⟩ := e₂
    simp only at a₁ a₂ s₁ s₂ n₁ n₂
    subst a₁ a₂ s₁ n₁ n₂
    rw [s₂]

theorem oRel_eq {o : Option (Span.Located Unit)} {o' : Option (Span.Located Unit)}
    (h : ORel (LocRel link.rr) o o') : o = o' := by
  match o, o', h with
  | none, none, _ => rfl
  | some a, some b, h =>
    obtain ⟨-, h⟩ := h
    obtain ⟨⟨⟩, l⟩ := a
    obtain ⟨⟨⟩, l'⟩ := b
    simp only at h
    rw [h]

/-- The precise failures of an error of the Rust port and of a lexical one of the naive lexer
other than trailing input agree only if the two have the same cause and span. -/
theorem precise_lexical {ε : Type} {w v : LexerError (Option ε)}
    (h : preciseOf w = preciseOf v) (hv : IsLexicalNT v) :
    w.cause = v.cause ∧ w.span = v.span := by
  obtain ⟨k, hk, hnt⟩ := hv
  have hk' : (k == .unexpectedTrailingToken) = false := by
    cases k <;> first | rfl | exact absurd rfl hnt
  have h2 := congrArg Prod.snd h
  simp only [preciseOf, preciseFailure, lexicalKey, hk, hk', Bool.false_eq_true,
    ↓reduceIte] at h2
  revert h2
  generalize w.cause = cw
  cases cw with
  | lexical kw =>
    by_cases ht : (kw == .unexpectedTrailingToken) = true
    · simp only [ht, ↓reduceIte]; nofun
    · simp only [ht, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
      rintro ⟨rfl, hs⟩
      exact ⟨hk.symm, hs⟩
  | consumer _ => nofun

/-- The collector's run ends as the naive lexer with the concrete collector, fed the cut of the
slices, ends, and writes down the entries it takes. -/
theorem collect_naive (version : Version) (slices : List ByteList) :
    (collect version slices).2 = ((runInputE VOps (VOps.new concreteCollector {} version) true
        (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).2.map entryOf ∧
      Matches (collect version slices).1 ((runInputE VOps (VOps.new concreteCollector {} version)
        true (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).1.1 := by
  -- the collector and the library's lexer with the concrete collector
  have hC := collect_runInputE slices (BSmtLib.Lexer.new Collector.mk version)
    (ZOps.new concreteCollector {} version) [] (rfl) trivial
  simp only [List.map_nil] at hC
  -- the library's lexer and the lexer with the batch in its state, fed the cut
  obtain ⟨z1, z2, -, -⟩ := BSmtLib.Facts.Proofs.Lexer.Consumers.ChainZE.runInput_cutE true slices
    (ZOps.new concreteCollector {} version) (XOps.new concreteCollector {} version) []
    (X1BatchInCoreLexer.Handed.lexerRel_new _ _)
  -- the Rust port and the lexer with the batch in its state
  obtain ⟨x1, x2, -⟩ := runInputE_alike WOps XOps WRustPortX1BatchInCore.Calls.LexRel
    (fun slice => BSmtLib.Facts.Proofs.Lexer.Consumers.ChainX1.slice_alike concreteCollector
      slice.toByteArray.toByteSlice)
    (BSmtLib.Facts.Proofs.Lexer.Consumers.ChainX1.eof_alike concreteCollector)
    (fun _ _ h => h.2.2) (fun _ _ _ h => ⟨h.1, h.2.1, rfl⟩) true
    (X1BatchInCoreLexer.Chunks.cutAll slices)
    (WOps.new concreteCollector {} version) (XOps.new concreteCollector {} version) []
    (WRustPortX1BatchInCore.Handed.new_rel _ _)
  -- the Rust port and the naive lexer
  obtain ⟨v1, v2, -, -⟩ := runInputE_alikeG WOps VOps
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.WVRel concreteCollector)
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.WVWeak concreteCollector) preciseOf
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wv_sliceP concreteCollector)
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wv_eofP concreteCollector)
    (fun _ _ h => h.1) (fun _ _ _ h => ⟨rfl, h.2⟩)
    (fun _ _ h => ⟨h.2.version, BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.cr_weak h.2⟩)
    true (X1BatchInCoreLexer.Chunks.cutAll slices)
    (WOps.new concreteCollector {} version) (VOps.new concreteCollector {} version) []
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wvRel_new _ _)
  -- the Rust port's errors do not go on
  have hW := runInputE_error_inv WOps
    (fun a => ∃ b, BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.WVRel concreteCollector a b)
    (fun e => e.continuesFrom = none)
    (fun slice a taken ⟨b, hab⟩ =>
      ⟨fun held hok held' =>
        ⟨VOps.withHeld ((VOps.lexSliceStep b slice.toByteArray.toByteSlice).run taken).1.2 held',
          rfl, ((BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wv_sliceP concreteCollector
            slice a b taken hab).2.2.1 (by rw [hok]; rfl)).2⟩,
        fun e he => BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wv_slice_none concreteCollector
          slice a b taken hab e he⟩)
    (fun a taken ⟨b, hab⟩ e he =>
      BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wv_eof_none concreteCollector a b taken
        hab e he)
    true (X1BatchInCoreLexer.Chunks.cutAll slices) (WOps.new concreteCollector {} version) []
    ⟨_, BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wvRel_new _ version⟩
  -- the naive lexer's errors are lexical
  have hV := runInputE_lexical true (X1BatchInCoreLexer.Chunks.cutAll slices)
    (VOps.new concreteCollector {} version) [] ⟨rfl, .idle, rfl⟩
  have hcoll : collect version slices =
      (resultOf ((collectWith (BSmtLib.Lexer.new Collector.mk version) slices).run []).1,
        ((collectWith (BSmtLib.Lexer.new Collector.mk version) slices).run []).2) := by
    rfl
  rw [hcoll]
  obtain ⟨hC1, hC2⟩ := hC
  rw [z1, ← x1] at hC2
  rw [z2, ← x2, v2] at hC1
  refine ⟨hC1, ?_⟩
  generalize ((runInputE WOps (WOps.new concreteCollector {} version) true
    (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).1.1 = w at hC2 v1 hW
  generalize ((runInputE VOps (VOps.new concreteCollector {} version) true
    (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).1.1 = v at v1 hV ⊢
  generalize resultOf ((collectWith (BSmtLib.Lexer.new Collector.mk version) slices).run []).1 = c
    at hC2 ⊢
  rcases c with ec | o <;> rcases w with ew | o' <;> rcases v with ev | o''
  · obtain ⟨hcause, hspan, hcont⟩ := hC2
    have v1' : preciseOf ew = preciseOf ev := by
      simpa only [Except.mapError, Except.error.injEq] using v1
    have hv := hV ev rfl
    obtain ⟨e1, e2⟩ := precise_lexical v1' hv
    obtain ⟨k, hk, -⟩ := hv
    rw [e1, hk] at hcause
    refine ⟨⟨k, ?_, hk⟩, hspan.trans e2, hcont.trans (hW ew rfl)⟩
    generalize ec.cause = cc at hcause
    cases cc with
    | lexical k' => cases hcause; rfl
    | consumer x => exact x.elim
  · cases v1
  · exact hC2.elim
  · exact hC2.elim
  · exact hC2.elim
  · exact hC2.elim
  · cases v1
  · have v1' : o' = o'' := by simpa only [Except.mapError, Except.ok.injEq] using v1
    subst v1'
    exact oRel_eq hC2

/-- The collector's run does not tell how its input is cut into slices. -/
theorem slicing (version : Version) (slices : List ByteList) :
    collect version slices = collect version [slices.flatten] := by
  obtain ⟨a1, a2⟩ := collect_naive version slices
  obtain ⟨b1, b2⟩ := collect_naive version [slices.flatten]
  have hS := BSmtLib.Facts.Proofs.Lexer.Consumers.VFlattenE.runInputE_flatten concreteCollector
    true (X1BatchInCoreLexer.Chunks.cutAll slices) (Lexer.Internal.VNaive.Core.initial version) none
    [] trivial
  have hF := BSmtLib.Facts.Proofs.Lexer.Consumers.VFlattenE.runInputE_flatten concreteCollector
    true (X1BatchInCoreLexer.Chunks.cutAll [slices.flatten])
    (Lexer.Internal.VNaive.Core.initial version) none [] trivial
  rw [X1BatchInCoreLexer.Chunks.flatten_cutAll] at hS hF
  rw [List.flatten_singleton] at hF
  obtain ⟨s1, s2, -, -⟩ := hS
  obtain ⟨f1, f2, -, -⟩ := hF
  have e1 : ((runInputE VOps (VOps.new concreteCollector {} version) true
      (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).1.1 =
      ((runInputE VOps (VOps.new concreteCollector {} version) true
        (X1BatchInCoreLexer.Chunks.cutAll [slices.flatten])).run []).1.1 := s1.trans f1.symm
  have e2 : ((runInputE VOps (VOps.new concreteCollector {} version) true
      (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).2 =
      ((runInputE VOps (VOps.new concreteCollector {} version) true
        (X1BatchInCoreLexer.Chunks.cutAll [slices.flatten])).run []).2 := s2.trans f2.symm
  rw [e1] at a2
  rw [e2] at a1
  exact Prod.ext (matches_unique a2 b2) (a1.trans b1.symm)

end BSmtLib.Facts.Proofs.PublicApi.Slicing
