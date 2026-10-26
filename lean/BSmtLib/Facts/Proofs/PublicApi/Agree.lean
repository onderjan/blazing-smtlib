module

public import BSmtLib.Facts.Proofs.PublicApi.WCollectE
public import BSmtLib.Facts.Proofs.PublicApi.Slicing
public import BSmtLib.Facts.Proofs.PublicApi.Resets
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# The lexers with the collector agree

`Facts.lexers_agree`: the runs of the lexers with the collector agree. The proof rests on three
facts:
- the lexer with the batch in its state with the collector runs as the Rust port does
  (`collectX1_collectW`), as the two lexers' calls correspond (`Api.lexSlice_couple`);
- the naive lexer and the Rust port, each with the collector, end as the naive lexer with the
  concrete collector ends when fed the same slices (`collectV_naive`, `collectW_naive`): with the
  same result, or with an error of the same lexical kind, writing down the entries it takes;
- the naive lexer does not tell how its input is cut (`VFlattenE`), and the collector's run ends
  as it does on the cut of the slices (`Slicing.collect_naive`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.Agree

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Facts.PublicApi.Adapters BSmtLib.Facts.PublicApi.Adapters.Chain
open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Facts.Proofs.PublicApi.Collector
open BSmtLib.Facts.Proofs.Lexer.Consumers.RunE
open BSmtLib.Facts.Proofs.Lexer.Simulation.Couple (MCouple)
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Api (ResRel EofRel AfterRel AfterEofRel)
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Calls (LexRel)
open BSmtLib.Facts.Proofs.PublicApi.Resets (collector_consumesAlike mcouple_collectM WLexer)
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer

/-! ## The lexer with the batch in its state runs as the Rust port -/

/-- The Rust port and the lexer with the batch in its state with the collector, from related
lexers, end alike fed the same slices and write down the same entries. -/
theorem collectBy_x1 (slices : List ByteList) : ∀ (l l' : WLexer), LexRel l l' →
    ∀ entries : List Entry,
    (collectBy (fun lexer slice => Lexer.Internal.WRustPort.Lexer.lexSlice lexer slice)
        (fun lexer => Lexer.Internal.WRustPort.Lexer.lexEof lexer) l slices).run entries =
      (collectBy (fun lexer slice => Lexer.Internal.X1BatchInCore.Lexer.lexSlice lexer slice)
        (fun lexer => Lexer.Internal.X1BatchInCore.Lexer.lexEof lexer) l' slices).run entries := by
  induction slices with
  | nil =>
    intro l l' h entries
    obtain ⟨h1, h2⟩ := mcouple_collectM
      (BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Api.lexEof_couple
        collector_consumesAlike l l' h) entries
    simp only [collectBy, StateT.run_bind]
    generalize (Lexer.Internal.WRustPort.Lexer.lexEof l).run entries = A at h1 h2 ⊢
    generalize (Lexer.Internal.X1BatchInCore.Lexer.lexEof l').run entries = B at h1 h2 ⊢
    obtain ⟨r, e⟩ := A
    obtain ⟨r', e'⟩ := B
    dsimp only at h1 h2
    subst h2
    rcases r with ⟨x, a⟩ | ⟨o, a⟩ <;> rcases r' with ⟨x', a'⟩ | ⟨o', a'⟩
    · obtain ⟨hx, -⟩ := h1
      subst hx
      rfl
    · exact h1.elim
    · exact h1.elim
    · obtain ⟨ho, -⟩ := h1
      dsimp only at ho
      subst ho
      rfl
  | cons slice slices ih =>
    intro l l' h entries
    obtain ⟨h1, h2⟩ := mcouple_collectM
      (BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Api.lexSlice_couple
        collector_consumesAlike l l' h slice.toByteArray.toByteSlice) entries
    simp only [collectBy, StateT.run_bind]
    generalize (Lexer.Internal.WRustPort.Lexer.lexSlice l
      slice.toByteArray.toByteSlice).run entries = A at h1 h2 ⊢
    generalize (Lexer.Internal.X1BatchInCore.Lexer.lexSlice l'
      slice.toByteArray.toByteSlice).run entries = B at h1 h2 ⊢
    obtain ⟨r, e⟩ := A
    obtain ⟨r', e'⟩ := B
    dsimp only at h1 h2
    subst h2
    rcases r with ⟨x, a⟩ | k <;> rcases r' with ⟨x', a'⟩ | k'
    · obtain ⟨hx, -⟩ := h1
      subst hx
      rfl
    · exact h1.elim
    · exact h1.elim
    · exact ih k k' h1 _

/-- The lexer with the batch in its state with the collector runs as the Rust port does. -/
theorem collectX1_collectW (version : Version) (slices : List ByteList) :
    collectX1 version slices = collectW version slices :=
  (collectBy_x1 slices _ _
    (BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Handed.new_rel Collector.mk version)
      []).symm

/-! ## The runs against the naive lexer with the concrete collector -/

abbrev VOps := BSmtLib.Facts.Lexer.Adapters.VNaive.lexOps
abbrev WOps := BSmtLib.Facts.Lexer.Adapters.WRustPort.lexOps

/-- A result of a run with the collector against one of the naive lexer with the concrete
collector: the same result, or errors of the same lexical kind. -/
def MatchesC : Except (LexerError Empty) (Option (Span.Located Unit)) →
    Except (LexerError (Option concreteCollector.Error))
      (Option (Span.Located concreteCollector.Result)) → Prop
  | .ok o, .ok o' => o = o'
  | .error e, .error e' => ∃ kind, e.cause = .lexical kind ∧ e'.cause = .lexical kind
  | _, _ => False

/-- Two runs with the collector that match the same one of the naive lexer and write down the
same entries are the same, but for where an error is. -/
theorem causeOnly_eq {c₁ c₂ : Except (LexerError Empty) (Option (Span.Located Unit)) × List Entry}
    {r : Except (LexerError (Option concreteCollector.Error))
      (Option (Span.Located concreteCollector.Result))}
    (h₁ : MatchesC c₁.1 r) (h₂ : MatchesC c₂.1 r) (he : c₁.2 = c₂.2) :
    causeOnly c₁ = causeOnly c₂ := by
  obtain ⟨r₁, e₁⟩ := c₁
  obtain ⟨r₂, e₂⟩ := c₂
  dsimp only at h₁ h₂ he
  subst he
  rcases r₁ with x₁ | o₁ <;> rcases r₂ with x₂ | o₂ <;> rcases r with x | o
  · obtain ⟨k₁, a₁, b₁⟩ := h₁
    obtain ⟨k₂, a₂, b₂⟩ := h₂
    rw [b₁] at b₂
    cases b₂
    simp only [causeOnly, a₁, a₂]
  all_goals first
    | exact h₁.elim
    | exact h₂.elim
    | (simp only [MatchesC] at h₁ h₂; subst h₁ h₂; rfl)

/-- An error that matches as `Slicing.Matches` says matches as `MatchesC` says. -/
theorem matchesC_of_matches {c : Except (LexerError Empty) (Option (Span.Located Unit))}
    {r : Except (LexerError (Option concreteCollector.Error))
      (Option (Span.Located concreteCollector.Result))}
    (h : Slicing.Matches c r) : MatchesC c r := by
  rcases c with x | o <;> rcases r with x' | o'
  · exact h.1
  · exact h.elim
  · exact h.elim
  · exact h

/-- A collector's error related to a lexical error of a lexer with the concrete collector has
its kind. -/
theorem cause_of_rel {e : LexerError Empty} {e' : LexerError (Option concreteCollector.Error)}
    {k : LexicalErrorKind} (h : CauseRel link.re e.cause e'.cause)
    (hk : e'.cause = .lexical k) : e.cause = .lexical k := by
  rw [hk] at h
  revert h
  generalize e.cause = c
  cases c with
  | lexical k' => intro h; cases h; rfl
  | consumer x => exact x.elim

/-- The naive lexer with the collector ends as the naive lexer with the concrete collector,
fed the same slices, ends, and writes down the entries it takes. -/
theorem collectV_naive (version : Version) (slices : List ByteList) :
    (collectV version slices).2 = ((runInputE VOps (VOps.new concreteCollector {} version) true
        slices).run []).2.map entryOf ∧
      MatchesC (collectV version slices).1 ((runInputE VOps (VOps.new concreteCollector {}
        version) true slices).run []).1.1 := by
  have hC := VCollectE.collectV_runInputE slices
    (Lexer.Internal.VNaive.Lexer.new Collector.mk version) (VOps.new concreteCollector {} version)
    [] rfl trivial
  have hV := VCollector.runInputE_lexical true slices (VOps.new concreteCollector {} version) []
    ⟨rfl, .idle, rfl⟩
  simp only [List.map_nil] at hC
  refine ⟨hC.1, ?_⟩
  obtain ⟨-, hC2⟩ := hC
  revert hC2 hV
  unfold collectV
  generalize ((runInputE VOps (VOps.new concreteCollector {} version) true slices).run []).1.1
    = v
  generalize ((collectBy (fun lexer slice => Lexer.Internal.VNaive.Lexer.lexSlice lexer slice)
    (fun lexer => Lexer.Internal.VNaive.Lexer.lexEof lexer)
    (Lexer.Internal.VNaive.Lexer.new Collector.mk version) slices).run []).1 = c
  intro hV hC2
  rcases c with ec | o <;> rcases v with ev | o'
  · obtain ⟨k, hk, -⟩ := hV ev rfl
    exact ⟨k, cause_of_rel hC2.1 hk, hk⟩
  · exact hC2.elim
  · exact hC2.elim
  · exact Slicing.oRel_eq hC2

/-- The Rust port with the collector ends as the naive lexer with the concrete collector, fed
the same slices, ends, and writes down the entries it takes. -/
theorem collectW_naive (version : Version) (slices : List ByteList) :
    (collectW version slices).2 = ((runInputE VOps (VOps.new concreteCollector {} version) true
        slices).run []).2.map entryOf ∧
      MatchesC (collectW version slices).1 ((runInputE VOps (VOps.new concreteCollector {}
        version) true slices).run []).1.1 := by
  -- the collector and the adapter's consumer
  have hC := WCollectE.collectW_runInputE slices
    (Lexer.Internal.WRustPort.Lexer.new Collector.mk version)
    (WOps.new concreteCollector {} version) [] rfl trivial
  -- the Rust port and the naive lexer
  obtain ⟨v1, v2, -, -⟩ := runInputE_alikeG WOps VOps
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.WVRel concreteCollector)
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.WVWeak concreteCollector)
    BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel.preciseOf
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wv_sliceP concreteCollector)
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wv_eofP concreteCollector)
    (fun _ _ h => h.1) (fun _ _ _ h => ⟨rfl, h.2⟩)
    (fun _ _ h => ⟨h.2.version, BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.cr_weak h.2⟩)
    true slices (WOps.new concreteCollector {} version) (VOps.new concreteCollector {} version) []
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wvRel_new _ _)
  -- the naive lexer's errors are lexical
  have hV := VCollector.runInputE_lexical true slices (VOps.new concreteCollector {} version) []
    ⟨rfl, .idle, rfl⟩
  simp only [List.map_nil] at hC
  obtain ⟨hC1, hC2⟩ := hC
  refine ⟨hC1.trans (congrArg (List.map entryOf) v2), ?_⟩
  revert hC2 hV v1
  unfold collectW
  generalize ((runInputE WOps (WOps.new concreteCollector {} version) true slices).run []).1.1
    = w
  generalize ((runInputE VOps (VOps.new concreteCollector {} version) true slices).run []).1.1
    = v
  generalize ((collectBy (fun lexer slice => Lexer.Internal.WRustPort.Lexer.lexSlice lexer slice)
    (fun lexer => Lexer.Internal.WRustPort.Lexer.lexEof lexer)
    (Lexer.Internal.WRustPort.Lexer.new Collector.mk version) slices).run []).1 = c
  intro v1 hV hC2
  rcases c with ec | o <;> rcases w with ew | o' <;> rcases v with ev | o''
  · have v1' : BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel.preciseOf ew =
        BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel.preciseOf ev := by
      simpa only [Except.mapError, Except.error.injEq] using v1
    have hv := hV ev rfl
    obtain ⟨e1, -⟩ := Slicing.precise_lexical v1' hv
    obtain ⟨k, hk, -⟩ := hv
    exact ⟨k, cause_of_rel hC2.1 (e1.trans hk), hk⟩
  · cases v1
  · exact hC2.elim
  · exact hC2.elim
  · exact hC2.elim
  · exact hC2.elim
  · cases v1
  · have v1' : o' = o'' := by simpa only [Except.mapError, Except.ok.injEq] using v1
    subst v1'
    exact Slicing.oRel_eq hC2

/-- The naive lexer with the concrete collector ends alike fed the slices and their cut, and takes
the same tokens. -/
theorem naive_cut (version : Version) (slices : List ByteList) :
    ((runInputE VOps (VOps.new concreteCollector {} version) true slices).run []).1.1 =
        ((runInputE VOps (VOps.new concreteCollector {} version) true
          (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).1.1 ∧
      ((runInputE VOps (VOps.new concreteCollector {} version) true slices).run []).2 =
        ((runInputE VOps (VOps.new concreteCollector {} version) true
          (X1BatchInCoreLexer.Chunks.cutAll slices)).run []).2 := by
  have hS := BSmtLib.Facts.Proofs.Lexer.Consumers.VFlattenE.runInputE_flatten concreteCollector
    true slices (Lexer.Internal.VNaive.Core.initial version) none [] trivial
  have hF := BSmtLib.Facts.Proofs.Lexer.Consumers.VFlattenE.runInputE_flatten concreteCollector
    true (X1BatchInCoreLexer.Chunks.cutAll slices) (Lexer.Internal.VNaive.Core.initial version)
    none [] trivial
  rw [X1BatchInCoreLexer.Chunks.flatten_cutAll] at hF
  obtain ⟨s1, s2, -, -⟩ := hS
  obtain ⟨f1, f2, -, -⟩ := hF
  exact ⟨s1.trans f1.symm, s2.trans f2.symm⟩

/-! ## The lexers agree -/

/-- The naive lexer, the Rust port and the lexer with the batch in its state with the collector
end as the library's lexer with it does, but for where an error is, and write down the same
entries. -/
theorem lexers_agree (version : Version) (slices : List ByteList) :
    causeOnly (collectV version slices) = causeOnly (collect version slices) ∧
      causeOnly (collectW version slices) = causeOnly (collect version slices) ∧
      causeOnly (collectX1 version slices) = causeOnly (collect version slices) := by
  obtain ⟨c1, c2⟩ := Slicing.collect_naive version slices
  obtain ⟨n1, n2⟩ := naive_cut version slices
  obtain ⟨v1, v2⟩ := collectV_naive version slices
  obtain ⟨w1, w2⟩ := collectW_naive version slices
  rw [n1] at v2 w2
  rw [n2] at v1 w1
  have hW := causeOnly_eq w2 (matchesC_of_matches c2) (w1.trans c1.symm)
  refine ⟨causeOnly_eq v2 (matchesC_of_matches c2) (v1.trans c1.symm), hW, ?_⟩
  rw [collectX1_collectW]
  exact hW

end BSmtLib.Facts.Proofs.PublicApi.Agree
