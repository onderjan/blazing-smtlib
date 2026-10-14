module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
import all BSmtLib.Lexer.Helpers
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The normal state on whitespace on the fast path

The step of the Rust port's normal state at whitespace other than a line feed, on the fast path.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Whitespace

open BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
open BSmtLib.Lexer.Internal.WRustPort (lexNormalFrom FastState Frame Held Past)
open BSmtLib.Lexer.Internal.WRustPort.Slice (get? get)
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Push
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Runs
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.StartWs
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.FastRuns BSmtLib.Lexer.Internal.VNaive

section

variable {floor : Option Nat} {low : Nat}

variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Token.Version}

/-- `normalSpec_lt` at whitespace other than a line feed, on the fast path. -/
theorem normalSpec_whitespace (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (n index : Nat)
    (ih : ∀ index, input.size - index < n → NormalSpec C v hd iv input offset base hframe index)
    (hn : input.size - index < n + 1)
    {c₀ : UInt8} (hget₀ : get? input index = some c₀) (hc40₀ : c₀ ≠ 40) (hc41₀ : c₀ ≠ 41)
    (hf : Lexer.Helpers.fastFlags c₀ = Lexer.Helpers.FAST_ON ||| Lexer.Helpers.FAST_DELIM |||
    Lexer.CharClass.RUN_NON_LF_WHITESPACE)
    (hwsr : isWhitespaceRun c₀ = true) :
    NormalSpec C v hd iv input offset base hframe index := by
  intro batch locals hindex hbatch origin horigin s coll held location hfix hoff hbase
    hline hlineStart hnormal hloc hheld hbytes
  rw [lexNormalFrom]
  split
  · rename_i hget; rw [hget₀] at hget; cases hget
  rename_i c hget
  have hcc : c = c₀ := Option.some.inj (hget.symm.trans hget₀)
  subst hcc
  obtain ⟨hi, hc⟩ := get?_eq hget
  dsimp only
  apply WP.wp_ite
  · intro hcp; exact absurd (by simpa using hcp) hc41₀
  intro hcp
  apply WP.wp_ite
  · intro hop; exact absurd (by simpa using hop) hc40₀
  intro hop
  have hc40 : c ≠ 40 := by simpa using hop
  have hc41 : c ≠ 41 := by simpa using hcp
  apply WP.wp_bind
  apply WP.wp_pure
  apply WP.wp_ite
  · intro hfast
    · -- whitespace other than a line feed
      by_cases hcon : C.concrete = true
      · simp only [answering_concrete, hcon, Bool.true_and]
        have hpipe : (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_PIPE != 0) = false
            := by rw [hf]; decide
        have hsym : (Lexer.Helpers.fastFlags c &&& Lexer.CharClass.RUN_SIMPLE_SYMBOL != 0) = false
            := by
          rw [hf]; decide
        have hemit : (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_EMIT != 0) = false
            := by rw [hf]; decide
        have hwsb : (Lexer.Helpers.fastFlags c &&& Lexer.CharClass.RUN_NON_LF_WHITESPACE != 0) =
            true := by
          rw [hf]; decide
        have hmask : Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK =
            Lexer.CharClass.RUN_NON_LF_WHITESPACE := by
          rw [hf]; decide
        have hw : isWhitespace input[index] = true := by
          rw [hc]
          simp only [isWhitespaceRun, Bool.and_eq_true] at hwsr
          exact hwsr.1
        have hj : Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
            (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK) =
            runEnd input isWhitespaceRun index := by
          rw [hmask, runEnd_eq endsRun_whitespace,
            ← runEnd_succ input _ index hi (by rw [hc]; exact hwsr)]
        have hle := le_runEnd input isWhitespaceRun (index + 1)
        rw [← runEnd_succ input _ index hi (by rw [hc]; exact hwsr)] at hle
        have hle' := runEnd_le input isWhitespaceRun index (Nat.le_of_lt hi)
        have hstop := fun h => runEnd_stop input isWhitespaceRun index h
        have hA := feedFrom_mode v true input isWhitespaceRun isWhitespaceRun_ne .whitespace
          (fun q l c hm hc => advance_whitespace_run true q l c hm hc) index
          ⟨.whitespace, location, .empty⟩ location rfl (Nat.le_of_lt hi)
        rw [← feedFrom_wsStart v input hi hw location, ← hcon, ← hj] at hA
        rw [← hj] at hle hle' hstop
        apply WP.wp_dite
        · -- the whitespace does not end on this line inside the slice
          intro _
          refine wp_store hline hlineStart ?_
          apply WP.wp_bind
          refine startWhitespace_wp v input offset base index batch _ hframe hindex hbatch s coll
            held location hfix hoff hbase hloc hheld hbytes hcon hi hw ?_ ?_ ?_
          · intro next batch' hnext hbatch' s' coll' held' locN hfix' hoff' hbase' hnormal' hloc'
              hheld' hbytes' heq
            dsimp only
            rw [WP.rust_loadLocals]
            unfold FastState.load
            apply WP.wp_bind; apply WP.wp_bind; apply WP.wp_getCore; apply WP.wp_pure
            refine wp_recurse (f := fun (r : Past input origin) => r.1)
              (ih next (by omega) batch' _ _ hbatch' origin _ s' coll' held' locN hfix' hoff'
                hbase' rfl rfl hnormal' hloc' hheld' hbytes') heq
          · intro s' hpost
            apply WP.wp_pure
            exact hpost
          · intro e s' coll' hf
            exact hf
        intro hws
        -- the whitespace ends inside the slice before a byte that is not a line feed
        obtain ⟨c', hgetR, hc'10⟩ : ∃ c', get? input
            (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
            (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK)) = some c' ∧ c' ≠ 10 := by
          simp only [hwsb, Bool.true_and] at hws
          revert hws
          cases get? input (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
            (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK)) with
          | none => intro h; exact absurd rfl h
          | some c' => intro h; exact ⟨c', rfl, by simpa using h⟩
        obtain ⟨hRs, hRc⟩ := get?_eq hgetR
        have hRq := hstop hRs
        have hadv := advance_whitespace_end true ⟨.whitespace, location,
          ByteArray.empty ++ bytesOf input index
            (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK))⟩
          (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
            (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK) - index))
          (c := input[Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
            (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK)]) rfl hRq
                (by rw [hRc]; exact hc'10)
        have hC : feedFrom v C.concrete input .idle location index =
            Prep [⟨.whitespace, bytesOf input index
                (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK)), location,
                afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                  (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK) - index)⟩]
              (feedFrom v C.concrete input .idle
                (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                  (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK) - index))
                (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                    (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK)))
            := by
          rw [hA, hcon, feedFrom_tokenBefore v true input hRs hadv, empty_append]
        have hidx : (if (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_PIPE != 0) = true then
            Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK) + 1
          else Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
              (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK)) =
            Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK) := by
          simp only [hpipe, Bool.false_eq_true, ↓reduceIte]
        apply WP.wp_dite
        · intro h; simp [hpipe, hsym] at h
        intro _
        apply WP.wp_ite
        · intro h; rw [hemit] at h; cases h
        intro _
        apply WP.wp_bind
        refine pushFast_wp input batch locals offset base _ _ _ index _ _ _ hindex _ hframe hbatch
          held hheld hbytes.symm ?_ ?_ s coll hfix.recovers ?_ ?_
        · simp only [hpipe, Bool.false_eq_true, ↓reduceIte]; omega
        · simp only [hpipe, Bool.false_eq_true, ↓reduceIte]; omega
        · intro r s' coll' held' hH hb hk hp
          rw [hfix.holding] at hp
          simp only [hpipe, hwsb, hemit, Bool.false_eq_true, Bool.false_or,
            hcon, Bool.and_true, ↓reduceIte] at hp
          rw [hline, hlineStart, onLine_eq hloc hindex (by omega)] at hp
          obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
          refine wp_recurse (f := fun (r : Past input origin) => r.1)
            (ih _ (by rw [hidx]; omega) r.val locals _ r.property origin _ s' coll' held'
              (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK) - index))
              (fixed_of_key hfix hk) (hoff.trans k8.symm) (hbase.trans k9.symm)
              (hline.trans k10.symm) (hlineStart.trans k11.symm) (k2.trans hnormal)
              (by rw [hidx]; exact (hloc.afterColumns hindex (by omega)).congr k10 k11) hH
              (hb.trans hbytes)) ?_
          rw [hidx, hC, outcome_pending_prep, outcome_pending_congr hp]
          rfl
        · intro e s' p d hn hss
          simp only [hpipe, hwsb, hemit, Bool.false_eq_true, Bool.false_or,
            hcon, Bool.and_true, ↓reduceIte] at hn
          rw [hline, hlineStart, onLine_eq hloc hindex (by omega)] at hn
          exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
            ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn
      have hcon' : C.concrete = false := by simpa using hcon
      simp only [answering_concrete, hcon', Bool.false_and, Bool.false_eq_true,
          ↓reduceIte, dite_false]
      have hpipe : (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_PIPE != 0) = false
          := by rw [hf]; decide
      have hsym : (Lexer.Helpers.fastFlags c &&& Lexer.CharClass.RUN_SIMPLE_SYMBOL != 0) = false :=
          by
        rw [hf]; decide
      have hemit : (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_EMIT != 0) = false
          := by rw [hf]; decide
      have hmask : Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK =
          Lexer.CharClass.RUN_NON_LF_WHITESPACE := by
        rw [hf]; decide
      have hj : Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
          (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK) =
          runEnd input isWhitespaceRun index := by
        rw [hmask, runEnd_eq endsRun_whitespace,
          ← runEnd_succ input _ index hi (by rw [hc]; exact hwsr)]
      have hle := le_runEnd input isWhitespaceRun (index + 1)
      rw [← runEnd_succ input _ index hi (by rw [hc]; exact hwsr)] at hle
      have hpure : feedFrom v C.concrete input .idle location index =
          feedFrom v C.concrete input .idle
            (afterColumns location (runEnd input isWhitespaceRun index - index))
            (runEnd input isWhitespaceRun index) :=
        feedFrom_idleRun v C.concrete input isWhitespaceRun isWhitespaceRun_ne
          (fun location c h => byteStep_idle_idle v C.concrete
            (by rw [hcon']; exact start_whitespaceRun v location h)) _ index rfl
          location (Nat.le_of_lt hi)
      apply WP.wp_dite
      · intro h; simp [hpipe, hsym] at h
      intro _
      apply WP.wp_ite
      · intro h; rw [hemit] at h; cases h
      intro _
      apply WP.wp_bind
      refine pushFast_wp input batch locals offset base _ _ _ index _ _ _ hindex _ hframe hbatch
        held hheld hbytes.symm ?_ ?_ s coll hfix.recovers ?_ ?_
      · simp only [hpipe, Bool.false_eq_true, ↓reduceIte, hj]; omega
      · simp only [hpipe, Bool.false_eq_true, ↓reduceIte, hj]
        exact runEnd_le input _ _ (Nat.le_of_lt hi)
      · intro r s' coll' held' hH hb hk hp
        rw [hfix.holding] at hp
        simp only [hemit, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hp
        obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
        have hidx : (if (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_PIPE != 0) = true then
              Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                  (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK) + 1
            else Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_RUN_MASK)) =
            runEnd input isWhitespaceRun index := by
          simp only [hpipe, Bool.false_eq_true, ↓reduceIte, hj]
        refine wp_recurse (f := fun (r : Past input origin) => r.1)
          (ih _ (by rw [hidx]; omega) r.val locals _ r.property origin _ s'
            coll' held'
            (afterColumns location (runEnd input isWhitespaceRun index - index))
            (fixed_of_key hfix hk) (hoff.trans k8.symm) (hbase.trans k9.symm)
            (hline.trans k10.symm) (hlineStart.trans k11.symm) (k2.trans hnormal)
            (by rw [hidx]; exact (hloc.afterColumns hindex (by omega)).congr k10 k11) hH
            (hb.trans hbytes)) ?_
        rw [hidx, ← hpure, outcome_pending_congr hp]
      · intro e s' p d hn hss
        simp only [hemit, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hn
        exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
          ⟨_, rfl⟩ hn
  intro hslow
  exact absurd (by rw [hf]; decide) hslow

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Whitespace
