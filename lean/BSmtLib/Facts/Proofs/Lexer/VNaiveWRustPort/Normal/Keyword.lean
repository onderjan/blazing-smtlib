module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
import all BSmtLib.Lexer.Internal.Helpers
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.WRustPort.Slice

@[expose] public section

/-!
# The normal state on a keyword

The step of the Rust port's normal state at the colon that starts a keyword.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Keyword

open BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
open BSmtLib.Lexer.Internal (CharClass)
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
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Delimiters
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.FastRuns
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Start BSmtLib.Lexer.Internal.VNaive

section

variable {floor : Option Nat} {low : Nat}

variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Token.Version}

set_option maxHeartbeats 250000 in
/-- `normalSpec_lt` at the colon that starts a keyword. -/
theorem normalSpec_keyword (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (n index : Nat)
    (ih : ∀ index, input.size - index < n → NormalSpec C v hd iv input offset base hframe index)
    (hn : input.size - index < n + 1)
    {c₀ : UInt8} (hget₀ : get? input index = some c₀) (hc40₀ : c₀ ≠ 40) (hc41₀ : c₀ ≠ 41)
    (hfoff₀ : (Lexer.Internal.Helpers.fastFlags c₀ &&& Lexer.Internal.Helpers.FAST_ON != 0) = false)
    (hst₀ : Lexer.Internal.Helpers.startOf c₀ = .colon) :
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
  · intro hfast; rw [hfoff₀] at hfast; cases hfast
  -- the slow path
  intro hslow
  have hfoff : (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_ON != 0) = false
      := by simpa using hslow
  obtain ⟨hl1, hl2, hl3⟩ := id hloc
  refine wp_store hline hlineStart ?_
  split
  all_goals first
    | (rename_i hst'; rw [hst₀] at hst'; cases hst'; done)
    | skip
  · -- a colon: a keyword
    rename_i hst
    have h58 := startOf_colon hst
    unfold Lexer.Internal.WRustPort.startToken Lexer.Internal.WRustPort.modifyContent
    apply WP.wp_bind
    apply WP.wp_bind; apply WP.wp_getCore
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_pure
    have hK : Lexer.Internal.WRustPort.Slice.runEnd input
        (index + 1) CharClass.RUN_SIMPLE_SYMBOL =
        runEnd input isSymbolByte (index + 1) := runEnd_eq endsRun_symbol _ _
    have hle := le_runEnd input isSymbolByte (index + 1)
    have hle' := runEnd_le input isSymbolByte (index + 1) hi
    have hstop := fun h => runEnd_stop input isSymbolByte (index + 1) h
    have hA : feedFrom v C.concrete input .idle location index =
        feedFrom v C.concrete input
          (.token ⟨.keyword, location,
            bytesOf input (index + 1) (runEnd input isSymbolByte (index + 1))⟩)
          (afterColumns location (runEnd input isSymbolByte (index + 1) - index))
          (runEnd input isSymbolByte (index + 1)) := by
      rw [feedFrom_startRun v C.concrete input isSymbolByte isSymbolByte_ne .keyword
        (fun q l c hm hc => advance_keyword_run C.concrete q l c hm hc) hi
        (q := ⟨.keyword, location, .empty⟩) (by rw [hc, h58]; rfl) rfl
        (by rw [hc, h58]; decide)]
      simp only [empty_append]
    rw [← hK] at hA hle hle' hstop
    apply WP.wp_dite
    · -- the keyword runs to the end of the slice: it is left in progress
      intro hsz
      have hsz' : Lexer.Internal.WRustPort.Slice.runEnd input
          (index + 1) CharClass.RUN_SIMPLE_SYMBOL = input.size := by
        simpa using hsz
      unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
        Lexer.Internal.WRustPort.leavePending
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_bind; apply WP.wp_modifyBound
      apply WP.wp_pure
      refine ⟨.token ⟨.keyword, location, bytesOf input (index + 1)
          (Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1) CharClass.RUN_SIMPLE_SYMBOL)⟩,
        afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
          CharClass.RUN_SIMPLE_SYMBOL - index),
        held, ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_,
            hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
        refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
        · rw [locAt_eq hloc]; rfl
        · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
        · fits_tac
      · dsimp only [LocAt, afterColumns, Past.from]
        refine ⟨?_, ?_, ?_⟩ <;> omega
      · rw [hA]; rfl
    · intro hsz
      have hJs : Lexer.Internal.WRustPort.Slice.runEnd input
          (index + 1) CharClass.RUN_SIMPLE_SYMBOL < input.size := by
        simp only [beq_iff_eq] at hsz
        omega
      have hstop' := hstop hJs
      apply WP.wp_bind; apply WP.wp_getCore
      have hsize : ∀ buf h1 h2, (Lexer.Internal.WRustPort.Slice.borrow input (index + 1)
          (Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1) CharClass.RUN_SIMPLE_SYMBOL) h1 h2).size buf =
            Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) CharClass.RUN_SIMPLE_SYMBOL - (index + 1) := by
        intro _ _ _
        simp only [Lexer.Internal.WRustPort.Slice.borrow,
            Lexer.Internal.Helpers.Content.size]; omega
      apply WP.wp_ite
      · -- an empty keyword
        intro hempty
        have he : Lexer.Internal.WRustPort.Slice.runEnd input
            (index + 1) CharClass.RUN_SIMPLE_SYMBOL = index + 1 := by
          have : (Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1) CharClass.RUN_SIMPLE_SYMBOL) - (index + 1) = 0 :=
              by
            simpa [hsize] using hempty
          omega
        obtain ⟨f, hf⟩ := advance_end_keyword_empty (location := afterColumns location
          (Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1) CharClass.RUN_SIMPLE_SYMBOL - index))
          (q := ⟨.keyword, location, bytesOf input (index + 1)
            (Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) CharClass.RUN_SIMPLE_SYMBOL)⟩) rfl hstop'
          (by rw [he, bytesOf_self input _ hi]; rfl)
        unfold Lexer.Internal.WRustPort.leave Lexer.Internal.WRustPort.error
            Lexer.Internal.WRustPort.errorWith
        wp_walk
        refine stepFails_here ?_ hheld
          ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
        rw [hA, feedFrom_advance_error v C.concrete input hJs hf]
      · intro hne
        have hne' : (bytesOf input (index + 1)
            (Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) CharClass.RUN_SIMPLE_SYMBOL)).isEmpty = false := by
          have : (Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1) CharClass.RUN_SIMPLE_SYMBOL) - (index + 1) ≠ 0 :=
              by
            simpa [hsize] using hne
          have hpos : (bytesOf input (index + 1)
              (Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) CharClass.RUN_SIMPLE_SYMBOL)).size ≠ 0 := by
            show (input.slice _ _).toByteArray.size ≠ 0
            rw [size_toByteArray, slice_size input hle (Nat.le_of_lt hJs)]
            exact this
          simp [ByteArray.isEmpty, hpos]
        have hC := feedFrom_end v C.concrete input hJs (q := ⟨.keyword, location,
            bytesOf input (index + 1)
              (Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) CharClass.RUN_SIMPLE_SYMBOL)⟩)
          (location := afterColumns location
            (Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) CharClass.RUN_SIMPLE_SYMBOL - index))
          (advance_end_keyword rfl hstop' hne')
        rw [← hA] at hC
        rw [get_eq hJs]
        apply WP.wp_ite
        · intro hnd
          have hnd' : Lexer.Internal.VNaive.isDelimiter
              input[Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) CharClass.RUN_SIMPLE_SYMBOL] = false := by
            rw [← isDelimiter_eq]; simpa using hnd
          rw [hnd'] at hC
          unfold Lexer.Internal.WRustPort.leave Lexer.Internal.WRustPort.errorAt
              Lexer.Internal.WRustPort.errorWith
          wp_walk
          refine stepFails_here ?_ hheld
            ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
          rw [hC]
          simp only [Bool.false_eq_true, ↓reduceIte]
        · intro hdl
          have hd' : Lexer.Internal.VNaive.isDelimiter
              input[Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) CharClass.RUN_SIMPLE_SYMBOL] = true := by
            rw [← isDelimiter_eq]; simpa using hdl
          rw [hd'] at hC
          simp only [↓reduceIte] at hC
          have hlex := borrowedLexeme_eq hloc hindex
            (j := Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) CharClass.RUN_SIMPLE_SYMBOL) (by omega)
            .keyword (input.slice (index + 1)
              (Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) CharClass.RUN_SIMPLE_SYMBOL))
          apply WP.wp_bind
          refine pushBorrowed_wp input batch offset base _ _ _ _ _ _ _ _ _ held hheld hbytes.symm
              ?_ ?_
            _ coll ?_ ?_ ?_
          · omega
          · omega
          · exact hfix.recovers
          · intro r s' coll' held' hH hb hk hp
            rw [hfix.holding] at hp
            have hp' : pending C hd s'.val.version coll' held' = pending C hd
                s.val.version coll (held ++
                [⟨.keyword, bytesOf input (index + 1)
                  (Lexer.Internal.WRustPort.Slice.runEnd input
                      (index + 1) CharClass.RUN_SIMPLE_SYMBOL), location,
                  afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                    CharClass.RUN_SIMPLE_SYMBOL - index)⟩]) :=
              hp.trans (congrArg (fun l => pending C hd s.val.version coll (held ++ [l])) hlex)
            obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
            rw [WP.rust_loadLocals]
            unfold FastState.load
            apply WP.wp_bind; apply WP.wp_bind; apply WP.wp_getCore; apply WP.wp_pure
            refine wp_recurse (f := fun (r : Past input origin) => r.1)
              (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
                (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                  CharClass.RUN_SIMPLE_SYMBOL - index))
                (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩)
                    (hoff.trans k8.symm)
                (hbase.trans k9.symm) rfl rfl k2
                ((hloc.afterColumns hindex (by omega)).congr k10 k11) hH
                (hb.trans hbytes)) ?_
            rw [hC, outcome_pending_prep, outcome_pending_congr hp']
          · intro e s' p d hn hss
            have hn' := hn
            replace hn' := stops_lexeme hlex hn'
            exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
              ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn'

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Keyword
