module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
import all BSmtLib.Lexer.Helpers
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.WRustPort.Slice

@[expose] public section

/-!
# The normal state on a hexadecimal or binary literal

The step of the Rust port's normal state at the hash that starts a hexadecimal or binary literal.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Hash

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
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Delimiters
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.NumeralRuns
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.StartLiterals BSmtLib.Lexer.Internal.VNaive

section

variable {floor : Option Nat} {low : Nat}

variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Token.Version}

set_option maxHeartbeats 350000 in
/-- `normalSpec_lt` at the hash that starts a hexadecimal or binary literal. -/
theorem normalSpec_hash (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (n index : Nat)
    (ih : ∀ index, input.size - index < n → NormalSpec C v hd iv input offset base hframe index)
    (hn : input.size - index < n + 1)
    {c₀ : UInt8} (hget₀ : get? input index = some c₀) (hc40₀ : c₀ ≠ 40) (hc41₀ : c₀ ≠ 41)
    (hfoff₀ : (Lexer.Helpers.fastFlags c₀ &&& Lexer.Helpers.FAST_ON != 0) = false)
    (hst₀ : Lexer.Helpers.startOf c₀ = .hash) :
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
  have hfoff : (Lexer.Helpers.fastFlags c &&& Lexer.Helpers.FAST_ON != 0) = false
      := by simpa using hslow
  obtain ⟨hl1, hl2, hl3⟩ := id hloc
  refine wp_store hline hlineStart ?_
  split
  all_goals first
    | (rename_i hst'; rw [hst₀] at hst'; cases hst'; done)
    | skip
  · -- a hash: a hexadecimal or binary literal
    rename_i hst
    have h35 := startOf_hash hst
    unfold Lexer.Internal.WRustPort.startToken Lexer.Internal.WRustPort.modifyContent
    apply WP.wp_bind
    apply WP.wp_bind; apply WP.wp_getCore
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_pure
    have hhash : feedFrom v C.concrete input .idle location index =
        feedFrom v C.concrete input (.token ⟨.hash, location, .empty⟩) (location.afterByte 35)
          (index + 1) := by
      rw [feedFrom_step hi (byteStep_idle_pending v C.concrete (by rw [hc, h35]; rfl)),
          prep_nil, hc, h35]
    split
    · -- the base is selected
      rename_i run hrun heqm
      obtain ⟨b, hb, hsel⟩ := Option.bind_eq_some_iff.mp hrun
      obtain ⟨hi1, hb'⟩ := get?_eq hb
      obtain ⟨radix, hadv, h10', hflag, hstate, htyp, hnotr⟩ : ∃ radix : Radix,
          advance C.concrete ⟨.hash, location, .empty⟩ (location.afterByte 35) input[index + 1] =
            .pending ⟨.digits radix, location, .empty⟩ ∧ input[index + 1] ≠ 10 ∧
          (∀ c, Lexer.CharClass.endsRun c run.flag = !radix.allows c) ∧
          (∀ (p : Pending) start content, p.mode = .digits radix → p.start = start →
            p.content = content → TokenAgrees v C.concrete run.state start content p) ∧
          run.tokenType = radix.category ∧ run.emptyError ≠ .unexpectedTrailingToken := by
        rw [hb']
        by_cases hx : (b == 120) = true
        · simp only [hx, ↓reduceIte, Option.some.injEq] at hsel
          subst hsel
          have hx' : b = 120 := by simpa using hx
          subst hx'
          exact ⟨.hexadecimal, rfl, by decide, endsRun_hex,
            fun _ _ _ hm hs hc => ⟨hs, hm, hc⟩, rfl, nofun⟩
        · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hsel
          by_cases hy : (b == 98) = true
          · simp only [hy, ↓reduceIte, Option.some.injEq] at hsel
            subst hsel
            have hy' : b = 98 := by simpa using hy
            subst hy'
            exact ⟨.binary, rfl, by decide, endsRun_binary,
              fun _ _ _ hm hs hc => ⟨hs, hm, hc⟩, rfl, nofun⟩
          · simp only [hy, Bool.false_eq_true, ↓reduceIte] at hsel
            cases hsel
      have hJ : Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag =
          runEnd input radix.allows (index + 1 + 1) := runEnd_eq hflag _ _
      have hle := le_runEnd input radix.allows (index + 1 + 1)
      have hle' := runEnd_le input radix.allows (index + 1 + 1) hi1
      have hstop := fun h => runEnd_stop input radix.allows (index + 1 + 1) h
      have hB : feedFrom v C.concrete input .idle location index =
          feedFrom v C.concrete input
            (.token ⟨.digits radix, location,
              bytesOf input (index + 1 + 1) (runEnd input radix.allows (index + 1 + 1))⟩)
            (afterColumns location
              (runEnd input radix.allows (index + 1 + 1) - index))
            (runEnd input radix.allows (index + 1 + 1)) := by
        rw [hhash, feedFrom_step hi1 (byteStep_token_pending v C.concrete hadv), prep_nil,
          feedFrom_mode v C.concrete input radix.allows (allows_ne radix) (.digits radix)
            (fun q l c hm hc => advance_digits_run radix C.concrete q l c hm hc)
                (index + 1 + 1) _ _ rfl
            hi1, afterByte_eq_afterColumns' _ _ h10', afterByte_eq_afterColumns' _ _ (by decide),
          afterColumns_add, afterColumns_add]
        simp only [empty_append]
        congr 2
        omega
      rw [← hJ] at hB hle hle' hstop
      apply WP.wp_dite
      · -- the digits run to the end of the slice: the literal is left in progress
        intro hsz
        have hsz' : Lexer.Internal.WRustPort.Slice.runEnd input
            (index + 1 + 1) run.flag = input.size := by
          simpa using hsz
        unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
          Lexer.Internal.WRustPort.leavePending
        apply WP.wp_bind; apply WP.wp_modifyCore
        apply WP.wp_bind; apply WP.wp_modifyBound
        apply WP.wp_pure
        refine ⟨.token ⟨.digits radix, location, bytesOf input (index + 1 + 1)
            (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag)⟩,
          afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1 + 1) run.flag - index),
          held, ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_,
              hheld, hbytes, ?_⟩
        · refine ⟨hstate _ _ _ rfl (locAt_eq hloc) ?_, ?_⟩
          · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
          · fits_tac
        · dsimp only [LocAt, afterColumns, Past.from]
          refine ⟨?_, ?_, ?_⟩ <;> omega
        · rw [hB]; rfl
      · intro hsz
        have hJs : Lexer.Internal.WRustPort.Slice.runEnd input
            (index + 1 + 1) run.flag < input.size := by
          simp only [beq_iff_eq] at hsz
          omega
        have hstop' := hstop hJs
        apply WP.wp_bind; apply WP.wp_getCore
        have hsize : ∀ buf h1 h2, (Lexer.Internal.WRustPort.Slice.borrow input (index + 1 + 1)
            (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag) h1 h2).size buf =
              Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag -
                  (index + 1 + 1) := fun _ _ _ => by
          simp only [Lexer.Internal.WRustPort.Slice.borrow, Lexer.Helpers.Content.size]; omega
        apply WP.wp_ite
        · -- no digit: the literal fails
          intro hempty
          have he : Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1 + 1) run.flag = index + 1 + 1 := by
            have : (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag) -
                (index + 1 + 1) = 0 := by
              simpa [hsize] using hempty
            omega
          obtain ⟨f, hf⟩ := advance_end_digits_empty (location := afterColumns location
            (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag - index))
            (q := ⟨.digits radix, location, bytesOf input (index + 1 + 1)
              (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag)⟩) rfl hstop'
            (by rw [he, bytesOf_self input _ hi1]; rfl)
          unfold Lexer.Internal.WRustPort.leave Lexer.Internal.WRustPort.error
              Lexer.Internal.WRustPort.errorWith
          wp_walk
          refine stepFails_here (he := ⟨_, rfl, hnotr⟩) ?_ hheld
            ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
          rw [hB, feedFrom_advance_error v C.concrete input hJs hf]
        · intro hne
          have hne' : (bytesOf input (index + 1 + 1)
              (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag)).isEmpty =
                  false := by
            have : (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag) -
                (index + 1 + 1) ≠ 0 := by
              simpa [hsize] using hne
            have hpos : (bytesOf input (index + 1 + 1)
                (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag)).size ≠ 0 :=
                    by
              show (input.slice _ _).toByteArray.size ≠ 0
              rw [size_toByteArray, slice_size input hle (Nat.le_of_lt hJs)]
              exact this
            simp [ByteArray.isEmpty, hpos]
          have hC := feedFrom_end v C.concrete input hJs (q := ⟨.digits radix, location,
              bytesOf input (index + 1 + 1) (Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1 + 1) run.flag)⟩)
            (location := afterColumns location
              (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag - index))
            (advance_end_digits rfl hstop' hne')
          rw [← hB] at hC
          rw [get_eq hJs]
          apply WP.wp_ite
          · intro hnd
            have hnd' : Lexer.Internal.VNaive.isDelimiter
                input[Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag] = false
                    := by
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
                input[Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag] = true
                    := by
              rw [← isDelimiter_eq]; simpa using hdl
            rw [hd'] at hC
            simp only [↓reduceIte] at hC
            have hlex := borrowedLexeme_eq hloc hindex
              (j := Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag)
                  (by omega) run.tokenType
              (input.slice (index + 1 + 1) (Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1 + 1) run.flag))
            apply WP.wp_bind
            refine pushBorrowed_wp input batch offset base _ _ _ _ _ _ _ _ _ held hheld
                hbytes.symm ?_ ?_
              _ coll ?_ ?_ ?_
            · omega
            · omega
            · exact hfix.recovers
            · intro r s' coll' held' hH hb hk hp
              rw [hfix.holding] at hp
              have hp' : pending C hd s'.val.version coll' held' = pending C hd
                  s.val.version coll (held ++
                  [⟨radix.category, bytesOf input (index + 1 + 1)
                    (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1 + 1) run.flag),
                        location,
                    afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input
                        (index + 1 + 1)
                      run.flag - index)⟩]) := by
                have := hp.trans (congrArg (fun l => pending C hd s.val.version coll
                    (held ++ [l])) hlex)
                rw [htyp] at this; exact this
              obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
              rw [WP.rust_loadLocals]
              unfold FastState.load
              apply WP.wp_bind; apply WP.wp_bind; apply WP.wp_getCore; apply WP.wp_pure
              refine wp_recurse (f := fun (r : Past input origin) => r.1)
                (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
                  (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input
                      (index + 1 + 1)
                    run.flag - index))
                  (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩)
                      (hoff.trans k8.symm)
                  (hbase.trans k9.symm) rfl rfl k2
                  ((hloc.afterColumns hindex (by omega)).congr k10 k11) hH
                  (hb.trans hbytes)) ?_
              rw [hC, outcome_pending_prep, outcome_pending_congr hp']
            · intro e s' p d hn hss
              have hn' := hn
              replace hn' := stops_lexeme hlex hn'
              rw [htyp] at hn'
              exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
                ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn'
    · -- no base is selected: the hash is left in progress
      unfold Lexer.Internal.WRustPort.leavePending
      apply WP.wp_bind; apply WP.wp_modifyBound
      apply WP.wp_pure
      refine ⟨.token ⟨.hash, location, .empty⟩, location.afterByte 35, held,
        ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_, hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
        refine ⟨⟨?_, rfl, (contentBytes_clear _).symm⟩, ?_⟩
        rw [locAt_eq hloc]; rfl
        · fits_tac
      · have := hloc.afterByte hindex (b := 35) (by decide)
        obtain ⟨h1, h2, h3⟩ := this
        dsimp only [LocAt, Past.from]
        refine ⟨?_, h2, h3⟩
        omega
      · rw [hhash]; rfl

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Hash
