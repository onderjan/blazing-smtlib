import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic

/-!
# The normal state on a numeral or a decimal

The step of the Rust port's normal state at the digit that starts a numeral or a decimal.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Digits

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

set_option hygiene false in
/-- A token on the slow path into the batch, ending at `hi`, and the loop going on after it, in
the proof of `normalSpec_lt`; `hC` is the naive lexer's run that hands the token over. -/
local macro "borrow_push" cat:term:max lo:term:max hi:term:max : tactic => `(tactic| (
  have hlex := borrowedLexeme_eq hloc hindex (j := $hi) (by omega) $cat (input.slice $lo $hi)
  apply WP.wp_bind
  refine pushBorrowed_wp input batch offset base _ _ _ _ _ _ _ _ _ held hheld hbytes.symm ?_ ?_ _
    coll ?_ ?_ ?_
  · omega
  · omega
  · exact hfix.recovers
  · intro r s' coll' held' hH hb hk hp
    rw [hfix.holding] at hp
    have hp' := hp.trans
      (congrArg (fun l => pending C hd s.val.version coll (held ++ [l])) hlex)
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
    rw [WP.rust_loadLocals]
    unfold FastState.load
    apply WP.wp_bind; apply WP.wp_bind; apply WP.wp_getCore; apply WP.wp_pure
    refine wp_recurse (f := fun (r : Past input origin) => r.1)
      (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
        (afterColumns location ($hi - index))
        (fixed_of_key' hk ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩) (hoff.trans k8.symm)
        (hbase.trans k9.symm) rfl rfl k2
        ((hloc.afterColumns hindex (by omega)).congr k10 k11) hH (hb.trans hbytes)) ?_
    rw [hC, outcome_pending_prep, outcome_pending_congr hp']
    try rfl
  · intro e s' p d hn hss
    have hn' := hn
    replace hn' := stops_lexeme hlex hn'
    exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
      ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn'))

/-- `normalSpec_lt` at the digit that starts a numeral or a decimal. -/
theorem normalSpec_digits (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (n index : Nat)
    (ih : ∀ index, input.size - index < n → NormalSpec C v hd iv input offset base hframe index)
    (hn : input.size - index < n + 1)
    {c₀ : UInt8} (hget₀ : get? input index = some c₀) (hc40₀ : c₀ ≠ 40) (hc41₀ : c₀ ≠ 41)
    (hfoff₀ : (Lexer.Helpers.fastFlags c₀ &&& Lexer.Helpers.FAST_ON != 0) = false)
    (hst₀ : Lexer.Helpers.startOf c₀ = .digit) :
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
  · -- a digit: a numeral or a decimal
    rename_i hst
    have hdg := startOf_digit hst
    have hstart : start v C.concrete location input[index] =
        .pending ⟨.numeral (c == 48), location, ByteArray.empty.push c⟩ := by
      rw [hc]; exact start_digit v C.concrete location hdg
    unfold Lexer.Internal.WRustPort.startToken Lexer.Internal.WRustPort.modifyContent
    apply WP.wp_bind
    apply WP.wp_bind; apply WP.wp_getCore
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_pure
    have hE : Lexer.Internal.WRustPort.Slice.runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT =
        runEnd input isDigit (index + 1) := runEnd_eq endsRun_digit _ _
    have hle := le_runEnd input isDigit (index + 1)
    have hle' := runEnd_le input isDigit (index + 1) hi
    have hstop := fun h => runEnd_stop input isDigit (index + 1) h
    have hmem := runEnd_mem input isDigit (index + 1)
    rw [← hE] at hle hle' hstop hmem
    have h10 : c ≠ 10 := isDigit_ne c hdg
    apply WP.wp_ite
    · -- a numeral with a leading zero
      intro hz
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hz
      obtain ⟨hz0, hlt⟩ := hz
      have hi1 : index + 1 < input.size := by omega
      have hd1 := hmem (index + 1) hi1 (Nat.le_refl _) hlt
      have hadv : ∃ f, advance C.concrete ⟨.numeral true, location, ByteArray.empty.push c⟩
          (location.afterByte c) input[index + 1] = .error f := by
        simp [advance, hd1]
      obtain ⟨f, hf⟩ := hadv
      unfold Lexer.Internal.WRustPort.leave Lexer.Internal.WRustPort.errorAt
          Lexer.Internal.WRustPort.errorWith
      wp_walk
      refine stepFails_here ?_ hheld
        ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
      rw [feedFrom_step hi (byteStep_idle_pending v C.concrete hstart), hc, hz0]
      simp only [beq_self_eq_true]
      rw [hz0] at hf
      rw [feedFrom_advance_error v C.concrete input hi1 hf]
      rfl
    intro hz
    have hz' : c = 48 → Lexer.Internal.WRustPort.Slice.runEnd input
        (index + 1) Lexer.CharClass.RUN_DIGIT = index + 1 := by
      intro h0
      simp only [h0, beq_self_eq_true, Bool.true_and, decide_eq_true_eq] at hz
      omega
    have hA : feedFrom v C.concrete input .idle location index =
        feedFrom v C.concrete input
          (.token ⟨.numeral (c == 48), location, bytesOf input index
            (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT)⟩)
          (afterColumns location
            (Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) Lexer.CharClass.RUN_DIGIT - index))
          (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT) := by
      rw [feedFrom_step hi (byteStep_idle_pending v C.concrete hstart), prep_nil]
      by_cases hz0 : c = 48
      · have he := hz' hz0
        rw [he, bytesOf_one input index hi, hc, afterByte_eq_afterColumns' _ _ h10]
        simp
      · have hfalse : (c == 48) = false := by simpa using hz0
        rw [hfalse, feedFrom_mode v C.concrete input isDigit isDigit_ne (.numeral false)
          (fun q l c hm hc => advance_numeral_run C.concrete q l c hm hc) (index + 1)
              _ _ rfl hi, ← hE]
        simp only
        rw [← hc, push_append_bytesOf _ input hi (by omega) hle', empty_append,
          afterByte_eq_afterColumns' _ _ (by rw [hc]; exact h10), afterColumns_add]
        congr 2
        omega
    split
    · -- a byte ends the digits inside the slice
      rename_i next hgetE
      obtain ⟨hEs, hEc⟩ := get?_eq hgetE
      have hEd := hstop hEs
      rw [hEc] at hEd
      apply WP.wp_ite
      · -- a dot: a decimal
        intro hdot
        have hdot' : next = 46 := by simpa using hdot
        have hF : Lexer.Internal.WRustPort.Slice.runEnd input
            (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                Lexer.CharClass.RUN_DIGIT =
            runEnd input isDigit
              (Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) Lexer.CharClass.RUN_DIGIT + 1) :=
          runEnd_eq endsRun_digit _ _
        have hlf := le_runEnd input isDigit
          (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
        have hlf' := runEnd_le input isDigit
          (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
              hEs
        have hstopF := fun h => runEnd_stop input isDigit
          (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT + 1) h
        have hmemF := runEnd_mem input isDigit
          (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
        have hB : feedFrom v C.concrete input .idle location index =
            feedFrom v C.concrete input
              (.token ⟨.fraction (false || decide
                  (Lexer.Internal.WRustPort.Slice.runEnd input
                      (index + 1) Lexer.CharClass.RUN_DIGIT + 1 <
                    runEnd input isDigit
                      (Lexer.Internal.WRustPort.Slice.runEnd input
                          (index + 1) Lexer.CharClass.RUN_DIGIT + 1))),
                location, bytesOf input index (runEnd input isDigit
                  (Lexer.Internal.WRustPort.Slice.runEnd input
                      (index + 1) Lexer.CharClass.RUN_DIGIT + 1))⟩)
              (afterColumns location (runEnd input isDigit
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) Lexer.CharClass.RUN_DIGIT + 1) - index))
              (runEnd input isDigit
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) Lexer.CharClass.RUN_DIGIT + 1)) := by
          have hadv : advance C.concrete ⟨.numeral (c == 48), location, bytesOf input index
              (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT)⟩
              (afterColumns location
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) Lexer.CharClass.RUN_DIGIT - index))
              input[Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) Lexer.CharClass.RUN_DIGIT] =
              .pending ⟨.fraction false, location, (bytesOf input index
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) Lexer.CharClass.RUN_DIGIT)).push 46⟩ := by
            rw [hEc, hdot']; rfl
          rw [hA, feedFrom_step hEs (byteStep_token_pending v C.concrete hadv), prep_nil,
            feedFrom_fraction v C.concrete input _ _ _ false rfl hEs, hEc, hdot',
            afterByte_eq_afterColumns' _ _ (by decide), afterColumns_add]
          simp only
          rw [← hdot', ← hEc, push_append_bytesOf _ input hEs (by omega) hlf',
            bytesOf_append input (by omega) (by omega) hlf', afterColumns_add]
          congr 2
          simp only [Nat.succ_eq_add_one] at *; omega
        rw [← hF] at hB hlf hlf' hstopF hmemF
        -- the last byte of the decimal so far: its dot, or a digit after it
        have hlastF : (input[Lexer.Internal.WRustPort.Slice.runEnd input
            (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
              Lexer.CharClass.RUN_DIGIT + 1) Lexer.CharClass.RUN_DIGIT - 1]'(by omega) == 46) =
            !decide (Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) Lexer.CharClass.RUN_DIGIT + 1 <
              Lexer.Internal.WRustPort.Slice.runEnd input
                  (Lexer.Internal.WRustPort.Slice.runEnd input
                      (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                Lexer.CharClass.RUN_DIGIT) := by
          by_cases hlt : Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1) Lexer.CharClass.RUN_DIGIT + 1 <
              Lexer.Internal.WRustPort.Slice.runEnd input
                  (Lexer.Internal.WRustPort.Slice.runEnd input
                      (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                Lexer.CharClass.RUN_DIGIT
          · have hdg := hmemF (Lexer.Internal.WRustPort.Slice.runEnd input
              (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
              Lexer.CharClass.RUN_DIGIT + 1) Lexer.CharClass.RUN_DIGIT - 1) (by omega) (by omega)
                  (by omega)
            simp only [hlt, decide_true, Bool.not_true]
            have : input[Lexer.Internal.WRustPort.Slice.runEnd input
                (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                Lexer.CharClass.RUN_DIGIT + 1) Lexer.CharClass.RUN_DIGIT - 1]'(by omega) ≠ 46 := by
              intro h; rw [h] at hdg; exact absurd hdg (by decide)
            simpa using this
          · have heq : Lexer.Internal.WRustPort.Slice.runEnd input
              (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                Lexer.CharClass.RUN_DIGIT + 1) Lexer.CharClass.RUN_DIGIT - 1 =
                Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) Lexer.CharClass.RUN_DIGIT := by omega
            simp only [hlt, decide_false, Bool.not_false]
            simp only [heq, hEc, hdot']
            rfl
        apply WP.wp_dite
        · -- the fraction runs to the end of the slice: the decimal is left in progress
          intro hsz
          have hsz' : Lexer.Internal.WRustPort.Slice.runEnd input
              (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
              Lexer.CharClass.RUN_DIGIT + 1) Lexer.CharClass.RUN_DIGIT = input.size
                  := by simpa using hsz
          unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
            Lexer.Internal.WRustPort.leavePending
          apply WP.wp_bind; apply WP.wp_modifyCore
          apply WP.wp_bind; apply WP.wp_modifyBound
          apply WP.wp_pure
          refine ⟨.token ⟨.fraction (false || decide
              (Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) Lexer.CharClass.RUN_DIGIT + 1 <
                Lexer.Internal.WRustPort.Slice.runEnd input
                    (Lexer.Internal.WRustPort.Slice.runEnd input
                        (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                  Lexer.CharClass.RUN_DIGIT)), location, bytesOf input index
              (Lexer.Internal.WRustPort.Slice.runEnd input
                  (Lexer.Internal.WRustPort.Slice.runEnd input
                      (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                Lexer.CharClass.RUN_DIGIT)⟩,
            afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input
              (Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) Lexer.CharClass.RUN_DIGIT + 1) Lexer.CharClass.RUN_DIGIT - index),
            held, ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_,
                ?_, hheld, hbytes,
            ?_⟩
          · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
            refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
            · rw [locAt_eq hloc]; rfl
            · rw [contentBytes_clear_extendSlice _ _ ?_, show ∀ a b, (input.slice a b).toByteArray =
                bytesOf input a b from fun _ _ => rfl, stored_last input (by omega) (by omega)]
              · simp only [Option.isNone_some, Bool.false_or]
                congr 1
                have hs : ∀ x : UInt8, (some x == some (46 : UInt8)) = (x == 46) := by
                  intro x; cases h : x == 46 <;> simp_all
                rw [hs, hlastF, Bool.not_not]
              · bound_tac
            · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
            · fits_tac
          · dsimp only [LocAt, afterColumns, Past.from]
            refine ⟨?_, ?_, ?_⟩ <;> omega
          · rw [hB]; rfl
        · intro hsz
          have hFs : Lexer.Internal.WRustPort.Slice.runEnd input
              (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
              Lexer.CharClass.RUN_DIGIT + 1) Lexer.CharClass.RUN_DIGIT < input.size := by
            simp only [beq_iff_eq] at hsz; omega
          have hstopF' := hstopF hFs
          apply WP.wp_bind; apply WP.wp_getCore
          rw [borrowed_last input (by omega) (by omega)]
          apply WP.wp_ite
          · -- no digit after the dot
            intro hnone
            have hlt : ¬ (Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) Lexer.CharClass.RUN_DIGIT + 1 <
                Lexer.Internal.WRustPort.Slice.runEnd input
                    (Lexer.Internal.WRustPort.Slice.runEnd input
                        (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                  Lexer.CharClass.RUN_DIGIT) := by
              intro hlt
              have := hlastF
              simp only [hlt, decide_true, Bool.not_true] at this
              simp [this] at hnone
            obtain ⟨f, hf⟩ := advance_end_fraction_none (location := afterColumns location
              (Lexer.Internal.WRustPort.Slice.runEnd input
                  (Lexer.Internal.WRustPort.Slice.runEnd input
                      (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                Lexer.CharClass.RUN_DIGIT - index))
              (q := ⟨.fraction (false || decide
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) Lexer.CharClass.RUN_DIGIT + 1 <
                  Lexer.Internal.WRustPort.Slice.runEnd input
                    (Lexer.Internal.WRustPort.Slice.runEnd input
                        (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                    Lexer.CharClass.RUN_DIGIT)), location, bytesOf input index
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (Lexer.Internal.WRustPort.Slice.runEnd input
                        (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                  Lexer.CharClass.RUN_DIGIT)⟩) (by simp [hlt]) hstopF'
            unfold Lexer.Internal.WRustPort.leave Lexer.Internal.WRustPort.error
                Lexer.Internal.WRustPort.errorWith
            wp_walk
            refine stepFails_here ?_ hheld
              ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
            rw [hB, feedFrom_advance_error v C.concrete input hFs hf]
          · intro hsome
            have hlt : Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) Lexer.CharClass.RUN_DIGIT + 1 <
                Lexer.Internal.WRustPort.Slice.runEnd input
                    (Lexer.Internal.WRustPort.Slice.runEnd input
                        (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                  Lexer.CharClass.RUN_DIGIT := by
              apply Classical.byContradiction
              intro hlt
              have := hlastF
              simp only [hlt, decide_false, Bool.not_false] at this
              simp [this] at hsome
            have hC := feedFrom_end v C.concrete input hFs (q := ⟨.fraction (false || decide
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) Lexer.CharClass.RUN_DIGIT + 1 <
                  Lexer.Internal.WRustPort.Slice.runEnd input
                    (Lexer.Internal.WRustPort.Slice.runEnd input
                        (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                    Lexer.CharClass.RUN_DIGIT)), location, bytesOf input index
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (Lexer.Internal.WRustPort.Slice.runEnd input
                        (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                  Lexer.CharClass.RUN_DIGIT)⟩)
              (location := afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) Lexer.CharClass.RUN_DIGIT + 1) Lexer.CharClass.RUN_DIGIT - index))
              (advance_end_fraction (by simp [hlt]) hstopF')
            rw [← hB] at hC
            rw [get_eq hFs]
            apply WP.wp_ite
            · intro hnd
              have hnd' : Lexer.Internal.VNaive.isDelimiter
                  input[Lexer.Internal.WRustPort.Slice.runEnd input
                  (Lexer.Internal.WRustPort.Slice.runEnd input
                      (index + 1) Lexer.CharClass.RUN_DIGIT + 1) Lexer.CharClass.RUN_DIGIT] =
                  false := by
                rw [← isDelimiter_eq]; simpa using hnd
              rw [hnd'] at hC
              unfold Lexer.Internal.WRustPort.leave Lexer.Internal.WRustPort.errorAt
                  Lexer.Internal.WRustPort.errorWith
              wp_walk
              refine stepFails_here ?_ hheld
                ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
              rw [hC]
              simp only [Bool.false_eq_true, ↓reduceIte]
            · intro hd'
              have hd'' : Lexer.Internal.VNaive.isDelimiter
                  input[Lexer.Internal.WRustPort.Slice.runEnd input
                  (Lexer.Internal.WRustPort.Slice.runEnd input
                      (index + 1) Lexer.CharClass.RUN_DIGIT + 1) Lexer.CharClass.RUN_DIGIT] =
                  true := by
                rw [← isDelimiter_eq]; simpa using hd'
              rw [hd''] at hC
              simp only [↓reduceIte] at hC
              borrow_push Token.TokenCategory.decimal index
                  (Lexer.Internal.WRustPort.Slice.runEnd input
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) Lexer.CharClass.RUN_DIGIT + 1) Lexer.CharClass.RUN_DIGIT)
      · -- the numeral ends before the byte
        intro hdot
        have hdot' : next ≠ 46 := by simpa using hdot
        have hC := feedFrom_end v C.concrete input hEs (q := ⟨.numeral (c == 48), location,
            bytesOf input index (Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) Lexer.CharClass.RUN_DIGIT)⟩)
          (location := afterColumns location
            (Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1) Lexer.CharClass.RUN_DIGIT - index))
          (advance_end_numeral rfl (by rw [hEc]; exact hEd) (by rw [hEc]; exact hdot'))
        rw [← hA, hEc] at hC
        apply WP.wp_ite
        · intro hnd
          have hnd' : Lexer.Internal.VNaive.isDelimiter next = false := by
            rw [← isDelimiter_eq]; simpa using hnd
          rw [hnd'] at hC
          unfold Lexer.Internal.WRustPort.leave Lexer.Internal.WRustPort.errorAt
              Lexer.Internal.WRustPort.errorWith
          wp_walk
          refine stepFails_here ?_ hheld
            ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
          rw [hC]
          simp only [Bool.false_eq_true, ↓reduceIte]
        · intro hd'
          have hd'' : Lexer.Internal.VNaive.isDelimiter next = true := by
            rw [← isDelimiter_eq]; simpa using hd'
          rw [hd''] at hC
          simp only [↓reduceIte] at hC
          borrow_push Token.TokenCategory.numeral index
            (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT)
    · -- the digits run to the end of the slice: the numeral is left in progress
      rename_i hgetE
      have hsz := Lexer.Internal.WRustPort.Slice.size_le_of_get?_none hgetE
      have hzero : (c == 48) = ((bytesOf input index
          (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT)).size
              == 1 &&
          (bytesOf input index (Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1) Lexer.CharClass.RUN_DIGIT)).get! 0 ==
            48) := by
        rw [bytesOf_size input (by omega) hle',
          bytesOf_get! input (by omega) hle' (k := 0) (by omega)]
        simp only [Nat.add_zero, hc]
        by_cases hz0 : c = 48
        · have he := hz' hz0
          simp [hz0, he]
        · simp [hz0]
      unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
        Lexer.Internal.WRustPort.leavePending
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_bind; apply WP.wp_modifyBound
      apply WP.wp_pure
      refine ⟨.token ⟨.numeral (c == 48), location, bytesOf input index
          (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1) Lexer.CharClass.RUN_DIGIT)⟩,
        afterColumns location
          (Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1) Lexer.CharClass.RUN_DIGIT - index),
        held, ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_,
            hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [locAt_eq hloc]; rfl
        · rw [contentBytes_clear_extendSlice _ _ ?_]
          · exact congrArg Mode.numeral hzero
          · bound_tac
        · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
        · rw [contentBytes_clear_extendSlice _ _ ?_, show ∀ a b, (input.slice a b).toByteArray =
            bytesOf input a b from fun _ _ => rfl, bytesOf_size input (by omega) hle']
          · omega
          · bound_tac
        · fits_tac
      · dsimp only [LocAt, afterColumns, Past.from]
        refine ⟨?_, ?_, ?_⟩ <;> omega
      · rw [hA]; rfl

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Digits
