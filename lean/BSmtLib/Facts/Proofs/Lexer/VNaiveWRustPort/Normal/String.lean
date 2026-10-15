module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# The normal state on a string literal

The step of the Rust port's normal state at the quote that starts a string literal.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.String

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
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.StartLiterals
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.TextRuns BSmtLib.Lexer.Internal.VNaive

section

variable {floor : Option Nat} {low : Nat}

variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Token.Version}

set_option hygiene false in
/-- A string left in progress at the end of its run, in the proof of `normalSpec_lt`. -/
local macro "string_stay" : tactic => `(tactic| (
  unfold Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
      Lexer.Internal.WRustPort.leavePending
  apply WP.wp_bind; apply WP.wp_modifyCore
  apply WP.wp_bind; apply WP.wp_modifyBound
  apply WP.wp_pure
  refine ⟨.token ⟨.string, location, bytesOf input (index + 1)
      (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1) CharClass.RUN_STRING_PLAIN)⟩,
    afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
      CharClass.RUN_STRING_PLAIN - index), held,
          ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩,
    Nat.le_refl _,
    ?_, ?_, hheld, hbytes, ?_⟩
  · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
    refine ⟨⟨?_, by simp [hv2'], ?_⟩, ?_⟩
    · rw [locAt_eq hloc]; rfl
    · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
    · fits_tac
  · dsimp only [LocAt, afterColumns, Past.from]
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · rw [hA]; rfl))

/-- `normalSpec_lt` at the quote that starts a string literal. -/
theorem normalSpec_string (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (n index : Nat)
    (ih : ∀ index, input.size - index < n → NormalSpec C v hd iv input offset base hframe index)
    (hn : input.size - index < n + 1)
    {c₀ : UInt8} (hget₀ : get? input index = some c₀) (hc40₀ : c₀ ≠ 40) (hc41₀ : c₀ ≠ 41)
    (hfoff₀ : (Lexer.Internal.Helpers.fastFlags c₀ &&& Lexer.Internal.Helpers.FAST_ON != 0) = false)
    (hst₀ : Lexer.Internal.Helpers.startOf c₀ = .quote) :
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
  · -- a quote: a string literal
    rename_i hst
    have h34 := startOf_quote hst
    unfold Lexer.Internal.WRustPort.startToken Lexer.Internal.WRustPort.modifyContent
    apply WP.wp_bind
    apply WP.wp_bind; apply WP.wp_getCore
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_pure
    apply WP.wp_bind; apply WP.wp_getCore
    have hq : feedFrom v C.concrete input .idle location index =
        feedFrom v C.concrete input
          (.token ⟨if v == .v2_0 then .legacyString else .string, location, .empty⟩)
          (location.afterByte 34) (index + 1) := by
      rw [feedFrom_step hi (byteStep_idle_pending v C.concrete (by rw [hc, h34]; rfl)),
          prep_nil, hc, h34]
    apply WP.wp_ite
    · -- under version 2.0 the string is left in progress at once
      intro hv2
      unfold Lexer.Internal.WRustPort.leavePending
      apply WP.wp_bind; apply WP.wp_modifyBound
      apply WP.wp_pure
      refine ⟨.token ⟨if v == .v2_0 then .legacyString else .string, location, .empty⟩,
        location.afterByte 34, held, ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5,
            hfix.6⟩, Nat.le_refl _,
        ?_, ?_,
        hheld, hbytes, ?_⟩
      · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
        refine ⟨⟨?_, rfl, (contentBytes_clear _).symm⟩, ?_⟩
        rw [locAt_eq hloc]; rfl
        · fits_tac
      · have := hloc.afterByte hindex (b := 34) (by decide)
        obtain ⟨h1, h2, h3⟩ := this
        dsimp only [LocAt, Past.from]
        refine ⟨?_, h2, h3⟩
        omega
      · rw [hq]; rfl
    · intro hv2
      have hv2' : (v == .v2_0) = false := by
        have : (s.val.version == .v2_0) = false := by simpa using hv2
        rw [← hfix.version]; exact this
      have hS : Lexer.Internal.WRustPort.Slice.runEnd input
          (index + 1) CharClass.RUN_STRING_PLAIN =
          runEnd input isStringRun (index + 1) := runEnd_eq endsRun_string _ _
      have hle := le_runEnd input isStringRun (index + 1)
      have hle' := runEnd_le input isStringRun (index + 1) hi
      have hstop := fun h => runEnd_stop input isStringRun (index + 1) h
      have hA : feedFrom v C.concrete input .idle location index =
          feedFrom v C.concrete input
            (.token ⟨.string, location,
              bytesOf input (index + 1) (runEnd input isStringRun (index + 1))⟩)
            (afterColumns location (runEnd input isStringRun (index + 1) - index))
            (runEnd input isStringRun (index + 1)) := by
        rw [feedFrom_startRun v C.concrete input isStringRun isStringRun_ne .string
          (fun q l c hm hc => advance_string_run C.concrete q l c hm hc) hi
          (q := ⟨.string, location, .empty⟩)
          (by
            rw [hc, h34]
            show start v false location 34 = _
            simp [start, hv2', show isWhitespace 34 = false from rfl]) rfl
          (by rw [hc, h34]; decide)]
        simp only [empty_append]
      rw [← hS] at hA hle hle' hstop
      split
      · rename_i quote next hwq hwn
        apply WP.wp_ite
        · -- closed by a quote that no quote follows
          intro hclose
          simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hclose
          obtain ⟨hq34, hn34⟩ := hclose
          obtain ⟨hA1, hAc⟩ := get?_eq hwq
          obtain ⟨hA2, hA2c⟩ := get?_eq hwn
          have hB : feedFrom v C.concrete input .idle location index =
              feedFrom v C.concrete input
                (.token ⟨.stringQuote, location, bytesOf input (index + 1)
                  (Lexer.Internal.WRustPort.Slice.runEnd input
                      (index + 1) CharClass.RUN_STRING_PLAIN)⟩)
                (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                  CharClass.RUN_STRING_PLAIN + 1 - index))
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) CharClass.RUN_STRING_PLAIN + 1) := by
            rw [hA, feedFrom_step hA1 (byteStep_token_pending v C.concrete
                (by rw [hAc, hq34]; rfl)),
              prep_nil, afterByte_eq_afterColumns' _ _ (by rw [hAc, hq34]; decide),
              afterColumns_add]
            congr 2
            omega
          have hC := feedFrom_end v C.concrete input hA2 (q := ⟨.stringQuote, location,
              bytesOf input (index + 1)
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) CharClass.RUN_STRING_PLAIN)⟩)
            (location := afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input
                (index + 1)
              CharClass.RUN_STRING_PLAIN + 1 - index))
            (advance_end_stringQuote rfl (by rw [hA2c]; exact hn34))
          rw [← hB, hA2c] at hC
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
          · intro hdl
            have hd' : Lexer.Internal.VNaive.isDelimiter next = true := by
              rw [← isDelimiter_eq]; simpa using hdl
            rw [hd'] at hC
            simp only [↓reduceIte] at hC
            have hlex := borrowedLexeme_eq hloc hindex
              (j := Lexer.Internal.WRustPort.Slice.runEnd input
                  (index + 1) CharClass.RUN_STRING_PLAIN + 1) (by omega)
              .string (input.slice (index + 1)
                (Lexer.Internal.WRustPort.Slice.runEnd input
                    (index + 1) CharClass.RUN_STRING_PLAIN))
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
                  [⟨.string, bytesOf input (index + 1)
                    (Lexer.Internal.WRustPort.Slice.runEnd input
                        (index + 1) CharClass.RUN_STRING_PLAIN), location,
                    afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                      CharClass.RUN_STRING_PLAIN + 1 - index)⟩]) :=
                hp.trans (congrArg (fun l => pending C hd s.val.version coll (held ++ [l])) hlex)
              obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
              rw [WP.rust_loadLocals]
              unfold FastState.load
              apply WP.wp_bind; apply WP.wp_bind; apply WP.wp_getCore; apply WP.wp_pure
              refine wp_recurse (f := fun (r : Past input origin) => r.1)
                (ih _ (by omega) r.val _ _ r.property origin _ s' coll' held'
                  (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                    CharClass.RUN_STRING_PLAIN + 1 - index))
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
        · intro _
          string_stay
      · string_stay

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.String
