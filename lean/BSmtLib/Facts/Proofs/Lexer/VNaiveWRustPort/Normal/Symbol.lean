module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
import all BSmtLib.Lexer.Internal.Helpers
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The normal state on a simple symbol

The step of the Rust port's normal state at a simple symbol that does not start with a digit,
on the fast path.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Symbol

open BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
open BSmtLib.Lexer.Internal (CharClass)
open BSmtLib.Lexer.Internal.WRustPort (lexNormalFrom FastState Frame Held Past)
open BSmtLib.Lexer.Internal.WRustPort.Slice (get? get)
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Push
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Runs
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.StartWs
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Delimiters
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.FastRuns BSmtLib.Lexer.Internal.VNaive

section

variable {floor : Option Nat} {low : Nat}

variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Token.Version}

/-- `normalSpec_lt` at a simple symbol that does not start with a digit, on the fast path. -/
theorem normalSpec_symbol (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) (n index : Nat)
    (ih : ∀ index, input.size - index < n → NormalSpec C v hd iv input offset base hframe index)
    (hn : input.size - index < n + 1)
    {c₀ : UInt8} (hget₀ : get? input index = some c₀) (hc40₀ : c₀ ≠ 40) (hc41₀ : c₀ ≠ 41)
    (hf : Lexer.Internal.Helpers.fastFlags c₀ = Lexer.Internal.Helpers.FAST_ON |||
        Lexer.Internal.Helpers.FAST_EMIT |||
    CharClass.RUN_SIMPLE_SYMBOL)
    (hsym : isSymbolByte c₀ = true) (hdig : isDigit c₀ = false) :
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
    · -- a simple symbol that does not start with a digit
      have hnw : (Lexer.Internal.Helpers.fastFlags c &&&
          CharClass.RUN_NON_LF_WHITESPACE != 0) = false
          := by
        rw [hf]; decide
      simp only [answering_concrete, hnw, Bool.and_false, Bool.false_and,
          Bool.false_eq_true, dite_false,
        Bool.or_false, ite_self]
      have hpipeb : (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_PIPE !=
          0) = false
          := by rw [hf]; decide
      have hemit : (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_EMIT !=
          0) = true
          := by rw [hf]; decide
      have hsymb : (Lexer.Internal.Helpers.fastFlags c &&&
          CharClass.RUN_SIMPLE_SYMBOL != 0) = true :=
          by
        rw [hf]; decide
      have hmask : Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_RUN_MASK =
          CharClass.RUN_SIMPLE_SYMBOL := by
        rw [hf]; decide
      have hj : Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
          (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_RUN_MASK) =
          runEnd input isSymbolByte (index + 1) := by
        rw [hmask, runEnd_eq endsRun_symbol]
      have hle := le_runEnd input isSymbolByte (index + 1)
      have hle' := runEnd_le input isSymbolByte (index + 1) hi
      have hstop := fun h => runEnd_stop input isSymbolByte (index + 1) h
      have hA : feedFrom v C.concrete input .idle location index =
          feedFrom v C.concrete input
            (.token ⟨.simpleSymbol, location,
              bytesOf input index (runEnd input isSymbolByte (index + 1))⟩)
            (afterColumns location (runEnd input isSymbolByte (index + 1) - index))
            (runEnd input isSymbolByte (index + 1)) := by
        rw [feedFrom_startRun v C.concrete input isSymbolByte isSymbolByte_ne .simpleSymbol
          (fun q l c hm hc => advance_simpleSymbol_run C.concrete q l c hm hc) hi
          (q := ⟨.simpleSymbol, location, ByteArray.empty.push input[index]⟩)
          (by rw [hc]; exact start_symbol _ _ _ _ hsym hdig) rfl
          (by rw [hc]; exact isSymbolByte_ne _ hsym)]
        simp only
        rw [push_append_bytesOf _ input hi (by omega) hle', empty_append]
      rw [← hj] at hA hle hle' hstop
      apply WP.wp_dite
      · -- the symbol runs to the end of the slice: it is left in progress
        intro h
        have hsz : Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
            (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_RUN_MASK)
                = input.size := by
          simp only [hpipeb, hsymb, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
            Bool.and_true, beq_iff_eq] at h
          exact h
        obtain ⟨hl1, hl2, hl3⟩ := id hloc
        rw [WP.rust_storeLocals]
        unfold FastState.store Lexer.Internal.WRustPort.storeUnfinishedSymbolRun
            Lexer.Internal.WRustPort.startToken
          Lexer.Internal.WRustPort.extendContent Lexer.Internal.WRustPort.modifyContent
              Lexer.Internal.WRustPort.leavePending
        apply WP.wp_bind; apply WP.wp_modifyCore
        apply WP.wp_bind
        apply WP.wp_bind
        apply WP.wp_bind; apply WP.wp_getCore
        apply WP.wp_bind; apply WP.wp_modifyCore
        apply WP.wp_bind; apply WP.wp_modifyCore
        apply WP.wp_pure
        dsimp only
        apply WP.wp_ite
        · intro h'; rw [hpipeb] at h'; exact absurd h' (by decide)
        · intro _
          apply WP.wp_bind; apply WP.wp_modifyCore
          apply WP.wp_modifyBound
          apply WP.wp_pure
          refine ⟨.token ⟨.simpleSymbol, location, bytesOf input index
              (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                  (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_RUN_MASK))⟩,
            afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
              (Lexer.Internal.Helpers.fastFlags c &&&
                  Lexer.Internal.Helpers.FAST_RUN_MASK) - index), held,
            ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, Nat.le_refl _, ?_, ?_,
                hheld, hbytes, ?_⟩
          · dsimp only [StAgrees, TokenAgrees, TokenAgreesNoWs]
            refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
            · rw [locAt_eq hloc, hline, hlineStart]; rfl
            · exact (contentBytes_clear_extendSlice _ _ (by bound_tac)).symm
            · fits_tac
          · simp only [LocAt, afterColumns, Past.from, Span.Location.Internal.offset_new,
              Span.Location.Internal.line_new, Span.Location.Internal.column_new]
            refine ⟨?_, ?_, ?_⟩ <;> omega
          · rw [hA]; rfl
      · -- the symbol ends inside the slice
        intro h
        have hJ : Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
            (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_RUN_MASK)
                < input.size := by
          simp only [hpipeb, hsymb, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
            Bool.and_true, beq_iff_eq] at h
          omega
        have hJs := hstop hJ
        have hidx : (if (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_PIPE != 0) = true then
            Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_RUN_MASK) + 1
          else Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
              (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_RUN_MASK)) =
            Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_RUN_MASK) := by
          simp only [hpipeb, Bool.false_eq_true, ↓reduceIte]
        have hC := feedFrom_end v C.concrete input hJ (q := ⟨.simpleSymbol, location,
            bytesOf input index
              (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                  (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_RUN_MASK))⟩)
          (location := afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input
              (index + 1)
            (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_RUN_MASK) - index))
          (advance_end_simpleSymbol rfl hJs)
        rw [← hA] at hC
        apply WP.wp_ite
        · intro _
          split
          · rename_i next heq
            simp only [hpipeb, Bool.false_eq_true, ↓reduceIte] at heq
            obtain ⟨hJ1, hJ1c⟩ := get?_eq heq
            rw [hJ1c] at hC
            apply WP.wp_ite
            · intro hnd
              have hnd' : Lexer.Internal.VNaive.isDelimiter next = false := by
                rw [← isDelimiter_eq]; simpa using hnd
              rw [hnd'] at hC
              rw [WP.rust_storeLocals]
              unfold FastState.store Lexer.Internal.WRustPort.leave
                  Lexer.Internal.WRustPort.startToken
                Lexer.Internal.WRustPort.modifyContent Lexer.Internal.WRustPort.errorAt
                    Lexer.Internal.WRustPort.errorWith
              wp_walk
              refine stepFails_here ?_ hheld
                ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩ rfl
              rw [hC]
              simp only [Bool.false_eq_true, ↓reduceIte]
              failure_eq hloc
            · intro hdl
              have hd' : Lexer.Internal.VNaive.isDelimiter next = true := by
                rw [← isDelimiter_eq]; simpa using hdl
              rw [hd'] at hC
              simp only [↓reduceIte] at hC
              have hlex : (if (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_EMIT != 0) = true
                  then
                  [onLine (if (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_PIPE != 0) = true
                      then
                      Token.TokenCategory.quotedSymbol
                    else Token.TokenCategory.unquotedSymbol)
                    (input.slice (if (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_PIPE != 0) =
                        true then index
                        + 1
                      else index)
                      (if (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_PIPE != 0) = true then
                        Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                            (Lexer.Internal.Helpers.fastFlags c &&&
                            Lexer.Internal.Helpers.FAST_RUN_MASK)
                      else if (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_PIPE != 0) = true
                          then
                        Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                          (Lexer.Internal.Helpers.fastFlags c &&&
                              Lexer.Internal.Helpers.FAST_RUN_MASK) + 1
                      else Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                        (Lexer.Internal.Helpers.fastFlags c &&&
                            Lexer.Internal.Helpers.FAST_RUN_MASK)))
                    locals.line locals.lineStart (offset + (index - base))
                    (offset + ((if (Lexer.Internal.Helpers.fastFlags c &&& Lexer.Internal.Helpers.FAST_PIPE != 0) =
                        true then
                      Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                        (Lexer.Internal.Helpers.fastFlags c &&&
                            Lexer.Internal.Helpers.FAST_RUN_MASK) + 1
                      else Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                        (Lexer.Internal.Helpers.fastFlags c &&&
                            Lexer.Internal.Helpers.FAST_RUN_MASK)) - base))]
                  else []) =
                  [⟨.unquotedSymbol, bytesOf input index
                      (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                      (Lexer.Internal.Helpers.fastFlags c &&&
                          Lexer.Internal.Helpers.FAST_RUN_MASK)), location,
                    afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                      (Lexer.Internal.Helpers.fastFlags c &&&
                          Lexer.Internal.Helpers.FAST_RUN_MASK) - index)⟩] := by
                simp only [hpipeb, hemit, Bool.false_eq_true, ↓reduceIte]
                rw [hline, hlineStart, onLine_eq hloc hindex (by omega)]
                rfl
              apply WP.wp_bind
              refine pushFast_wp input batch locals offset base _ _ _ index _ _ _ hindex _ hframe
                hbatch held hheld hbytes.symm ?_ ?_ s coll hfix.recovers
                ?_ ?_
              · simp only [hpipeb, Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [hpipeb, Bool.false_eq_true, ↓reduceIte]; omega
              · intro r s' coll' held' hH hb hk hp
                rw [hfix.holding] at hp
                simp only [hnw, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hp
                rw [hlex] at hp
                obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
                refine wp_recurse (f := fun (r : Past input origin) => r.1)
                  (ih _ (by rw [hidx]; omega) r.val locals _ r.property origin _ s' coll' held'
                    (afterColumns location (Lexer.Internal.WRustPort.Slice.runEnd input (index + 1)
                      (Lexer.Internal.Helpers.fastFlags c &&&
                          Lexer.Internal.Helpers.FAST_RUN_MASK) - index))
                    (fixed_of_key hfix hk) (hoff.trans k8.symm) (hbase.trans k9.symm)
                    (hline.trans k10.symm) (hlineStart.trans k11.symm) (k2.trans hnormal)
                    (by rw [hidx]; exact (hloc.afterColumns hindex (by omega)).congr k10 k11) hH
                    (hb.trans hbytes)) ?_
                rw [hidx, hC, outcome_pending_prep, outcome_pending_congr hp]
              · intro e s' p d hn hss
                simp only [hnw, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hn
                rw [hlex] at hn
                exact stepFails_of_stops' hss ⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩
                  ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn
          · rename_i heq
            simp only [hpipeb, Bool.false_eq_true, ↓reduceIte] at heq
            have := Lexer.Internal.WRustPort.Slice.size_le_of_get?_none heq
            omega
        · intro h'; rw [hemit] at h'; exact absurd rfl h'
  intro hslow
  exact absurd (by rw [hf]; decide) hslow

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Symbol
