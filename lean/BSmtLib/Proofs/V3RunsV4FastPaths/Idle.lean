import BSmtLib.Proofs.V3RunsV4FastPaths.Loops

/-!
# The idle steps

The idle step with fast paths, `V4FastPaths.lexIdle`, followed by the lexer over runs' loop,
agrees with the lexer over runs' idle step `V3Runs.lexIdle` followed by the same loop
(`lexIdle_agrees`), case by case over the fast paths.
-/

namespace BSmtLib.Proofs.Lexer.V3RunsV4FastPaths

open V1Naive V2Batched V3Runs V2BatchedV3Runs

theorem afterByte_of_ne (location : Location) (c : UInt8) (h : c ≠ 10) :
    location.afterByte c = location.afterColumn := by
  unfold Location.afterByte
  split
  · rename_i hc
    exact absurd (beq_iff_eq.mp hc) h
  · rfl

theorem get?_pos (s : ByteSlice) (j : Nat) (h : j < s.size) : s[j]? = some s[j] := by
  simp [h]

theorem get?_neg (s : ByteSlice) (j : Nat) (h : ¬ j < s.size) : s[j]? = none := by
  simp [h]

theorem space_facts_bool (c : UInt8) :
    (!isWhitespaceRun c || (!isSymbolByte c && c != 124)) = true :=
  byte_cases (P := fun c => (!isWhitespaceRun c || (!isSymbolByte c && c != 124)) = true)
    (by decide +kernel) c

theorem space_not_symbol (c : UInt8) (h : isWhitespaceRun c = true) : isSymbolByte c = false := by
  have := space_facts_bool c
  simp_all

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

theorem lexIdle_agrees [LawfulMonad m] (recover : Location → StateT H m Unit)
    (sliceStart : Nat) (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R))
    (i : Nat) (hi : i < slice.size) (core : Core) (batch : Array Lexeme)
    (hfits : Fits core batch) :
    erase <$> (do
      let ⟨(outcome, core, batch, ⟨next, _⟩), hfits⟩ ←
        V3Runs.lexIdle sliceStart slice i hi core batch hfits
      cont (loop3 V3Runs.lexIdle recover sliceStart slice) sliceStart slice committed flow
        outcome core batch next hfits) =
    erase <$> (do
      let ⟨(outcome, core, batch, ⟨next, _⟩), hfits⟩ ←
        V4FastPaths.lexIdle sliceStart slice i hi core batch hfits
      cont (loop3 V3Runs.lexIdle recover sliceStart slice) sliceStart slice committed flow
        outcome core batch next hfits) := by
  simp only [V4FastPaths.lexIdle]
  by_cases hp : (slice[i] == 41 || slice[i] == 40) = true
  · simp only [hp, ite_true]
    have hnl : slice[i] ≠ 10 := by
      intro h; rw [h] at hp; exact absurd hp (by decide)
    simp only [V3Runs.lexIdle, startS, start_paren _ _ _ _ hp, bind_assoc]
    refine congrArg (erase <$> ·) (emit_bind_congr ?_ rfl ?_)
    · rw [afterByte_of_ne _ _ hnl]
    · intro o c b _ _ _ _
      simp only [pure_bind]
  · simp only [hp, Bool.false_eq_true, ite_false]
    by_cases hq : slice[i] = 124
    · have hs : isWhitespaceRun slice[i] = false := by rw [hq]; rfl
      simp only [hq, show ((124 : UInt8) == 124) = true from rfl, ite_true, Bool.true_or,
        Bool.not_true, Bool.false_eq_true, ite_false, Bool.false_and, Bool.and_false,
        Bool.or_false, show isWhitespaceRun 124 = false from rfl, Bool.true_and, Bool.not_false]
      by_cases hj : runEnd slice isQuotedRun (i + 1) < slice.size
      · simp only [get?_pos slice _ hj]
        by_cases hc : slice[runEnd slice isQuotedRun (i + 1)] = 124
        · simp only [hc, show (some (124 : UInt8) != some 124) = false from rfl,
            Bool.false_eq_true, ite_false]
          simp only [V3Runs.lexIdle, startS, runS, hq, start_quoted,
            run_quoted_closed _ slice i core.location _ rfl hj hc]
          have hle := le_runEnd slice isQuotedRun (i + 1)
          by_cases h1 : runEnd slice isQuotedRun (i + 1) + 1 < slice.size
          · simp only [get?_pos slice _ h1, h1, dite_true]
            by_cases hd : isDelimiter slice[runEnd slice isQuotedRun (i + 1) + 1] = true
            · simp only [hd, ite_true, Bool.not_true, Bool.false_eq_true, ite_false, bind_assoc]
              refine congrArg (erase <$> ·) (emit_bind_congr ?_ ?_ ?_)
              · simp only [hq, show ((124 : UInt8) == 124) = true from rfl, ite_true]
              · simp only [hq, show ((124 : UInt8) == 124) = true from rfl, ite_true]
              · intro o c b _ _ _ _
                simp only [pure_bind]
            · simp only [hd, Bool.false_eq_true, ite_false, Bool.not_false, ite_true, pure_bind]
              exact cont_failed _ _ _ _ _ _ rfl _ _ _ _ _
          · simp only [get?_neg slice _ h1, h1, dite_false, pure_bind, cont_next]
            have : runEnd slice isQuotedRun (i + 1) + 1 = slice.size := by omega
            exact congrArg (erase <$> ·) (loop3_congr this.symm rfl)
        · have : (some slice[runEnd slice isQuotedRun (i + 1)] != some (124 : UInt8)) = true := by
            simp [hc]
          simp only [this, ite_true]
      · simp only [get?_neg slice _ hj, show ((none : Option UInt8) != some 124) = true from rfl,
          ite_true]
    · have hq' : (slice[i] == 124) = false := by simpa using hq
      by_cases hsp : isWhitespaceRun slice[i] = true
      · have hsym : isSymbolByte slice[i] = false := space_not_symbol _ hsp
        have hnl : slice[i] ≠ 10 := isWhitespaceRun_ne _ hsp
        simp only [hq', hsp, hsym, Bool.false_or, Bool.true_or, Bool.not_true, Bool.false_eq_true,
          ite_false, ite_true, Bool.false_and, Bool.and_true, Bool.true_and, Bool.not_false]
        have hle := le_runEnd slice isWhitespaceRun (i + 1)
        cases hws : Consume.consumesWhitespaceAndComments (H := H) with
        | false =>
          simp only [Bool.false_and, Bool.false_eq_true, ite_false, Bool.not_false, ite_true,
            Nat.add_zero, pure_bind, cont_next]
          simp only [V3Runs.lexIdle, startS, start_space _ _ _ _ hsp, hws,
            Bool.false_eq_true, ite_false, pure_bind, cont_next]
          rw [loop3_skip recover sliceStart slice committed batch flow hws _ (i + 1) rfl (by omega)
            { core with
              activity := .idle, location := core.location.afterByte slice[i]
              startedBefore := trivial } rfl _
            (fits_idle hfits _ (show core.location.offset ≤
              (afterColumns (core.location.afterByte slice[i]) _).offset by
                rw [afterColumns_offset, afterByte_offset]; omega))]
          refine congrArg (erase <$> ·) (loop3_congr rfl ?_)
          congr 1
          rw [afterColumns_afterByte _ _ hnl]
          congr 1
          omega
        | true =>
          simp only [Bool.true_and, Bool.not_true, Bool.false_eq_true, ite_false]
          by_cases hj : runEnd slice isWhitespaceRun (i + 1) < slice.size
          · simp only [get?_pos slice _ hj]
            by_cases hn : slice[runEnd slice isWhitespaceRun (i + 1)] = 10
            · have : (some slice[runEnd slice isWhitespaceRun (i + 1)] == none ||
                  some slice[runEnd slice isWhitespaceRun (i + 1)] == some (10 : UInt8)) =
                  true := by
                simp [hn]
              simp only [this, ite_true]
            · have : (some slice[runEnd slice isWhitespaceRun (i + 1)] == none ||
                  some slice[runEnd slice isWhitespaceRun (i + 1)] == some (10 : UInt8)) =
                  false := by
                simp [hn]
              simp only [this, Bool.false_eq_true, ite_false, Nat.add_zero]
              simp only [V3Runs.lexIdle, startS, runS, start_space _ _ _ _ hsp, hws, ite_true,
                run_space_inside _ slice i core.location _ hnl _ rfl hj hn, Ran.lift, bind_assoc]
              refine congrArg (erase <$> ·) (emit_bind_congr ?_ ?_ ?_)
              · simp only [hq', hsp, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
              · rw [push_append_bytesOf .empty slice hi (by omega) (Nat.le_of_lt hj), empty_append]
                simp only [hq', hsp, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
              · intro o c b _ _ _ _
                simp only [pure_bind]
          · simp only [get?_neg slice _ hj,
              show ((none : Option UInt8) == none || (none : Option UInt8) == some 10) = true
                from rfl, ite_true]
      · have hsp' : isWhitespaceRun slice[i] = false := by simpa using hsp
        simp only [hq', hsp', Bool.false_or, Bool.not_false, Bool.false_eq_true, ite_false,
          Bool.and_false, Bool.false_and, Bool.true_and, Bool.not_false]
        by_cases hsym : (isSymbolByte slice[i] && !isDigit slice[i]) = true
        · have hs1 : isSymbolByte slice[i] = true := by simp_all
          have hd1 : isDigit slice[i] = false := by simp_all
          have hnl : slice[i] ≠ 10 := isSymbolByte_ne _ hs1
          simp only [hsym, Bool.not_true, Bool.false_eq_true, ite_false]
          have hle := le_runEnd slice isSymbolByte (i + 1)
          by_cases hj : runEnd slice isSymbolByte (i + 1) < slice.size
          · simp only [get?_pos slice _ hj, Nat.add_zero,
              show (some slice[runEnd slice isSymbolByte (i + 1)] == none) = false from rfl,
              Bool.false_eq_true, ite_false, ite_true]
            simp only [V3Runs.lexIdle, startS, runS, start_symbol _ _ _ _ hs1 hd1,
              run_symbol_inside _ slice i core.location _ hnl _ rfl hj]
            by_cases hd : isDelimiter slice[runEnd slice isSymbolByte (i + 1)] = true
            · simp only [hd, ite_true, Ran.lift, Bool.not_true, Bool.false_eq_true, ite_false,
                bind_assoc]
              refine congrArg (erase <$> ·) (emit_bind_congr ?_ ?_ ?_)
              · simp only [hq', hsp', Bool.false_eq_true, ite_false, Nat.add_zero]
              · rw [push_append_bytesOf .empty slice hi (by omega) (Nat.le_of_lt hj), empty_append]
                simp only [hq', hsp', Bool.false_eq_true, ite_false, Nat.add_zero]
              · intro o c b _ _ _ _
                simp only [pure_bind]
            · simp only [hd, Bool.false_eq_true, ite_false, Ran.lift, Bool.not_false, ite_true,
                pure_bind]
              exact cont_failed _ _ _ _ _ _ rfl _ _ _ _ _
          · simp only [get?_neg slice _ hj, show ((none : Option UInt8) == none) = true from rfl,
              ite_true]
        · simp only [hsym, Bool.not_false, ite_true]

end

end BSmtLib.Proofs.Lexer.V3RunsV4FastPaths
