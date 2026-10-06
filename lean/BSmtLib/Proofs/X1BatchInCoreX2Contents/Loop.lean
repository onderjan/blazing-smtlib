import BSmtLib.Proofs.X1BatchInCoreX2Contents.Normal

/-!
# The loop of the normal state, in both lexers

The loop of the normal state (`lexNormalFrom`) is the same code in both lexers but for the
contents of the tokens it lexes from the slice. It is simulated by induction on the bytes left
after its index, branch by branch: each branch of one lexer is split, then the same branch
of the other, and the branches that do not match are dismissed.
-/

namespace BSmtLib.Proofs.X1BatchInCoreX2Contents

open BSmtLib.Proofs.Simulation

theorem ite_slice (q : Prop) [Decidable q] (input : ByteSlice) (a b c d : Nat) :
    (if q then input.slice a b else input.slice c d) =
      input.slice (if q then a else c) (if q then b else d) := by
  split <;> rfl

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} (hblind : ContentBlind H m R E)
include hblind

theorem lexNormalFrom_sim (input : ByteSlice) (offset base : Nat) (origin : Nat) :
    ∀ k (index : Nat) (batch : TokenBatch), input.size - index = k →
      ∀ hframe hframe' hindex hindex' hbatch hbatch' horigin horigin',
      SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
        (Lexer.X2Contents.lexNormalFrom (H := H) (m := m) (R := R) (E := E) input offset base
          index batch hframe hindex hbatch origin horigin)
        (Lexer.X1BatchInCore.lexNormalFrom input offset base index batch hframe' hindex' hbatch'
          origin horigin') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro index batch hk hframe hframe' hindex hindex' hbatch hbatch' horigin horigin'
  -- the second lexer's match first, as the first lexer's branches start with a `have`
  rw [Lexer.X1BatchInCore.lexNormalFrom]
  split
  · rename_i hget'
    rw [Lexer.X2Contents.lexNormalFrom]
    split
    · refine SimF.seq (leave_sim _ _ _ _ _ _ _ _) fun _ => ?_
      exact SimF.pure (fun _ h => h) rfl
    · rename_i c hget
      exact absurd (hget'.symm.trans hget) (by simp)
  · rename_i c hget'
    rw [Lexer.X2Contents.lexNormalFrom]
    split
    · rename_i hget
      exact absurd (hget.symm.trans hget') (by simp)
    rename_i c' hget
    obtain rfl : c' = c := Option.some.inj (hget.symm.trans hget')
    have hlt := Lexer.Slice.lt_size_of_get? hget
    have hafter : index + 1 ≤ input.size := hlt
    refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · -- a closing parenthesis
      refine getCore_bind fun _ _ => ?_
      refine SimF.ite Iff.rfl
        (fun _ => SimF.bind (modifyCore_same (fun _ => rfl) fun _ => rfl) fun _ => ?_)
        fun _ => ?_
      all_goals
        refine SimF.bind (pushFast_sim hblind input batch offset base _ index (index + 1) index
          (index + 1) true (Nat.le_succ _) hafter _ _ _ _ _ _ _ _ _ _) fun x => ?_
        obtain ⟨b, hb⟩ := x
        exact ih _ (by omega) _ _ rfl _ _ _ _ _ _ _ _
    refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · -- an opening parenthesis
      refine getCore_bind fun _ _ => ?_
      refine SimF.ite Iff.rfl
        (fun _ => SimF.bind (modifyCore_same (fun _ => rfl) fun _ => rfl) fun _ => ?_)
        fun _ => ?_
      all_goals
        refine SimF.bind (pushFast_sim hblind input batch offset base _ index (index + 1) index
          (index + 1) true (Nat.le_succ _) hafter _ _ _ _ _ _ _ _ _ _) fun x => ?_
        obtain ⟨b, hb⟩ := x
        exact ih _ (by omega) _ _ rfl _ _ _ _ _ _ _ _
    conv => arg 6; zeta
    conv => arg 7; zeta
    refine SimF.ite Iff.rfl (fun hon => ?_) fun hon => ?_
    · -- the fast path
      have hre := runEnd_le hafter (Lexer.fastFlags c' &&& Lexer.FAST_RUN_MASK)
      have hle := Lexer.Slice.le_runEnd input (index + 1)
        (Lexer.fastFlags c' &&& Lexer.FAST_RUN_MASK)
      refine SimF.bind consumes_sim fun w => ?_
      refine SimF.dite Iff.rfl (fun _ _ => ?_) fun _ _ => ?_
      · refine SimF.bind (startWhitespace_sim hblind input offset base index batch _ _ _ _ _ _ _ _)
          fun x => ?_
        rcases x with _ | ⟨⟨next, b⟩, hnext, hb⟩
        · exact SimF.pure (fun _ h => h) rfl
        · exact ih _ (by omega) _ _ rfl _ _ _ _ _ _ _ _
      refine SimF.dite Iff.rfl (fun _ _ => ?_) fun hu _ => ?_
      · refine SimF.seq (storeUnfinishedSymbolRun_sim input _ offset base index _ _ batch hre _ _
          _ _ _ _ _ _) fun _ => ?_
        exact SimF.pure (fun _ h => h) rfl
      refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · -- the token is emitted: the byte after it must delimit it
        split
        · rename_i next hn
          refine SimF.hide_left fun F hF => ?_
          split
          · rename_i next' hn'
            obtain rfl : next' = next := Option.some.inj (hn'.symm.trans hn)
            subst hF
            refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
            · refine SimF.seq (leave_sim _ _ _ _ _ _ _ _) fun _ => ?_
              refine SimF.bind (startToken_sim _ _ _ _ _) fun _ => ?_
              refine SimF.bind (failAt_sim id _ _ (fun _ => BFits)) fun _ => ?_
              refine SimF.bind (pushFast_sim' hblind input batch offset base _ _
                (fastCategory_eq _ _)
                _ _ _ (ite_slice _ _ _ _ _ _) index _ _ (by repeat' split <;> omega)
                (by repeat' split <;> first | omega | contradiction) _ _ _ _ _ _ _ _ _ _)
                fun x => ?_
              obtain ⟨b, hb⟩ := x
              exact ih _ (by split <;> omega) _ _ rfl _ _ _ _ _ _ _ _
            · refine SimF.bind (pushFast_sim' hblind input batch offset base _ _
                (fastCategory_eq _ _)
                _ _ _ (ite_slice _ _ _ _ _ _) index _ _ (by repeat' split <;> omega)
                (by repeat' split <;> first | omega | contradiction) _ _ _ _ _ _ _ _ _ _)
                fun x => ?_
              obtain ⟨b, hb⟩ := x
              exact ih _ (by split <;> omega) _ _ rfl _ _ _ _ _ _ _ _
          · rename_i hn'
            exact absurd (hn'.symm.trans hn) (by simp)
        · rename_i hn
          refine SimF.hide_left fun F hF => ?_
          split
          · rename_i next' hn'
            exact absurd (hn'.symm.trans hn) (by simp)
          · subst hF
            refine SimF.bind (startToken_sim _ _ _ _ _) fun x => ?_
            obtain ⟨s, hs⟩ := x
            refine SimF.seq (extendContentFrom_sim input _ _ _ (ite_slice _ _ _ _ _ _)
              (.inl (by repeat' split <;> first | omega | contradiction))) fun _ => ?_
            refine SimF.seq (leavePending_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ => ?_
            exact SimF.pure (fun _ h => h) rfl
      · refine SimF.bind (pushFast_sim' hblind input batch offset base _ _ (fastCategory_eq _ _)
          _ _ _ (ite_slice _ _ _ _ _ _) index _ _ (by repeat' split <;> omega)
          (by repeat' split <;> first | omega | contradiction) _ _ _ _ _ _ _ _ _ _)
          fun x => ?_
        obtain ⟨b, hb⟩ := x
        exact ih _ (by split <;> omega) _ _ rfl _ _ _ _ _ _ _ _
    · -- the slow path, by the start of the token
      split
      all_goals
        rename_i h2
        refine SimF.hide_left fun F hF => ?_
        split
      all_goals
        rename_i h1
        subst hF
      all_goals first
        | (exfalso; exact Lexer.Start.noConfusion (h1.symm.trans h2))
        | skip
      · -- a line feed
        refine SimF.bind consumes_sim fun w => ?_
        refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
        · refine SimF.bind (startWhitespace_sim hblind input offset base index batch _ _ _ _ _ _ _
            _) fun x => ?_
          rcases x with _ | ⟨⟨next, b⟩, hnext, hb⟩
          · exact SimF.pure (fun _ h => h) rfl
          · exact ih _ (by omega) _ _ rfl _ _ _ _ _ _ _ _
        · refine SimF.seq (markLineFeedAt_sim _) fun _ => ?_
          exact ih _ (by omega) _ _ rfl _ _ _ _ _ _ _ _
      · -- a comment
        refine SimF.bind (startToken_sim _ _ _ _ _) fun x => ?_
        obtain ⟨ts, hts⟩ := x
        dsimp only
        have hre := runEnd_le hafter Lexer.RUN_COMMENT_PLAIN
        have hle := Lexer.Slice.le_runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN
        split
        · rename_i c2 hb2
          have hlt2 := Lexer.Slice.lt_size_of_get? hb2
          refine SimF.hide_left fun F hF => ?_
          split
          · rename_i c1 hb1
            obtain rfl : c1 = c2 := Option.some.inj (hb1.symm.trans hb2)
            subst hF
            have hcs :
                index + 1 ≤ Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN + 1 :=
              by omega
            have hce :
                Lexer.Slice.runEnd input (index + 1) Lexer.RUN_COMMENT_PLAIN + 1 ≤ input.size :=
              hlt2
            refine SimF.ite Iff.rfl (fun _ => SimF.seq (markLineFeedAt_sim _) fun _ => ?_)
              fun _ => ?_
            all_goals
              refine SimF.bind consumes_sim fun w => ?_
              refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
              · refine SimF.bind (pushBorrowed_sim' hblind input batch offset base _ _ _ _ rfl _ _
                  hcs
                  hce _ _ _ _ _ _ _ _) fun x => ?_
                exact ih _ (by omega) _ _ rfl _ _ _ _ _ _ _ _
              · refine SimF.bind (SimF.pure (ψ := id) (Q := fun _ => BFits) (fun _ h => h) rfl)
                  fun x => ?_
                exact ih _ (by omega) _ _ rfl _ _ _ _ _ _ _ _
          · rename_i hb1
            exact absurd (hb1.symm.trans hb2) (by simp)
        · rename_i hb2
          refine SimF.hide_left fun F hF => ?_
          split
          · rename_i c1 hb1
            exact absurd (hb1.symm.trans hb2) (by simp)
          · subst hF
            refine SimF.bind consumes_sim fun w => ?_
            refine SimF.ite Iff.rfl
              (fun _ => SimF.seq (extendContent_sim input _ _ (.inl hre)) fun _ => ?_) fun _ => ?_
            all_goals
              refine SimF.seq (leavePending_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ => ?_
              exact SimF.pure (fun _ h => h) rfl
      · -- a hash
        refine SimF.bind (startToken_sim _ _ _ _ _) fun x => ?_
        obtain ⟨ts, hts⟩ := x
        dsimp only
        split
        · rename_i run2 hrun2 heq2
          refine SimF.hide_left fun F hF => ?_
          split
          · rename_i run1 hrun1 heq1
            have e := heq1.symm.trans heq2
            simp only [Option.some.injEq, Subtype.mk.injEq] at e
            subst e hF
            obtain ⟨c2, hc2, -⟩ := Option.bind_eq_some_iff.mp hrun1
            have hs : index + 1 + 1 ≤ input.size := Lexer.Slice.lt_size_of_get? hc2
            have hre := runEnd_le hs run1.flag
            have hle := Lexer.Slice.le_runEnd input (index + 1 + 1) run1.flag
            refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
            · refine SimF.seq (extendContent_sim input _ _ (.inl hre)) fun _ => ?_
              refine SimF.seq (leavePending_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ => ?_
              exact SimF.pure (fun _ h => h) rfl
            refine getCore_bind fun cc _ => ?_
            refine SimF.ite
              (by rw [coreMap_tokenContent, size_borrow input hle hre _ cc.tokenContent])
              (fun _ => SimF.seq (leave_sim _ _ _ _ _ _ _ _) fun _ =>
                SimF.bind (fail_sim id _ _ (fun _ => BFits)) fun _ => ?_) fun _ => ?_
            all_goals
              refine SimF.ite Iff.rfl (fun _ => SimF.seq (leave_sim _ _ _ _ _ _ _ _) fun _ =>
                SimF.bind (failAt_sim id _ _ (fun _ => BFits)) fun _ => ?_) fun _ => ?_
            all_goals
              refine SimF.bind (pushBorrowed_sim' hblind input batch offset base
                _ _ _ _ rfl _ _ hle hre
                _ _ _ _ _ _ _ _) fun x => ?_
              exact ih _ (by omega) _ _ rfl _ _ _ _ _ _ _ _
          · rename_i hno
            exact absurd heq2 (hno _ _)
        · rename_i hno
          refine SimF.hide_left fun F hF => ?_
          split
          · rename_i run1 hrun1 heq1
            exact absurd heq1 (hno _ _)
          · subst hF
            refine SimF.seq (leavePending_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ => ?_
            exact SimF.pure (fun _ h => h) rfl
      · -- a string literal
        refine SimF.bind (startToken_sim _ _ _ _ _) fun x => ?_
        obtain ⟨ts, hts⟩ := x
        dsimp only
        refine getCore_bind fun cc _ => ?_
        refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
        · refine SimF.seq (leavePending_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ => ?_
          exact SimF.pure (fun _ h => h) rfl
        have hre := runEnd_le hafter Lexer.RUN_STRING_PLAIN
        have hle := Lexer.Slice.le_runEnd input (index + 1) Lexer.RUN_STRING_PLAIN
        split
        · rename_i aq2 nx2 heq2
          have haq : index < aq2 := by
            have h := heq2
            split at h
            · split at h
              · split at h
                · split at h
                  · simp only [Option.some.injEq, Prod.mk.injEq] at h
                    omega
                  · simp at h
                · simp at h
              · simp at h
            · simp at h
          refine SimF.hide_left fun F hF => ?_
          split
          · rename_i aq1 nx1 heq1
            have e := heq1.symm.trans heq2
            simp only [Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            subst hF
            refine SimF.ite Iff.rfl (fun _ => SimF.seq (leave_sim _ _ _ _ _ _ _ _) fun _ =>
              SimF.bind (failAt_sim id _ _ (fun _ => BFits)) fun _ => ?_) fun _ => ?_
            all_goals
              refine SimF.bind (pushBorrowed_sim' hblind input batch offset base
                _ _ _ _ rfl _ _ hle hre
                _ _ _ _ _ _ _ _) fun x => ?_
              exact ih _ (by omega) _ _ rfl _ _ _ _ _ _ _ _
          · rename_i heq1
            exact absurd (heq1.symm.trans heq2) (by simp)
        · rename_i heq2
          refine SimF.hide_left fun F hF => ?_
          split
          · rename_i aq1 nx1 heq1
            exact absurd (heq1.symm.trans heq2) (by simp)
          · subst hF
            refine SimF.seq (extendContent_sim input _ _ (.inl hre)) fun _ => ?_
            refine SimF.seq (leavePending_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ => ?_
            exact SimF.pure (fun _ h => h) rfl
      · -- a keyword
        refine SimF.bind (startToken_sim _ _ _ _ _) fun x => ?_
        obtain ⟨ts, hts⟩ := x
        dsimp only
        have hre := runEnd_le hafter Lexer.RUN_SIMPLE_SYMBOL
        have hle := Lexer.Slice.le_runEnd input (index + 1) Lexer.RUN_SIMPLE_SYMBOL
        refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
        · refine SimF.seq (extendContent_sim input _ _ (.inl hre)) fun _ => ?_
          refine SimF.seq (leavePending_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ => ?_
          exact SimF.pure (fun _ h => h) rfl
        refine getCore_bind fun cc _ => ?_
        refine SimF.ite
          (by rw [coreMap_tokenContent, size_borrow input hle hre _ cc.tokenContent])
          (fun _ => SimF.seq (leave_sim _ _ _ _ _ _ _ _) fun _ =>
            SimF.bind (fail_sim id _ _ (fun _ => BFits)) fun _ => ?_) fun _ => ?_
        all_goals
          refine SimF.ite Iff.rfl (fun _ => SimF.seq (leave_sim _ _ _ _ _ _ _ _) fun _ =>
            SimF.bind (failAt_sim id _ _ (fun _ => BFits)) fun _ => ?_) fun _ => ?_
        all_goals
          refine SimF.bind (pushBorrowed_sim' hblind input batch offset base
            _ _ _ _ rfl _ _ hle hre
            _ _ _ _ _ _ _ _) fun x => ?_
          exact ih _ (by omega) _ _ rfl _ _ _ _ _ _ _ _
      · -- a numeral or a decimal
        refine SimF.bind (startToken_sim _ _ _ _ _) fun x => ?_
        obtain ⟨ts, hts⟩ := x
        dsimp only
        have hre := runEnd_le hafter Lexer.RUN_DIGIT
        have hle := Lexer.Slice.le_runEnd input (index + 1) Lexer.RUN_DIGIT
        refine SimF.ite Iff.rfl (fun _ => SimF.seq (leave_sim _ _ _ _ _ _ _ _) fun _ =>
          SimF.bind (failAt_sim id _ _ (fun _ => BFits)) fun _ => ?_) fun _ => ?_
        all_goals
          split
          · rename_i nx2 hn2
            have hlt2 := Lexer.Slice.lt_size_of_get? hn2
            refine SimF.hide_left fun F hF => ?_
            split
            · rename_i nx1 hn1
              obtain rfl : nx1 = nx2 := Option.some.inj (hn1.symm.trans hn2)
              subst hF
              refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
              · -- a decimal
                have hs : Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1 ≤ input.size :=
                  hlt2
                have hre' := runEnd_le hs Lexer.RUN_DIGIT
                have hle' := Lexer.Slice.le_runEnd input
                  (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT
                refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
                · refine SimF.seq (extendContent_sim input _ _ (.inl hre')) fun _ => ?_
                  refine SimF.seq (leavePending_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ => ?_
                  exact SimF.pure (fun _ h => h) rfl
                have hcs : index ≤ Lexer.Slice.runEnd input
                    (Lexer.Slice.runEnd input (index + 1) Lexer.RUN_DIGIT + 1) Lexer.RUN_DIGIT := by
                  omega
                refine getCore_bind fun cc _ => ?_
                refine SimF.ite
                  (by rw [coreMap_tokenContent, last?_borrow input hcs hre' _ cc.tokenContent])
                  (fun _ => SimF.seq (leave_sim _ _ _ _ _ _ _ _) fun _ =>
                    SimF.bind (fail_sim id _ _ (fun _ => BFits)) fun _ => ?_) fun _ => ?_
                all_goals
                  refine SimF.ite Iff.rfl (fun _ => SimF.seq (leave_sim _ _ _ _ _ _ _ _) fun _ =>
                    SimF.bind (failAt_sim id _ _ (fun _ => BFits)) fun _ => ?_) fun _ => ?_
                all_goals
                  refine SimF.bind (pushBorrowed_sim' hblind input batch offset base _ _ _ _ rfl _ _
                    hcs hre' _ _ _ _ _ _ _ _) fun x => ?_
                  exact ih _ (by omega) _ _ rfl _ _ _ _ _ _ _ _
              · -- a numeral
                refine SimF.ite Iff.rfl (fun _ => SimF.seq (leave_sim _ _ _ _ _ _ _ _) fun _ =>
                  SimF.bind (failAt_sim id _ _ (fun _ => BFits)) fun _ => ?_) fun _ => ?_
                all_goals
                  refine SimF.bind (pushBorrowed_sim' hblind input batch offset base _ _ _ _ rfl _ _
                    (by omega) hre _ _ _ _ _ _ _ _) fun x => ?_
                  exact ih _ (by omega) _ _ rfl _ _ _ _ _ _ _ _
            · rename_i hn1
              exact absurd (hn1.symm.trans hn2) (by simp)
          · rename_i hn2
            refine SimF.hide_left fun F hF => ?_
            split
            · rename_i nx1 hn1
              exact absurd (hn1.symm.trans hn2) (by simp)
            · subst hF
              refine SimF.seq (extendContent_sim input _ _ (.inl hre)) fun _ => ?_
              refine SimF.seq (leavePending_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ => ?_
              exact SimF.pure (fun _ h => h) rfl
      all_goals
        -- a byte that starts no token
        refine SimF.bind (startToken_sim _ _ _ _ _) fun _ => ?_
        refine SimF.seq (leave_sim _ _ _ _ _ _ _ _) fun _ => ?_
        exact failAt_sim id _ _ _

theorem lexNormal_sim (input : ByteSlice) (start : Nat) (hstart hstart') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.lexNormal (H := H) (m := m) (R := R) (E := E) input start hstart)
      (Lexer.X1BatchInCore.lexNormal input start hstart') := by
  unfold Lexer.X2Contents.lexNormal Lexer.X1BatchInCore.lexNormal
  refine SimF.bind (SimF.modifyGet (ψ := id) (Q := fun _ => BFits) (fun _ _ => rfl)
    fun _ hc => hc) fun x => ?_
  obtain ⟨⟨offset, base, batch⟩, hframe, hbatch, hfloor⟩ := x
  refine SimF.bind (lexNormalFrom_sim hblind input _ _ _ _ _ _ rfl _ _ _ _ _ _ _ _) fun x => ?_
  exact SimF.pure (fun _ h => h) rfl

end

end BSmtLib.Proofs.X1BatchInCoreX2Contents
