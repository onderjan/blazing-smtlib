import BSmtLib.Proofs.V2BatchedV3Runs.RunEq

/-!
# A token in progress

The batched lexer's loop, from a byte of a token in progress, does what the lexer over runs
makes of the rest of the token (`loop2_token`): it steps over the run of bytes that the token
takes as they are, and then does at the byte that ends the run what the lexer over runs does.
-/

namespace BSmtLib.Proofs.Lexer.V2BatchedV3Runs

open V1Naive V2Batched V3Runs

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

theorem core_self (slice : ByteSlice) (i : Nat) (hi : i ≤ slice.size) (p : Pending) (core : Core)
    (hact : core.activity = .token p) :
    { core with
      activity := .token { p with content := p.content ++ bytesOf slice i i }
      location := afterColumns core.location (i - i) } = core := by
  rw [bytesOf_self slice i hi, ByteArray.append_empty, Nat.sub_self, afterColumns_zero]
  obtain ⟨v, iv, loc, act, d⟩ := core
  simp only at hact
  subst hact
  rfl

theorem core_token (p : Pending) (core : Core) (hact : core.activity = .token p) :
    { core with activity := .token p, location := core.location } = core := by
  obtain ⟨v, iv, loc, act, d⟩ := core
  simp only at hact
  subst hact
  rfl

/-- The batched lexer's loop from the end of a run of a token does what the lexer over runs
does there, given that from the byte after it on it does what the lexer over runs makes of the
rest of the token. -/
theorem loop2_runOrPending [LawfulMonad m] (recover : Location → StateT H m Unit)
    (sliceStart : Nat) (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R))
    (batch : Array Lexeme) (core : Core) {i j : Nat} (hij : i ≤ j) (hj : j ≤ slice.size)
    (q : Pending) (location : Location)
    (ih : j < slice.size → ∀ (q' : Pending) (core' : Core), core'.activity = .token q' →
      erase <$> loop2 recover sliceStart slice (j + 1) committed core' batch flow =
        erase <$> expand recover sliceStart slice committed flow core' batch
          (run (Consume.consumesWhitespaceAndComments (H := H)) slice q' (j + 1)
            core'.location)) :
    erase <$> loop2 recover sliceStart slice j committed
        { core with activity := .token q, location } batch flow =
      erase <$> expand recover sliceStart slice committed flow core batch
        ((runOrPending (Consume.consumesWhitespaceAndComments (H := H)) slice q j
          location).lift hij) := by
  rw [expand_lift]
  unfold runOrPending
  split
  · rename_i h
    rw [loop2_byte recover sliceStart slice committed flow batch j h q _ rfl (ih h)]
    refine expand_blank (H := H) (m := m) (R := R) (E := E) _ _ _ _ _ ?_ _ _
    rfl
  · have : j = slice.size := by omega
    subst this
    rfl

theorem loop2_token [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R))
    (batch : Array Lexeme) :
    ∀ n i, slice.size - i = n → i ≤ slice.size → ∀ (p : Pending) (core : Core),
      core.activity = .token p →
      erase <$> loop2 recover sliceStart slice i committed core batch flow =
        erase <$> expand recover sliceStart slice committed flow core batch
          (run (Consume.consumesWhitespaceAndComments (H := H)) slice p i core.location) := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ihn i hn hi p core hact
  -- what the loop does from the byte after the end of a run on
  have ih : ∀ j, i ≤ j → j < slice.size → ∀ (q' : Pending) (core' : Core),
      core'.activity = .token q' →
      erase <$> loop2 recover sliceStart slice (j + 1) committed core' batch flow =
        erase <$> expand recover sliceStart slice committed flow core' batch
          (run (Consume.consumesWhitespaceAndComments (H := H)) slice q' (j + 1)
            core'.location) :=
    fun j hij hj q' core' hact' => ihn (slice.size - (j + 1)) (by omega) (j + 1) rfl (by omega)
      q' core' hact'
  -- a mode with a run that keeps the mode
  have steps : ∀ (pred : UInt8 → Bool) (mode : Mode),
      (∀ (q : Pending) location c, q.mode = mode → pred c = true →
        advance (Consume.consumesWhitespaceAndComments (H := H)) q location c =
          .pending { q with content := q.content.push c }) →
      (∀ c, pred c = true → c ≠ 10) → p.mode = mode →
      erase <$> loop2 recover sliceStart slice i committed core batch flow =
        erase <$> expand recover sliceStart slice committed flow core batch
          ((runOrPending (Consume.consumesWhitespaceAndComments (H := H)) slice
            { p with content := p.content ++ bytesOf slice i (runEnd slice pred i) }
            (runEnd slice pred i)
            (afterColumns core.location (runEnd slice pred i - i))).lift
            (le_runEnd slice pred i)) := by
    intro pred mode hstep hnl hm
    rw [loop2_steps recover sliceStart slice committed batch flow pred mode hstep hnl _ i rfl hi
      p core hm hact]
    exact loop2_runOrPending recover sliceStart slice committed flow batch core _
      (runEnd_le slice pred i hi) _ _
      (fun hj => ih _ (le_runEnd slice pred i) hj)
  -- a mode without a run
  have single :
      erase <$> loop2 recover sliceStart slice i committed core batch flow =
        erase <$> expand recover sliceStart slice committed flow core batch
          (runOrPending (Consume.consumesWhitespaceAndComments (H := H)) slice p i
            core.location) := by
    have e := loop2_runOrPending recover sliceStart slice committed flow batch core
      (Nat.le_refl i) hi p core.location (fun hj => ih i (Nat.le_refl i) hj)
    rw [lift_self, core_token p core hact] at e
    exact e
  obtain ⟨mode, start, content⟩ := p
  cases mode with
  | numeral zero =>
    rw [run_numeral]
    split
    · rename_i hz
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
      obtain ⟨hi', hd⟩ := runEnd_start slice isDigit i hz.2
      rw [loop2_lt _ _ _ _ _ _ _ _ hi']
      have hadv : advance (Consume.consumesWhitespaceAndComments (H := H))
          ⟨.numeral zero, start, content⟩ core.location slice[i] =
          .error (failAtByte .numeralLeadingZero start core.location) := by
        simp [advance, hd, hz.1]
      simp only [V2Batched.lexByte, hact, hadv, pure_bind, expand]
      exact cont_failed _ _ _ _ _ _ rfl _ _ _
    · rename_i hz
      cases zero with
      | false => exact steps isDigit (.numeral false) (advance_numeral_run _) isDigit_ne rfl
      | true =>
        have hend : runEnd slice isDigit i = i := by
          have := le_runEnd slice isDigit i
          simp only [Bool.true_and, decide_eq_true_eq] at hz
          omega
        have e := loop2_runOrPending recover sliceStart slice committed flow batch core
          (le_runEnd slice isDigit i) (runEnd_le slice isDigit i hi)
          ⟨.numeral true, start, content ++ bytesOf slice i (runEnd slice isDigit i)⟩
          (afterColumns core.location (runEnd slice isDigit i - i))
          (fun hj => ih _ (le_runEnd slice isDigit i) hj)
        have hc : { core with
            activity :=
              .token ⟨.numeral true, start, content ++ bytesOf slice i (runEnd slice isDigit i)⟩
            location := afterColumns core.location (runEnd slice isDigit i - i) } = core := by
          rw [hend]
          exact core_self slice i hi ⟨.numeral true, start, content⟩ core hact
        rw [hc] at e
        conv at e => lhs; rw [hend]
        exact e
  | fraction digits =>
    rw [run_fraction]
    cases digits with
    | true =>
      simp only [Bool.true_or]
      exact steps isDigit (.fraction true) (advance_fraction_run _) isDigit_ne rfl
    | false =>
      simp only [Bool.false_or]
      by_cases hlt : i < runEnd slice isDigit i
      · obtain ⟨hi', hd⟩ := runEnd_start slice isDigit i hlt
        have hadv : advance (Consume.consumesWhitespaceAndComments (H := H))
            ⟨.fraction false, start, content⟩ core.location slice[i] =
            .pending ⟨.fraction true, start, content.push slice[i]⟩ := by
          simp [advance, hd]
        rw [loop2_pending recover sliceStart slice committed batch flow i hi' _ _ core hact hadv]
        rw [loop2_steps recover sliceStart slice committed batch flow isDigit (.fraction true)
          (advance_fraction_run _) isDigit_ne _ (i + 1) rfl (by omega) _ _ rfl rfl]
        have hend := runEnd_succ slice isDigit i hi' hd
        have e := loop2_runOrPending recover sliceStart slice committed flow batch core
          (le_runEnd slice isDigit i) (runEnd_le slice isDigit i hi)
          ⟨.fraction true, start, content ++ bytesOf slice i (runEnd slice isDigit i)⟩
          (afterColumns core.location (runEnd slice isDigit i - i))
          (fun hj => ih _ (le_runEnd slice isDigit i) hj)
        simp only [hlt, decide_true]
        rw [← e, ← hend]
        have hle := le_runEnd slice isDigit (i + 1)
        rw [push_append_bytesOf content slice hi' (by omega) (runEnd_le slice isDigit i hi),
          afterColumns_afterByte core.location slice[i] (isDigit_ne _ hd)]
        congr 4
        omega
      · have hend : runEnd slice isDigit i = i := by
          have := le_runEnd slice isDigit i
          omega
        simp only [hlt, decide_false]
        have e := loop2_runOrPending recover sliceStart slice committed flow batch core
          (le_runEnd slice isDigit i) (runEnd_le slice isDigit i hi)
          ⟨.fraction false, start, content ++ bytesOf slice i (runEnd slice isDigit i)⟩
          (afterColumns core.location (runEnd slice isDigit i - i))
          (fun hj => ih _ (le_runEnd slice isDigit i) hj)
        have hc : { core with
            activity :=
              .token ⟨.fraction false, start, content ++ bytesOf slice i (runEnd slice isDigit i)⟩
            location := afterColumns core.location (runEnd slice isDigit i - i) } = core := by
          rw [hend]
          exact core_self slice i hi ⟨.fraction false, start, content⟩ core hact
        rw [hc] at e
        conv at e => lhs; rw [hend]
        exact e
  | hash => rw [run_hash]; exact single
  | digits radix =>
    rw [run_digits]
    exact steps radix.allows (.digits radix) (advance_digits_run radix _) (allows_ne radix) rfl
  | keyword =>
    rw [run_keyword]
    exact steps isSymbolByte .keyword (advance_keyword_run _) isSymbolByte_ne rfl
  | simpleSymbol =>
    rw [run_simpleSymbol]
    exact steps isSymbolByte .simpleSymbol (advance_simpleSymbol_run _) isSymbolByte_ne rfl
  | quotedSymbol =>
    rw [run_quotedSymbol]
    exact steps isQuotedRun .quotedSymbol (advance_quotedSymbol_run _) isQuotedRun_ne rfl
  | quotedSymbolClosed => rw [run_quotedSymbolClosed]; exact single
  | string =>
    rw [run_string]
    exact steps isStringRun .string (advance_string_run _) isStringRun_ne rfl
  | stringQuote => rw [run_stringQuote]; exact single
  | legacyString =>
    rw [run_legacyString]
    exact steps isLegacyStringRun .legacyString (advance_legacyString_run _)
      isLegacyStringRun_ne rfl
  | legacyEscape => rw [run_legacyEscape]; exact single
  | legacyQuote => rw [run_legacyQuote]; exact single
  | comment =>
    rw [run_comment]
    exact steps isCommentRun .comment (advance_comment_run _) isCommentRun_ne rfl
  | whitespace =>
    rw [run_whitespace]
    exact steps isWhitespaceRun .whitespace (advance_whitespace_run _) isWhitespaceRun_ne rfl

end

end BSmtLib.Proofs.Lexer.V2BatchedV3Runs
