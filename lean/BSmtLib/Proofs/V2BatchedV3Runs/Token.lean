import BSmtLib.Proofs.V2BatchedV3Runs.RunEq

/-!
# A token in progress

The batched lexer's loop, from a byte of a token in progress, does what the lexer over runs
makes of the rest of the token (`loop2_token`): it steps over the run of bytes that the token
takes as they are, and then does at the byte that ends the run what the lexer over runs does.
-/

namespace BSmtLib.Proofs.Lexer.V2BatchedV3Runs

open V1Naive V2Batched V3Runs

theorem spec_unlift {size i i' : Nat} {p : Pending} {location : Location} {h : i ≤ i'}
    {r : Ran size i'} (hr : (r.lift h).Spec p location) : r.Spec p location := by
  cases r <;> exact hr

theorem runOrPending_lift_congr {ws : Bool} {slice : ByteSlice} {q q' : Pending} {i j j' : Nat}
    {location location' : Location} {h : i ≤ j} {h' : i ≤ j'} (hj : j = j') (hq : q = q')
    (hl : location = location') :
    (runOrPending ws slice q j location).lift h =
      (runOrPending ws slice q' j' location').lift h' := by
  subst hj hq hl
  rfl

/-- A token that starts where the token in progress in `core` starts starts before any location
that many columns on. -/
theorem started_cols {core : Core} {p q : Pending} (hact : core.activity = .token p)
    (hq : q.start = p.start) (n : Nat) :
    q.start.offset < (afterColumns core.location n).offset := by
  rw [hq, afterColumns_offset]
  have := core.started hact
  omega

/-- A batch that fits a state with a token in progress fits it with any token in progress that
starts at the same place. -/
theorem fits_token {core : Core} {batch : Array Lexeme} {p q : Pending} (hfits : Fits core batch)
    (hact : core.activity = .token p) (hq : q.start = p.start) (location : Location)
    (hs : q.start.offset < location.offset) :
    Fits { core with activity := .token q, location, startedBefore := hs } batch :=
  ⟨hfits.1, show _ ≤ q.start.offset by rw [hq]; exact Fits.le_start hfits hact⟩

theorem core_token (p : Pending) (core : Core) (hact : core.activity = .token p)
    (hs : p.start.offset < core.location.offset) :
    { core with activity := .token p, location := core.location, startedBefore := hs } = core := by
  obtain ⟨v, iv, loc, act, d, s⟩ := core
  simp only at hact
  subst hact
  rfl

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

theorem expand_congr' [LawfulMonad m] {recover : Location → StateT H m Unit} {sliceStart : Nat}
    {slice : ByteSlice} {committed : Nat} {flow : ControlFlow (Located R)} {c₁ c₂ : Core}
    (hb : blank c₁ = blank c₂) {batch : Array Lexeme} {p₁ p₂ : Pending}
    {location₁ location₂ : Location} {h₁ : Fits c₁ batch} {h₂ : Fits c₂ batch}
    {hlast₁ : lastEnd 0 batch.toList ≤ p₁.start.offset}
    {hlast₂ : lastEnd 0 batch.toList ≤ p₂.start.offset}
    {hstart₁ : p₁.start.offset < location₁.offset} {hstart₂ : p₂.start.offset < location₂.offset}
    {i : Nat} {r₁ r₂ : Ran slice.size i} (e : r₁ = r₂) {hr₁ : r₁.Spec p₁ location₁}
    {hr₂ : r₂.Spec p₂ location₂} :
    erase <$> expand recover sliceStart slice committed flow c₁ batch p₁ location₁ h₁ hlast₁
        hstart₁ r₁ hr₁ =
      erase <$> expand recover sliceStart slice committed flow c₂ batch p₂ location₂ h₂ hlast₂
        hstart₂ r₂ hr₂ := by
  subst e
  exact expand_congr _ _ _ _ _ hb _ _ _ _ _ _ _ _ _ _

/-- The batched lexer's loop from the end of a run of a token does what the lexer over runs
does there, given that from the byte after it on it does what the lexer over runs makes of the
rest of the token. -/
theorem loop2_runOrPending [LawfulMonad m] (recover : Location → StateT H m Unit)
    (sliceStart : Nat) (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R))
    (batch : Array Lexeme) (core : Core) (hfits : Fits core batch) {i j : Nat} (hij : i ≤ j)
    (hj : j ≤ slice.size) (q : Pending) (location : Location)
    (hs : q.start.offset < location.offset)
    (hfits' : Fits { core with activity := .token q, location, startedBefore := hs } batch)
    (ih : j < slice.size → ∀ (q' : Pending) (core' : Core) (hact' : core'.activity = .token q')
      (hfits' : Fits core' batch) (r : Ran slice.size (j + 1)) (hr : r.Spec q' core'.location),
      r = run (Consume.consumesWhitespaceAndComments (H := H)) slice q' (j + 1) core'.location →
      erase <$> loop2 recover sliceStart slice (j + 1) committed core' batch flow hfits' =
        erase <$> expand recover sliceStart slice committed flow core' batch q' core'.location
          hfits' (Fits.le_start hfits' hact') (core'.started hact') r hr)
    (p : Pending) (location₀ : Location) (hlast : lastEnd 0 batch.toList ≤ p.start.offset)
    (hstart : p.start.offset < location₀.offset) (r : Ran slice.size i)
    (hr : r.Spec p location₀)
    (hr0 : r = (runOrPending (Consume.consumesWhitespaceAndComments (H := H)) slice q j
      location).lift hij) :
    erase <$> loop2 recover sliceStart slice j committed
        { core with activity := .token q, location, startedBefore := hs } batch flow hfits' =
      erase <$> expand recover sliceStart slice committed flow core batch p location₀ hfits hlast
        hstart r hr := by
  subst hr0
  rw [expand_lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec_unlift hr)]
  by_cases h : j < slice.size
  · rw [loop2_byte recover sliceStart slice committed flow batch j h q _ rfl hfits' (ih h) _
      (byteRan_spec _ _ _ _ _ _) rfl]
    refine expand_congr' (H := H) (m := m) (R := R) (E := E) ?_ ?_
    · rfl
    · unfold runOrPending
      simp only [h, ↓reduceDIte]
  · have : j = slice.size := by omega
    subst this
    have e : runOrPending (Consume.consumesWhitespaceAndComments (H := H)) slice q slice.size
        location = .pending q location := by
      unfold runOrPending
      simp only [h, ↓reduceDIte]
    rw [expand_congr' (c₂ := core) (p₂ := q) (location₂ := location) (h₂ := hfits)
      (hlast₂ := hfits'.2) (hstart₂ := hs) (hr₂ := ⟨rfl, Nat.le_refl _⟩) rfl e]
    rfl

theorem loop2_token [LawfulMonad m] (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located R))
    (batch : Array Lexeme) :
    ∀ n i, slice.size - i = n → i ≤ slice.size → ∀ (p : Pending) (core : Core)
      (hact : core.activity = .token p) (hfits : Fits core batch) (r : Ran slice.size i)
      (hr : r.Spec p core.location),
      r = run (Consume.consumesWhitespaceAndComments (H := H)) slice p i core.location →
      erase <$> loop2 recover sliceStart slice i committed core batch flow hfits =
        erase <$> expand recover sliceStart slice committed flow core batch p core.location
          hfits (Fits.le_start hfits hact) (core.started hact) r hr := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ihn i hn hi p core hact hfits r hr hr0
  -- what the loop does from the byte after the end of a run on
  have ih : ∀ j, i ≤ j → j < slice.size → ∀ (q' : Pending) (core' : Core)
      (hact' : core'.activity = .token q') (hfits' : Fits core' batch)
      (r : Ran slice.size (j + 1)) (hr : r.Spec q' core'.location),
      r = run (Consume.consumesWhitespaceAndComments (H := H)) slice q' (j + 1) core'.location →
      erase <$> loop2 recover sliceStart slice (j + 1) committed core' batch flow hfits' =
        erase <$> expand recover sliceStart slice committed flow core' batch q' core'.location
          hfits' (Fits.le_start hfits' hact') (core'.started hact') r hr :=
    fun j hij hj q' core' hact' hfits' r hr hr0 =>
      ihn (slice.size - (j + 1)) (by omega) (j + 1) rfl (by omega) q' core' hact' hfits' r hr hr0
  -- a mode with a run that keeps the mode
  have steps : ∀ (pred : UInt8 → Bool) (mode : Mode),
      (∀ (q : Pending) location c, q.mode = mode → pred c = true →
        advance (Consume.consumesWhitespaceAndComments (H := H)) q location c =
          .pending { q with content := q.content.push c }) →
      (∀ c, pred c = true → c ≠ 10) → p.mode = mode →
      r = (runOrPending (Consume.consumesWhitespaceAndComments (H := H)) slice
          { p with content := p.content ++ bytesOf slice i (runEnd slice pred i) }
          (runEnd slice pred i)
          (afterColumns core.location (runEnd slice pred i - i))).lift
          (le_runEnd slice pred i) →
      erase <$> loop2 recover sliceStart slice i committed core batch flow hfits =
        erase <$> expand recover sliceStart slice committed flow core batch p core.location
          hfits (Fits.le_start hfits hact) (core.started hact) r hr := by
    intro pred mode hstep hnl hm hr0
    have hs := started_cols
      (q := { p with content := p.content ++ bytesOf slice i (runEnd slice pred i) })
      hact rfl (runEnd slice pred i - i)
    rw [loop2_steps recover sliceStart slice committed batch flow pred mode hstep hnl _ i rfl hi
      p core hm hact hfits hs (fits_token hfits hact rfl _ hs)]
    exact loop2_runOrPending recover sliceStart slice committed flow batch core hfits _
      (runEnd_le slice pred i hi) _ _ _ _
      (fun hj => ih _ (le_runEnd slice pred i) hj) _ _ _ _ r hr hr0
  -- a mode without a run
  have single :
      r = runOrPending (Consume.consumesWhitespaceAndComments (H := H)) slice p i
          core.location →
      erase <$> loop2 recover sliceStart slice i committed core batch flow hfits =
        erase <$> expand recover sliceStart slice committed flow core batch p core.location
          hfits (Fits.le_start hfits hact) (core.started hact) r hr := by
    intro hr0
    rw [loop2_congr (h' := fits_token hfits hact rfl core.location (core.started hact))
      (core_token p core hact (core.started hact)).symm]
    exact loop2_runOrPending recover sliceStart slice committed flow batch core hfits
      (Nat.le_refl i) hi p core.location (core.started hact) _
      (fun hj => ih i (Nat.le_refl i) hj) _ _ _ _ r hr (by rw [hr0, lift_self])
  obtain ⟨mode, start, content⟩ := p
  have hstart : start.offset < core.location.offset := core.started hact
  cases mode with
  | numeral zero =>
    rw [run_numeral] at hr0
    split at hr0
    · rename_i hz
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
      obtain ⟨hi', hd⟩ := runEnd_start slice isDigit i hz.2
      rw [loop2_lt _ _ _ _ _ _ _ _ _ hi']
      have hadv : advance (Consume.consumesWhitespaceAndComments (H := H))
          ⟨.numeral zero, start, content⟩ core.location slice[i] =
          .error (failAtByte .numeralLeadingZero start core.location) := by
        simp [advance, hd, hz.1]
      subst hr0
      simp only [V2Batched.lexByte, withEq, hact, advanceS, hadv, pure_bind, expand]
      exact cont_failed _ _ _ _ _ _ rfl _ _ _ _ _
    · rename_i hz
      cases zero with
      | false => exact steps isDigit (.numeral false) (advance_numeral_run _) isDigit_ne rfl hr0
      | true =>
        have hend : runEnd slice isDigit i = i := by
          have := le_runEnd slice isDigit i
          simp only [Bool.true_and, decide_eq_true_eq] at hz
          omega
        refine single ?_
        rw [hr0, runOrPending_lift_congr (h' := Nat.le_refl i)
          (q' := ⟨.numeral true, start, content⟩) (location' := core.location) hend
          (by rw [hend, bytesOf_self slice i hi, ByteArray.append_empty])
          (by rw [hend, Nat.sub_self, afterColumns_zero]), lift_self]
  | fraction digits =>
    rw [run_fraction] at hr0
    cases digits with
    | true =>
      simp only [Bool.true_or] at hr0
      exact steps isDigit (.fraction true) (advance_fraction_run _) isDigit_ne rfl hr0
    | false =>
      simp only [Bool.false_or] at hr0
      by_cases hlt : i < runEnd slice isDigit i
      · simp only [hlt, decide_true] at hr0
        obtain ⟨hi', hd⟩ := runEnd_start slice isDigit i hlt
        have hadv : advance (Consume.consumesWhitespaceAndComments (H := H))
            ⟨.fraction false, start, content⟩ core.location slice[i] =
            .pending ⟨.fraction true, start, content.push slice[i]⟩ := by
          simp [advance, hd]
        have hs1 : start.offset < (core.location.afterByte slice[i]).offset := by
          rw [afterByte_offset]; omega
        rw [loop2_pending recover sliceStart slice committed batch flow i hi' _ _ core hact hfits
          hadv hs1 (fits_token hfits hact rfl _ hs1)]
        have hfits1 := fits_token (q := ⟨.fraction true, start, content.push slice[i]⟩) hfits hact
          rfl _ hs1
        have hs2 := started_cols
          (core := { core with
            activity := .token ⟨.fraction true, start, content.push slice[i]⟩
            location := core.location.afterByte slice[i], startedBefore := hs1 })
          (q := ⟨.fraction true, start,
            content.push slice[i] ++ bytesOf slice (i + 1) (runEnd slice isDigit (i + 1))⟩)
          rfl rfl (runEnd slice isDigit (i + 1) - (i + 1))
        rw [loop2_steps recover sliceStart slice committed batch flow isDigit (.fraction true)
          (advance_fraction_run _) isDigit_ne _ (i + 1) rfl (by omega)
          ⟨.fraction true, start, content.push slice[i]⟩ _ rfl rfl hfits1 hs2
          (fits_token hfits1 rfl rfl _ hs2)]
        have hend := runEnd_succ slice isDigit i hi' hd
        have hle := le_runEnd slice isDigit (i + 1)
        have hle' := runEnd_le slice isDigit (i + 1) (by omega)
        refine loop2_runOrPending recover sliceStart slice committed flow batch core hfits
          (i := i) (j := runEnd slice isDigit (i + 1)) (by omega) hle' _ _ _ _
          (fun hj => ih _ (by omega) hj) _ _ _ _ r hr ?_
        rw [hr0]
        refine runOrPending_lift_congr hend ?_ ?_
        · show _ = (⟨.fraction true, start,
            content.push slice[i] ++ bytesOf slice (i + 1) (runEnd slice isDigit (i + 1))⟩ :
              Pending)
          rw [push_append_bytesOf content slice hi' (by omega) hle', hend]
        · rw [afterColumns_afterByte _ _ (isDigit_ne _ hd), hend]
          congr 1
          omega
      · have hend : runEnd slice isDigit i = i := by
          have := le_runEnd slice isDigit i
          omega
        simp only [hlt, decide_false] at hr0
        refine single ?_
        rw [hr0, runOrPending_lift_congr (h' := Nat.le_refl i)
          (q' := ⟨.fraction false, start, content⟩) (location' := core.location) hend
          (by rw [hend, bytesOf_self slice i hi, ByteArray.append_empty])
          (by rw [hend, Nat.sub_self, afterColumns_zero]), lift_self]
  | hash => rw [run_hash] at hr0; exact single hr0
  | digits radix =>
    rw [run_digits] at hr0
    exact steps radix.allows (.digits radix) (advance_digits_run radix _) (allows_ne radix) rfl
      hr0
  | keyword =>
    rw [run_keyword] at hr0
    exact steps isSymbolByte .keyword (advance_keyword_run _) isSymbolByte_ne rfl hr0
  | simpleSymbol =>
    rw [run_simpleSymbol] at hr0
    exact steps isSymbolByte .simpleSymbol (advance_simpleSymbol_run _) isSymbolByte_ne rfl hr0
  | quotedSymbol =>
    rw [run_quotedSymbol] at hr0
    exact steps isQuotedRun .quotedSymbol (advance_quotedSymbol_run _) isQuotedRun_ne rfl hr0
  | quotedSymbolClosed => rw [run_quotedSymbolClosed] at hr0; exact single hr0
  | string =>
    rw [run_string] at hr0
    exact steps isStringRun .string (advance_string_run _) isStringRun_ne rfl hr0
  | stringQuote => rw [run_stringQuote] at hr0; exact single hr0
  | legacyString =>
    rw [run_legacyString] at hr0
    exact steps isLegacyStringRun .legacyString (advance_legacyString_run _)
      isLegacyStringRun_ne rfl hr0
  | legacyEscape => rw [run_legacyEscape] at hr0; exact single hr0
  | legacyQuote => rw [run_legacyQuote] at hr0; exact single hr0
  | comment =>
    rw [run_comment] at hr0
    exact steps isCommentRun .comment (advance_comment_run _) isCommentRun_ne rfl hr0
  | whitespace =>
    rw [run_whitespace] at hr0
    exact steps isWhitespaceRun .whitespace (advance_whitespace_run _) isWhitespaceRun_ne rfl
      hr0

end

end BSmtLib.Proofs.Lexer.V2BatchedV3Runs
