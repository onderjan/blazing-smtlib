import BSmtLib.Proofs.V2BatchedV3Runs.Byte

/-!
# The lexer over runs, byte by byte

For each mode of a token in progress, the lexer over runs' `V3Runs.run` takes the run of bytes
that the token takes as they are, and then does at the byte that ends the run what the naive
lexer's step `advance` does there (`byteRan`), or leaves the token in progress at the end of
the slice (`runOrPending`). And the naive lexer's step takes each byte of the run as it is
(`advance_*_run`).
-/

namespace BSmtLib.Proofs.Lexer.V2BatchedV3Runs

open V1Naive V3Runs

theorem lift_lift {size i j k : Nat} (h1 : j ≤ k) (h2 : i ≤ j) (r : Ran size k) :
    (r.lift h1).lift h2 = r.lift (Nat.le_trans h2 h1) := by
  cases r <;> rfl

theorem lift_self {size i : Nat} (h : i ≤ i) (r : Ran size i) : r.lift h = r := by
  cases r <;> rfl

theorem runEnd_stop (s : ByteSlice) (p : UInt8 → Bool) (i : Nat) (h : runEnd s p i < s.size) :
    p s[runEnd s p i] = false := by
  fun_induction runEnd s p i with
  | case1 i hi hp ih => exact ih h
  | case2 i hi hp => simpa using hp
  | case3 i hi => omega

theorem runEnd_start (s : ByteSlice) (p : UInt8 → Bool) (i : Nat) (h : i < runEnd s p i) :
    ∃ hi : i < s.size, p s[i] = true := by
  rw [runEnd] at h
  split at h
  · rename_i hi
    split at h
    · rename_i hp; exact ⟨hi, hp⟩
    · omega
  · omega

theorem runEnd_succ (s : ByteSlice) (p : UInt8 → Bool) (i : Nat) (hi : i < s.size)
    (hp : p s[i] = true) : runEnd s p i = runEnd s p (i + 1) := by
  rw [runEnd]; simp only [hi, dite_true, hp, ite_true]

section

variable (ws : Bool) (slice : ByteSlice) (start : Location) (content : ByteArray) (i : Nat)
  (location : Location)

/-! ## The modes with a run -/

theorem run_numeral (zero : Bool) :
    run ws slice ⟨.numeral zero, start, content⟩ i location =
      if zero && i < runEnd slice isDigit i then
        .error (failAtByte .numeralLeadingZero start location)
      else
        (runOrPending ws slice
          ⟨.numeral zero, start, content ++ bytesOf slice i (runEnd slice isDigit i)⟩
          (runEnd slice isDigit i) (afterColumns location (runEnd slice isDigit i - i))).lift
          (le_runEnd slice isDigit i) := by
  rw [run]
  simp only
  have hle := le_runEnd slice isDigit i
  split
  · rfl
  · rename_i hz
    unfold runOrPending
    split
    · rename_i h
      have hstop := runEnd_stop slice isDigit i h
      simp only [byteRan, advance]
      generalize slice[runEnd slice isDigit i] = c at hstop ⊢
      by_cases h1 : c = 46
      · subst h1; simp [hstop, lift_lift]
      · simp [Ran.lift, h1, hstop, delimited, V3Runs.delimited]
        split <;> rfl
    · have : (zero && runEnd slice isDigit i == i) = zero := by
        cases zero <;> simp_all; omega
      simp [this, Ran.lift]

theorem run_digits (radix : Radix) :
    run ws slice ⟨.digits radix, start, content⟩ i location =
      (runOrPending ws slice
        ⟨.digits radix, start, content ++ bytesOf slice i (runEnd slice radix.allows i)⟩
        (runEnd slice radix.allows i)
        (afterColumns location (runEnd slice radix.allows i - i))).lift
        (le_runEnd slice radix.allows i) := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · rename_i h
    have hstop := runEnd_stop slice radix.allows i h
    simp only [byteRan, advance]
    generalize slice[runEnd slice radix.allows i] = c at hstop ⊢
    by_cases he : (content ++ bytesOf slice i (runEnd slice radix.allows i)).isEmpty = true <;>
      simp [Ran.lift, hstop, V3Runs.delimited, he] <;> split <;> rfl
  · rfl

theorem run_keyword :
    run ws slice ⟨.keyword, start, content⟩ i location =
      (runOrPending ws slice
        ⟨.keyword, start, content ++ bytesOf slice i (runEnd slice isSymbolByte i)⟩
        (runEnd slice isSymbolByte i)
        (afterColumns location (runEnd slice isSymbolByte i - i))).lift
        (le_runEnd slice isSymbolByte i) := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · rename_i h
    have hstop := runEnd_stop slice isSymbolByte i h
    simp only [byteRan, advance]
    generalize slice[runEnd slice isSymbolByte i] = c at hstop ⊢
    by_cases he : (content ++ bytesOf slice i (runEnd slice isSymbolByte i)).isEmpty = true <;>
      simp [Ran.lift, hstop, V3Runs.delimited, he] <;> split <;> rfl
  · rfl

theorem run_simpleSymbol :
    run ws slice ⟨.simpleSymbol, start, content⟩ i location =
      (runOrPending ws slice
        ⟨.simpleSymbol, start, content ++ bytesOf slice i (runEnd slice isSymbolByte i)⟩
        (runEnd slice isSymbolByte i)
        (afterColumns location (runEnd slice isSymbolByte i - i))).lift
        (le_runEnd slice isSymbolByte i) := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · rename_i h
    have hstop := runEnd_stop slice isSymbolByte i h
    simp only [byteRan, advance]
    generalize slice[runEnd slice isSymbolByte i] = c at hstop ⊢
    simp [Ran.lift, hstop, V3Runs.delimited]
    split <;> rfl
  · rfl

theorem run_quotedSymbol :
    run ws slice ⟨.quotedSymbol, start, content⟩ i location =
      (runOrPending ws slice
        ⟨.quotedSymbol, start, content ++ bytesOf slice i (runEnd slice isQuotedRun i)⟩
        (runEnd slice isQuotedRun i)
        (afterColumns location (runEnd slice isQuotedRun i - i))).lift
        (le_runEnd slice isQuotedRun i) := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · rename_i h
    have hstop := runEnd_stop slice isQuotedRun i h
    simp only [byteRan, advance]
    generalize slice[runEnd slice isQuotedRun i] = c at hstop ⊢
    simp only [isQuotedRun] at hstop
    by_cases h1 : c = 124
    · subst h1; simp [lift_lift]
    · by_cases h2 : c = 92
      · subst h2; simp [Ran.lift]
      · by_cases h3 : c = 10
        · subst h3; simp [lift_lift, show isTextByte 10 = true from rfl]
        · have ht : isTextByte c = false := by simp_all
          simp [Ran.lift, h1, h2, h3, ht]
  · rfl

theorem run_string :
    run ws slice ⟨.string, start, content⟩ i location =
      (runOrPending ws slice
        ⟨.string, start, content ++ bytesOf slice i (runEnd slice isStringRun i)⟩
        (runEnd slice isStringRun i)
        (afterColumns location (runEnd slice isStringRun i - i))).lift
        (le_runEnd slice isStringRun i) := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · rename_i h
    have hstop := runEnd_stop slice isStringRun i h
    simp only [byteRan, advance]
    generalize slice[runEnd slice isStringRun i] = c at hstop ⊢
    simp only [isStringRun] at hstop
    by_cases h1 : c = 34
    · subst h1; simp [lift_lift]
    · by_cases h3 : c = 10
      · subst h3; simp [lift_lift, show isTextByte 10 = true from rfl]
      · have ht : isTextByte c = false := by simp_all
        simp [Ran.lift, h1, h3, ht]
  · rfl

theorem run_legacyString :
    run ws slice ⟨.legacyString, start, content⟩ i location =
      (runOrPending ws slice
        ⟨.legacyString, start, content ++ bytesOf slice i (runEnd slice isLegacyStringRun i)⟩
        (runEnd slice isLegacyStringRun i)
        (afterColumns location (runEnd slice isLegacyStringRun i - i))).lift
        (le_runEnd slice isLegacyStringRun i) := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · rename_i h
    have hstop := runEnd_stop slice isLegacyStringRun i h
    simp only [byteRan, advance]
    generalize slice[runEnd slice isLegacyStringRun i] = c at hstop ⊢
    simp only [isLegacyStringRun] at hstop
    simp only [legacyStringByte]
    by_cases h1 : c = 34
    · subst h1; simp [lift_lift]
    · by_cases h2 : c = 92
      · subst h2; simp [lift_lift]
      · by_cases h3 : c = 10
        · subst h3; simp [lift_lift, show isTextByte 10 = true from rfl]
        · have ht : isTextByte c = false := by simp_all
          simp [Ran.lift, h1, h2, h3, ht]
  · rfl

theorem run_comment :
    run ws slice ⟨.comment, start, content⟩ i location =
      (runOrPending ws slice
        ⟨.comment, start, content ++ bytesOf slice i (runEnd slice isCommentRun i)⟩
        (runEnd slice isCommentRun i)
        (afterColumns location (runEnd slice isCommentRun i - i))).lift
        (le_runEnd slice isCommentRun i) := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · rename_i h
    have hstop := runEnd_stop slice isCommentRun i h
    simp only [byteRan, advance]
    generalize slice[runEnd slice isCommentRun i] = c at hstop ⊢
    simp only [isCommentRun] at hstop
    have hc : (c == 10 || c == 13) = true := by
      cases h10 : c == 10 <;> cases h13 : c == 13 <;> simp_all
    simp only [hc, ite_true]
    cases ws <;> rfl
  · rfl

theorem run_whitespace :
    run ws slice ⟨.whitespace, start, content⟩ i location =
      (runOrPending ws slice
        ⟨.whitespace, start, content ++ bytesOf slice i (runEnd slice isWhitespaceRun i)⟩
        (runEnd slice isWhitespaceRun i)
        (afterColumns location (runEnd slice isWhitespaceRun i - i))).lift
        (le_runEnd slice isWhitespaceRun i) := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · rename_i h
    have hstop := runEnd_stop slice isWhitespaceRun i h
    simp only [byteRan, advance]
    generalize slice[runEnd slice isWhitespaceRun i] = c at hstop ⊢
    simp only [isWhitespaceRun] at hstop
    by_cases h1 : c = 10
    · subst h1; simp [lift_lift, show isWhitespace 10 = true from rfl]
    · have ht : isWhitespace c = false := by simp_all
      simp [Ran.lift, h1, ht]
  · rfl

/-- In a fraction, the first digit after the dot changes the mode, so the run is taken with the
mode it ends in. -/
theorem run_fraction (digits : Bool) :
    run ws slice ⟨.fraction digits, start, content⟩ i location =
      (runOrPending ws slice
        ⟨.fraction (digits || decide (i < runEnd slice isDigit i)), start,
          content ++ bytesOf slice i (runEnd slice isDigit i)⟩
        (runEnd slice isDigit i)
        (afterColumns location (runEnd slice isDigit i - i))).lift
        (le_runEnd slice isDigit i) := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · rename_i h
    have hstop := runEnd_stop slice isDigit i h
    simp only [byteRan, advance]
    generalize slice[runEnd slice isDigit i] = c at hstop ⊢
    generalize (digits || decide (i < runEnd slice isDigit i)) = d
    cases d <;> simp [Ran.lift, hstop, V3Runs.delimited] <;> split <;> rfl
  · rfl

/-! ## The modes without a run -/

theorem run_hash :
    run ws slice ⟨.hash, start, content⟩ i location =
      runOrPending ws slice ⟨.hash, start, content⟩ i location := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · simp only [byteRan, advance]
    generalize slice[i] = c
    by_cases h1 : c = 120
    · subst h1; simp
    · by_cases h2 : c = 98
      · subst h2; simp
      · simp [h1, h2]
  · rfl

theorem run_quotedSymbolClosed :
    run ws slice ⟨.quotedSymbolClosed, start, content⟩ i location =
      runOrPending ws slice ⟨.quotedSymbolClosed, start, content⟩ i location := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · simp only [byteRan, advance, V3Runs.delimited]
    split <;> rfl
  · rfl

theorem run_stringQuote :
    run ws slice ⟨.stringQuote, start, content⟩ i location =
      runOrPending ws slice ⟨.stringQuote, start, content⟩ i location := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · simp only [byteRan, advance, V3Runs.delimited]
    generalize slice[i] = c
    by_cases h1 : c = 34
    · subst h1; simp
    · simp only [h1, beq_iff_eq, ite_false]
      split <;> rfl
  · rfl

theorem run_legacyEscape :
    run ws slice ⟨.legacyEscape, start, content⟩ i location =
      runOrPending ws slice ⟨.legacyEscape, start, content⟩ i location := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · simp only [byteRan, advance, legacyStringByte]
    generalize slice[i] = c
    by_cases h1 : c = 34
    · subst h1; simp
    · by_cases h2 : c = 92
      · subst h2; simp
      · by_cases ht : isTextByte c = true
        · simp [h1, h2, ht]
        · simp [h1, h2, ht]
  · rfl

theorem run_legacyQuote :
    run ws slice ⟨.legacyQuote, start, content⟩ i location =
      runOrPending ws slice ⟨.legacyQuote, start, content⟩ i location := by
  rw [run]
  simp only
  unfold runOrPending
  split
  · simp only [byteRan, advance, V3Runs.delimited]
    split <;> rfl
  · rfl

end

/-! ## The naive lexer's step over a run -/

theorem advance_numeral_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = (.numeral false)) (hc : isDigit c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance]

theorem advance_fraction_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = (.fraction true)) (hc : isDigit c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance]

theorem advance_digits_run (radix : Radix) (ws : Bool) (q : Pending) (location : Location)
    (c : UInt8)
    (hm : q.mode = (.digits radix)) (hc : radix.allows c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance, Radix.allows]

theorem advance_keyword_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .keyword) (hc : isSymbolByte c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance]

theorem advance_simpleSymbol_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .simpleSymbol) (hc : isSymbolByte c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance]

theorem advance_quotedSymbol_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .quotedSymbol) (hc : isQuotedRun c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance, isQuotedRun]

theorem advance_string_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .string) (hc : isStringRun c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance, isStringRun]

theorem advance_legacyString_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .legacyString) (hc : isLegacyStringRun c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance, legacyStringByte, isLegacyStringRun]

theorem advance_comment_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .comment) (hc : isCommentRun c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance, isCommentRun]

theorem advance_whitespace_run (ws : Bool) (q : Pending) (location : Location) (c : UInt8)
    (hm : q.mode = .whitespace) (hc : isWhitespaceRun c = true) :
    advance ws q location c = .pending { q with content := q.content.push c } := by
  obtain ⟨mode, start, content⟩ := q
  subst hm
  simp_all [advance, isWhitespaceRun]

theorem isDigit_ne (c : UInt8) (hc : isDigit c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem isSymbolByte_ne (c : UInt8) (hc : isSymbolByte c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem isQuotedRun_ne (c : UInt8) (hc : isQuotedRun c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem isStringRun_ne (c : UInt8) (hc : isStringRun c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem isLegacyStringRun_ne (c : UInt8) (hc : isLegacyStringRun c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem isCommentRun_ne (c : UInt8) (hc : isCommentRun c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem isWhitespaceRun_ne (c : UInt8) (hc : isWhitespaceRun c = true) : c ≠ 10 := by
  intro h; subst h; exact absurd hc (by decide)

theorem allows_ne (radix : Radix) (c : UInt8) (hc : radix.allows c = true) : c ≠ 10 := by
  intro h; subst h; cases radix <;> exact absurd hc (by decide)

end BSmtLib.Proofs.Lexer.V2BatchedV3Runs
