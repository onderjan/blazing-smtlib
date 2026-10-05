import BSmtLib.Proofs.V2BatchedV3Runs
import BSmtLib.Proofs.Lexer.V4FastPaths
import BSmtLib.Proofs.V1Naive.Facts

/-!
# The tokens of the fast paths, lexed by the lexer over runs

What the lexer over runs makes of the tokens that the fast paths of `V4FastPaths` take: how the
naive lexer's step `start` starts them, and what `V3Runs.run` gives for the rest of them when
the run of their bytes ends inside the slice.
-/

namespace BSmtLib.Proofs.Lexer.V3RunsV4FastPaths

open V1Naive V3Runs V2BatchedV3Runs

/-! ## Starting a token -/

theorem symbol_facts_bool (c : UInt8) :
    (!(isSymbolByte c && !isDigit c) || (!isWhitespace c && c != 40 && c != 41 && c != 59 &&
      c != 35 && c != 34 && c != 58 && c != 124)) = true :=
  byte_cases (P := fun c => (!(isSymbolByte c && !isDigit c) || (!isWhitespace c && c != 40 &&
    c != 41 && c != 59 && c != 35 && c != 34 && c != 58 && c != 124)) = true)
    (by decide +kernel) c

theorem start_symbol (version : Version) (ws : Bool) (location : Location) (c : UInt8)
    (hs : isSymbolByte c = true) (hd : isDigit c = false) :
    start version ws location c = .pending ⟨.simpleSymbol, location, ByteArray.empty.push c⟩ := by
  have := symbol_facts_bool c
  simp only [hs, hd, Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := this
  simp [start, h1, h2, h3, h4, h5, h6, h7, h8, hs, hd]

theorem start_space (version : Version) (ws : Bool) (location : Location) (c : UInt8)
    (hs : isWhitespaceRun c = true) :
    start version ws location c =
      if ws then .pending ⟨.whitespace, location, ByteArray.empty.push c⟩ else .idle := by
  have : isWhitespace c = true := by simp_all [isWhitespaceRun]
  simp [start, this]

theorem start_quoted (version : Version) (ws : Bool) (location : Location) :
    start version ws location 124 = .pending ⟨.quotedSymbol, location, .empty⟩ := rfl

theorem start_paren (version : Version) (ws : Bool) (location : Location) (c : UInt8)
    (hc : (c == 41 || c == 40) = true) :
    start version ws location c =
      .token ⟨if c == 41 then .parenClose else .parenOpen, ByteArray.empty.push c, location,
        location.afterColumn⟩ := by
  simp only [Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with rfl | rfl <;> rfl

/-! ## The rest of a token -/

theorem afterByte_afterColumns (location : Location) (c : UInt8) (h : c ≠ 10) (n : Nat) :
    (afterColumns location n).afterByte c = afterColumns location (n + 1) := by
  unfold Location.afterByte
  split
  · rename_i hc
    exact absurd (beq_iff_eq.mp hc) h
  · simp only [afterColumns, Location.afterColumn]
    rw [Nat.add_assoc, Nat.add_assoc]

theorem empty_append (b : ByteArray) : ByteArray.empty ++ b = b := by
  apply ByteArray.ext
  rw [ByteArray.data_append, show ByteArray.empty.data = #[] from rfl, Array.empty_append]

section

variable (ws : Bool) (slice : ByteSlice) (i : Nat) (location : Location)

/-- A quoted symbol whose run ends at a pipe inside the slice: the pipe closes it. -/
theorem run_quoted_closed (j : Nat) (hjdef : runEnd slice isQuotedRun (i + 1) = j)
    (hj : j < slice.size) (hp : slice[j] = 124) :
    run ws slice ⟨.quotedSymbol, location, .empty⟩ (i + 1) (location.afterByte 124) =
      if h1 : j + 1 < slice.size then
        if isDelimiter slice[j + 1] then
          .tokenBefore ⟨.quotedSymbol, bytesOf slice (i + 1) j, location,
            afterColumns location (j + 1 - i)⟩ (j + 1)
            (by have := le_runEnd slice isQuotedRun (i + 1); omega) h1
        else .error (failAtByte .missingDelimiter location (afterColumns location (j + 1 - i)))
      else
        .pending ⟨.quotedSymbolClosed, location, bytesOf slice (i + 1) j⟩
          (afterColumns location (j + 1 - i)) := by
  have hle := le_runEnd slice isQuotedRun (i + 1)
  have hloc : (afterColumns (location.afterByte 124) (j - (i + 1))).afterByte 124 =
      afterColumns location (j + 1 - i) := by
    rw [afterColumns_afterByte _ _ (by decide), afterByte_afterColumns _ _ (by decide)]
    congr 1; omega
  rw [run_quotedSymbol]
  unfold runOrPending
  subst hjdef
  simp only [hj, dite_true]
  simp only [byteRan, advance, hp, show ((124 : UInt8) == 124) = true from rfl, ite_true,
    empty_append, hloc]
  rw [run_quotedSymbolClosed]
  unfold runOrPending
  split
  · rename_i h1
    simp only [byteRan, advance]
    by_cases hd : isDelimiter slice[runEnd slice isQuotedRun (i + 1) + 1] = true
    · simp only [hd, ite_true]; rfl
    · simp only [hd, Bool.false_eq_true, ite_false]; rfl
  · rfl

/-- A simple symbol whose run ends inside the slice. -/
theorem run_symbol_inside (c : UInt8) (hc : c ≠ 10) (j : Nat)
    (hjdef : runEnd slice isSymbolByte (i + 1) = j) (hj : j < slice.size) :
    run ws slice ⟨.simpleSymbol, location, ByteArray.empty.push c⟩ (i + 1) (location.afterByte c) =
      ((if isDelimiter slice[j] then
          .tokenBefore ⟨.unquotedSymbol, (ByteArray.empty.push c) ++ bytesOf slice (i + 1) j,
            location, afterColumns location (j - i)⟩ j (Nat.le_refl _) hj
        else .error (failAtByte .missingDelimiter location (afterColumns location (j - i))) :
        Ran slice.size j).lift (by have := le_runEnd slice isSymbolByte (i + 1); omega)) := by
  have hle := le_runEnd slice isSymbolByte (i + 1)
  have hloc :
      afterColumns (location.afterByte c) (j - (i + 1)) = afterColumns location (j - i) := by
    rw [afterColumns_afterByte _ _ hc]
    congr 1; omega
  rw [run_simpleSymbol]
  subst hjdef
  have hstop := runEnd_stop slice isSymbolByte (i + 1) hj
  unfold runOrPending
  simp only [hj, dite_true]
  simp only [byteRan, advance, hstop, hloc, Bool.false_eq_true, ite_false]
  by_cases hd : isDelimiter slice[runEnd slice isSymbolByte (i + 1)] = true
  · simp only [hd, ite_true] <;> rfl
  · simp only [hd, Bool.false_eq_true, ite_false] <;> rfl

/-- Whitespace whose run ends inside the slice at a byte other than a line feed. -/
theorem run_space_inside (c : UInt8) (hc : c ≠ 10) (j : Nat)
    (hjdef : runEnd slice isWhitespaceRun (i + 1) = j) (hj : j < slice.size)
    (hn : slice[j] ≠ 10) :
    run ws slice ⟨.whitespace, location, ByteArray.empty.push c⟩ (i + 1) (location.afterByte c) =
      ((.tokenBefore ⟨.whitespace, (ByteArray.empty.push c) ++ bytesOf slice (i + 1) j,
            location, afterColumns location (j - i)⟩ j (Nat.le_refl _) hj :
        Ran slice.size j).lift (by have := le_runEnd slice isWhitespaceRun (i + 1); omega)) := by
  have hle := le_runEnd slice isWhitespaceRun (i + 1)
  have hloc :
      afterColumns (location.afterByte c) (j - (i + 1)) = afterColumns location (j - i) := by
    rw [afterColumns_afterByte _ _ hc]
    congr 1; omega
  rw [run_whitespace]
  subst hjdef
  have hstop := runEnd_stop slice isWhitespaceRun (i + 1) hj
  have hsp : isWhitespace slice[runEnd slice isWhitespaceRun (i + 1)] = false := by
    simp only [isWhitespaceRun, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hstop
    rcases hstop with h | h
    · exact h
    · exact absurd h hn
  unfold runOrPending
  simp only [hj, dite_true]
  simp only [byteRan, advance, hsp, hloc, Bool.false_eq_true, ite_false] <;> rfl

end

end BSmtLib.Proofs.Lexer.V3RunsV4FastPaths
