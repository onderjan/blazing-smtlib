import BSmtLib.Proofs.VNaiveWRustPort.Feed
import BSmtLib.Proofs.VNaiveWRustPort.Tables

/-!
# The Rust port's runs against the naive lexer's bytes

A run scan of the Rust port ends where the run of bytes that pass a test ends (`runEnd`), by
the byte tables, and the naive lexer's pure run over the bytes of a run takes each as a part of
the token, or passes it over (`feedFrom_tokenRun`, `feedFrom_idleRun`). A token ended by a byte
that delimits it is handed over before the byte, which is then lexed with no token in progress
(`feedFrom_tokenBefore`).
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open VNaive BSmtLib.Proofs.Simulation
open BSmtLib.Lexer (endsRun RUN_FLAGS RUN_DIGIT RUN_SIMPLE_SYMBOL RUN_HEX_DIGIT RUN_BINARY_DIGIT
  RUN_NON_LF_WHITESPACE RUN_QUOTED_PLAIN RUN_STRING_PLAIN RUN_COMMENT_PLAIN)

/-! ## Run scans -/

theorem runEndBy_eq (stops : UInt8 → Bool) (P : UInt8 → Bool) (hP : ∀ c, stops c = !P c)
    (s : ByteSlice) (i : Nat) : Lexer.Slice.runEndBy stops s i = runEnd s P i := by
  fun_induction Lexer.Slice.runEndBy stops s i with
  | case1 i h hs =>
    rw [runEnd]
    simp only [h, dite_true]
    rw [hP] at hs
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hs
    simp [hs]
  | case2 i h hs ih =>
    rw [runEnd]
    simp only [h, dite_true]
    rw [hP] at hs
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hs
    simp [hs, ih]
  | case3 i h =>
    rw [runEnd]
    simp [h]

/-- A run scan of the Rust port with a mask, as a run of bytes that pass a test. -/
theorem runEnd_eq {mask : UInt8} {P : UInt8 → Bool} (hP : ∀ c, endsRun c mask = !P c)
    (s : ByteSlice) (i : Nat) : Lexer.Slice.runEnd s i mask = runEnd s P i :=
  runEndBy_eq _ P hP s i

/-- A run scan of the Rust port from within the slice ends within it. -/
theorem runEndBy_le (stops : UInt8 → Bool) (s : ByteSlice) {i : Nat} (h : i ≤ s.size) :
    Lexer.Slice.runEndBy stops s i ≤ s.size := by
  rw [runEndBy_eq stops (fun c => !stops c) (fun c => by simp) s i]
  exact runEnd_le s _ i h

/-- Shows that an index into the slice, possibly the end of a run scan, is within the slice. -/
macro "bound_tac" : tactic =>
  `(tactic| first
    | omega
    | exact runEndBy_le _ _ (by omega))

/-- Shows that the content buffer of a token begun in the step fits its array. -/
macro "fits_tac" : tactic =>
  `(tactic| first
    | exact fits_clear_extendSlice _ _ (by bound_tac)
    | exact fits_clear _
    | exact fits_push (fits_clear _) _
    | exact fits_empty)

/-- The run of the Rust port over a string under version 2.0. -/
theorem runEndAll_legacy (s : ByteSlice) (i : Nat) :
    Lexer.Slice.runEndAll s i (RUN_STRING_PLAIN ||| RUN_QUOTED_PLAIN) =
      runEnd s isLegacyRun i :=
  runEndBy_eq _ isLegacyRun endsRunAll_legacy s i

/-! ## The naive lexer over runs -/

section

variable (v : Version) (s : ByteSlice)

/-- The naive lexer takes each byte of a run as a part of the token in progress. -/
theorem feedFrom_tokenRun (P : UInt8 → Bool) (hP10 : ∀ c, P c = true → c ≠ 10) (mode : Mode)
    (hstep : ∀ (q : Pending) (location : Location) (c : UInt8), q.mode = mode → P c = true →
      byteStep v (.token q) location c = some (.token { q with content := q.content.push c }, [])) :
    ∀ (n i : Nat), s.size - i = n → ∀ (q : Pending) (location : Location), q.mode = mode →
      i ≤ s.size →
      feedFrom v s (.token q) location i =
        feedFrom v s (.token { q with content := q.content ++ bytesOf s i (runEnd s P i) })
          (afterColumns location (runEnd s P i - i)) (runEnd s P i) := by
  intro n
  induction n with
  | zero =>
    intro i hn q location hm hi
    have he : runEnd s P i = i := by
      rw [runEnd]; simp [show ¬ i < s.size by omega]
    rw [he, bytesOf_self s i hi, ByteArray.append_empty, Nat.sub_self, afterColumns_zero]
  | succ n ih =>
    intro i hn q location hm hi
    have hlt : i < s.size := by omega
    by_cases hp : P s[i] = true
    · have hr := runEnd_succ s P i hlt hp
      rw [feedFrom_step hlt (hstep q location s[i] hm hp),
        ih (i + 1) (by omega) { q with content := q.content.push s[i] } _ hm hlt, hr]
      have hle := le_runEnd s P (i + 1)
      have hle' := runEnd_le s P (i + 1) (by omega)
      rw [prep_nil, push_append_bytesOf _ s hlt (by omega) hle',
        afterColumns_afterByte _ _ (hP10 _ hp), show runEnd s P (i + 1) - (i + 1) + 1 =
          runEnd s P (i + 1) - i by omega]
    · have he : runEnd s P i = i := by
        rw [runEnd]; simp [hlt, hp]
      rw [he, bytesOf_self s i hi, ByteArray.append_empty, Nat.sub_self, afterColumns_zero]

/-- The naive lexer passes each byte of a run over with no token in progress. -/
theorem feedFrom_idleRun (P : UInt8 → Bool) (hP10 : ∀ c, P c = true → c ≠ 10)
    (hstep : ∀ (location : Location) (c : UInt8), P c = true →
      byteStep v .idle location c = some (.idle, [])) :
    ∀ (n i : Nat), s.size - i = n → ∀ (location : Location), i ≤ s.size →
      feedFrom v s .idle location i =
        feedFrom v s .idle (afterColumns location (runEnd s P i - i))
          (runEnd s P i) := by
  intro n
  induction n with
  | zero =>
    intro i hn location hi
    have he : runEnd s P i = i := by
      rw [runEnd]; simp [show ¬ i < s.size by omega]
    rw [he, Nat.sub_self, afterColumns_zero]
  | succ n ih =>
    intro i hn location hi
    have hlt : i < s.size := by omega
    by_cases hp : P s[i] = true
    · have hr := runEnd_succ s P i hlt hp
      rw [feedFrom_step hlt (hstep location s[i] hp), ih (i + 1) (by omega) _ hlt, hr, prep_nil]
      have hle := le_runEnd s P (i + 1)
      rw [afterColumns_afterByte _ _ (hP10 _ hp), show runEnd s P (i + 1) - (i + 1) + 1 =
          runEnd s P (i + 1) - i by omega]
    · have he : runEnd s P i = i := by
        rw [runEnd]; simp [hlt, hp]
      rw [he, Nat.sub_self, afterColumns_zero]

/-- A token ended by the byte at `j`, which delimits it, is handed over, and the byte is lexed
with no token in progress. -/
theorem feedFrom_tokenBefore {j : Nat} (hj : j < s.size) {q : Pending} {location : Location}
    {l : Lexeme} (h : advance false q location s[j] = .tokenBefore l) :
    feedFrom v s (.token q) location j = Prep [l] (feedFrom v s .idle location j) := by
  rw [feedFrom_lt hj, feedFrom_lt hj]
  simp only [byteStep, h]
  cases startStep v location s[j] with
  | none => simp [failedBefore, h, withBefore]
  | some e =>
    obtain ⟨st, ls⟩ := e
    simp only [Option.map_some]
    rw [prep_prep]
    rfl

/-- A token in progress at a byte that it fails at. -/
theorem feedFrom_advance_error {j : Nat} (hj : j < s.size) {q : Pending} {location : Location}
    {f : LexFailure} (h : advance false q location s[j] = .error f) :
    feedFrom v s (.token q) location j = .error [] := by
  rw [feedFrom_lt hj]
  simp only [byteStep, h, failedBefore]

/-- A byte that fails with no token in progress. -/
theorem feedFrom_start_error {j : Nat} (hj : j < s.size) {location : Location} {f : LexFailure}
    (h : start v false location s[j] = .error f) :
    feedFrom v s .idle location j = .error [] := by
  rw [feedFrom_lt hj]
  simp only [byteStep, startStep, h, failedBefore]

end

end BSmtLib.Proofs.Lexer.VNaiveWRustPort
