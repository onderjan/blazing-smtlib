import BSmtLib.Proofs.V1NaiveWRustPort.Step

/-!
# The naive lexer's pure run over the pieces of a token

What the naive lexer's pure run `feedFrom` does over the pieces of a token that the Rust port
lexes in one go: the run of bytes that a mode takes as they are (`feedFrom_mode`), the first
digit of a fraction (`feedFrom_fraction`), and the byte that ends a token, which delimits it or
raises an error (`feedFrom_end`).
-/

namespace BSmtLib.Proofs.Lexer.V1NaiveWRustPort

open V1Naive BSmtLib.Proofs.Simulation

theorem afterByte_eq_afterColumns' (location : Location) (c : UInt8) (h : c ≠ 10) :
    location.afterByte c = afterColumns location 1 := by
  rw [← afterColumns_afterByte location c h 0, afterColumns_zero]

section

variable (v : Version) (s : ByteSlice)

theorem byteStep_token_pending {q q' : Pending} {location : Location} {c : UInt8}
    (h : advance false q location c = .pending q') :
    byteStep v (.token q) location c = some (.token q', []) := by
  simp [byteStep, h]

theorem byteStep_token_idle {q : Pending} {location : Location} {c : UInt8}
    (h : advance false q location c = .idle) :
    byteStep v (.token q) location c = some (.idle, []) := by
  simp [byteStep, h]

theorem byteStep_idle_pending {p : Pending} {location : Location} {c : UInt8}
    (h : start v false location c = .pending p) :
    byteStep v .idle location c = some (.token p, []) := by
  simp [byteStep, startStep, h]

theorem byteStep_idle_idle {location : Location} {c : UInt8}
    (h : start v false location c = .idle) :
    byteStep v .idle location c = some (.idle, []) := by
  simp [byteStep, startStep, h]

/-- A run of bytes that a mode takes as they are. -/
theorem feedFrom_mode (P : UInt8 → Bool) (hP10 : ∀ c, P c = true → c ≠ 10) (mode : Mode)
    (hrun : ∀ (q : Pending) (location : Location) (c : UInt8), q.mode = mode → P c = true →
      advance false q location c = .pending { q with content := q.content.push c })
    (i : Nat) (q : Pending) (location : Location) (hm : q.mode = mode) (hi : i ≤ s.size) :
    feedFrom v s (.token q) location i =
      feedFrom v s (.token { q with content := q.content ++ bytesOf s i (runEnd s P i) })
        (afterColumns location (runEnd s P i - i)) (runEnd s P i) :=
  feedFrom_tokenRun v s P hP10 mode
    (fun q location c hm hp => byteStep_token_pending v (hrun q location c hm hp)) _ i rfl q
    location hm hi

theorem afterColumns_add (location : Location) (a b : Nat) :
    afterColumns (afterColumns location a) b = afterColumns location (a + b) := by
  simp only [afterColumns, Nat.add_assoc]

/-- A byte that starts a token, and the run of bytes that its mode takes as they are. -/
theorem feedFrom_startRun (P : UInt8 → Bool) (hP10 : ∀ c, P c = true → c ≠ 10) (mode : Mode)
    (hrun : ∀ (q : Pending) (location : Location) (c : UInt8), q.mode = mode → P c = true →
      advance false q location c = .pending { q with content := q.content.push c })
    {i : Nat} (hi : i < s.size) {location : Location} {q : Pending}
    (hstart : start v false location s[i] = .pending q) (hm : q.mode = mode)
    (h10 : s[i] ≠ 10) :
    feedFrom v s .idle location i =
      feedFrom v s
        (.token { q with content := q.content ++ bytesOf s (i + 1) (runEnd s P (i + 1)) })
        (afterColumns location (runEnd s P (i + 1) - i)) (runEnd s P (i + 1)) := by
  rw [feedFrom_step hi (byteStep_idle_pending v hstart), prep_nil,
    feedFrom_mode v s P hP10 mode hrun (i + 1) q _ hm hi, afterByte_eq_afterColumns' _ _ h10,
    afterColumns_add]
  have := le_runEnd s P (i + 1)
  congr 2
  omega

/-- The digits of a fraction: the first one is the first digit after the dot. -/
theorem feedFrom_fraction (i : Nat) (q : Pending) (location : Location) (d : Bool)
    (hm : q.mode = .fraction d) (hi : i ≤ s.size) :
    feedFrom v s (.token q) location i =
      feedFrom v s (.token ⟨.fraction (d || decide (i < runEnd s isDigit i)), q.start,
          q.content ++ bytesOf s i (runEnd s isDigit i)⟩)
        (afterColumns location (runEnd s isDigit i - i)) (runEnd s isDigit i) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  by_cases hlt : i < runEnd s isDigit i
  · obtain ⟨his, hp⟩ := runEnd_start s isDigit i hlt
    have hr := runEnd_succ s isDigit i his hp
    have hadv : advance false ⟨.fraction d, start, content⟩ location s[i] =
        .pending ⟨.fraction true, start, content.push s[i]⟩ := by
      simp [advance, hp]
    rw [feedFrom_step his (byteStep_token_pending v hadv), prep_nil,
      feedFrom_mode v s isDigit isDigit_ne (.fraction true)
        (fun q location c hm hc => advance_fraction_run false q location c hm hc) (i + 1) _ _ rfl
        his]
    have hle := le_runEnd s isDigit (i + 1)
    have hle' := runEnd_le s isDigit (i + 1) his
    simp only [← hr, hlt, decide_true, Bool.or_true]
    rw [push_append_bytesOf _ s his (by omega) (by omega),
      afterColumns_afterByte _ _ (isDigit_ne _ hp),
      show runEnd s isDigit i - (i + 1) + 1 = runEnd s isDigit i - i by omega]
  · have he : runEnd s isDigit i = i := by
      have := le_runEnd s isDigit i
      omega
    rw [he, bytesOf_self s i hi, ByteArray.append_empty, Nat.sub_self, afterColumns_zero]
    simp

/-- A byte that ends the token in progress: if it delimits the token, the token is handed over
and the byte is lexed with no token in progress; otherwise the run fails. -/
theorem feedFrom_end {j : Nat} (hj : j < s.size) {q : Pending} {location : Location}
    {l : Lexeme} {f : LexFailure}
    (h : advance false q location s[j] =
      if isDelimiter s[j] then .tokenBefore l else .error f) :
    feedFrom v s (.token q) location j =
      if isDelimiter s[j] then Prep [l] (feedFrom v s .idle location j) else .error [] := by
  split
  · rename_i hd
    simp only [hd, ↓reduceIte] at h
    exact feedFrom_tokenBefore v s hj h
  · rename_i hd
    simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
    exact feedFrom_advance_error v s hj h

end

/-! ## The bytes that end a token -/

section

variable {q : Pending} {location : Location} {c : UInt8}

theorem advance_end_simpleSymbol (hm : q.mode = .simpleSymbol) (hc : isSymbolByte c = false) :
    advance false q location c =
      if isDelimiter c then .tokenBefore ⟨.unquotedSymbol, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance, hc]

theorem advance_end_keyword (hm : q.mode = .keyword) (hc : isSymbolByte c = false)
    (hne : q.content.isEmpty = false) :
    advance false q location c =
      if isDelimiter c then .tokenBefore ⟨.keyword, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm hne
  subst hm
  simp [advance, hc, hne]

theorem advance_end_keyword_empty (hm : q.mode = .keyword) (hc : isSymbolByte c = false)
    (he : q.content.isEmpty = true) : ∃ f, advance false q location c = .error f := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm he
  subst hm
  simp [advance, hc, he]

theorem advance_end_digits {radix : Radix} (hm : q.mode = .digits radix)
    (hc : radix.allows c = false) (hne : q.content.isEmpty = false) :
    advance false q location c =
      if isDelimiter c then .tokenBefore ⟨radix.category, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm hne
  subst hm
  simp [advance, hc, hne]

theorem advance_end_digits_empty {radix : Radix} (hm : q.mode = .digits radix)
    (hc : radix.allows c = false) (he : q.content.isEmpty = true) :
    ∃ f, advance false q location c = .error f := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm he
  subst hm
  simp [advance, hc, he]

theorem advance_end_numeral {z : Bool} (hm : q.mode = .numeral z) (hc : isDigit c = false)
    (hdot : c ≠ 46) :
    advance false q location c =
      if isDelimiter c then .tokenBefore ⟨.numeral, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance, hc, hdot]

theorem advance_end_fraction (hm : q.mode = .fraction true) (hc : isDigit c = false) :
    advance false q location c =
      if isDelimiter c then .tokenBefore ⟨.decimal, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance, hc]

theorem advance_end_fraction_none (hm : q.mode = .fraction false) (hc : isDigit c = false) :
    ∃ f, advance false q location c = .error f := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance, hc]

theorem advance_end_quotedSymbolClosed (hm : q.mode = .quotedSymbolClosed) :
    advance false q location c =
      if isDelimiter c then .tokenBefore ⟨.quotedSymbol, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance]

theorem advance_end_stringQuote (hm : q.mode = .stringQuote) (hc : c ≠ 34) :
    advance false q location c =
      if isDelimiter c then .tokenBefore ⟨.string, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance, hc]

theorem advance_end_legacyQuote (hm : q.mode = .legacyQuote) :
    advance false q location c =
      if isDelimiter c then .tokenBefore ⟨.string, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance]

end

/-! ## The bytes of a piece of a slice -/

theorem bytesOf_size (s : ByteSlice) {i j : Nat} (hij : i ≤ j) (hj : j ≤ s.size) :
    (bytesOf s i j).size = j - i := by
  show (bytesOf s i j).data.size = j - i
  have h2 := s.stop_le_size_byteArray
  simp only [ByteSlice.size] at hj
  simp only [ByteArray.size] at h2
  rw [data_bytesOf s hij hj, Array.size_extract]
  omega

theorem bytesOf_get! (s : ByteSlice) {i j k : Nat} (hij : i ≤ j) (hj : j ≤ s.size)
    (hk : i + k < j) : (bytesOf s i j).get! k = s[i + k]'(by omega) := by
  have h2 := s.stop_le_size_byteArray
  simp only [ByteSlice.size] at hj
  simp only [ByteArray.size] at h2
  show (bytesOf s i j).data[k]! = _
  rw [data_bytesOf s hij (by simp only [ByteSlice.size]; omega), getElem_slice]
  rw [getElem!_pos _ _ (by rw [Array.size_extract]; omega), Array.getElem_extract]
  congr 1
  omega

/-- Every byte of a run passes its test. -/
theorem runEnd_mem (s : ByteSlice) (P : UInt8 → Bool) (i : Nat) :
    ∀ k (hk : k < s.size), i ≤ k → k < runEnd s P i → P s[k] = true := by
  fun_induction runEnd s P i with
  | case1 i hi hp ih =>
    intro k hk hik hkr
    by_cases e : k = i
    · subst e; exact hp
    · exact ih k hk (by omega) hkr
  | case2 i hi hp => intro k hk hik hkr; omega
  | case3 i hi => intro k hk hik hkr; omega

theorem digit_facts (c : UInt8) :
    (!isDigit c || (!isWhitespace c && c != 40 && c != 41 && c != 59 && c != 35 && c != 34 &&
      c != 58 && c != 124)) = true :=
  byte_table (P := fun c => (!isDigit c || (!isWhitespace c && c != 40 && c != 41 && c != 59 &&
    c != 35 && c != 34 && c != 58 && c != 124)) = true) (by decide +kernel) c

theorem start_digit (v : Version) (location : Location) {c : UInt8} (hd : isDigit c = true) :
    start v false location c = .pending ⟨.numeral (c == 48), location, ByteArray.empty.push c⟩ := by
  have := digit_facts c
  simp only [hd, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := this
  simp [start, h1, h2, h3, h4, h5, h6, h7, h8, hd]

/-- The last stored byte of a piece of a slice. -/
theorem stored_last (s : ByteSlice) {i j : Nat} (hij : i < j) (hj : j ≤ s.size) :
    lastOf (bytesOf s i j) = some (s[j - 1]'(by omega)) := by
  have hs := bytesOf_size s (Nat.le_of_lt hij) hj
  simp only [lastOf, hs, show (j - i == 0) = false by simp; omega,
    Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
  rw [bytesOf_get! s (Nat.le_of_lt hij) hj (k := j - i - 1) (by omega)]
  congr 1
  omega

theorem bytesOf_append (s : ByteSlice) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k)
    (hk : k ≤ s.size) : bytesOf s i j ++ bytesOf s j k = bytesOf s i k := by
  apply ByteArray.ext
  have h2 := s.stop_le_size_byteArray
  simp only [ByteSlice.size] at hk
  simp only [ByteArray.size] at h2
  rw [ByteArray.data_append, data_bytesOf s hij (by simp only [ByteSlice.size]; omega),
    data_bytesOf s hjk (by simp only [ByteSlice.size]; omega),
    data_bytesOf s (Nat.le_trans hij hjk) (by simp only [ByteSlice.size]; omega)]
  apply Array.ext
  · simp only [Array.size_append, Array.size_extract]; omega
  · intro n h1 h3
    simp only [Array.size_append, Array.size_extract] at h1
    rw [Array.getElem_append, Array.getElem_extract]
    split
    · rw [Array.getElem_extract]
    · rename_i hn
      have hm : min (s.start + j) s.byteArray.data.size = s.start + j := Nat.min_eq_left (by omega)
      simp only [Array.size_extract, hm] at hn ⊢
      rw [Array.getElem_extract]
      congr 1
      omega

/-- The last byte of a piece of a slice, borrowed from it. -/
theorem borrowed_last (s : ByteSlice) {i j : Nat} (hij : i < j) (hj : j ≤ s.size)
    (stored : BSmtLib.Lexer.ContentBuffer) :
    (Lexer.Slice.borrow s i j).last? stored = some (s[j - 1]'(by omega)) := by
  have h1 := s.stop_le_size_byteArray
  have h2 := s.start_le_stop
  simp only [ByteSlice.size] at hj
  simp only [Lexer.Slice.borrow, BSmtLib.Lexer.Content.last?,
    show (s.start + j == s.start + i) = false by simp; omega, Bool.false_eq_true, ↓reduceIte,
    Option.some.injEq]
  rw [getElem_slice, get!_eq_getElem!]
  simp only [ByteArray.size] at h1
  rw [getElem!_pos _ _ (by simp only [ByteArray.size]; omega)]
  congr 1
  omega

end BSmtLib.Proofs.Lexer.V1NaiveWRustPort
