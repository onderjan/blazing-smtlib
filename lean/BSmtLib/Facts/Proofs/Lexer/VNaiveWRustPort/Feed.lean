module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure
public import BSmtLib.Facts.Proofs.Lexer.Consumers.Pure
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# The naive lexer's pure run over a slice from an index, for every consumer

`feedFrom` is the naive lexer's pure run up to an error `VNaive.lexBytesW` over the bytes of a
slice from an index on, for a consumer that takes whitespace and comments if `ws`
(`feedFrom_toByteSlice`), stated by indices, as the Rust port reads a slice: the state and the
location after the bytes and the lexemes they finish, or on an error, the lexemes finished before
it. The lemmas below are about the run over runs of bytes that a mode takes as they are, and
over the bytes that end a token.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed

open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure BSmtLib.Lexer.Internal.VNaive

/-- The bytes of the slice from `i` on, from the state at `location`, for a consumer that takes
whitespace and comments if `ws`: the state and the location after them and the lexemes they
finish, or on an error, the lexemes finished before it. -/
def feedFrom (version : Token.Version) (ws : Bool) (s : ByteSlice) (st : St)
    (location : Span.Location)
    (i : Nat) : Except (List Lexeme) (St × Span.Location × List Lexeme) :=
  if h : i < s.size then
    match byteStepW version ws st location s[i] with
    | none => .error (failedBeforeW ws st location s[i])
    | some (st', ls) => Prep ls (feedFrom version ws s st' (location.afterByte s[i]) (i + 1))
  else
    .ok (st, location, [])
termination_by s.size - i

theorem feedFrom_lt {version : Token.Version} {ws : Bool} {s : ByteSlice} {i : Nat} (h : i < s.size)
    (st : St) (location : Span.Location) :
    feedFrom version ws s st location i =
      match byteStepW version ws st location s[i] with
      | none => .error (failedBeforeW ws st location s[i])
      | some (st', ls) => Prep ls (feedFrom version ws s st'
          (location.afterByte s[i]) (i + 1)) := by
  rw [feedFrom]
  simp only [h, dite_true]

theorem feedFrom_ge {version : Token.Version} {ws : Bool} {s : ByteSlice} {i : Nat}
    (h : ¬ i < s.size)
    (st : St) (location : Span.Location) : feedFrom version ws s st location i = .ok
        (st, location, []) := by
  rw [feedFrom]
  simp only [h, dite_false]

/-- A byte that the pure step takes with the lexemes `ls`. -/
theorem feedFrom_step {version : Token.Version} {ws : Bool} {s : ByteSlice} {i : Nat}
    (h : i < s.size)
    {st st' : St} {location : Span.Location} {ls : List Lexeme}
    (hstep : byteStepW version ws st location s[i] = some (st', ls)) :
    feedFrom version ws s st location i =
      Prep ls (feedFrom version ws s st' (location.afterByte s[i]) (i + 1)) := by
  rw [feedFrom_lt h, hstep]

/-- A byte that the pure step fails at. -/
theorem feedFrom_fail {version : Token.Version} {ws : Bool} {s : ByteSlice} {i : Nat}
    (h : i < s.size)
    {st : St} {location : Span.Location} (hstep : byteStepW version ws st location s[i] = none) :
    feedFrom version ws s st location i = .error (failedBeforeW ws st location s[i]) := by
  rw [feedFrom_lt h, hstep]

/-- The run over a slice of the bytes of a list is the run over the list from the index on. -/
theorem feedFrom_toByteSlice (version : Token.Version) (ws : Bool) (bytes : List UInt8) :
    ∀ (n i : Nat), bytes.length - i = n → ∀ (st : St) (location : Span.Location),
      feedFrom version ws bytes.toByteArray.toByteSlice st location i =
        lexBytesW version ws st location (bytes.drop i) := by
  intro n
  induction n with
  | zero =>
    intro i hn st location
    have hle : bytes.length ≤ i := by omega
    rw [feedFrom_ge (by rw [size_toByteSlice]; omega), List.drop_eq_nil_of_le hle]
    rfl
  | succ n ih =>
    intro i hn st location
    have hlt : i < bytes.length := by omega
    have hs : i < bytes.toByteArray.toByteSlice.size := by rw [size_toByteSlice]; exact hlt
    rw [feedFrom_lt hs, getElem_toByteSlice, List.drop_eq_getElem_cons hlt]
    simp only [lexBytesW]
    cases byteStepW version ws st location bytes[i] with
    | none => rfl
    | some e =>
      obtain ⟨st', ls⟩ := e
      simp only
      rw [← getElem_toByteSlice bytes i hs, ih (i + 1) (by omega), getElem_toByteSlice]

section

variable (v : Token.Version) (ws : Bool) (s : ByteSlice)

/-- The naive lexer takes each byte of a run as a part of the token in progress. -/
theorem feedFrom_tokenRun (P : UInt8 → Bool) (hP10 : ∀ c, P c = true → c ≠ 10) (mode : Mode)
    (hstep : ∀ (q : Pending) (location : Span.Location) (c : UInt8), q.mode = mode → P c = true →
      byteStepW v ws (.token q) location c = some (.token { q with
          content := q.content.push c }, [])) :
    ∀ (n i : Nat), s.size - i = n → ∀ (q : Pending) (location : Span.Location), q.mode = mode →
      i ≤ s.size →
      feedFrom v ws s (.token q) location i =
        feedFrom v ws s (.token { q with content := q.content ++ bytesOf s i (runEnd s P i) })
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
    (hstep : ∀ (location : Span.Location) (c : UInt8), P c = true →
      byteStepW v ws .idle location c = some (.idle, [])) :
    ∀ (n i : Nat), s.size - i = n → ∀ (location : Span.Location), i ≤ s.size →
      feedFrom v ws s .idle location i =
        feedFrom v ws s .idle (afterColumns location (runEnd s P i - i))
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
theorem feedFrom_tokenBefore {j : Nat} (hj : j < s.size) {q : Pending} {location : Span.Location}
    {l : Lexeme} (h : advance ws q location s[j] = .tokenBefore l) :
    feedFrom v ws s (.token q) location j = Prep [l] (feedFrom v ws s .idle location j) := by
  rw [feedFrom_lt hj, feedFrom_lt hj]
  simp only [byteStepW, h]
  cases startStepW v ws location s[j] with
  | none => simp [failedBeforeW, h, withBefore]
  | some e =>
    obtain ⟨st, ls⟩ := e
    simp only [Option.map_some]
    rw [prep_prep]
    rfl

/-- A token in progress at a byte that it fails at. -/
theorem feedFrom_advance_error {j : Nat} (hj : j < s.size) {q : Pending} {location : Span.Location}
    {f : LexFailure} (h : advance ws q location s[j] = .error f) :
    feedFrom v ws s (.token q) location j = .error [] := by
  rw [feedFrom_lt hj]
  simp only [byteStepW, h, failedBeforeW]

/-- A byte that fails with no token in progress. -/
theorem feedFrom_start_error {j : Nat} (hj : j < s.size) {location : Span.Location} {f : LexFailure}
    (h : start v ws location s[j] = .error f) :
    feedFrom v ws s .idle location j = .error [] := by
  rw [feedFrom_lt hj]
  simp only [byteStepW, startStepW, h, failedBeforeW]

end

section

variable (v : Token.Version) (ws : Bool) (s : ByteSlice)

theorem byteStep_token_pending {q q' : Pending} {location : Span.Location} {c : UInt8}
    (h : advance ws q location c = .pending q') :
    byteStepW v ws (.token q) location c = some (.token q', []) := by
  simp [byteStepW, h]

theorem byteStep_token_idle {q : Pending} {location : Span.Location} {c : UInt8}
    (h : advance ws q location c = .idle) :
    byteStepW v ws (.token q) location c = some (.idle, []) := by
  simp [byteStepW, h]

theorem byteStep_idle_pending {p : Pending} {location : Span.Location} {c : UInt8}
    (h : start v ws location c = .pending p) :
    byteStepW v ws .idle location c = some (.token p, []) := by
  simp [byteStepW, startStepW, h]

theorem byteStep_idle_idle {location : Span.Location} {c : UInt8}
    (h : start v ws location c = .idle) :
    byteStepW v ws .idle location c = some (.idle, []) := by
  simp [byteStepW, startStepW, h]

/-- A run of bytes that a mode takes as they are. -/
theorem feedFrom_mode (P : UInt8 → Bool) (hP10 : ∀ c, P c = true → c ≠ 10) (mode : Mode)
    (hrun : ∀ (q : Pending) (location : Span.Location) (c : UInt8), q.mode = mode → P c = true →
      advance ws q location c = .pending { q with content := q.content.push c })
    (i : Nat) (q : Pending) (location : Span.Location) (hm : q.mode = mode) (hi : i ≤ s.size) :
    feedFrom v ws s (.token q) location i =
      feedFrom v ws s (.token { q with content := q.content ++ bytesOf s i (runEnd s P i) })
        (afterColumns location (runEnd s P i - i)) (runEnd s P i) :=
  feedFrom_tokenRun v ws s P hP10 mode
    (fun q location c hm hp => byteStep_token_pending v ws (hrun q location c hm hp)) _ i rfl q
    location hm hi

theorem afterColumns_add (location : Span.Location) (a b : Nat) :
    afterColumns (afterColumns location a) b = afterColumns location (a + b) := by
  simp only [afterColumns, Nat.add_assoc]

/-- A byte that starts a token, and the run of bytes that its mode takes as they are. -/
theorem feedFrom_startRun (P : UInt8 → Bool) (hP10 : ∀ c, P c = true → c ≠ 10) (mode : Mode)
    (hrun : ∀ (q : Pending) (location : Span.Location) (c : UInt8), q.mode = mode → P c = true →
      advance ws q location c = .pending { q with content := q.content.push c })
    {i : Nat} (hi : i < s.size) {location : Span.Location} {q : Pending}
    (hstart : start v ws location s[i] = .pending q) (hm : q.mode = mode)
    (h10 : s[i] ≠ 10) :
    feedFrom v ws s .idle location i =
      feedFrom v ws s
        (.token { q with content := q.content ++ bytesOf s (i + 1) (runEnd s P (i + 1)) })
        (afterColumns location (runEnd s P (i + 1) - i)) (runEnd s P (i + 1)) := by
  rw [feedFrom_step hi (byteStep_idle_pending v ws hstart), prep_nil,
    feedFrom_mode v ws s P hP10 mode hrun (i + 1) q _ hm hi, afterByte_eq_afterColumns' _ _ h10,
    afterColumns_add]
  have := le_runEnd s P (i + 1)
  congr 2
  omega

/-- The digits of a fraction: the first one is the first digit after the dot. -/
theorem feedFrom_fraction (i : Nat) (q : Pending) (location : Span.Location) (d : Bool)
    (hm : q.mode = .fraction d) (hi : i ≤ s.size) :
    feedFrom v ws s (.token q) location i =
      feedFrom v ws s (.token ⟨.fraction (d || decide (i < runEnd s isDigit i)), q.start,
          q.content ++ bytesOf s i (runEnd s isDigit i)⟩)
        (afterColumns location (runEnd s isDigit i - i)) (runEnd s isDigit i) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  by_cases hlt : i < runEnd s isDigit i
  · obtain ⟨his, hp⟩ := runEnd_start s isDigit i hlt
    have hr := runEnd_succ s isDigit i his hp
    have hadv : advance ws ⟨.fraction d, start, content⟩ location s[i] =
        .pending ⟨.fraction true, start, content.push s[i]⟩ := by
      simp [advance, hp]
    rw [feedFrom_step his (byteStep_token_pending v ws hadv), prep_nil,
      feedFrom_mode v ws s isDigit isDigit_ne (.fraction true)
        (fun q location c hm hc => advance_fraction_run ws q location c hm hc) (i + 1) _ _ rfl
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
theorem feedFrom_end {j : Nat} (hj : j < s.size) {q : Pending} {location : Span.Location}
    {l : Lexeme} {f : LexFailure}
    (h : advance ws q location s[j] =
      if isDelimiter s[j] then .tokenBefore l else .error f) :
    feedFrom v ws s (.token q) location j =
      if isDelimiter s[j] then Prep [l] (feedFrom v ws s .idle location j) else .error [] := by
  split
  · rename_i hd
    simp only [hd, ↓reduceIte] at h
    exact feedFrom_tokenBefore v ws s hj h
  · rename_i hd
    simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
    exact feedFrom_advance_error v ws s hj h

end

section

variable {ws : Bool} {q : Pending} {location : Span.Location} {c : UInt8}

theorem advance_end_simpleSymbol (hm : q.mode = .simpleSymbol) (hc : isSymbolByte c = false) :
    advance ws q location c =
      if isDelimiter c then .tokenBefore ⟨.unquotedSymbol, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance, hc]

theorem advance_end_keyword (hm : q.mode = .keyword) (hc : isSymbolByte c = false)
    (hne : q.content.isEmpty = false) :
    advance ws q location c =
      if isDelimiter c then .tokenBefore ⟨.keyword, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm hne
  subst hm
  simp [advance, hc, hne]

theorem advance_end_keyword_empty (hm : q.mode = .keyword) (hc : isSymbolByte c = false)
    (he : q.content.isEmpty = true) : ∃ f, advance ws q location c = .error f := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm he
  subst hm
  simp [advance, hc, he]

theorem advance_end_digits {radix : Radix} (hm : q.mode = .digits radix)
    (hc : radix.allows c = false) (hne : q.content.isEmpty = false) :
    advance ws q location c =
      if isDelimiter c then .tokenBefore ⟨radix.category, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm hne
  subst hm
  simp [advance, hc, hne]

theorem advance_end_digits_empty {radix : Radix} (hm : q.mode = .digits radix)
    (hc : radix.allows c = false) (he : q.content.isEmpty = true) :
    ∃ f, advance ws q location c = .error f := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm he
  subst hm
  simp [advance, hc, he]

theorem advance_end_numeral {z : Bool} (hm : q.mode = .numeral z) (hc : isDigit c = false)
    (hdot : c ≠ 46) :
    advance ws q location c =
      if isDelimiter c then .tokenBefore ⟨.numeral, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance, hc, hdot]

theorem advance_end_fraction (hm : q.mode = .fraction true) (hc : isDigit c = false) :
    advance ws q location c =
      if isDelimiter c then .tokenBefore ⟨.decimal, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance, hc]

theorem advance_end_fraction_none (hm : q.mode = .fraction false) (hc : isDigit c = false) :
    ∃ f, advance ws q location c = .error f := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance, hc]

theorem advance_end_quotedSymbolClosed (hm : q.mode = .quotedSymbolClosed) :
    advance ws q location c =
      if isDelimiter c then .tokenBefore ⟨.quotedSymbol, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance]

theorem advance_end_stringQuote (hm : q.mode = .stringQuote) (hc : c ≠ 34) :
    advance ws q location c =
      if isDelimiter c then .tokenBefore ⟨.string, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance, hc]

theorem advance_end_legacyQuote (hm : q.mode = .legacyQuote) :
    advance ws q location c =
      if isDelimiter c then .tokenBefore ⟨.string, q.content, q.start, location⟩
      else .error (failAtByte .missingDelimiter q.start location) := by
  obtain ⟨mode, start, content⟩ := q
  simp only at hm
  subst hm
  simp [advance]

end

theorem start_digit (v : Token.Version) (ws : Bool) (location : Span.Location) {c : UInt8}
    (hd : isDigit c = true) :
    start v ws location c = .pending ⟨.numeral (c == 48), location, ByteArray.empty.push c⟩ := by
  have := digit_facts c
  simp only [hd, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := this
  simp [start, h1, h2, h3, h4, h5, h6, h7, h8, hd]

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
