import BSmtLib.Proofs.V1Naive.Sound

/-!
# The naive lexer finishes every tokenisation

`run_complete`: when an input has a tokenisation, the pure run of the naive lexer finishes it
and gives the lexemes of its tokens and then the end-of-file lexeme. The proof follows the
tokenisation: the run passes over whitespace without a lexeme, and over each token to a state
that finishes the token's lexeme at the delimiter or the end of the input after it.
-/

namespace BSmtLib.Proofs.Lexer.V1Naive

open BSmtLib.Spec.Lexicon BSmtLib.Spec.Lexicon.Regex BSmtLib.SpecChecks.Lexicon

/-! ## Runs that finish no lexeme -/

/-- `Reaches version st location bytes st'`: the bytes take the run from `st` at `location` to
`st'`, finishing no lexeme. -/
def Reaches (version : Version) (st : St) (location : Location) (bytes : List UInt8)
    (st' : St) : Prop :=
  feedBytes version st location bytes = some (st', advanceLoc location bytes, [])

theorem reaches_nil {version : Version} {st : St} {location : Location} :
    Reaches version st location [] st := rfl

theorem reaches_cons {version : Version} {st st₁ st' : St} {location : Location} {c : UInt8}
    {cs : List UInt8} (h : byteStep version st location c = some (st₁, []))
    (h' : Reaches version st₁ (location.afterByte c) cs st') :
    Reaches version st location (c :: cs) st' := by
  unfold Reaches at h' ⊢
  simp only [feedBytes, h, h', Option.map_some, List.nil_append]
  rfl

theorem reaches_append {version : Version} {st st₁ st' : St} {location : Location}
    {a b : List UInt8} (h : Reaches version st location a st₁)
    (h' : Reaches version st₁ (advanceLoc location a) b st') :
    Reaches version st location (a ++ b) st' := by
  unfold Reaches at h h' ⊢
  rw [feedBytes_append, h]
  simp [h', advanceLoc_append]

theorem reaches_pending {version : Version} {p p' : Pending} {location : Location} {c : UInt8}
    (h : advance false p location c = .pending p') :
    byteStep version (.token p) location c = some (.token p', []) := by
  simp [byteStep, h]

theorem runFrom_reaches {version : Version} {st st' : St} {location : Location}
    {a b : List UInt8} (h : Reaches version st location a st') :
    runFrom version st location (a ++ b) = runFrom version st' (advanceLoc location a) b := by
  rw [runFrom_append, h]
  simp

/-- Bytes that each go on with the token in progress, keeping the invariant `I` of it and of
the bytes so far. -/
theorem reaches_segment {version : Version} {I : Pending → Chars → Prop} (xs : Chars)
    (hstep : ∀ q pre location x, I q pre → x ∈ xs →
      ∃ q', advance false q location x = .pending q' ∧ I q' (pre ++ [x])) :
    ∀ p pre location, I p pre →
      ∃ p', Reaches version (.token p) location xs (.token p') ∧ I p' (pre ++ xs) := by
  induction xs with
  | nil => exact fun p pre location h => ⟨p, reaches_nil, by simpa using h⟩
  | cons x xs ih =>
    intro p pre location h
    obtain ⟨q, hq, hI⟩ := hstep p pre location x h (by simp)
    obtain ⟨p', hr, hI'⟩ := ih (fun q pre location y hq hy => hstep q pre location y hq (by
      simp [hy])) q (pre ++ [x]) (location.afterByte x) hI
    exact ⟨p', reaches_cons (reaches_pending hq) hr, by simpa using hI'⟩

/-! ## Whitespace -/

theorem start_whitespace {version : Version} {location : Location} {c : UInt8}
    (h : whiteSpaceChar [c]) : start version false location c = .idle := by
  have hw := (whitespace_iff c).mpr h
  simp [start, hw]

theorem start_comment (version : Version) (location : Location) :
    start version false location 59 =
      .pending { mode := .comment, start := location, content := .empty } := by
  rfl


/-- A comment without its line break leaves the run in a comment. -/
theorem reaches_openComment {version : Version} {location : Location} {b : Chars}
    (hb : ∀ x ∈ b, ¬ LineBreak x.toNat) :
    ∃ p, Reaches version .idle location (59 :: b) (.token p) ∧ p.mode = .comment := by
  obtain ⟨p', hr, hm⟩ := reaches_segment (version := version)
    (I := fun q _ => q.mode = .comment) b (fun q pre loc x hq hx => by
      have hx' : ((x == 10) || (x == 13)) = false := by
        cases h : ((x == 10) || (x == 13))
        · rfl
        · exact absurd ((lineBreak_iff x).mp h) (hb x hx)
      exact ⟨{ mode := .comment, start := q.start, content := q.content.push x },
        by simp [advance, hq, hx'], rfl⟩)
    { mode := .comment, start := location, content := .empty } [] (location.afterByte 59) rfl
  exact ⟨p', reaches_cons (by simp [byteStep, startStep, start_comment]) hr, hm⟩

/-- A comment and the line break that ends it leave the run with no token in progress. -/
theorem reaches_comment {version : Version} {location : Location} {b : Chars} {l : UInt8}
    (hb : ∀ x ∈ b, ¬ LineBreak x.toNat) (hl : LineBreak l.toNat) :
    Reaches version .idle location (59 :: (b ++ [l])) .idle := by
  obtain ⟨p, hr, hm⟩ := reaches_openComment (version := version) (location := location) hb
  have hl' := (lineBreak_iff l).mpr hl
  exact reaches_append (a := 59 :: b) hr
    (reaches_cons (st₁ := .idle) (by simp [byteStep, advance, hm, hl']) reaches_nil)

theorem reaches_wsPart {version : Version} {location : Location} {p : Chars}
    (h : alt whiteSpaceChar comment p) : Reaches version .idle location p .idle := by
  rcases h with h | h
  · obtain ⟨c, rfl, -⟩ := whiteSpaceChar_inv h
    exact reaches_cons (by simp [byteStep, startStep, start_whitespace h]) reaches_nil
  · obtain ⟨b, l, rfl, hb, hl⟩ := comment_inv h
    exact reaches_comment hb hl

/-- Whitespace leaves the run with no token in progress. -/
theorem reaches_whitespace {version : Version} {w : Chars} (h : whitespace w) :
    ∀ location, Reaches version .idle location w .idle := by
  obtain ⟨parts, rfl, hparts⟩ := h
  induction parts with
  | nil => exact fun _ => reaches_nil
  | cons p ps ih =>
    intro location
    exact reaches_append (reaches_wsPart (hparts p (by simp)))
      (ih (fun q hq => hparts q (List.mem_cons_of_mem _ hq)) _)

/-- Whitespace at the end of the input finishes only the end-of-file lexeme. -/
theorem runFrom_whitespaceAtEnd {version : Version} {e : Chars} (h : whitespaceAtEnd e)
    (location : Location) :
    runFrom version .idle location e = some [eofLexeme (advanceLoc location e)] := by
  obtain ⟨w, z, rfl, hw, hz⟩ := h
  rw [runFrom_reaches (reaches_whitespace hw location), advanceLoc_append]
  rcases hz with rfl | hz
  · rfl
  · obtain ⟨b, rfl, hb⟩ := commentAtEnd_inv hz
    obtain ⟨p, hr, hm⟩ := reaches_openComment (version := version)
      (location := advanceLoc location w) hb
    have e : (59 :: b) = (59 :: b) ++ [] := by simp
    rw [e, runFrom_reaches hr, runFrom_nil]
    simp [endStep, finish, hm]


/-! ## Tokens -/

/-- The lexeme of a token of the kind with the characters `text`, from `start` to `end`. -/
def lexemeFor (version : Spec.Lexicon.Version) (category : Category) (start «end» : Location)
    (text : Chars) : Lexeme :=
  { category := lexCategory category,
    content := ⟨(Spec.Lexicon.Token.content version ⟨category, 0, text⟩).toArray⟩,
    start, «end» }

/-- From no token in progress at any location, the characters `text` of a token of the kind,
followed by what may follow such a token, finish the token's lexeme before the rest. -/
def TokenRun (version : Spec.Lexicon.Version) (category : Category) (text : Chars) : Prop :=
  ∀ location rest, DelimRest rest →
    runFrom (Adapter.toVersion version) .idle location (text ++ rest) =
      (runFrom (Adapter.toVersion version) .idle (advanceLoc location text) rest).map
        (lexemeFor version category location (advanceLoc location text) text :: ·)

/-- The token in progress `p` finishes as the token of the kind with the characters `text`
from `start`, at a delimiter or at the end of the input. -/
def Closes (version : Spec.Lexicon.Version) (category : Category) (start : Location)
    (text : Chars) (p : Pending) : Prop :=
  (∀ location d, Delim d.toNat → ∃ l, advance false p location d = .tokenBefore l ∧
    LexemeIs version category start location text l) ∧
  (∀ location, ∃ l, finish false p location = .token l ∧
    LexemeIs version category start location text l)

theorem tokenRun_of_closes {version : Spec.Lexicon.Version} {category : Category}
    {text : Chars}
    (h : ∀ location, ∃ p, Reaches (Adapter.toVersion version) .idle location text (.token p) ∧
      Closes version category location text p) :
    TokenRun version category text := by
  intro location rest hrest
  obtain ⟨p, hr, hadv, hfin⟩ := h location
  rw [runFrom_reaches hr]
  generalize advanceLoc location text = loc'
  rcases hrest with rfl | ⟨d, r, rfl, hd⟩
  · obtain ⟨l, hf, hl⟩ := hfin loc'
    rw [runFrom_nil, runFrom_nil]
    simp [endStep, hf, lexemeIs_eq hl, lexemeFor]
  · obtain ⟨l, ha, hl⟩ := hadv loc' d hd
    rw [runFrom_cons, runFrom_cons]
    simp only [byteStep, ha]
    rw [lexemeIs_eq hl]
    cases startStep (Adapter.toVersion version) loc' d with
    | none => rfl
    | some e =>
      obtain ⟨st, ls⟩ := e
      simp only [Option.map_some, Option.bind_some]
      cases runFrom (Adapter.toVersion version) st (loc'.afterByte d) r <;> rfl

/-- What a delimiter is not. -/
theorem delim_facts {d : UInt8} (h : Delim d.toNat) :
    isDigit d = false ∧ d ≠ 46 ∧ isSymbolByte d = false ∧ isHexDigit d = false ∧
      isBinaryDigit d = false ∧ d ≠ 34 ∧ isDelimiter d = true := by
  revert h
  refine byte_cases (P := fun d => Delim d.toNat → isDigit d = false ∧ d ≠ 46 ∧
      isSymbolByte d = false ∧ isHexDigit d = false ∧ isBinaryDigit d = false ∧ d ≠ 34 ∧
      isDelimiter d = true) ?_ d
  unfold Delim
  decide +kernel

/-! ## Closing the token in progress -/

theorem closes_numeral {version : Spec.Lexicon.Version} {start : Location} {s : Chars}
    {p : Pending} {zero : Bool} (hm : p.mode = .numeral zero) (hs : p.start = start)
    (hk : p.content.data.toList = s) :
    Closes version .numeral start s p := by
  refine ⟨fun loc d hd => ?_, fun loc => ?_⟩
  · obtain ⟨h1, h2, -, -, -, -, h7⟩ := delim_facts hd
    exact ⟨⟨_, p.content, p.start, loc⟩, by simp [advance, hm, h1, h2, h7], rfl, hk, hs, rfl⟩
  · exact ⟨⟨_, p.content, p.start, loc⟩, by simp [finish, hm], rfl, hk, hs, rfl⟩

theorem closes_decimal {version : Spec.Lexicon.Version} {start : Location} {s : Chars}
    {p : Pending} (hm : p.mode = .fraction true) (hs : p.start = start)
    (hk : p.content.data.toList = s) :
    Closes version .decimal start s p := by
  refine ⟨fun loc d hd => ?_, fun loc => ?_⟩
  · obtain ⟨h1, -, -, -, -, -, h7⟩ := delim_facts hd
    exact ⟨⟨_, p.content, p.start, loc⟩, by simp [advance, hm, h1, h7], rfl, hk, hs, rfl⟩
  · exact ⟨⟨_, p.content, p.start, loc⟩, by simp [finish, hm], rfl, hk, hs, rfl⟩

theorem closes_hexadecimal {version : Spec.Lexicon.Version} {start : Location} {s : Chars}
    {p : Pending} (hm : p.mode = .digits .hexadecimal) (hs : p.start = start)
    (hne : p.content.data.toList ≠ []) (hk : s = 35 :: 120 :: p.content.data.toList) :
    Closes version .hexadecimal start s p := by
  have he : p.content.isEmpty = false := by
    cases h : p.content.isEmpty
    · rfl
    · exact absurd ((isEmpty_iff _).mp h) hne
  subst hk
  refine ⟨fun loc d hd => ?_, fun loc => ?_⟩
  · obtain ⟨-, -, -, h4, -, -, h7⟩ := delim_facts hd
    exact ⟨⟨_, p.content, p.start, loc⟩,
      by simp [advance, hm, he, h4, h7, Radix.allows, Radix.category],
      rfl, rfl, hs, rfl⟩
  · exact ⟨⟨_, p.content, p.start, loc⟩, by simp [finish, hm, he, Radix.category],
      rfl, rfl, hs, rfl⟩

theorem closes_binary {version : Spec.Lexicon.Version} {start : Location} {s : Chars}
    {p : Pending} (hm : p.mode = .digits .binary) (hs : p.start = start)
    (hne : p.content.data.toList ≠ []) (hk : s = 35 :: 98 :: p.content.data.toList) :
    Closes version .binary start s p := by
  have he : p.content.isEmpty = false := by
    cases h : p.content.isEmpty
    · rfl
    · exact absurd ((isEmpty_iff _).mp h) hne
  subst hk
  refine ⟨fun loc d hd => ?_, fun loc => ?_⟩
  · obtain ⟨-, -, -, -, h5, -, h7⟩ := delim_facts hd
    exact ⟨⟨_, p.content, p.start, loc⟩,
      by simp [advance, hm, he, h5, h7, Radix.allows, Radix.category],
      rfl, rfl, hs, rfl⟩
  · exact ⟨⟨_, p.content, p.start, loc⟩, by simp [finish, hm, he, Radix.category],
      rfl, rfl, hs, rfl⟩

theorem closes_keyword {version : Spec.Lexicon.Version} {start : Location} {s : Chars}
    {p : Pending} (hm : p.mode = .keyword) (hs : p.start = start)
    (hne : p.content.data.toList ≠ []) (hk : s = 58 :: p.content.data.toList) :
    Closes version .keyword start s p := by
  have he : p.content.isEmpty = false := by
    cases h : p.content.isEmpty
    · rfl
    · exact absurd ((isEmpty_iff _).mp h) hne
  subst hk
  refine ⟨fun loc d hd => ?_, fun loc => ?_⟩
  · obtain ⟨-, -, h3, -, -, -, h7⟩ := delim_facts hd
    exact ⟨⟨_, p.content, p.start, loc⟩, by simp [advance, hm, he, h3, h7], rfl, rfl, hs, rfl⟩
  · exact ⟨⟨_, p.content, p.start, loc⟩, by simp [finish, hm, he], rfl, rfl, hs, rfl⟩

theorem closes_symbol {version : Spec.Lexicon.Version} {start : Location} {s : Chars}
    {p : Pending} {category : Category} (hc : category = .simpleSymbol ∨ category = .reserved)
    (hm : p.mode = .simpleSymbol) (hs : p.start = start) (hk : p.content.data.toList = s) :
    Closes version category start s p := by
  have hcat : lexCategory category = .unquotedSymbol := by rcases hc with rfl | rfl <;> rfl
  have hcon : Spec.Lexicon.Token.content version ⟨category, 0, s⟩ = s := by
    rcases hc with rfl | rfl <;> rfl
  refine ⟨fun loc d hd => ?_, fun loc => ?_⟩
  · obtain ⟨-, -, h3, -, -, -, h7⟩ := delim_facts hd
    exact ⟨⟨_, p.content, p.start, loc⟩, by simp [advance, hm, h3, h7], hcat.symm,
      hk.trans hcon.symm, hs, rfl⟩
  · exact ⟨⟨_, p.content, p.start, loc⟩, by simp [finish, hm], hcat.symm,
      hk.trans hcon.symm, hs, rfl⟩

theorem closes_quoted {version : Spec.Lexicon.Version} {start : Location} {s : Chars}
    {p : Pending} (hm : p.mode = .quotedSymbolClosed) (hs : p.start = start)
    (hk : s = 124 :: (p.content.data.toList ++ [124])) :
    Closes version .quotedSymbol start s p := by
  have hcon : Spec.Lexicon.Token.content version ⟨.quotedSymbol, 0, s⟩ =
      p.content.data.toList := by
    show ((s.drop 1).dropLast) = _
    rw [hk]
    simp
  refine ⟨fun loc d hd => ?_, fun loc => ?_⟩
  · obtain ⟨-, -, -, -, -, -, h7⟩ := delim_facts hd
    exact ⟨⟨_, p.content, p.start, loc⟩, by simp [advance, hm, h7], rfl, hcon.symm, hs, rfl⟩
  · exact ⟨⟨_, p.content, p.start, loc⟩, by simp [finish, hm], rfl, hcon.symm, hs, rfl⟩

theorem closes_string {version : Spec.Lexicon.Version} {start : Location} {s : Chars}
    {p : Pending} (hm : p.mode = .stringQuote ∨ p.mode = .legacyQuote) (hs : p.start = start)
    (hk : p.content.data.toList = Spec.Lexicon.Token.content version ⟨.string, 0, s⟩) :
    Closes version .string start s p := by
  refine ⟨fun loc d hd => ?_, fun loc => ?_⟩
  · obtain ⟨-, -, -, -, -, h6, h7⟩ := delim_facts hd
    rcases hm with hm | hm <;>
      exact ⟨⟨_, p.content, p.start, loc⟩, by simp [advance, hm, h6, h7], rfl, hk, hs, rfl⟩
  · rcases hm with hm | hm <;>
      exact ⟨⟨_, p.content, p.start, loc⟩, by simp [finish, hm], rfl, hk, hs, rfl⟩


/-! ## Passing over a token -/

theorem reaches_start {version : Version} {location : Location} {c : UInt8} {p : Pending}
    (h : start version false location c = .pending p) :
    Reaches version .idle location [c] (.token p) :=
  reaches_cons (by simp [byteStep, startStep, h]) reaches_nil

theorem reaches_one {version : Version} {location : Location} {c : UInt8} {p p' : Pending}
    (h : advance false p location c = .pending p') :
    Reaches version (.token p) location [c] (.token p') :=
  reaches_cons (reaches_pending h) reaches_nil

/-- Parts that each take the token in progress on, keeping the invariant `I` of it and of the
bytes so far. -/
theorem reaches_parts {version : Version} {I : Pending → Chars → Prop} {r : Regex}
    (hunit : ∀ q pre location u, I q pre → r u →
      ∃ q', Reaches version (.token q) location u (.token q') ∧ I q' (pre ++ u))
    {b : Chars} (hb : star r b) :
    ∀ p pre location, I p pre →
      ∃ p', Reaches version (.token p) location b (.token p') ∧ I p' (pre ++ b) := by
  obtain ⟨parts, rfl, hparts⟩ := hb
  induction parts with
  | nil => exact fun p pre location h => ⟨p, reaches_nil, by simpa using h⟩
  | cons u us ih =>
    intro p pre location h
    obtain ⟨q, hq, hI⟩ := hunit p pre location u h (hparts u (by simp))
    obtain ⟨p', hr, hI'⟩ := ih (fun v hv => hparts v (List.mem_cons_of_mem _ hv)) q (pre ++ u)
      _ hI
    exact ⟨p', reaches_append hq hr, by simpa using hI'⟩

/-- What a byte of a simple symbol is not. -/
theorem symChar_facts {d : UInt8} (h : SymChar d.toNat) :
    isWhitespace d = false ∧ d ≠ 40 ∧ d ≠ 41 ∧ d ≠ 59 ∧ d ≠ 35 ∧ d ≠ 34 ∧ d ≠ 58 ∧
      d ≠ 124 ∧ isSymbolByte d = true := by
  have hs := (isSymbolByte_iff d).mpr h
  clear h
  revert hs
  refine byte_cases (P := fun d => isSymbolByte d = true → isWhitespace d = false ∧ d ≠ 40 ∧
    d ≠ 41 ∧ d ≠ 59 ∧ d ≠ 35 ∧ d ≠ 34 ∧ d ≠ 58 ∧ d ≠ 124 ∧ isSymbolByte d = true) ?_ d
  decide +kernel

theorem symChar_of_digit {d : UInt8} (h : IsDigit d.toNat) : SymChar d.toNat := Or.inr (Or.inl h)

theorem start_digit {version : Version} {location : Location} {d : UInt8}
    (h : IsDigit d.toNat) :
    start version false location d =
      .pending
        { mode := .numeral (d == 48), start := location,
          content := ByteArray.empty.push d } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := symChar_facts (symChar_of_digit h)
  have hd := (isDigit_iff d).mpr h
  simp [start, h1, h2, h3, h4, h5, h6, h7, h8, hd]

theorem start_symbol {version : Version} {location : Location} {d : UInt8}
    (h : SymChar d.toNat) (hn : ¬ IsDigit d.toNat) :
    start version false location d =
      .pending
        { mode := .simpleSymbol, start := location, content := ByteArray.empty.push d } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := symChar_facts h
  have hd : isDigit d = false := by
    cases e : isDigit d
    · rfl
    · exact absurd ((isDigit_iff d).mp e) hn
  simp [start, h1, h2, h3, h4, h5, h6, h7, h8, hd, h9]

/-- A segment of digits in a numeral other than `0`. -/
theorem reaches_digits_numeral {version : Version} {ds : Chars}
    (hds : ∀ x ∈ ds, IsDigit x.toNat) (p : Pending) (pre : Chars) (location : Location)
    (h : p.mode = .numeral false ∧ p.content.data.toList = pre) :
    ∃ p', Reaches version (.token p) location ds (.token p') ∧
      (p'.mode = .numeral false ∧ p'.content.data.toList = pre ++ ds) ∧ p'.start = p.start := by
  obtain ⟨p', hr, hI⟩ := reaches_segment (version := version)
    (I := fun q pre => (q.mode = .numeral false ∧ q.content.data.toList = pre) ∧
      q.start = p.start) ds
    (fun q pre loc x hq hx => by
      have hd := (isDigit_iff x).mpr (hds x hx)
      refine ⟨{ q with mode := .numeral false, content := q.content.push x },
        by simp [advance, hq.1.1, hd], ⟨rfl, ?_⟩, hq.2⟩
      rw [toList_push, hq.1.2])
    p pre location ⟨h, rfl⟩
  exact ⟨p', hr, hI⟩

theorem reaches_numeral {version : Version} {s : Chars} (hs : numeral s) (location : Location) :
    ∃ p, Reaches version .idle location s (.token p) ∧ (∃ zero, p.mode = .numeral zero) ∧
      p.start = location ∧ p.content.data.toList = s := by
  by_cases h0 : s = [48]
  · subst h0
    exact ⟨_, reaches_start (start_digit (by unfold IsDigit; decide)), ⟨_, rfl⟩, rfl, rfl⟩
  · obtain ⟨d, ds, rfl, hd, hd0, hds⟩ := numeral_head hs h0
    have hz : (d == 48) = false := by simpa using hd0
    obtain ⟨p', hr, ⟨hm, hk⟩, hst⟩ := reaches_digits_numeral (version := version) hds
      { mode := .numeral (d == 48), start := location, content := ByteArray.empty.push d } [d]
      (location.afterByte d) ⟨by rw [hz], rfl⟩
    exact ⟨p', reaches_append (a := [d]) (reaches_start (start_digit hd)) hr, ⟨_, hm⟩, hst,
      hk⟩

theorem run_numeral (version : Spec.Lexicon.Version) {s : Chars} (hs : numeral s) :
    TokenRun version .numeral s := by
  refine tokenRun_of_closes fun location => ?_
  obtain ⟨p, hr, ⟨zero, hm⟩, hst, hk⟩ := reaches_numeral (version := Adapter.toVersion version)
    hs location
  exact ⟨p, hr, closes_numeral hm hst hk⟩

theorem run_decimal (version : Spec.Lexicon.Version) {s : Chars} (hs : decimal s) :
    TokenRun version .decimal s := by
  refine tokenRun_of_closes fun location => ?_
  obtain ⟨n, r1, rfl, hn, dot, r2, rfl, hdot, z, n', rfl, hz, hn'⟩ := hs
  have hdot2 : dot = [46] := hdot
  subst hdot2
  obtain ⟨p, hr, ⟨zero, hm⟩, hst, hk⟩ := reaches_numeral (version := Adapter.toVersion version)
    hn location
  -- the dot
  have hdot' : advance false p (advanceLoc location n) 46 =
      .pending { p with mode := .fraction false, content := p.content.push 46 } := by
    simp [advance, hm, show isDigit 46 = false from rfl]
  -- the digits after the dot
  have hdigits : ∀ x ∈ z ++ n', IsDigit x.toNat := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have := star_mem (P := fun x => x.toNat = 48) (single_mem fun p hp => ⟨48, hp, rfl⟩) hz x hx
      simp only [IsDigit]; omega
    · obtain ⟨d, ds, rfl, hd, hds⟩ := numeral_inv hn'
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hd
      · exact hds x hx
  obtain ⟨e, es, he⟩ : ∃ e es, z ++ n' = e :: es := by
    obtain ⟨d, ds, rfl, -⟩ := numeral_inv hn'
    cases z with
    | nil => exact ⟨d, ds, rfl⟩
    | cons y ys => exact ⟨y, ys ++ d :: ds, rfl⟩
  rw [he] at hdigits ⊢
  have hfirst : advance false { p with mode := .fraction false, content := p.content.push 46 }
      (advanceLoc (advanceLoc location n) [46]) e =
      .pending { p with mode := .fraction true, content := (p.content.push 46).push e } := by
    have hd := (isDigit_iff e).mpr (hdigits e (by simp))
    simp [advance, hd]
  obtain ⟨p', hr', hI⟩ := reaches_segment (version := Adapter.toVersion version)
    (I := fun q pre => (q.mode = .fraction true ∧ q.content.data.toList = pre) ∧
      q.start = p.start) es
    (fun q pre loc x hq hx => by
      have hd := (isDigit_iff x).mpr (hdigits x (by simp [hx]))
      refine ⟨{ q with mode := .fraction true, content := q.content.push x },
        by simp [advance, hq.1.1, hd], ⟨rfl, ?_⟩, hq.2⟩
      rw [toList_push, hq.1.2])
    { p with mode := .fraction true, content := (p.content.push 46).push e } (n ++ [46, e])
      (advanceLoc location (n ++ [46, e]))
      ⟨⟨rfl, by simp [hk]⟩, rfl⟩
  refine ⟨p', ?_, closes_decimal hI.1.1 (hI.2.trans hst) (by rw [hI.1.2]; simp)⟩
  have h1 := reaches_append hr (reaches_one hdot')
  have h2 := reaches_append h1 (by rw [advanceLoc_append]; exact reaches_one hfirst)
  have h3 := reaches_append h2 (by simpa [advanceLoc_append] using hr')
  simpa using h3


/-- Bytes each of which extends the token in progress in the mode `m` when it has the
property `P`. -/
theorem reaches_extend {version : Version} {m : Mode} {P : UInt8 → Prop} {xs : Chars}
    (hstep : ∀ (q : Pending) location x, q.mode = m → P x →
      advance false q location x = .pending { q with mode := m, content := q.content.push x })
    (hxs : ∀ x ∈ xs, P x) (p : Pending) (location : Location) (hm : p.mode = m) :
    ∃ p', Reaches version (.token p) location xs (.token p') ∧ p'.mode = m ∧
      p'.start = p.start ∧ p'.content.data.toList = p.content.data.toList ++ xs := by
  obtain ⟨p', hr, hI⟩ := reaches_segment (version := version)
    (I := fun q pre => q.mode = m ∧ q.start = p.start ∧ q.content.data.toList = pre) xs
    (fun q pre loc x hq hx => ⟨_, hstep q loc x hq.1 (hxs x hx), rfl, hq.2.1,
      by rw [toList_push, hq.2.2]⟩)
    p p.content.data.toList location ⟨hm, rfl, rfl⟩
  exact ⟨p', hr, hI⟩

/-- Every character of a match of `plus r`, where `r` matches single characters, matches
`r`. -/
theorem plus_chars {r : Regex} (hs : ∀ p, r p → ∃ c, p = [c]) {t : Chars} (h : plus r t) :
    ∀ x ∈ t, r [x] :=
  plus_mem (P := fun x => r [x]) (single_mem fun p hp => by
    obtain ⟨c, rfl⟩ := hs p hp
    exact ⟨c, rfl, hp⟩) h

theorem star_chars {r : Regex} (hs : ∀ p, r p → ∃ c, p = [c]) {t : Chars} (h : star r t) :
    ∀ x ∈ t, r [x] :=
  star_mem (P := fun x => r [x]) (single_mem fun p hp => by
    obtain ⟨c, rfl⟩ := hs p hp
    exact ⟨c, rfl, hp⟩) h

theorem plus_ne_nil {r : Regex} (hne : ∀ p, r p → p ≠ []) {t : Chars} (h : plus r t) :
    t ≠ [] := by
  obtain ⟨a, b, rfl, ha, -⟩ := h
  simp [hne a ha]

theorem hexChar_single {p : Chars} (h : altAll [digit, range 65 70, range 97 102] p) :
    ∃ c, p = [c] := by
  obtain ⟨r, hr, hp⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> obtain ⟨c, rfl, -⟩ := hp <;> exact ⟨c, rfl⟩

theorem run_hexadecimal (version : Spec.Lexicon.Version) {s : Chars} (hs : hexadecimal s) :
    TokenRun version .hexadecimal s := by
  refine tokenRun_of_closes fun location => ?_
  obtain ⟨ds, rfl, hds⟩ := seq_lit hs
  have hall := plus_chars (fun _ => hexChar_single) hds
  have hne := plus_ne_nil (fun p hp => by obtain ⟨c, rfl⟩ := hexChar_single hp; simp) hds
  have h0 : start (Adapter.toVersion version) false location 35 =
      .pending { mode := .hash, start := location, content := .empty } := rfl
  have h1 : advance false { mode := .hash, start := location, content := .empty }
      (location.afterByte 35) 120 =
      .pending { mode := .digits .hexadecimal, start := location, content := .empty } := rfl
  obtain ⟨p', hr, hm, hst, hk⟩ := reaches_extend (version := Adapter.toVersion version)
    (m := .digits .hexadecimal) (P := fun x => isHexDigit x = true) (xs := ds)
    (fun q loc x hq hx => by simp [advance, hq, Radix.allows, hx])
    (fun x hx => (hexDigit_iff x).mpr (hall x hx))
    { mode := .digits .hexadecimal, start := location, content := .empty }
    (advanceLoc location [35, 120]) rfl
  refine ⟨p', ?_, closes_hexadecimal hm hst (by simpa [hk] using hne) (by simp [hk]; rfl)⟩
  have := reaches_append (reaches_append (reaches_start h0) (reaches_one h1)) hr
  rw [show chars "#x" = [35, 120] from rfl]
  simpa using this

theorem run_binary (version : Spec.Lexicon.Version) {s : Chars} (hs : binary s) :
    TokenRun version .binary s := by
  refine tokenRun_of_closes fun location => ?_
  obtain ⟨ds, rfl, hds⟩ := seq_lit hs
  have hsingle : ∀ p, oneOf "01" p → ∃ c, p = [c] := fun p hp => by
    obtain ⟨c, rfl, -⟩ := oneOf_inv hp
    exact ⟨c, rfl⟩
  have hall := plus_chars hsingle hds
  have hne := plus_ne_nil (fun p hp => by obtain ⟨c, rfl⟩ := hsingle p hp; simp) hds
  have h0 : start (Adapter.toVersion version) false location 35 =
      .pending { mode := .hash, start := location, content := .empty } := rfl
  have h1 : advance false { mode := .hash, start := location, content := .empty }
      (location.afterByte 35) 98 =
      .pending { mode := .digits .binary, start := location, content := .empty } := rfl
  obtain ⟨p', hr, hm, hst, hk⟩ := reaches_extend (version := Adapter.toVersion version)
    (m := .digits .binary) (P := fun x => isBinaryDigit x = true) (xs := ds)
    (fun q loc x hq hx => by simp [advance, hq, Radix.allows, hx])
    (fun x hx => (binaryDigit_iff x).mpr (hall x hx))
    { mode := .digits .binary, start := location, content := .empty }
    (advanceLoc location [35, 98]) rfl
  refine ⟨p', ?_, closes_binary hm hst (by simpa [hk] using hne) (by simp [hk]; rfl)⟩
  have := reaches_append (reaches_append (reaches_start h0) (reaches_one h1)) hr
  rw [show chars "#b" = [35, 98] from rfl]
  simpa using this

theorem run_keyword (version : Spec.Lexicon.Version) {s : Chars} (hs : keyword s) :
    TokenRun version .keyword s := by
  refine tokenRun_of_closes fun location => ?_
  obtain ⟨ds, rfl, hall⟩ := keyword_inv hs
  have hne : ds ≠ [] := by
    obtain ⟨t, hts, hpl⟩ := seq_lit hs
    have hts' : 58 :: ds = 58 :: t := hts
    have e : t = ds := (List.cons.inj hts').2.symm
    subst e
    exact plus_ne_nil (fun p hp => by obtain ⟨c, rfl, -⟩ := symChar_inv hp; simp) hpl
  have h0 : start (Adapter.toVersion version) false location 58 =
      .pending { mode := .keyword, start := location, content := .empty } := rfl
  obtain ⟨p', hr, hm, hst, hk⟩ := reaches_extend (version := Adapter.toVersion version)
    (m := .keyword) (P := fun x => SymChar x.toNat) (xs := ds)
    (fun q loc x hq hx => by simp [advance, hq, (isSymbolByte_iff x).mpr hx])
    hall { mode := .keyword, start := location, content := .empty }
    (advanceLoc location [58]) rfl
  refine ⟨p', ?_, closes_keyword hm hst (by simpa [hk] using hne) (by simp [hk])⟩
  have := reaches_append (reaches_start h0) hr
  simpa using this

/-- Every reserved word is a non-empty sequence of characters of simple symbols that does not
start with a digit. -/
theorem reservedWords_shape' (version : Spec.Lexicon.Version) :
    ∀ w ∈ reservedWords version, w ≠ [] ∧ ¬ IsDigit (w.headD 0).toNat ∧
      ∀ x ∈ w, SymChar x.toNat := by
  unfold SymChar IsDigit
  cases version <;> decide

theorem reservedWords_shape (version : Spec.Lexicon.Version) :
    ∀ w ∈ reservedWords version, ∃ c t, w = c :: t ∧ ¬ IsDigit c.toNat ∧
      ∀ x ∈ w, SymChar x.toNat := by
  intro w hw
  obtain ⟨hne, hd, hall⟩ := reservedWords_shape' version w hw
  obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact ⟨c, t, rfl, hd, hall⟩

theorem run_symbol (version : Spec.Lexicon.Version) {s : Chars} {category : Category}
    (hc : category = .simpleSymbol ∨ category = .reserved) (hs : categoryRegex version category s) :
    TokenRun version category s := by
  refine tokenRun_of_closes fun location => ?_
  obtain ⟨c, t, rfl, hd, hall⟩ : ∃ c t, s = c :: t ∧ ¬ IsDigit c.toNat ∧
      ∀ x ∈ s, SymChar x.toNat := by
    rcases hc with rfl | rfl
    · obtain ⟨c, t, rfl, hd, hall, -⟩ := simpleSymbol_inv hs
      exact ⟨c, t, rfl, hd, hall⟩
    · exact reservedWords_shape version s (litOneOf_iff.mp hs)
  obtain ⟨p', hr, hm, hst, hk⟩ := reaches_extend (version := Adapter.toVersion version)
    (m := .simpleSymbol) (P := fun x => SymChar x.toNat) (xs := t)
    (fun q loc x hq hx => by simp [advance, hq, (isSymbolByte_iff x).mpr hx])
    (fun x hx => hall x (by simp [hx]))
    { mode := .simpleSymbol, start := location, content := ByteArray.empty.push c }
    (location.afterByte c) rfl
  refine ⟨p', ?_, closes_symbol hc hm hst (by simp [hk])⟩
  exact reaches_append (a := [c]) (reaches_start (start_symbol (hall c (by simp)) hd)) hr

theorem run_quoted (version : Spec.Lexicon.Version) {s : Chars} (hs : quotedSymbol s) :
    TokenRun version .quotedSymbol s := by
  refine tokenRun_of_closes fun location => ?_
  obtain ⟨t, rfl, b, e, rfl, hb, rfl⟩ := seq_lit hs
  have hsingle : ∀ p, QuotedChar p → ∃ c, p = [c] := fun p ⟨hp, _⟩ => by
    rcases hp with h | h
    · obtain ⟨c, rfl, -⟩ := whiteSpaceChar_inv h
      exact ⟨c, rfl⟩
    · exact printableOrSpace_inv (Or.inl h)
  have hall := star_chars hsingle hb
  have h0 : start (Adapter.toVersion version) false location 124 =
      .pending { mode := .quotedSymbol, start := location, content := .empty } := rfl
  obtain ⟨p', hr, hm, hst, hk⟩ := reaches_extend (version := Adapter.toVersion version)
    (m := .quotedSymbol) (P := fun x => QuotedChar [x]) (xs := b)
    (fun q loc x hq hx => by
      obtain ⟨hx1, hx2⟩ := hx
      have h124 : x ≠ 124 := fun e => hx2 (oneOf_one.mpr (by rw [e]; decide))
      have h92 : x ≠ 92 := fun e => hx2 (oneOf_one.mpr (by rw [e]; decide))
      have ht := (text_iff x).mpr (spaceOrPrintable_one.mp hx1)
      simp [advance, hq, h124, h92, ht])
    hall { mode := .quotedSymbol, start := location, content := .empty }
    (location.afterByte 124) rfl
  have h1 : advance false p' (advanceLoc (location.afterByte 124) b) 124 =
      .pending { p' with mode := .quotedSymbolClosed } := by simp [advance, hm]
  refine ⟨{ p' with mode := .quotedSymbolClosed }, ?_, closes_quoted rfl hst (by simp [hk]; rfl)⟩
  have := reaches_append (reaches_append (a := [124]) (reaches_start h0) hr) (reaches_one h1)
  rw [show chars "|" = [124] from rfl]
  simpa using this

theorem run_paren (version : Spec.Lexicon.Version) {s : Chars} {category : Category}
    (hc : category = .parenOpen ∨ category = .parenClose) (hs : categoryRegex version category s) :
    ∀ location rest,
      runFrom (Adapter.toVersion version) .idle location (s ++ rest) =
        (runFrom (Adapter.toVersion version) .idle (advanceLoc location s) rest).map
          (lexemeFor version category location (advanceLoc location s) s :: ·) := by
  intro location rest
  rcases hc with rfl | rfl
  · have e : s = [40] := hs
    subst e
    rw [List.singleton_append, runFrom_cons]
    have hst : byteStep (Adapter.toVersion version) .idle location 40 =
        some (.idle, [lexemeFor version .parenOpen location (location.afterByte 40) [40]]) := rfl
    rw [hst, Option.bind_some]
    rfl
  · have e : s = [41] := hs
    subst e
    rw [List.singleton_append, runFrom_cons]
    have hst : byteStep (Adapter.toVersion version) .idle location 41 =
        some (.idle, [lexemeFor version .parenClose location (location.afterByte 41) [41]]) := rfl
    rw [hst, Option.bind_some]
    rfl


theorem run_string (version : Spec.Lexicon.Version) (hv : version ≠ .v2_0) {s : Chars}
    (hs : string s) : TokenRun version .string s := by
  refine tokenRun_of_closes fun location => ?_
  obtain ⟨b, rfl, hb⟩ := string_inv hs
  have hv' : (Adapter.toVersion version == .v2_0) = false := by
    cases h : (Adapter.toVersion version == .v2_0)
    · rfl
    · exact absurd ((toVersion_beq version).mp h) hv
  have h0 : start (Adapter.toVersion version) false location 34 =
      .pending { mode := .string, start := location, content := .empty } := by
    simp [start, hv', show isWhitespace 34 = false from rfl]
  obtain ⟨p', hr, hm, hst, -, hk⟩ := reaches_parts (version := Adapter.toVersion version)
    (I := fun q pre => q.mode = .string ∧ q.start = location ∧ StringBody pre ∧
      q.content.data.toList = unescape pre)
    (fun q pre loc u ⟨hm, hst, hpre, hk⟩ hu => by
      rcases stringUnit_inv hu with ⟨c, rfl, hc⟩ | rfl
      · have ht : isTextByte c = true := by
          rcases hu with ⟨hp, -⟩ | h
          · exact (text_iff c).mpr hp
          · exact absurd h (by simp [lit_iff, chars])
        refine ⟨{ q with mode := .string, content := q.content.push c },
          reaches_one (by simp [advance, hm, hc, ht]), rfl, hst, star_snoc hpre hu, ?_⟩
        rw [toList_push, hk, unescape_append hpre]
        rfl
      · have h1 : advance false q loc 34 = .pending { q with mode := .stringQuote } := by
          simp [advance, hm]
        have h2 : advance false { q with mode := .stringQuote } (loc.afterByte 34) 34 =
            .pending { q with mode := .string, content := q.content.push 34 } := by
          simp [advance]
        refine ⟨_, reaches_append (a := [34]) (reaches_one h1) (reaches_one h2), rfl, hst,
          star_snoc hpre hu, ?_⟩
        rw [toList_push, hk, unescape_append hpre]
        rfl)
    hb { mode := .string, start := location, content := .empty } [] (location.afterByte 34)
      ⟨rfl, rfl, star_parts [] (by simp), rfl⟩
  have h1 : advance false p' (advanceLoc (location.afterByte 34) b) 34 =
      .pending { p' with mode := .stringQuote } := by simp [advance, hm]
  refine ⟨{ p' with mode := .stringQuote }, ?_, closes_string (Or.inl rfl) hst ?_⟩
  · have := reaches_append (reaches_append (a := [34]) (reaches_start h0) hr) (reaches_one h1)
    simpa using this
  · show _ = (if version = .v2_0 then unescape20 else unescape)
      (((34 :: (b ++ [34])).drop 1).dropLast)
    simp only [hv, ↓reduceIte]
    simpa using hk

theorem run_string20 (version : Spec.Lexicon.Version) (hv : version = .v2_0) {s : Chars}
    (hs : string20 s) : TokenRun version .string s := by
  refine tokenRun_of_closes fun location => ?_
  obtain ⟨b, rfl, hb⟩ := string20_inv hs
  have hv' : (Adapter.toVersion version == .v2_0) = true := (toVersion_beq version).mpr hv
  have h0 : start (Adapter.toVersion version) false location 34 =
      .pending { mode := .legacyString, start := location, content := .empty } := by
    simp [start, hv', show isWhitespace 34 = false from rfl]
  obtain ⟨p', hr, hm, hst, -, hk⟩ := reaches_parts (version := Adapter.toVersion version)
    (r := alt (minus (alt printableChar whiteSpaceChar) (oneOf "\"\\"))
      (seq (lit "\\") (alt printableChar whiteSpaceChar)))
    (I := fun q pre => q.mode = .legacyString ∧ q.start = location ∧ StringBody20 pre ∧
      q.content.data.toList = unescape20 pre)
    (fun q pre loc u ⟨hm, hst, hpre, hk⟩ hu => by
      rcases stringUnit20_inv hu with ⟨c, rfl, h34, h92⟩ | ⟨d, rfl⟩
      · have ht : isTextByte c = true := by
          rcases hu with ⟨hp, -⟩ | ⟨a, b', h, ha, -⟩
          · exact (text_iff c).mpr hp
          · rw [lit_iff] at ha
            subst ha
            simp [chars] at h
            exact absurd h.1 h92
        refine ⟨{ q with mode := .legacyString, content := q.content.push c },
          reaches_one (by simp [advance, hm, legacyStringByte, h34, h92, ht]), rfl, hst,
          star_snoc hpre hu, ?_⟩
        rw [toList_push, hk, unescape20_append hpre]
        simp [unescape20]
      · have ht : isTextByte d = true := by
          rcases hu with ⟨hp, -⟩ | ⟨a, b', h, ha, hb'⟩
          · obtain ⟨c, hc⟩ := printableOrSpace_inv hp
            simp at hc
          · rw [lit_iff] at ha
            subst ha
            have : b' = [d] := by
              have h' := h.symm
              simp [chars] at h'
              exact h'.2
            subst this
            exact (text_iff d).mpr hb'
        have h1 : advance false q loc 92 = .pending { q with mode := .legacyEscape } := by
          simp [advance, hm, legacyStringByte]
        by_cases he : d = 34 ∨ d = 92
        · have hc : ((d == 34) || (d == 92)) = true := by rcases he with rfl | rfl <;> rfl
          have h2 : advance false { q with mode := .legacyEscape } (loc.afterByte 92) d =
              .pending { q with mode := .legacyString, content := q.content.push d } := by
            simp [advance, hc]
          refine ⟨_, reaches_append (a := [92]) (reaches_one h1) (reaches_one h2), rfl, hst,
            star_snoc hpre hu, ?_⟩
          rw [toList_push, hk, unescape20_append hpre]
          rcases he with rfl | rfl <;> rfl
        · have h34 : d ≠ 34 := fun e => he (Or.inl e)
          have h92 : d ≠ 92 := fun e => he (Or.inr e)
          have hc : ((d == 34) || (d == 92)) = false := by simp [h34, h92]
          have h2 : advance false { q with mode := .legacyEscape } (loc.afterByte 92) d =
              .pending
                { q with mode := .legacyString, content := (q.content.push 92).push d } := by
            simp [advance, hc, legacyStringByte, h34, h92, ht]
          refine ⟨_, reaches_append (a := [92]) (reaches_one h1) (reaches_one h2), rfl, hst,
            star_snoc hpre hu, ?_⟩
          rw [toList_push, toList_push, hk, unescape20_append hpre]
          simp [unescape20, h34, h92])
    hb { mode := .legacyString, start := location, content := .empty } []
      (location.afterByte 34) ⟨rfl, rfl, star_parts [] (by simp), rfl⟩
  have h1 : advance false p' (advanceLoc (location.afterByte 34) b) 34 =
      .pending { p' with mode := .legacyQuote } := by simp [advance, hm, legacyStringByte]
  refine ⟨{ p' with mode := .legacyQuote }, ?_, closes_string (Or.inr rfl) hst ?_⟩
  · have := reaches_append (reaches_append (a := [34]) (reaches_start h0) hr) (reaches_one h1)
    simpa using this
  · show _ = (if version = .v2_0 then unescape20 else unescape)
      (((34 :: (b ++ [34])).drop 1).dropLast)
    simp only [hv, ↓reduceIte]
    simpa using hk


/-! ## Tokenisations -/

/-- From no token in progress, a token and what follows it finish the token's lexeme before
the rest. -/
theorem token_run {version : Spec.Lexicon.Version} {category : Category} {s rest : Chars}
    (hs : categoryRegex version category s) (hd : Delimited category rest)
    (location : Location) :
    runFrom (Adapter.toVersion version) .idle location (s ++ rest) =
      (runFrom (Adapter.toVersion version) .idle (advanceLoc location s) rest).map
        (lexemeFor version category location (advanceLoc location s) s :: ·) := by
  cases category with
  | parenOpen => exact run_paren version (Or.inl rfl) hs location rest
  | parenClose => exact run_paren version (Or.inr rfl) hs location rest
  | numeral => exact run_numeral version hs location rest (delimRest_of hd (by simp) (by simp))
  | decimal => exact run_decimal version hs location rest (delimRest_of hd (by simp) (by simp))
  | hexadecimal =>
    exact run_hexadecimal version hs location rest (delimRest_of hd (by simp) (by simp))
  | binary => exact run_binary version hs location rest (delimRest_of hd (by simp) (by simp))
  | string =>
    by_cases hv : version = .v2_0
    · have hs' : string20 s := by simpa [categoryRegex, hv] using hs
      exact run_string20 version hv hs' location rest (delimRest_of hd (by simp) (by simp))
    · have hs' : string s := by simpa [categoryRegex, hv] using hs
      exact run_string version hv hs' location rest (delimRest_of hd (by simp) (by simp))
  | simpleSymbol =>
    exact run_symbol version (Or.inl rfl) hs location rest (delimRest_of hd (by simp) (by simp))
  | quotedSymbol => exact run_quoted version hs location rest (delimRest_of hd (by simp) (by simp))
  | keyword => exact run_keyword version hs location rest (delimRest_of hd (by simp) (by simp))
  | reserved =>
    exact run_symbol version (Or.inr rfl) hs location rest (delimRest_of hd (by simp) (by simp))

/-- The pure run finishes every tokenisation, after any input before it. -/
theorem runFrom_complete {version : Spec.Lexicon.Version} {offset : Nat} {input : Chars}
    {tokens : List Spec.Lexicon.Token} (h : TokenizationFrom version offset input tokens) :
    ∀ before, offset = before.length →
      runFrom (Adapter.toVersion version) .idle (locAfter before) input =
        some (tokens.map (lexemeOf version (before ++ input)) ++
          [eofLexeme (locAfter (before ++ input))]) := by
  induction h with
  | done hw =>
    intro before _
    rw [runFrom_whitespaceAtEnd hw, ← locAfter_append]
    rfl
  | token hw hs hd hrest ih =>
    rename_i w category s rest offset tokens
    intro before hoff
    rw [List.append_assoc, runFrom_reaches (reaches_whitespace hw _), ← locAfter_append,
      token_run hs hd, ← locAfter_append,
      ih (before ++ w ++ s) (by simp [hoff, Nat.add_assoc])]
    simp only [Option.map_some, List.map_cons, List.cons_append, List.append_assoc]
    congr 2
    · have h1 : (before ++ (w ++ (s ++ rest))).take (before.length + w.length) =
          before ++ w := by
        rw [← List.append_assoc]
        exact List.take_left' (by simp)
      have h2 : (before ++ (w ++ (s ++ rest))).take (before.length + w.length + s.length) =
          before ++ w ++ s := by
        rw [← List.append_assoc, ← List.append_assoc]
        exact List.take_left' (by simp [Nat.add_assoc])
      simp only [lexemeFor, lexemeOf, hoff, h1, h2]
      simp only [List.append_assoc]
      rfl

/-- The pure run finishes every tokenisation of the input with the lexemes of its tokens and
then the end-of-file lexeme. -/
theorem run_complete {version : Spec.Lexicon.Version} {input : Chars}
    {tokens : List Spec.Lexicon.Token} (h : Tokenization version input tokens) :
    run (Adapter.toVersion version) input =
      some (tokens.map (lexemeOf version input) ++ [eofLexeme (locAfter input)]) := by
  have := runFrom_complete h [] rfl
  simp only [List.nil_append] at this
  exact this

end BSmtLib.Proofs.Lexer.V1Naive
