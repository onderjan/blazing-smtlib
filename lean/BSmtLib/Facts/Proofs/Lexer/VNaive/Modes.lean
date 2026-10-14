import BSmtLib.Facts.Proofs.Lexer.VNaive.Facts

/-!
# What the modes of the naive lexer stand for

`ModeInv` relates the mode of a token in progress and its content to the characters of the
token so far, and `LexemeIs` relates a finished lexeme to a token of the spec. The lemmas
`start_sound`, `advance_sound` and `finish_sound` show that each part of the pure step keeps
the relation, and that a lexeme it finishes is a token of the spec's `categoryRegex`.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaive.Modes

open BSmtLibSpec.Lexicon BSmtLibSpec.Regex
open BSmtLibSpec (Regex)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Facts BSmtLib.Lexer.Error BSmtLib.Lexer.Internal.VNaive
open BSmtLibSpec.Facts.Proofs.Lexicon.Lemmas BSmtLibSpec.Facts.Proofs.Lexicon.Unique

/-! ## Helpers -/

theorem toList_push (a : ByteArray) (c : UInt8) :
    (a.push c).data.toList = a.data.toList ++ [c] := by
  simp [ByteArray.push]

theorem toList_empty : ByteArray.empty.data.toList = [] := rfl

theorem toList_push_empty (c : UInt8) : (ByteArray.empty.push c).data.toList = [c] := rfl

theorem isEmpty_iff (a : ByteArray) : a.isEmpty = true ↔ a.data.toList = [] := by
  simp only [ByteArray.isEmpty, beq_iff_eq]
  show a.data.size = 0 ↔ _
  rw [← Array.length_toList]
  exact List.length_eq_zero_iff

theorem toVersion_beq (version : BSmtLibSpec.Lexicon.Version) :
    (Lexer.Adapters.toVersion version == .v2_0) = true ↔ version = .v2_0 := by
  cases version <;> decide

/-- A sequence of zero or more parts and one more part. -/
theorem star_snoc {r : Regex} {b u : Chars} (hb : star r b) (hu : r u) : star r (b ++ u) := by
  obtain ⟨parts, rfl, hparts⟩ := hb
  refine ⟨parts ++ [u], by simp, fun p hp => ?_⟩
  rcases List.mem_append.mp hp with hp | hp
  · exact hparts p hp
  · rw [List.mem_singleton.mp hp]
    exact hu

/-- A sequence of one or more parts and one more part. -/
theorem plus_snoc {r : Regex} {b u : Chars} (hb : plus r b) (hu : r u) : plus r (b ++ u) := by
  obtain ⟨a, b', rfl, ha, hb'⟩ := hb
  exact ⟨a, b' ++ u, by simp, ha, star_snoc hb' hu⟩

/-- A sequence of one or more single characters of `r`. -/
theorem plus_of_chars {r : Regex} {s : Chars} (hne : s ≠ []) (h : ∀ x ∈ s, r [x]) :
    plus r s := by
  obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact plus_each (h c (by simp)) (fun x hx => h x (by simp [hx]))

/-! ## The bodies of string literals -/

/-- The body of a string literal from 2.5 on. -/
abbrev StringBody : Regex :=
  star (alt (minus (alt printableChar whiteSpaceChar) (lit "\"")) (lit "\"\""))

/-- The body of a string literal in 2.0. -/
abbrev StringBody20 : Regex :=
  star (alt (minus (alt printableChar whiteSpaceChar) (oneOf "\"\\"))
    (seq (lit "\\") (alt printableChar whiteSpaceChar)))

/-- A character of a quoted symbol between its bars. -/
abbrev QuotedChar : Regex := minus (alt whiteSpaceChar printableChar) (oneOf "|\\")

theorem unescape_unit {u : Chars}
    (h : alt (minus (alt printableChar whiteSpaceChar) (lit "\"")) (lit "\"\"") u) (x : Chars) :
    unescape (u ++ x) = unescape u ++ unescape x := by
  rcases stringUnit_inv h with ⟨c, rfl, hc⟩ | rfl
  · cases x with
    | nil => simp [unescape]
    | cons d x =>
      simp only [List.singleton_append, unescape]
      simp [hc]
  · simp [unescape]

theorem unescape_append {b : Chars} (hb : StringBody b) (x : Chars) :
    unescape (b ++ x) = unescape b ++ unescape x := by
  obtain ⟨parts, rfl, hparts⟩ := hb
  induction parts with
  | nil => simp [unescape]
  | cons p ps ih =>
    have hp := hparts p (by simp)
    have hps : ∀ q ∈ ps, _ := fun q hq => hparts q (List.mem_cons_of_mem _ hq)
    simp only [List.flatten_cons, List.append_assoc]
    rw [unescape_unit hp, unescape_unit hp, ih hps, List.append_assoc]

theorem unescape20_unit {u : Chars}
    (h : alt (minus (alt printableChar whiteSpaceChar) (oneOf "\"\\"))
      (seq (lit "\\") (alt printableChar whiteSpaceChar)) u) (x : Chars) :
    unescape20 (u ++ x) = unescape20 u ++ unescape20 x := by
  rcases stringUnit20_inv h with ⟨c, rfl, hc, hc'⟩ | ⟨d, rfl⟩
  · cases x with
    | nil => simp [unescape20]
    | cons e x =>
      simp only [List.singleton_append, unescape20]
      simp [hc']
  · by_cases hd : d = 34 ∨ d = 92
    · simp [unescape20, hd]
    · have hd' : d ≠ 92 := fun e => hd (Or.inr e)
      have hd34 : d ≠ 34 := fun e => hd (Or.inl e)
      cases x with
      | nil => simp [unescape20]
      | cons e x => simp [unescape20, hd34, hd']

theorem unescape20_append {b : Chars} (hb : StringBody20 b) (x : Chars) :
    unescape20 (b ++ x) = unescape20 b ++ unescape20 x := by
  obtain ⟨parts, rfl, hparts⟩ := hb
  induction parts with
  | nil => simp [unescape20]
  | cons p ps ih =>
    have hp := hparts p (by simp)
    have hps : ∀ q ∈ ps, _ := fun q hq => hparts q (List.mem_cons_of_mem _ hq)
    simp only [List.flatten_cons, List.append_assoc]
    rw [unescape20_unit hp, unescape20_unit hp, ih hps, List.append_assoc]

/-! ## Numbers -/

theorem numeral_zero : numeral [48] := Or.inl rfl

theorem numeral_of_digits {d : UInt8} {ds : Chars} (hd : IsDigit d.toNat) (h0 : d ≠ 48)
    (hds : ∀ x ∈ ds, IsDigit x.toNat) : numeral (d :: ds) := by
  refine Or.inr ⟨plus_each (r := digit) ?_ fun x hx => ?_, fun h => h0 ?_⟩
  · exact range_one.mpr hd
  · exact range_one.mpr (hds x hx)
  · exact (startsWith_lit_one "0" rfl).mp h

/-- A numeral that is not `0` starts with a digit other than `0`. -/
theorem numeral_head {s : Chars} (h : numeral s) (h0 : s ≠ [48]) :
    ∃ d ds, s = d :: ds ∧ IsDigit d.toNat ∧ d ≠ 48 ∧ ∀ x ∈ ds, IsDigit x.toNat := by
  obtain ⟨d, ds, rfl, hd, hds⟩ := numeral_inv h
  refine ⟨d, ds, rfl, hd, fun e => ?_, hds⟩
  subst e
  rcases h with h | ⟨-, h⟩
  · exact h0 h
  · exact h ((startsWith_lit_one "0" rfl).mpr rfl)

/-- A non-empty sequence of digits is zeros followed by a numeral. -/
theorem zeros_numeral {ds : Chars} (hne : ds ≠ []) (h : ∀ x ∈ ds, IsDigit x.toNat) :
    seq (star (lit "0")) numeral ds := by
  induction ds with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    by_cases hx : x = 48
    · subst hx
      by_cases hxs : xs = []
      · subst hxs
        exact ⟨[], [48], rfl, star_parts [] (by simp), numeral_zero⟩
      · obtain ⟨z, n, hzn, hz, hn⟩ := ih hxs (fun y hy => h y (by simp [hy]))
        refine ⟨48 :: z, n, by simp [hzn], ?_, hn⟩
        obtain ⟨parts, rfl, hparts⟩ := hz
        refine ⟨[48] :: parts, rfl, fun p hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · rfl
        · exact hparts p hp
    · exact ⟨[], x :: xs, rfl, star_parts [] (by simp),
        numeral_of_digits (h x (by simp)) hx (fun y hy => h y (by simp [hy]))⟩

/-! ## The relation -/

/-- The category of the lexer for a kind of token of the spec. -/
def lexCategory : Category → Token.TokenCategory
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral => .numeral
  | .decimal => .decimal
  | .hexadecimal => .hexadecimal
  | .binary => .binary
  | .string => .string
  | .simpleSymbol | .reserved => .unquotedSymbol
  | .quotedSymbol => .quotedSymbol
  | .keyword => .keyword

/-- The lexeme `l` is the token of the kind with the characters `text`, from `start` to
`end`. -/
def LexemeIs (version : BSmtLibSpec.Lexicon.Version) (category : Category)
    (start «end» : Span.Location)
    (text : Chars) (l : Lexeme) : Prop :=
  l.category = lexCategory category ∧
    l.content.data.toList = BSmtLibSpec.Lexicon.Token.content version ⟨category, 0, text⟩ ∧
    l.start = start ∧ l.end = «end»

/--
`ModeInv version mode text content`: a token in progress in the mode, whose characters so far
are `text`, has the content `content`.
-/
def ModeInv (version : BSmtLibSpec.Lexicon.Version) : Mode → Chars → Chars → Prop
  | .numeral zero, text, content =>
    content = text ∧ numeral text ∧ (zero = true ↔ text = [48])
  | .fraction digits, text, content =>
    content = text ∧ ∃ n ds, text = n ++ 46 :: ds ∧ numeral n ∧
      (∀ x ∈ ds, IsDigit x.toNat) ∧ (digits = true ↔ ds ≠ [])
  | .hash, text, content => text = [35] ∧ content = []
  | .digits .hexadecimal, text, content =>
    text = 35 :: 120 :: content ∧ ∀ x ∈ content, altAll [digit, range 65 70, range 97 102] [x]
  | .digits .binary, text, content =>
    text = 35 :: 98 :: content ∧ ∀ x ∈ content, oneOf "01" [x]
  | .keyword, text, content => text = 58 :: content ∧ ∀ x ∈ content, SymChar x.toNat
  | .simpleSymbol, text, content =>
    content = text ∧ ∃ c rest, text = c :: rest ∧ ¬ IsDigit c.toNat ∧ ∀ x ∈ text, SymChar x.toNat
  | .quotedSymbol, text, content => text = 124 :: content ∧ ∀ x ∈ content, QuotedChar [x]
  | .quotedSymbolClosed, text, content =>
    text = 124 :: (content ++ [124]) ∧ ∀ x ∈ content, QuotedChar [x]
  | .string, text, content =>
    version ≠ .v2_0 ∧ ∃ b, text = 34 :: b ∧ StringBody b ∧ content = unescape b
  | .stringQuote, text, content =>
    version ≠ .v2_0 ∧ ∃ b, text = 34 :: (b ++ [34]) ∧ StringBody b ∧ content = unescape b
  | .legacyString, text, content =>
    version = .v2_0 ∧ ∃ b, text = 34 :: b ∧ StringBody20 b ∧ content = unescape20 b
  | .legacyEscape, text, content =>
    version = .v2_0 ∧ ∃ b, text = 34 :: (b ++ [92]) ∧ StringBody20 b ∧ content = unescape20 b
  | .legacyQuote, text, content =>
    version = .v2_0 ∧ ∃ b, text = 34 :: (b ++ [34]) ∧ StringBody20 b ∧ content = unescape20 b
  | .comment, text, _ => ∃ b, text = 59 :: b ∧ ∀ x ∈ b, ¬ LineBreak x.toNat
  | .whitespace, _, _ => False

/-- What a byte with no token in progress does, as the spec sees it. -/
def StartSound (version : BSmtLibSpec.Lexicon.Version) (location : Span.Location) (c : UInt8) :
    Started → Prop
  | .idle => whiteSpaceChar [c]
  | .pending p => p.start = location ∧ ModeInv version p.mode [c] p.content.data.toList
  | .token l => ∃ category, (category = .parenOpen ∨ category = .parenClose) ∧
      categoryRegex version category [c] ∧
      LexemeIs version category location (location.afterByte c) [c] l
  | .error _ => True

/-- What a byte does to a token in progress with the characters `text`, as the spec sees
it. -/
def AdvanceSound (version : BSmtLibSpec.Lexicon.Version) (p : Pending) (text : Chars)
    (location : Span.Location) (c : UInt8) : Advanced → Prop
  | .pending p' => p'.start = p.start ∧ ModeInv version p'.mode (text ++ [c]) p'.content.data.toList
  | .idle => comment (text ++ [c])
  | .tokenWith _ => False
  | .tokenBefore l => Delim c.toNat ∧ ∃ category, categoryRegex version category text ∧
      LexemeIs version category p.start location text l
  | .error _ => True

/-- What the end of the input does to a token in progress with the characters `text`, as the
spec sees it. -/
def FinishSound (version : BSmtLibSpec.Lexicon.Version) (p : Pending) (text : Chars)
    (location : Span.Location) : Finished → Prop
  | .none => commentAtEnd text
  | .token l => ∃ category, categoryRegex version category text ∧
      LexemeIs version category p.start location text l
  | .error _ => True

/-! ## The steps keep the relation -/

theorem start_sound (version : BSmtLibSpec.Lexicon.Version) (location : Span.Location) (c : UInt8) :
    StartSound version location c (start (Lexer.Adapters.toVersion version) false location c) := by
  unfold start
  by_cases hw : isWhitespace c = true
  · simp only [hw, Bool.false_eq_true, ite_true, ite_false]
    exact (whitespace_iff c).mp hw
  simp only [hw, Bool.false_eq_true, ite_false]
  by_cases h40 : c = 40
  · subst h40
    exact ⟨.parenOpen, Or.inl rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [h40, beq_iff_eq, ite_false]
  by_cases h41 : c = 41
  · subst h41
    exact ⟨.parenClose, Or.inr rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [h41, ite_false]
  by_cases h59 : c = 59
  · subst h59
    exact ⟨rfl, [], rfl, by simp⟩
  simp only [h59, ite_false]
  by_cases h35 : c = 35
  · subst h35
    exact ⟨rfl, rfl, rfl⟩
  simp only [h35, ite_false]
  by_cases h34 : c = 34
  · subst h34
    by_cases hv : version = .v2_0
    · have := (toVersion_beq version).mpr hv
      simp only [this, ite_true]
      exact ⟨rfl, hv, [], rfl, star_parts [] (by simp), rfl⟩
    · have : (Lexer.Adapters.toVersion version == .v2_0) = false := by
        cases h : (Lexer.Adapters.toVersion version == .v2_0)
        · rfl
        · exact absurd ((toVersion_beq version).mp h) hv
      simp only [this, Bool.false_eq_true, ite_false]
      exact ⟨rfl, hv, [], rfl, star_parts [] (by simp), rfl⟩
  simp only [h34, ite_false]
  by_cases h58 : c = 58
  · subst h58
    exact ⟨rfl, rfl, by simp⟩
  simp only [h58, ite_false]
  by_cases h124 : c = 124
  · subst h124
    exact ⟨rfl, rfl, by simp⟩
  simp only [h124, ite_false]
  by_cases hd : isDigit c = true
  · simp only [hd, ite_true]
    refine ⟨rfl, toList_push_empty c, ?_, ?_⟩
    · by_cases h48 : c = 48
      · subst h48
        exact numeral_zero
      · exact numeral_of_digits ((isDigit_iff c).mp hd) h48 (by simp)
    · simp [beq_iff_eq]
  simp only [hd, Bool.false_eq_true, ite_false]
  by_cases hs : isSymbolByte c = true
  · simp only [hs, ite_true]
    refine ⟨rfl, toList_push_empty c, c, [], rfl, fun h => hd ((isDigit_iff c).mpr h), ?_⟩
    simpa using (isSymbolByte_iff c).mp hs
  simp only [hs, Bool.false_eq_true, ite_false]
  trivial

/-- A token that the byte delimits, if it is a delimiter. -/
theorem delimited_sound {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} {kind : LexicalErrorKind} (category : Category)
    (hr : categoryRegex version category text)
    (hk : p.content.data.toList = BSmtLibSpec.Lexicon.Token.content version ⟨category, 0, text⟩) :
    AdvanceSound version p text location c
      (if isDelimiter c = true then
        .tokenBefore
          { category := lexCategory category, content := p.content, start := p.start,
            «end» := location }
      else .error (failAtByte kind p.start location)) := by
  by_cases hd : isDelimiter c = true
  · simp only [hd, ite_true]
    exact ⟨(isDelimiter_iff c).mp hd, category, hr, rfl, hk, rfl, rfl⟩
  · simp only [hd, Bool.false_eq_true, ite_false]
    trivial

theorem advance_numeral {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} {zero : Bool} (hm : p.mode = .numeral zero)
    (h : ModeInv version (.numeral zero) text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  obtain ⟨hk, hn, hz⟩ := h
  simp only [advance, hm]
  by_cases hd : isDigit c = true
  · simp only [hd, ite_true]
    cases zero
    · simp only [Bool.false_eq_true, ite_false]
      have h0 : text ≠ [48] := fun e => absurd (hz.mpr e) (by simp)
      obtain ⟨d, ds, rfl, hdd, hd0, hds⟩ := numeral_head hn h0
      refine ⟨rfl, by rw [toList_push, hk], ?_, by simp⟩
      exact numeral_of_digits hdd hd0 (by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hds x hx
        · rw [List.mem_singleton.mp hx]; exact (isDigit_iff c).mp hd)
    · simp only [ite_true]
      trivial
  simp only [hd, Bool.false_eq_true, ite_false]
  by_cases h46 : c = 46
  · subst h46
    simp only [beq_self_eq_true, ite_true]
    exact ⟨rfl, by rw [toList_push, hk], text, [], rfl, hn, by simp, by simp⟩
  simp only [beq_iff_eq, h46, ite_false]
  exact delimited_sound .numeral hn hk


theorem advance_fraction {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} {digits : Bool} (hm : p.mode = .fraction digits)
    (h : ModeInv version (.fraction digits) text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  obtain ⟨hk, n, ds, rfl, hn, hds, hdig⟩ := h
  simp only [advance, hm]
  by_cases hd : isDigit c = true
  · simp only [hd, ite_true]
    refine ⟨rfl, by rw [toList_push, hk], n, ds ++ [c], by simp, hn, ?_, by simp⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hds x hx
    · rw [List.mem_singleton.mp hx]; exact (isDigit_iff c).mp hd
  simp only [hd, Bool.false_eq_true, ite_false]
  cases digits
  · simp only [Bool.not_false, ite_true]
    trivial
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    have hne : ds ≠ [] := hdig.mp rfl
    refine delimited_sound .decimal ?_ hk
    show decimal (n ++ 46 :: ds)
    exact ⟨n, [46] ++ ds, rfl, hn, ⟨[46], ds, rfl, rfl, zeros_numeral hne hds⟩⟩

theorem advance_hash {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} (hm : p.mode = .hash)
    (h : ModeInv version .hash text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  obtain ⟨rfl, hk⟩ := h
  simp only [advance, hm]
  by_cases h120 : c = 120
  · subst h120
    simp only [beq_self_eq_true, ite_true]
    exact ⟨rfl, by rw [hk]; rfl, by rw [hk]; simp⟩
  simp only [beq_iff_eq, h120, ite_false]
  by_cases h98 : c = 98
  · subst h98
    simp only [ite_true]
    exact ⟨rfl, by rw [hk]; rfl, by rw [hk]; simp⟩
  simp only [h98, ite_false]
  trivial

theorem advance_digits {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} {radix : Radix} (hm : p.mode = .digits radix)
    (h : ModeInv version (.digits radix) text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  simp only [advance, hm]
  cases radix with
  | hexadecimal =>
    obtain ⟨rfl, hall⟩ := h
    by_cases ha : Radix.allows .hexadecimal c = true
    · simp only [ha, ite_true]
      refine ⟨rfl, by rw [toList_push]; simp, ?_⟩
      intro x hx
      rw [toList_push] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hall x hx
      · rw [List.mem_singleton.mp hx]; exact (hexDigit_iff c).mp ha
    simp only [ha, Bool.false_eq_true, ite_false]
    by_cases he : p.content.isEmpty = true
    · simp only [he, ite_true]
      trivial
    simp only [he, Bool.false_eq_true, ite_false]
    have hne : p.content.data.toList ≠ [] := fun e => he ((isEmpty_iff _).mpr e)
    exact delimited_sound .hexadecimal ⟨[35, 120], _, rfl, rfl, plus_of_chars hne hall⟩ rfl
  | binary =>
    obtain ⟨rfl, hall⟩ := h
    by_cases ha : Radix.allows .binary c = true
    · simp only [ha, ite_true]
      refine ⟨rfl, by rw [toList_push]; simp, ?_⟩
      intro x hx
      rw [toList_push] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hall x hx
      · rw [List.mem_singleton.mp hx]; exact (binaryDigit_iff c).mp ha
    simp only [ha, Bool.false_eq_true, ite_false]
    by_cases he : p.content.isEmpty = true
    · simp only [he, ite_true]
      trivial
    simp only [he, Bool.false_eq_true, ite_false]
    have hne : p.content.data.toList ≠ [] := fun e => he ((isEmpty_iff _).mpr e)
    exact delimited_sound .binary ⟨[35, 98], _, rfl, rfl, plus_of_chars hne hall⟩ rfl

theorem symChar_regex {x : UInt8} (h : SymChar x.toNat) :
    altAll [letter, digit, symbolPunctuation] [x] :=
  (symbolByte_iff x).mp ((isSymbolByte_iff x).mpr h)

theorem advance_keyword {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} (hm : p.mode = .keyword)
    (h : ModeInv version .keyword text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  obtain ⟨rfl, hall⟩ := h
  simp only [advance, hm]
  by_cases hs : isSymbolByte c = true
  · simp only [hs, ite_true]
    refine ⟨rfl, by rw [toList_push]; simp, ?_⟩
    intro x hx
    rw [toList_push] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hall x hx
    · rw [List.mem_singleton.mp hx]; exact (isSymbolByte_iff c).mp hs
  simp only [hs, Bool.false_eq_true, ite_false]
  by_cases he : p.content.isEmpty = true
  · simp only [he, ite_true]
    trivial
  simp only [he, Bool.false_eq_true, ite_false]
  have hne : p.content.data.toList ≠ [] := fun e => he ((isEmpty_iff _).mpr e)
  exact delimited_sound .keyword
    ⟨[58], _, rfl, rfl, plus_of_chars hne fun x hx => symChar_regex (hall x hx)⟩ rfl

/-- The category of a simple symbol or reserved word with the characters. -/
def symbolCategory (version : BSmtLibSpec.Lexicon.Version) (text : Chars) : Category :=
  if text ∈ reservedWords version then .reserved else .simpleSymbol

theorem symbolCategory_regex {version : BSmtLibSpec.Lexicon.Version} {c : UInt8} {rest : Chars}
    (hd : ¬ IsDigit c.toNat) (hall : ∀ x ∈ c :: rest, SymChar x.toNat) :
    categoryRegex version (symbolCategory version (c :: rest)) (c :: rest) := by
  unfold symbolCategory
  by_cases hr : c :: rest ∈ reservedWords version
  · simp only [hr, ite_true, categoryRegex]
    exact litOneOf_iff.mpr hr
  · simp only [hr, ite_false, categoryRegex]
    exact simpleSymbol_of (fun x hx => symChar_regex (hall x hx)) hd hr

theorem lexCategory_symbol (version : BSmtLibSpec.Lexicon.Version) (text : Chars) :
    lexCategory (symbolCategory version text) = .unquotedSymbol := by
  unfold symbolCategory
  split <;> rfl

theorem content_symbol (version : BSmtLibSpec.Lexicon.Version) (text : Chars) :
    BSmtLibSpec.Lexicon.Token.content version ⟨symbolCategory version text, 0, text⟩ = text := by
  unfold symbolCategory
  split <;> rfl

theorem advance_simpleSymbol {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} (hm : p.mode = .simpleSymbol)
    (h : ModeInv version .simpleSymbol text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  obtain ⟨hk, d, rest, rfl, hd, hall⟩ := h
  simp only [advance, hm]
  by_cases hs : isSymbolByte c = true
  · simp only [hs, ite_true]
    refine ⟨rfl, by rw [toList_push, hk], d, rest ++ [c], rfl, hd, ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hall x hx
    · rw [List.mem_singleton.mp hx]; exact (isSymbolByte_iff c).mp hs
  simp only [hs, Bool.false_eq_true, ite_false]
  by_cases hdl : isDelimiter c = true
  · simp only [hdl, ite_true]
    refine ⟨(isDelimiter_iff c).mp hdl, symbolCategory version (d :: rest),
      symbolCategory_regex hd hall, ?_, ?_, rfl, rfl⟩
    · rw [lexCategory_symbol]
    · rw [content_symbol, hk]
  · simp only [hdl, Bool.false_eq_true, ite_false]
    trivial

theorem quotedChar_of {c : UInt8} (ht : isTextByte c = true) (h124 : c ≠ 124) (h92 : c ≠ 92) :
    QuotedChar [c] := by
  refine ⟨spaceOrPrintable_one.mpr ((text_iff c).mp ht), fun h => ?_⟩
  rw [oneOf_one] at h
  have e : chars "|\\" = [124, 92] := rfl
  rw [e] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · exact h124 h
  · exact h92 h

theorem advance_quotedSymbol {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} (hm : p.mode = .quotedSymbol)
    (h : ModeInv version .quotedSymbol text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  obtain ⟨rfl, hall⟩ := h
  simp only [advance, hm]
  by_cases h124 : c = 124
  · subst h124
    simp only [beq_self_eq_true, ite_true]
    exact ⟨rfl, by simp, hall⟩
  simp only [beq_iff_eq, h124, ite_false]
  by_cases h92 : c = 92
  · simp only [h92, ite_true]
    trivial
  simp only [h92, ite_false]
  by_cases ht : isTextByte c = true
  · simp only [ht, ite_true]
    refine ⟨rfl, by rw [toList_push]; simp, ?_⟩
    intro x hx
    rw [toList_push] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hall x hx
    · rw [List.mem_singleton.mp hx]; exact quotedChar_of ht h124 h92
  simp only [ht, Bool.false_eq_true, ite_false]
  trivial

theorem advance_quotedSymbolClosed {version : BSmtLibSpec.Lexicon.Version} {p : Pending}
    {text : Chars} {location : Span.Location} {c : UInt8} (hm : p.mode = .quotedSymbolClosed)
    (h : ModeInv version .quotedSymbolClosed text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  obtain ⟨rfl, hall⟩ := h
  simp only [advance, hm]
  refine delimited_sound .quotedSymbol ?_ ?_
  · exact ⟨[124], _ ++ [124], rfl, rfl, _, [124], rfl, star_each hall, rfl⟩
  · show _ = ((124 :: (p.content.data.toList ++ [124])).drop 1).dropLast
    simp

theorem stringUnit_of {c : UInt8} (ht : isTextByte c = true) (h34 : c ≠ 34) :
    alt (minus (alt printableChar whiteSpaceChar) (lit "\"")) (lit "\"\"") [c] := by
  refine Or.inl ⟨(text_iff c).mp ht, fun h => h34 ?_⟩
  have : [c] = [34] := h
  simpa using this

theorem advance_string {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} (hm : p.mode = .string)
    (h : ModeInv version .string text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  obtain ⟨hv, b, rfl, hb, hk⟩ := h
  simp only [advance, hm]
  by_cases h34 : c = 34
  · subst h34
    simp only [beq_self_eq_true, ite_true]
    exact ⟨rfl, hv, b, rfl, hb, hk⟩
  simp only [beq_iff_eq, h34, ite_false]
  by_cases ht : isTextByte c = true
  · simp only [ht, ite_true]
    have hu := stringUnit_of ht h34
    refine ⟨rfl, hv, b ++ [c], by simp, star_snoc hb hu, ?_⟩
    rw [toList_push, hk, unescape_append hb]
    rfl
  simp only [ht, Bool.false_eq_true, ite_false]
  trivial

theorem advance_stringQuote {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} (hm : p.mode = .stringQuote)
    (h : ModeInv version .stringQuote text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  obtain ⟨hv, b, rfl, hb, hk⟩ := h
  simp only [advance, hm]
  by_cases h34 : c = 34
  · subst h34
    simp only [beq_self_eq_true, ite_true]
    have hu : alt (minus (alt printableChar whiteSpaceChar) (lit "\"")) (lit "\"\"") [34, 34] :=
      Or.inr rfl
    refine ⟨rfl, hv, b ++ [34, 34], by simp, star_snoc hb hu, ?_⟩
    rw [toList_push, hk, unescape_append hb]
    rfl
  simp only [beq_iff_eq, h34, ite_false]
  refine delimited_sound .string ?_ ?_
  · show (if version = .v2_0 then string20 else string) _
    simp only [hv, ↓reduceIte]
    exact ⟨[34], b ++ [34], rfl, rfl, b, [34], rfl, hb, rfl⟩
  · show _ = (if version = .v2_0 then unescape20 else unescape)
      (((34 :: (b ++ [34])).drop 1).dropLast)
    simp only [hv, ↓reduceIte, hk]
    simp

theorem stringUnit20_char {c : UInt8} (ht : isTextByte c = true) (h34 : c ≠ 34)
    (h92 : c ≠ 92) :
    alt (minus (alt printableChar whiteSpaceChar) (oneOf "\"\\"))
      (seq (lit "\\") (alt printableChar whiteSpaceChar)) [c] := by
  refine Or.inl ⟨(text_iff c).mp ht, fun h => ?_⟩
  rw [oneOf_one] at h
  have e : chars "\"\\" = [34, 92] := rfl
  rw [e] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · exact h34 h
  · exact h92 h

theorem stringUnit20_escape {c : UInt8} (ht : isTextByte c = true) :
    alt (minus (alt printableChar whiteSpaceChar) (oneOf "\"\\"))
      (seq (lit "\\") (alt printableChar whiteSpaceChar)) [92, c] :=
  Or.inr ⟨[92], [c], rfl, rfl, (text_iff c).mp ht⟩

theorem legacyStringByte_sound {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {b : Chars}
    {location : Span.Location} {c : UInt8} (hv : version = .v2_0) (hb : StringBody20 b)
    (hk : p.content.data.toList = unescape20 b) :
    AdvanceSound version p (34 :: b) location c (legacyStringByte p location c) := by
  unfold legacyStringByte
  by_cases h34 : c = 34
  · subst h34
    simp only [beq_self_eq_true, ite_true]
    exact ⟨rfl, hv, b, rfl, hb, hk⟩
  simp only [beq_iff_eq, h34, ite_false]
  by_cases h92 : c = 92
  · subst h92
    simp only [ite_true]
    exact ⟨rfl, hv, b, rfl, hb, hk⟩
  simp only [h92, ite_false]
  by_cases ht : isTextByte c = true
  · simp only [ht, ite_true]
    refine ⟨rfl, hv, b ++ [c], by simp, star_snoc hb (stringUnit20_char ht h34 h92), ?_⟩
    rw [toList_push, hk, unescape20_append hb]
    rfl
  simp only [ht, Bool.false_eq_true, ite_false]
  trivial

theorem advance_legacyString {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} (hm : p.mode = .legacyString)
    (h : ModeInv version .legacyString text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  obtain ⟨hv, b, rfl, hb, hk⟩ := h
  simp only [advance, hm]
  exact legacyStringByte_sound hv hb hk

theorem advance_legacyEscape {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} (hm : p.mode = .legacyEscape)
    (h : ModeInv version .legacyEscape text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  obtain ⟨hv, b, rfl, hb, hk⟩ := h
  simp only [advance, hm]
  by_cases he : c = 34 ∨ c = 92
  · have hc : ((c == 34) || (c == 92)) = true := by
      rcases he with rfl | rfl <;> rfl
    simp only [hc, ite_true]
    have ht : isTextByte c = true := by rcases he with rfl | rfl <;> rfl
    refine ⟨rfl, hv, b ++ [92, c], by simp, star_snoc hb (stringUnit20_escape ht), ?_⟩
    rw [toList_push, hk, unescape20_append hb]
    rcases he with rfl | rfl <;> rfl
  · have h34 : c ≠ 34 := fun e => he (Or.inl e)
    have h92 : c ≠ 92 := fun e => he (Or.inr e)
    have hc : ((c == 34) || (c == 92)) = false := by
      simp [h34, h92]
    simp only [hc, Bool.false_eq_true, ite_false]
    unfold legacyStringByte
    simp only [beq_iff_eq, h34, h92, ite_false]
    by_cases ht : isTextByte c = true
    · simp only [ht, ite_true]
      refine ⟨rfl, hv, b ++ [92, c], by simp, star_snoc hb (stringUnit20_escape ht), ?_⟩
      rw [toList_push, toList_push, hk, unescape20_append hb]
      simp [unescape20, h34, h92]
    simp only [ht, Bool.false_eq_true, ite_false]
    trivial

theorem advance_legacyQuote {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} (hm : p.mode = .legacyQuote)
    (h : ModeInv version .legacyQuote text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  obtain ⟨hv, b, rfl, hb, hk⟩ := h
  simp only [advance, hm]
  refine delimited_sound .string ?_ ?_
  · show (if version = .v2_0 then string20 else string) _
    simp only [hv, ↓reduceIte]
    exact ⟨[34], b ++ [34], rfl, rfl, b, [34], rfl, hb, rfl⟩
  · show _ = (if version = .v2_0 then unescape20 else unescape)
      (((34 :: (b ++ [34])).drop 1).dropLast)
    simp only [hv, ↓reduceIte, hk]
    simp

theorem advance_comment {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    {location : Span.Location} {c : UInt8} (hm : p.mode = .comment)
    (h : ModeInv version .comment text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  obtain ⟨b, rfl, hb⟩ := h
  simp only [advance, hm]
  by_cases hl : ((c == 10) || (c == 13)) = true
  · simp only [hl, Bool.false_eq_true, ite_true, ite_false]
    refine ⟨[59], b ++ [c], rfl, rfl, b, [c], rfl, ?_, lineBreak_one.mpr ((lineBreak_iff c).mp hl)⟩
    exact star_each fun x hx => ⟨⟨x, rfl, Nat.zero_le _, by have := x.toNat_lt; omega⟩,
      fun h => hb x hx (lineBreak_one.mp h)⟩
  · simp only [hl, Bool.false_eq_true, ite_false]
    refine ⟨rfl, b ++ [c], rfl, ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hb x hx
    · rw [List.mem_singleton.mp hx]
      exact fun h => hl ((lineBreak_iff c).mpr h)

/-- A byte keeps the relation of the token in progress, and a lexeme it finishes is a token of
the spec. -/
theorem advance_sound {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    (location : Span.Location) (c : UInt8)
    (h : ModeInv version p.mode text p.content.data.toList) :
    AdvanceSound version p text location c (advance false p location c) := by
  cases hm : p.mode <;> rw [hm] at h
  · exact advance_numeral hm h
  · exact advance_fraction hm h
  · exact advance_hash hm h
  · exact advance_digits hm h
  · exact advance_keyword hm h
  · exact advance_simpleSymbol hm h
  · exact advance_quotedSymbol hm h
  · exact advance_quotedSymbolClosed hm h
  · exact advance_string hm h
  · exact advance_stringQuote hm h
  · exact advance_legacyString hm h
  · exact advance_legacyEscape hm h
  · exact advance_legacyQuote hm h
  · exact advance_comment hm h
  · exact h.elim


/-- The end of the input keeps the relation of the token in progress: a lexeme it finishes is
a token of the spec, and a comment it ends runs to the end of the input. -/
theorem finish_sound {version : BSmtLibSpec.Lexicon.Version} {p : Pending} {text : Chars}
    (location : Span.Location) (h : ModeInv version p.mode text p.content.data.toList) :
    FinishSound version p text location (finish false p location) := by
  unfold finish
  cases hm : p.mode <;> rw [hm] at h <;> simp only
  case numeral zero =>
    obtain ⟨hk, hn, -⟩ := h
    exact ⟨.numeral, hn, rfl, hk, rfl, rfl⟩
  case fraction digits =>
    obtain ⟨hk, n, ds, rfl, hn, hds, hdig⟩ := h
    cases digits
    · trivial
    · have hne : ds ≠ [] := hdig.mp rfl
      exact ⟨.decimal, ⟨n, [46] ++ ds, rfl, hn, ⟨[46], ds, rfl, rfl, zeros_numeral hne hds⟩⟩,
        rfl, hk, rfl, rfl⟩
  case hash => trivial
  case digits radix =>
    cases radix with
    | hexadecimal =>
      obtain ⟨rfl, hall⟩ := h
      by_cases he : p.content.isEmpty = true
      · simp only [he, ite_true]
        trivial
      simp only [he, Bool.false_eq_true, ite_false]
      have hne : p.content.data.toList ≠ [] := fun e => he ((isEmpty_iff _).mpr e)
      exact ⟨.hexadecimal, ⟨[35, 120], _, rfl, rfl, plus_of_chars hne hall⟩, rfl, rfl, rfl, rfl⟩
    | binary =>
      obtain ⟨rfl, hall⟩ := h
      by_cases he : p.content.isEmpty = true
      · simp only [he, ite_true]
        trivial
      simp only [he, Bool.false_eq_true, ite_false]
      have hne : p.content.data.toList ≠ [] := fun e => he ((isEmpty_iff _).mpr e)
      exact ⟨.binary, ⟨[35, 98], _, rfl, rfl, plus_of_chars hne hall⟩, rfl, rfl, rfl, rfl⟩
  case keyword =>
    obtain ⟨rfl, hall⟩ := h
    by_cases he : p.content.isEmpty = true
    · simp only [he, ite_true]
      trivial
    simp only [he, Bool.false_eq_true, ite_false]
    have hne : p.content.data.toList ≠ [] := fun e => he ((isEmpty_iff _).mpr e)
    exact ⟨.keyword, ⟨[58], _, rfl, rfl, plus_of_chars hne fun x hx => symChar_regex (hall x hx)⟩,
      rfl, rfl, rfl, rfl⟩
  case simpleSymbol =>
    obtain ⟨hk, d, rest, rfl, hd, hall⟩ := h
    exact ⟨symbolCategory version (d :: rest), symbolCategory_regex hd hall,
      by rw [lexCategory_symbol], by rw [content_symbol, hk], rfl, rfl⟩
  case quotedSymbol => trivial
  case quotedSymbolClosed =>
    obtain ⟨rfl, hall⟩ := h
    refine ⟨.quotedSymbol, ⟨[124], _ ++ [124], rfl, rfl, _, [124], rfl, star_each hall, rfl⟩,
      rfl, ?_, rfl, rfl⟩
    show _ = ((124 :: (p.content.data.toList ++ [124])).drop 1).dropLast
    simp
  case string => trivial
  case stringQuote =>
    obtain ⟨hv, b, rfl, hb, hk⟩ := h
    refine ⟨.string, ?_, rfl, ?_, rfl, rfl⟩
    · show (if version = .v2_0 then string20 else string) _
      simp only [hv, ↓reduceIte]
      exact ⟨[34], b ++ [34], rfl, rfl, b, [34], rfl, hb, rfl⟩
    · show _ = (if version = .v2_0 then unescape20 else unescape)
        (((34 :: (b ++ [34])).drop 1).dropLast)
      simp only [hv, ↓reduceIte, hk]
      simp
  case legacyString => trivial
  case legacyEscape => trivial
  case legacyQuote =>
    obtain ⟨hv, b, rfl, hb, hk⟩ := h
    refine ⟨.string, ?_, rfl, ?_, rfl, rfl⟩
    · show (if version = .v2_0 then string20 else string) _
      simp only [hv, ↓reduceIte]
      exact ⟨[34], b ++ [34], rfl, rfl, b, [34], rfl, hb, rfl⟩
    · show _ = (if version = .v2_0 then unescape20 else unescape)
        (((34 :: (b ++ [34])).drop 1).dropLast)
      simp only [hv, ↓reduceIte, hk]
      simp
  case comment =>
    obtain ⟨b, rfl, hb⟩ := h
    simp only [Bool.false_eq_true, ite_false]
    refine ⟨[59], b, rfl, rfl, ?_⟩
    exact star_each fun x hx => ⟨⟨x, rfl, Nat.zero_le _, by have := x.toNat_lt; omega⟩,
      fun h => hb x hx (lineBreak_one.mp h)⟩
  case whitespace => exact h.elim

end BSmtLib.Facts.Proofs.Lexer.VNaive.Modes
