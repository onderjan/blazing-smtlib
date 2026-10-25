module

public import BSmtLibSpec.Facts.Proofs.Lexicon.Lemmas

@[expose] public section

/-!
# Printing tokens

Two ways back from lexicon tokens to characters.

- The concrete printer writes an input back exactly. The spec's tokens do not record the
  characters between them, whitespace and comments, so the concrete reading of an input is its
  tokenisation together with these gaps, which `readConcrete` takes from the input at the
  offsets of the tokens. `Gap` and `Concrete` are the only places that know how gaps are
  represented.
- The canonical layout writes each token's characters with the gap given by `separator`
  between two tokens, nothing before the first and a line feed after the last. It is the
  concrete printer with every gap replaced by its separator and the final one by `finalGap`.
  `place` gives the offsets at which it puts the tokens; reading the layout gives back the
  tokens at those offsets.

Not trusted: everything here is proved.
-/

namespace BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Tokens

open BSmtLibSpec.Lexicon BSmtLibSpec.Regex
open BSmtLibSpec.Facts.Proofs.Lexicon.Lemmas

/-! ## Concrete readings -/

/-- The characters between two tokens, before the first or after the last: whitespace and
comments, which the spec's tokens do not record. -/
abbrev Gap := Chars

/-- A concrete reading of an input: each token with the gap before it, and the gap after the
last token. -/
structure Concrete where
  pieces : List (Gap × Token)
  final : Gap

/-- The tokens of a concrete reading. -/
def Concrete.tokens (concrete : Concrete) : List Token := concrete.pieces.map Prod.snd

/-- The concrete printer: every gap and every token's characters, as they are. -/
def printConcrete (concrete : Concrete) : Chars :=
  (concrete.pieces.flatMap fun piece => piece.1 ++ piece.2.text) ++ concrete.final

/-- The concrete reading of an input whose first character is at `offset`, with the tokens
given: the gap before a token is the characters from the end of the previous token to the
token's offset, and the final gap is what follows the last token. -/
def readConcreteFrom : Nat → Chars → List Token → Concrete
  | _, input, [] => ⟨[], input⟩
  | offset, input, token :: tokens =>
    let before := token.offset - offset
    let rest := readConcreteFrom (token.offset + token.text.length)
      (input.drop (before + token.text.length)) tokens
    ⟨(input.take before, token) :: rest.pieces, rest.final⟩

/-- The concrete reading of an input with the tokens given, its tokenisation. -/
def readConcrete (input : Chars) (tokens : List Token) : Concrete :=
  readConcreteFrom 0 input tokens

theorem printConcrete_cons (gap : Gap) (token : Token) (pieces : List (Gap × Token))
    (final : Gap) :
    printConcrete ⟨(gap, token) :: pieces, final⟩ =
      gap ++ token.text ++ printConcrete ⟨pieces, final⟩ := by
  simp [printConcrete, List.append_assoc]

theorem readConcreteFrom_tokens (offset : Nat) (input : Chars) (tokens : List Token) :
    (readConcreteFrom offset input tokens).tokens = tokens := by
  induction tokens generalizing offset input with
  | nil => rfl
  | cons token tokens ih =>
    have := ih (token.offset + token.text.length)
      (input.drop (token.offset - offset + token.text.length))
    simp only [Concrete.tokens] at this ⊢
    simp [readConcreteFrom, this]

/-- The concrete printer writes back the input of a tokenisation. -/
theorem printConcrete_readConcreteFrom {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} (h : Tokenization.From version offset input tokens) :
    printConcrete (readConcreteFrom offset input tokens) = input := by
  induction h with
  | done => simp [readConcreteFrom, printConcrete]
  | @token w _ s rest offset _ _ _ _ _ ih =>
    have hbefore : offset + w.length - offset = w.length := by omega
    have hdrop : (w ++ s ++ rest).drop (w.length + s.length) = rest := by
      rw [List.append_assoc, ← List.drop_drop, List.drop_left, List.drop_left]
    have htake : (w ++ s ++ rest).take w.length = w := by
      rw [List.append_assoc, List.take_left]
    simp only [readConcreteFrom, hbefore, hdrop, htake]
    rw [printConcrete_cons]
    simp only [Nat.add_assoc] at ih ⊢
    rw [ih, List.append_assoc]

/-- The gaps of the concrete reading of a tokenisation are whitespace, and the final one is
whitespace at the end of the input. -/
theorem readConcreteFrom_gaps {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} (h : Tokenization.From version offset input tokens) :
    (∀ piece ∈ (readConcreteFrom offset input tokens).pieces, whitespace piece.1) ∧
      whitespaceAtEnd (readConcreteFrom offset input tokens).final := by
  induction h with
  | done hw => exact ⟨by simp [readConcreteFrom], hw⟩
  | @token w _ s rest offset _ hw _ _ _ ih =>
    have hbefore : offset + w.length - offset = w.length := by omega
    have hdrop : (w ++ s ++ rest).drop (w.length + s.length) = rest := by
      rw [List.append_assoc, ← List.drop_drop, List.drop_left, List.drop_left]
    have htake : (w ++ s ++ rest).take w.length = w := by
      rw [List.append_assoc, List.take_left]
    simp only [readConcreteFrom, hbefore, hdrop, htake]
    simp only [Nat.add_assoc] at ih ⊢
    refine ⟨fun piece hpiece => ?_, ih.2⟩
    rcases List.mem_cons.mp hpiece with rfl | hpiece
    · exact hw
    · exact ih.1 piece hpiece

/-! ## The canonical layout -/

/-- Where the canonical layout is after a token: the token's category, and the depth of the
parentheses open after it. -/
abbrev Place := Category × Nat

/-- The depth of the parentheses open after a token of the category, after a token at `place`
if there is one: one more after `(`, one fewer after `)`, but not below none. -/
def depthAfter (place : Option Place) (category : Category) : Nat :=
  let depth := match place with
    | none => 0
    | some (_, depth) => depth
  match category with
  | .parenOpen => depth + 1
  | .parenClose => depth - 1
  | _ => depth

/-- Where the canonical layout is after a token of the category, after a token at `place` if
there is one. -/
def after (place : Option Place) (category : Category) : Place :=
  (category, depthAfter place category)

/-- The gap the canonical layout writes before a token of the category `next`, after a token
at `place` if there is one: nothing before the first token, a line feed after a token that ends
a top-level item, that is, after which no parenthesis is open, and otherwise a single space,
except after `(` and before `)`. -/
def separator : Option Place → Category → Gap
  | none, _ => []
  | some (previous, depth), next =>
    if depth = 0 then [10]
    else if previous = .parenOpen ∨ next = .parenClose then [] else [32]

/-- Each token with the gap the canonical layout writes before it, after a token at `place` if
there is one. -/
def canonicalFrom : Option Place → List Token → List (Gap × Token)
  | _, [] => []
  | place, token :: tokens =>
    (separator place token.category, token) :: canonicalFrom (some (after place token.category))
      tokens

/-- The gap the canonical layout writes after the last token: a line feed, which ends the last
line, and nothing if there are no tokens. -/
def finalGap (tokens : List Token) : Gap := if tokens.isEmpty then [] else [10]

/-- The canonical layout of the tokens: the concrete printer, with every gap between two tokens
replaced by its separator, no gap before the first token and a line feed after the last. -/
def layout (tokens : List Token) : Chars :=
  printConcrete ⟨canonicalFrom none tokens, finalGap tokens⟩

/-- The tokens at the offsets at which the canonical layout puts them, after a token at `place`
if there is one, when its first character is at `offset`. -/
def placeFrom : Option Place → Nat → List Token → List Token
  | _, _, [] => []
  | place, offset, token :: tokens =>
    let start := offset + (separator place token.category).length
    ⟨token.category, start, token.text⟩ ::
      placeFrom (some (after place token.category)) (start + token.text.length) tokens

/-- The tokens at the offsets at which `layout` puts them. -/
def place (tokens : List Token) : List Token := placeFrom none 0 tokens

/-- The category and the characters of a token: the token without its offset. -/
def form (token : Token) : Category × Chars := (token.category, token.text)

/-- Placing tokens keeps their categories and characters. -/
theorem placeFrom_form (place : Option Place) (offset : Nat) (tokens : List Token) :
    (placeFrom place offset tokens).map form = tokens.map form := by
  induction tokens generalizing place offset with
  | nil => rfl
  | cons token tokens ih => simp [placeFrom, form, ih]

theorem place_form (tokens : List Token) : (place tokens).map form = tokens.map form :=
  placeFrom_form none 0 tokens

/-- The layout depends on the tokens only through their categories and characters. -/
theorem canonicalFrom_print_eq (place : Option Place) (final : Gap)
    {tokens tokens' : List Token} (h : tokens.map form = tokens'.map form) :
    printConcrete ⟨canonicalFrom place tokens, final⟩ =
      printConcrete ⟨canonicalFrom place tokens', final⟩ := by
  induction tokens generalizing place tokens' with
  | nil =>
    cases tokens' with
    | nil => rfl
    | cons _ _ => simp at h
  | cons token tokens ih =>
    cases tokens' with
    | nil => simp at h
    | cons token' tokens' =>
      simp only [List.map_cons, List.cons.injEq, form, Prod.mk.injEq] at h
      obtain ⟨⟨hc, ht⟩, h⟩ := h
      simp only [canonicalFrom, printConcrete_cons, hc, ht]
      rw [ih (some (after place token'.category)) h]

theorem layout_eq {tokens tokens' : List Token} (h : tokens.map form = tokens'.map form) :
    layout tokens = layout tokens' := by
  have hfinal : finalGap tokens = finalGap tokens' := by
    have := congrArg List.length h
    simp only [List.length_map] at this
    cases tokens <;> cases tokens' <;> simp_all [finalGap]
  rw [layout, layout, hfinal]
  exact canonicalFrom_print_eq none _ h

/-- Every token of a tokenisation is a token of its category. -/
theorem tokenizationFrom_regex {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} (h : Tokenization.From version offset input tokens) :
    ∀ token ∈ tokens, categoryRegex version token.category token.text := by
  induction h with
  | done => simp
  | token _ hs _ _ ih =>
    intro token htoken
    rcases List.mem_cons.mp htoken with rfl | htoken
    · exact hs
    · exact ih token htoken

/-! ## Whitespace -/

theorem whitespace_append {a b : Chars} (ha : whitespace a) (hb : whitespace b) :
    whitespace (a ++ b) := by
  obtain ⟨ps, rfl, hps⟩ := ha
  obtain ⟨qs, rfl, hqs⟩ := hb
  refine ⟨ps ++ qs, by simp, fun p hp => ?_⟩
  rcases List.mem_append.mp hp with hp | hp
  · exact hps p hp
  · exact hqs p hp

theorem whitespace_lineFeed : whitespace [10] :=
  star_each fun c hc => Or.inl (whiteSpaceChar_one.mpr (by simp at hc; simp [hc]))

theorem whitespace_separator (place : Option Place) (next : Category) :
    whitespace (separator place next) := by
  cases place with
  | none => exact whitespace_nil
  | some place =>
    obtain ⟨previous, depth⟩ := place
    simp only [separator]
    split
    · exact whitespace_lineFeed
    · split
      · exact whitespace_nil
      · exact whitespace_spaces (by simp)

theorem whitespace_finalGap (tokens : List Token) : whitespace (finalGap tokens) := by
  simp only [finalGap]
  split
  · exact whitespace_nil
  · exact whitespace_lineFeed

theorem whitespaceAtEnd_of {w : Chars} (h : whitespace w) : whitespaceAtEnd w :=
  ⟨w, [], by simp, h, Or.inl rfl⟩

/-! ## Delimitation -/

/-- The category is a parenthesis. -/
def IsParen (category : Category) : Prop := category = .parenOpen ∨ category = .parenClose

/-- Where the separator is empty, one of the two tokens is a parenthesis. -/
theorem separator_empty {place : Place} {next : Category} (h : separator (some place) next = []) :
    IsParen place.1 ∨ IsParen next := by
  obtain ⟨previous, depth⟩ := place
  simp only [separator] at h
  split at h
  · simp at h
  · split at h
    · rename_i hp
      rcases hp with hp | hp
      · exact Or.inl (Or.inl hp)
      · exact Or.inr (Or.inr hp)
    · simp at h

/-- A separator that is not empty starts with a white space character. -/
theorem separator_nonempty {place : Place} {next : Category} {c : UInt8} {more : Chars}
    (h : separator (some place) next = c :: more) : whiteSpaceChar [c] := by
  obtain ⟨previous, depth⟩ := place
  simp only [separator] at h
  split at h
  · simp only [List.cons.injEq] at h
    rw [← h.1]
    exact whiteSpaceChar_one.mpr (by decide)
  · split at h
    · simp at h
    · simp only [List.cons.injEq] at h
      rw [← h.1]
      exact whiteSpaceChar_one.mpr (by decide)

/-- The characters of a parenthesis. -/
theorem paren_text {version : Version} {category : Category} {s : Chars}
    (h : categoryRegex version category s) (hp : IsParen category) :
    ∃ c, s = [c] ∧ oneOf "();" [c] := by
  rcases hp with rfl | rfl
  · exact ⟨40, h, by rw [oneOf_one]; decide⟩
  · exact ⟨41, h, by rw [oneOf_one]; decide⟩

/-- What the canonical layout writes after a token at `place` delimits it, if the gap after the
last token is empty or starts with a white space character. -/
theorem delimited_canonicalFrom {version : Version} (place : Place) {tokens : List Token}
    {final : Gap} (hfinal : final = [] ∨ ∃ c more, final = c :: more ∧ whiteSpaceChar [c])
    (hall : ∀ token ∈ tokens, categoryRegex version token.category token.text) :
    Tokenization.Delimited place.1
      (printConcrete ⟨canonicalFrom (some place) tokens, final⟩) := by
  cases tokens with
  | nil =>
    simp only [canonicalFrom, printConcrete, List.flatMap_nil, List.nil_append]
    rcases hfinal with rfl | ⟨c, more, rfl, hc⟩
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact delimited_by (Or.inl hc)
  | cons next tokens =>
    simp only [canonicalFrom, printConcrete_cons]
    cases hsep : separator (some place) next.category with
    | cons c more =>
      simp only [List.cons_append]
      exact delimited_by (Or.inl (separator_nonempty hsep))
    | nil =>
      rcases separator_empty hsep with hc | hn
      · rcases hc with hc | hc
        · exact Or.inl hc
        · exact Or.inr (Or.inl hc)
      · obtain ⟨c, hs, hcp⟩ := paren_text (hall next (by simp)) hn
        simp only [List.nil_append, hs, List.singleton_append]
        exact delimited_by (Or.inr hcp)

/-! ## Reading the canonical layout -/

/-- Whitespace followed by the canonical layout, with whitespace after the last token that is
empty or starts with a white space character, has the placed tokens as a tokenisation. -/
theorem canonicalFrom_tokenization {version : Version} {tokens : List Token}
    (hall : ∀ token ∈ tokens, categoryRegex version token.category token.text)
    (place : Option Place) (offset : Nat) {w final : Chars} (hw : whitespace w)
    (hf : whitespace final)
    (hfinal : final = [] ∨ ∃ c more, final = c :: more ∧ whiteSpaceChar [c]) :
    Tokenization.From version offset (w ++ printConcrete ⟨canonicalFrom place tokens, final⟩)
      (placeFrom place (offset + w.length) tokens) := by
  induction tokens generalizing place offset w with
  | nil =>
    simpa [canonicalFrom, printConcrete, placeFrom] using
      Tokenization.From.done (version := version) (offset := offset)
        (whitespaceAtEnd_of (whitespace_append hw hf))
  | cons token tokens ih =>
    have hrest : ∀ t ∈ tokens, categoryRegex version t.category t.text :=
      fun t ht => hall t (List.mem_cons_of_mem _ ht)
    have hw' := whitespace_append hw (whitespace_separator place token.category)
    have htail := ih hrest (some (after place token.category))
      (offset + (w ++ separator place token.category).length + token.text.length)
      whitespace_nil
    simp only [List.nil_append, List.length_nil, Nat.add_zero] at htail
    have := Tokenization.From.token hw' (hall token (by simp))
      (delimited_canonicalFrom (after place token.category) hfinal hrest) htail
    simpa [canonicalFrom, printConcrete_cons, placeFrom, List.append_assoc, Nat.add_assoc,
      after] using this

/-- The canonical layout has the placed tokens as a tokenisation. -/
theorem layout_tokenization {version : Version} {tokens : List Token}
    (hall : ∀ token ∈ tokens, categoryRegex version token.category token.text) :
    Tokenization version (layout tokens) (place tokens) := by
  have hfinal : finalGap tokens = [] ∨
      ∃ c more, finalGap tokens = c :: more ∧ whiteSpaceChar [c] := by
    simp only [finalGap]
    split
    · exact Or.inl rfl
    · exact Or.inr ⟨10, [], rfl, whiteSpaceChar_one.mpr (by decide)⟩
  simpa [Tokenization, layout, place] using
    canonicalFrom_tokenization hall none 0 whitespace_nil (whitespace_finalGap tokens) hfinal

/-- Every token being a token of its category is the same as the tokens being, but for their
offsets, the tokenisation of some input. -/
theorem regex_iff_readable {version : Version} {tokens : List Token} :
    (∀ token ∈ tokens, categoryRegex version token.category token.text) ↔
      ∃ input tokens', Tokenization version input tokens' ∧
        tokens'.map form = tokens.map form := by
  constructor
  · exact fun h => ⟨_, _, layout_tokenization h, place_form tokens⟩
  · rintro ⟨input, tokens', h, hform⟩ token htoken
    have hmem : form token ∈ tokens'.map form := hform ▸ List.mem_map_of_mem htoken
    obtain ⟨token', htoken', heq⟩ := List.mem_map.mp hmem
    simp only [form, Prod.mk.injEq] at heq
    rw [← heq.1, ← heq.2]
    exact tokenizationFrom_regex h token' htoken'

end BSmtLibSpec.Facts.Proofs.Lexicon.RoundTrip.Tokens
