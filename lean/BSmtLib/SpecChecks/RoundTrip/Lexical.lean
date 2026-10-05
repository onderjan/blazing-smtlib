import BSmtLib.SpecChecks.Unique
import BSmtLib.SpecChecks.RoundTrip.Tokens
import BSmtLib.Spec.Grammar

/-!
# Writing syntax tokens as lexical tokens

The way back from a syntax token to the category and characters of a lexical token, in a
version: a symbol in the form it records, a string literal with its content escaped, and every
other token as it was read. A syntax token read from a lexical token is written as a lexical
token of its category that is read back as the same syntax token; it is written as the very
token it was read from, except for one form that reading forgets: a backslash in a 2.0 string
literal that does not start `\\` or `\"` stands for itself, and is written back escaped.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Lexicon

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Lexicon.Regex BSmtLib.Spec.Grammar

/-! ## The writer -/

/-- A character of a string literal's content, as the version writes it inside the literal:
from 2.5 on, `"` doubled; in 2.0, `"` and `\` each after a backslash. -/
def escapeChar (version : Version) (c : UInt8) : Chars :=
  if version = .v2_0 then (if c = 34 ∨ c = 92 then [92, c] else [c])
  else if c = 34 then [34, 34] else [c]

/-- A symbol in the form it records: simple, or between bars. -/
def symbolForm (symbol : Tree.Symbol) : Category × Chars :=
  if symbol.quoted then (.quotedSymbol, 124 :: (symbol.name ++ [124]))
  else (.simpleSymbol, symbol.name)

/-- The category and characters of the lexical token the syntax token is written as. -/
def lexForm (version : Version) : SyntaxToken → Category × Chars
  | .parenOpen => (.parenOpen, chars "(")
  | .parenClose => (.parenClose, chars ")")
  | .numeral digits => (.numeral, digits)
  | .decimal text => (.decimal, text)
  | .hexadecimal digits => (.hexadecimal, chars "#x" ++ digits)
  | .binary digits => (.binary, chars "#b" ++ digits)
  | .string content => (.string, 34 :: (content.flatMap (escapeChar version) ++ [34]))
  | .symbol symbol => symbolForm symbol
  | .keyword name => (.keyword, 58 :: name)
  | .reserved w => (.reserved, w)

/-- The lexical token the syntax token is written as, at offset 0. -/
def lexToken (version : Version) (token : SyntaxToken) : Token :=
  ⟨(lexForm version token).1, 0, (lexForm version token).2⟩

/-! ## The forgotten form -/

/-- The body of a 2.0 string literal has a backslash that does not start `\\` or `\"`, reading
`\\` and `\"` as pairs from the left. -/
def loneBackslash : Chars → Bool
  | a :: b :: rest =>
    if a = 92 then (if b = 34 ∨ b = 92 then loneBackslash rest else true)
    else loneBackslash (b :: rest)
  | _ => false

/-- In the version, no string literal among the tokens has a backslash that does not start
`\\` or `\"`; only 2.0 has such a backslash. -/
def NoLoneBackslash (version : Version) (tokens : List Token) : Prop :=
  version = .v2_0 → ∀ token ∈ tokens, token.category = .string →
    loneBackslash ((token.text.drop 1).dropLast) = false

/-! ## Reading back what is written -/

theorem chars_hex : chars "#x" = [35, 120] := by decide

theorem chars_bin : chars "#b" = [35, 98] := by decide

theorem unescape_cons {c : UInt8} (hc : c ≠ 34) (rest : Chars) :
    unescape (c :: rest) = c :: unescape rest := by
  cases rest with
  | nil => rfl
  | cons b rest => simp [unescape, hc]

theorem unescape20_cons {c : UInt8} (hc : c ≠ 92) (rest : Chars) :
    unescape20 (c :: rest) = c :: unescape20 rest := by
  cases rest with
  | nil => rfl
  | cons b rest => simp [unescape20, hc]

theorem unescape_escape {version : Version} (hv : version ≠ .v2_0) (content : Chars) :
    unescape (content.flatMap (escapeChar version)) = content := by
  induction content with
  | nil => rfl
  | cons c rest ih =>
    by_cases hc : c = 34
    · subst hc
      simp [escapeChar, hv, unescape, ih]
    · simp [escapeChar, hv, hc, unescape_cons hc, ih]

theorem unescape20_escape (content : Chars) :
    unescape20 (content.flatMap (escapeChar .v2_0)) = content := by
  induction content with
  | nil => rfl
  | cons c rest ih =>
    by_cases hc : c = 34 ∨ c = 92
    · simp only [List.flatMap_cons, escapeChar, hc, ite_true]
      simp [unescape20, hc, ih]
    · have hc92 : c ≠ 92 := fun e => hc (Or.inr e)
      simp [escapeChar, hc, unescape20_cons hc92, ih]

theorem drop_dropLast_quote (body : Chars) (q : UInt8) :
    ((q :: (body ++ [q])).drop 1).dropLast = body := by
  simp

theorem content_string {version : Version} (body : Chars) (o : Nat) :
    Token.content version ⟨.string, o, 34 :: (body ++ [34])⟩ =
      (if version = .v2_0 then unescape20 else unescape) body := by
  simp [Token.content]

/-- A written syntax token is read back as itself. -/
theorem ofToken_lexToken (version : Version) (token : SyntaxToken) :
    SyntaxToken.ofToken version (lexToken version token) = token := by
  cases token with
  | string content =>
    simp only [lexToken, lexForm, SyntaxToken.ofToken]
    rw [content_string]
    by_cases hv : version = .v2_0
    · subst hv
      simp [unescape20_escape]
    · simp [hv, unescape_escape hv]
  | symbol symbol =>
    obtain ⟨name, quoted⟩ := symbol
    cases quoted <;> simp [lexToken, lexForm, symbolForm, SyntaxToken.ofToken, Token.content]
  | hexadecimal digits => simp [lexToken, lexForm, SyntaxToken.ofToken, Token.content, chars_hex]
  | binary digits => simp [lexToken, lexForm, SyntaxToken.ofToken, Token.content, chars_bin]
  | keyword name => simp [lexToken, lexForm, SyntaxToken.ofToken, Token.content]
  | _ => rfl

/-- The offset of a token does not change what it stands for. -/
theorem ofToken_offset (version : Version) (token : Token) (offset : Nat) :
    SyntaxToken.ofToken version ⟨token.category, offset, token.text⟩ =
      SyntaxToken.ofToken version token := by
  simp [SyntaxToken.ofToken, Token.content]

/-! ## String bodies -/

theorem flatMap_congr {α β : Type} {f g : α → List β} {l : List α}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp),
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- A character allowed in a string literal: printable or white space. -/
def StringChar (c : UInt8) : Prop := alt printableChar whiteSpaceChar [c]

/-- What a part of the body of a string literal from 2.5 on stands for. -/
def decodeUnit (p : Chars) : Chars := if p = [34, 34] then [34] else p

theorem unescape_parts {parts : List Chars}
    (h : ∀ p ∈ parts, alt (minus (alt printableChar whiteSpaceChar) (lit "\"")) (lit "\"\"") p) :
    unescape parts.flatten = parts.flatMap decodeUnit := by
  induction parts with
  | nil => rfl
  | cons p ps ih =>
    have ih := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    rcases stringUnit_inv (h p (by simp)) with ⟨c, rfl, hc⟩ | rfl
    · simp [decodeUnit, unescape_cons hc, ih]
    · simp [decodeUnit, unescape, ih]

/-- What a part of the body of a 2.0 string literal stands for. -/
def decodeUnit20 : Chars → Chars
  | [92, d] => if d = 34 ∨ d = 92 then [d] else [92, d]
  | p => p

theorem unescape20_parts {parts : List Chars}
    (h : ∀ p ∈ parts, alt (minus (alt printableChar whiteSpaceChar) (oneOf "\"\\"))
      (seq (lit "\\") (alt printableChar whiteSpaceChar)) p) :
    unescape20 parts.flatten = parts.flatMap decodeUnit20 := by
  induction parts with
  | nil => rfl
  | cons p ps ih =>
    have ih := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    rcases stringUnit20_inv (h p (by simp)) with ⟨c, rfl, -, hc⟩ | ⟨d, rfl⟩
    · have : decodeUnit20 [c] = [c] := by
        unfold decodeUnit20
        split
        · rename_i heq
          simp at heq
        · rfl
      simp [this, unescape20_cons hc, ih]
    · by_cases hd : d = 34 ∨ d = 92
      · simp [decodeUnit20, hd, unescape20, ih]
      · have hd92 : d ≠ 92 := fun e => hd (Or.inr e)
        simp [decodeUnit20, hd, unescape20, unescape20_cons hd92, ih]

theorem loneBackslash_parts {parts : List Chars}
    (h : ∀ p ∈ parts, alt (minus (alt printableChar whiteSpaceChar) (oneOf "\"\\"))
      (seq (lit "\\") (alt printableChar whiteSpaceChar)) p)
    (hl : loneBackslash parts.flatten = false) :
    ∀ p ∈ parts, ∀ d, p = [92, d] → d = 34 ∨ d = 92 := by
  induction parts with
  | nil => simp
  | cons p ps ih =>
    have hps := fun q hq => h q (List.mem_cons_of_mem _ hq)
    intro q hq d hqd
    rcases List.mem_cons.mp hq with rfl | hq
    · subst hqd
      by_cases hd : d = 34 ∨ d = 92
      · exact hd
      exfalso
      cases hrest : ps.flatten with
      | nil => simp [loneBackslash, hrest, hd] at hl
      | cons b r => simp [loneBackslash, hrest, hd] at hl
    · refine ih hps ?_ q hq d hqd
      rcases stringUnit20_inv (h p (by simp)) with ⟨c, rfl, -, hc⟩ | ⟨e, rfl⟩
      · cases hrest : ps.flatten with
        | nil => rfl
        | cons b r => simpa [loneBackslash, hc, hrest] using hl
      · by_cases he : e = 34 ∨ e = 92
        · simpa [loneBackslash, he] using hl
        · simp [loneBackslash, he] at hl

/-- Every character of the content of a string literal is allowed in one. -/
theorem stringChar_unit {p : Chars}
    (h : alt (minus (alt printableChar whiteSpaceChar) (lit "\"")) (lit "\"\"") p) :
    ∀ x ∈ decodeUnit p, StringChar x := by
  rcases h with ⟨hp, hn⟩ | h
  · have hne : p ≠ [34, 34] := by
      intro e
      subst e
      obtain ⟨c, hc⟩ := printableOrSpace_inv hp
      simp at hc
    simp only [decodeUnit, hne, ite_false]
    obtain ⟨c, rfl⟩ := printableOrSpace_inv hp
    simpa [StringChar] using hp
  · rw [lit_iff] at h
    subst h
    have : decodeUnit (chars "\"\"") = [34] := by decide
    rw [this]
    simp only [List.mem_singleton, forall_eq, StringChar]
    exact printableOrSpace_one.mpr (by decide)

theorem stringChar_unit20 {p : Chars}
    (h : alt (minus (alt printableChar whiteSpaceChar) (oneOf "\"\\"))
      (seq (lit "\\") (alt printableChar whiteSpaceChar)) p) :
    ∀ x ∈ decodeUnit20 p, StringChar x := by
  rcases h with ⟨hp, hn⟩ | h
  · obtain ⟨c, rfl⟩ := printableOrSpace_inv hp
    have : decodeUnit20 [c] = [c] := by
      unfold decodeUnit20
      split
      · rename_i heq
        simp at heq
      · rfl
    rw [this]
    simpa [StringChar] using hp
  · obtain ⟨b, rfl, hb⟩ := seq_lit h
    obtain ⟨d, rfl⟩ := printableOrSpace_inv hb
    have h92 : StringChar 92 := printableOrSpace_one.mpr (by decide)
    have hd : StringChar d := hb
    show ∀ x ∈ decodeUnit20 [92, d], StringChar x
    by_cases hdd : d = 34 ∨ d = 92
    · simp [decodeUnit20, hdd, hd]
    · simp [decodeUnit20, hdd, hd, h92]

/-- The escaped content of a string literal is a body of a string literal of the version. -/
theorem escaped_body {version : Version} {content : Chars} (h : ∀ x ∈ content, StringChar x) :
    categoryRegex version .string (34 :: (content.flatMap (escapeChar version) ++ [34])) := by
  have hparts : content.flatMap (escapeChar version) =
      (content.map (escapeChar version)).flatten := by
    simp [List.flatMap]
  by_cases hv : version = .v2_0
  · subst hv
    simp only [categoryRegex, ite_true]
    refine ⟨[34], _, rfl, rfl, _, [34], rfl, ?_, rfl⟩
    rw [hparts]
    refine star_parts _ fun p hp => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    have hcs := h c hc
    by_cases hq : c = 34 ∨ c = 92
    · simp only [escapeChar, ite_true, hq]
      exact Or.inr (seq_intro (a := [92]) (show ([92] : Chars) = chars "\\" by decide) hcs)
    · simp only [escapeChar, ite_true, hq, ite_false]
      refine Or.inl ⟨hcs, ?_⟩
      rw [oneOf_one]
      intro hm
      apply hq
      have e : chars "\"\\" = [34, 92] := by decide
      rw [e] at hm
      simpa using hm
  · simp only [categoryRegex, hv, ite_false]
    refine ⟨[34], _, rfl, rfl, _, [34], rfl, ?_, rfl⟩
    rw [hparts]
    refine star_parts _ fun p hp => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    have hcs := h c hc
    by_cases hq : c = 34
    · subst hq
      simp only [escapeChar, hv, ite_false, ite_true]
      exact Or.inr (show ([34, 34] : Chars) = chars "\"\"" by decide)
    · simp only [escapeChar, hv, hq, ite_false]
      refine Or.inl ⟨hcs, ?_⟩
      intro hm
      rw [lit_iff] at hm
      apply hq
      have e : chars "\"" = [34] := by decide
      rw [e] at hm
      simpa using hm

/-! ## Written tokens are tokens -/

/-- A syntax token read from a token of the version is written as a token of the version. -/
theorem lexForm_regex {version : Version} {token : Token}
    (h : categoryRegex version token.category token.text) :
    categoryRegex version (lexForm version (SyntaxToken.ofToken version token)).1
      (lexForm version (SyntaxToken.ofToken version token)).2 := by
  obtain ⟨category, offset, text⟩ := token
  cases category with
  | string =>
    simp only [SyntaxToken.ofToken, lexForm]
    apply escaped_body
    by_cases hv : version = .v2_0
    · subst hv
      have h' : string20 text := by simpa [categoryRegex] using h
      obtain ⟨b, rfl, parts, rfl, hparts⟩ := string20_inv h'
      rw [content_string]
      simp only [ite_true]
      rw [unescape20_parts hparts]
      intro x hx
      obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.mp hx
      exact stringChar_unit20 (hparts p hp) x hxp
    · have h' : string text := by simpa [categoryRegex, hv] using h
      obtain ⟨b, rfl, parts, rfl, hparts⟩ := string_inv h'
      rw [content_string]
      simp only [hv, ite_false]
      rw [unescape_parts hparts]
      intro x hx
      obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.mp hx
      exact stringChar_unit (hparts p hp) x hxp
  | quotedSymbol =>
    obtain ⟨b, rfl, -⟩ := quotedSymbol_inv h
    simpa [SyntaxToken.ofToken, lexForm, symbolForm, Token.content] using h
  | hexadecimal =>
    obtain ⟨t, rfl, -⟩ := hexadecimal_inv h
    simpa [SyntaxToken.ofToken, lexForm, Token.content, chars_hex, chars_bin] using h
  | binary =>
    obtain ⟨t, rfl, -⟩ := binary_inv h
    simpa [SyntaxToken.ofToken, lexForm, Token.content, chars_hex, chars_bin] using h
  | keyword =>
    obtain ⟨t, rfl, -⟩ := keyword_inv h
    simpa [SyntaxToken.ofToken, lexForm, Token.content] using h
  | simpleSymbol => simpa [SyntaxToken.ofToken, lexForm, symbolForm, Token.content] using h
  | parenOpen => exact rfl
  | parenClose => exact rfl
  | numeral => simpa [SyntaxToken.ofToken, lexForm] using h
  | decimal => simpa [SyntaxToken.ofToken, lexForm] using h
  | reserved => simpa [SyntaxToken.ofToken, lexForm] using h

/-- A syntax token read from a token of the version is written as that very token, except for
a 2.0 string literal with a backslash that does not start `\\` or `\"`. -/
theorem lexForm_ofToken {version : Version} {token : Token}
    (h : categoryRegex version token.category token.text)
    (hl : NoLoneBackslash version [token]) :
    lexForm version (SyntaxToken.ofToken version token) = form token := by
  obtain ⟨category, offset, text⟩ := token
  cases category with
  | string =>
    simp only [SyntaxToken.ofToken, lexForm, form, Prod.mk.injEq, true_and]
    by_cases hv : version = .v2_0
    · subst hv
      have h' : string20 text := by simpa [categoryRegex] using h
      obtain ⟨b, rfl, parts, rfl, hparts⟩ := string20_inv h'
      have hlone := hl rfl _ (List.mem_singleton_self _) rfl
      simp only [drop_dropLast_quote] at hlone
      rw [content_string]
      simp only [ite_true]
      rw [unescape20_parts hparts]
      have hpart := loneBackslash_parts hparts hlone
      congr 1
      rw [List.flatMap_assoc]
      congr 1
      simp only [List.flatten_eq_flatMap]
      apply flatMap_congr
      intro p hp
      rcases stringUnit20_inv (hparts p hp) with ⟨c, rfl, hc34, hc92⟩ | ⟨d, rfl⟩
      · have : decodeUnit20 [c] = [c] := by
          unfold decodeUnit20
          split
          · rename_i heq
            simp at heq
          · rfl
        simp [this, escapeChar, hc34, hc92]
      · have hd := hpart _ hp d rfl
        simp [decodeUnit20, hd, escapeChar]
    · have h' : string text := by simpa [categoryRegex, hv] using h
      obtain ⟨b, rfl, parts, rfl, hparts⟩ := string_inv h'
      rw [content_string]
      simp only [hv, ite_false]
      rw [unescape_parts hparts]
      congr 1
      rw [List.flatMap_assoc]
      congr 1
      simp only [List.flatten_eq_flatMap]
      apply flatMap_congr
      intro p hp
      rcases stringUnit_inv (hparts p hp) with ⟨c, rfl, hc⟩ | rfl
      · simp [decodeUnit, escapeChar, hv, hc]
      · simp [decodeUnit, escapeChar, hv]
  | quotedSymbol =>
    obtain ⟨b, rfl, -⟩ := quotedSymbol_inv h
    simp [SyntaxToken.ofToken, lexForm, symbolForm, Token.content, form]
  | hexadecimal =>
    obtain ⟨t, rfl, -⟩ := hexadecimal_inv h
    simp [SyntaxToken.ofToken, lexForm, Token.content, chars_hex, form]
  | binary =>
    obtain ⟨t, rfl, -⟩ := binary_inv h
    simp [SyntaxToken.ofToken, lexForm, Token.content, chars_bin, form]
  | keyword =>
    obtain ⟨t, rfl, -⟩ := keyword_inv h
    simp [SyntaxToken.ofToken, lexForm, Token.content, form]
  | simpleSymbol => simp [SyntaxToken.ofToken, lexForm, symbolForm, Token.content, form]
  | parenOpen =>
    have h' : text = chars "(" := h
    simp [SyntaxToken.ofToken, lexForm, form, h']
  | parenClose =>
    have h' : text = chars ")" := h
    simp [SyntaxToken.ofToken, lexForm, form, h']
  | numeral => rfl
  | decimal => rfl
  | reserved => rfl

end BSmtLib.SpecChecks.Lexicon
