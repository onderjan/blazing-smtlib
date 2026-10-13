import BSmtLib.SpecChecks.Unique
import BSmtLibSpec.Lexer

/-!
# Tokenisation across a closing parenthesis

An input whose tokenisation ends with a `)` that ends the input, followed by more characters:
every tokenisation of the whole starts with the tokens of the first part and goes on with a
tokenisation of the rest from where the first part ends (`tokenizationFrom_close_prefix`), and
the tokens of the first part followed by a tokenisation of the rest are one of the whole
(`tokenizationFrom_close_append`). A parenthesis needs no delimiter, so nothing after it can
change the tokens before it, and a lexer fed the first part may hand over all its tokens
(`close_handoverMaximal`). The rest read from any offset is tokenised as on its own, its tokens
moved (`tokenizationFrom_moveBy`, `tokenizationFrom_moveBy_inv`).

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Lexicon

open BSmtLibSpec BSmtLibSpec.Lexicon BSmtLibSpec.Regex
open BSmtLibSpec.Lexicon.Properties
open BSmtLibSpec.Regex (Chars chars)

/-- A tokenisation with a token has a non-empty input. -/
theorem tokenizationFrom_ne_nil {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} (h : Tokenization.From version offset input tokens) (hne : tokens ≠ []) :
    input ≠ [] := by
  cases h with
  | done => exact absurd rfl hne
  | token _ hs =>
    obtain ⟨c, t, rfl, -, -⟩ := token_shape hs
    simp

/-- A token delimited by a non-empty rest is delimited by the rest followed by anything. -/
theorem delimited_append {category : Category} {rest : Chars} (more : Chars)
    (h : Tokenization.Delimited category rest) (hne : rest ≠ []) : Tokenization.Delimited category (rest ++ more) := by
  rcases h with h | h | h | ⟨c, m, rfl, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd h hne
  · exact Or.inr (Or.inr (Or.inr ⟨c, m ++ more, rfl, hc⟩))

/-- Every tokenisation of an input that starts with characters whose tokenisation ends with a
`)` at their end starts with that tokenisation, and goes on with one of the rest. -/
theorem tokenizationFrom_close_prefix {version : Version} {offset : Nat} {start : Chars}
    {tokens : List Token} (h : Tokenization.From version offset start tokens)
    (hclose : EndsWithClose tokens (offset + start.length)) {more : Chars}
    {tokens' : List Token} (h' : Tokenization.From version offset (start ++ more) tokens') :
    ∃ others, tokens' = tokens ++ others ∧
      Tokenization.From version (offset + start.length) more others := by
  induction h generalizing tokens' with
  | done => obtain ⟨_, h, -⟩ := hclose; simp at h
  | @token w category s rest offset tokens hw hs hd hrest ih =>
    obtain ⟨last, hlast, hcat, hend⟩ := hclose
    cases tokens with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      simp only [List.length_append] at hend
      have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hr
      simp only [List.append_nil] at h' ⊢
      obtain ⟨ts, -, hts, rfl⟩ := tokenizationFrom_head hw hs
        (headOf_delimited hs (Or.inr (Or.inl hcat))) h'
      exact ⟨ts, rfl, by simpa [List.length_append, Nat.add_assoc] using hts⟩
    | cons t ts =>
      have hne : rest ≠ [] := tokenizationFrom_ne_nil hrest (by simp)
      rw [List.append_assoc] at h'
      obtain ⟨ts', -, hts', rfl⟩ := tokenizationFrom_head hw hs
        (headOf_delimited hs (delimited_append more hd hne)) h'
      have hclose' : EndsWithClose (t :: ts)
          (offset + w.length + s.length + rest.length) := by
        refine ⟨last, ?_, hcat, ?_⟩
        · simpa [List.getLast?_cons_cons] using hlast
        · simp only [List.length_append] at hend
          omega
      obtain ⟨others, rfl, hothers⟩ := ih hclose' hts'
      exact ⟨others, rfl, by simpa [List.length_append, Nat.add_assoc] using hothers⟩

/-- The tokens of characters whose tokenisation ends with a `)` at their end, followed by a
tokenisation of more characters, are a tokenisation of the two. -/
theorem tokenizationFrom_close_append {version : Version} {offset : Nat} {start : Chars}
    {tokens : List Token} (h : Tokenization.From version offset start tokens)
    (hclose : EndsWithClose tokens (offset + start.length)) {more : Chars}
    {others : List Token} (h' : Tokenization.From version (offset + start.length) more others) :
    Tokenization.From version offset (start ++ more) (tokens ++ others) := by
  induction h with
  | done => obtain ⟨_, h, -⟩ := hclose; simp at h
  | @token w category s rest offset tokens hw hs hd hrest ih =>
    obtain ⟨last, hlast, hcat, hend⟩ := hclose
    rw [List.append_assoc]
    cases tokens with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      simp only [List.length_append] at hend
      have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hr
      simp only [List.nil_append, List.length_append, List.length_nil, Nat.add_zero] at h' ⊢
      exact .token hw hs (Or.inr (Or.inl hcat)) (by simpa [Nat.add_assoc] using h')
    | cons t ts =>
      have hne : rest ≠ [] := tokenizationFrom_ne_nil hrest (by simp)
      have hclose' : EndsWithClose (t :: ts)
          (offset + w.length + s.length + rest.length) := by
        refine ⟨last, ?_, hcat, ?_⟩
        · simpa [List.getLast?_cons_cons] using hlast
        · simp only [List.length_append] at hend
          omega
      have h'' : Tokenization.From version (offset + w.length + s.length + rest.length) more
          others := by simpa [List.length_append, Nat.add_assoc] using h'
      exact .token hw hs (delimited_append more hd hne) (ih hclose' h'')

/-- The tokenisations of characters whose tokenisation ends with a `)` at their end, followed
by more, are its tokens followed by the tokenisations of the more on their own. -/
theorem tokenizationFrom_close_iff {version : Version} {offset : Nat} {start : Chars}
    {tokens : List Token} (h : Tokenization.From version offset start tokens)
    (hclose : EndsWithClose tokens (offset + start.length)) (more : Chars)
    (tokens' : List Token) :
    Tokenization.From version offset (start ++ more) tokens' ↔
      ∃ others, tokens' = tokens ++ others ∧
        Tokenization.From version (offset + start.length) more others := by
  constructor
  · exact tokenizationFrom_close_prefix h hclose
  · rintro ⟨others, rfl, h'⟩
    exact tokenizationFrom_close_append h hclose h'

/-- Every token of a tokenisation that ends with a `)` at the end of the input but that `)`
ends before the end of the input. -/
theorem close_delimiterSeen {version : Version} {offset : Nat} {start : Chars}
    {tokens : List Token} (h : Tokenization.From version offset start tokens)
    (hclose : EndsWithClose tokens (offset + start.length)) :
    ∀ token ∈ tokens, token.category = .parenClose ∨
      token.offset + token.text.length < offset + start.length := by
  induction h with
  | done => obtain ⟨_, h, -⟩ := hclose; simp at h
  | @token w category s rest offset tokens hw hs hd hrest ih =>
    obtain ⟨last, hlast, hcat, hend⟩ := hclose
    intro token htoken
    cases tokens with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      simp only [List.mem_singleton] at htoken
      subst hlast htoken
      exact Or.inl hcat
    | cons t ts =>
      have hne : rest ≠ [] := tokenizationFrom_ne_nil hrest (by simp)
      have hclose' : EndsWithClose (t :: ts)
          (offset + w.length + s.length + rest.length) := by
        refine ⟨last, ?_, hcat, ?_⟩
        · simpa [List.getLast?_cons_cons] using hlast
        · simp only [List.length_append] at hend
          omega
      have hlen : 0 < rest.length := List.length_pos_iff.mpr hne
      rcases List.mem_cons.mp htoken with rfl | htoken
      · right
        simp only [List.length_append]
        omega
      · rcases ih hclose' token htoken with hc | hc
        · exact Or.inl hc
        · right
          simp only [List.length_append]
          omega

/-- A lexer fed characters whose tokenisation ends with a `)` at their end may hand over all
their tokens, and no more: it holds nothing back. -/
theorem close_handoverMaximal {version : Version} {start : Chars} {tokens : List Token}
    (h : Tokenization version start tokens) (hclose : EndsWithClose tokens start.length) :
    BSmtLibSpec.Lexer.HandoverMaximal version start tokens := by
  have hclose' : EndsWithClose tokens (0 + start.length) := by simpa using hclose
  have hready : BSmtLibSpec.Lexer.HandoverReady version start tokens := by
    refine ⟨fun rest tokens' h' => tokenizationFrom_close_prefix h hclose' h' |>.imp
      fun _ h => h.1, fun token htoken => ?_⟩
    rcases close_delimiterSeen h hclose' token htoken with hc | hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (by simpa using hc))
  refine ⟨hready, fun tokens' h' => ?_⟩
  obtain ⟨more, rfl⟩ := h'.1 [] tokens (by simpa using h)
  simp

/-! ## Reading the rest on its own -/

/-- A tokenisation of characters read further to the right. -/
theorem tokenizationFrom_moveBy {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} (h : Tokenization.From version offset input tokens) (k : Nat) :
    Tokenization.From version (offset + k) input (tokens.map (Token.moveBy k)) := by
  induction h with
  | done hw => exact .done hw
  | @token w category s rest offset tokens hw hs hd hrest ih =>
    have e : offset + k + w.length = offset + w.length + k := by omega
    have ih' : Tokenization.From version (offset + k + w.length + s.length) rest
        (tokens.map (Token.moveBy k)) := by
      rw [show offset + k + w.length + s.length = offset + w.length + s.length + k by omega]
      exact ih
    simpa [Token.moveBy, e] using Tokenization.From.token hw hs hd ih'

/-- A tokenisation of characters read from `offset + k` is one read from `offset`, moved. -/
theorem tokenizationFrom_moveBy_inv {version : Version} {offset k : Nat} {input : Chars}
    {tokens : List Token} (h : Tokenization.From version (offset + k) input tokens) :
    ∃ tokens₀, tokens = tokens₀.map (Token.moveBy k) ∧
      Tokenization.From version offset input tokens₀ := by
  generalize ho : offset + k = o at h
  induction h generalizing offset with
  | done hw => exact ⟨[], rfl, .done hw⟩
  | @token w category s rest o tokens hw hs hd hrest ih =>
    subst ho
    obtain ⟨tokens₀, rfl, h₀⟩ := ih (offset := offset + w.length + s.length) (by omega)
    refine ⟨⟨category, offset + w.length, s⟩ :: tokens₀, ?_, .token hw hs hd h₀⟩
    simp only [List.map_cons, Token.moveBy, List.cons.injEq, Token.mk.injEq, and_true, true_and]
    omega

end BSmtLib.SpecChecks.Lexicon
