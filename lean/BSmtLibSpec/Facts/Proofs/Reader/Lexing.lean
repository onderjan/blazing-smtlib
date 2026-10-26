module

public import BSmtLibSpec.Reader
public import BSmtLibSpec.Grammar.Properties
public import BSmtLibSpec.Facts.Proofs.Lexer.StreamingFacts
public import BSmtLibSpec.Facts.Proofs.Lexicon.Compose
public import BSmtLibSpec.Facts.Proofs.Lexer.Consumers

@[expose] public section

/-!
# What a correct lexer hands over to a parser

This module gives facts about a lexer that is `Correct`, as a parser of scripts sees what it
hands over:
- what it hands over depends only on the input, not on how the input is cut into slices
  (`fed_eq_of_flatten`);
- every token it hands over stands, for a parser, for the syntax token of the token in the
  version read (`received_handed`);
- characters whose tokenisation ends with a `)` at their end are handed over first whatever
  follows them (`handed_close_prefix`);
- a whole input that has a tokenisation is handed over with the end of the file
  (`fed_complete`);
- whatever it hands over is the start of a tokenisation of an input that agrees with the input
  up to the end of the last token handed over, followed by the end of the file only if the input
  has a tokenisation (`fed_readout`).

Not trusted: everything here is proved.
-/

namespace BSmtLibSpec.Facts.Proofs.Reader.Lexing

open BSmtLibSpec.Lexicon BSmtLibSpec.Lexer BSmtLibSpec.Grammar
open BSmtLibSpec.Lexicon.Properties
open BSmtLibSpec.Regex (Chars)
open BSmtLibSpec.Parser
open BSmtLibSpec.Facts.Proofs.Lexer.Streaming BSmtLibSpec.Facts.Proofs.Lexer.StreamingFacts
open BSmtLibSpec.Facts.Proofs.Lexicon.Compose BSmtLibSpec.Facts.Proofs.Lexicon.Lemmas
open BSmtLibSpec.Facts.Proofs.Lexicon.Unique

/-! ## Slices -/

/-- A correct lexer does the same on two ways of cutting an input into slices. -/
theorem fed_eq_of_flatten {feed : Version → List Chars → Bool → Fed} (h : Correct feed)
    {version : Version} {slices slices' : List Chars} (ended : Bool)
    (he : slices.flatten = slices'.flatten) :
    feed version slices ended = feed version slices' ended := by
  have hf : (feed version slices ended).failed = (feed version slices' ended).failed := by
    have h₁ := failsCorrectly_of_correct h version slices ended
    have h₂ := failsCorrectly_of_correct h version slices' ended
    simp only [FailsCorrectly] at h₁ h₂
    rw [he] at h₁
    exact Bool.eq_iff_iff.mpr (h₁.trans h₂.symm)
  have hh : (feed version slices ended).handed = (feed version slices' ended).handed := by
    by_cases hc : Complete version slices.flatten ended
    · have hend : ended = true := hc.1
      subst hend
      obtain ⟨t₁, ht₁, he₁⟩ := handsOverAll_of_correct h hc
      obtain ⟨t₂, ht₂, he₂⟩ := handsOverAll_of_correct h (he ▸ hc)
      rw [he₁, he₂, he]
      rw [he] at ht₁
      rw [tokenizationFrom_unique ht₁ ht₂]
    · obtain ⟨s, hs⟩ := exists_longestViableStart version slices.flatten
      obtain ⟨t₁, hm₁, he₁⟩ := handsOverMaximal_of_correct h hc s hs
      obtain ⟨t₂, hm₂, he₂⟩ := handsOverMaximal_of_correct h (he ▸ hc) s (he ▸ hs)
      rw [he₁, he₂, he, handoverMaximal_unique hs.2.1 hm₁ hm₂]
  cases hfeed : feed version slices ended
  cases hfeed' : feed version slices' ended
  rw [hfeed, hfeed'] at hh hf
  simp_all

/-! ## Tokens as a parser receives them -/

/-- A lexical token, wherever it is located, stands for its syntax token, which is one that a
lexer hands over in the version. -/
theorem received_handed {version : Version} {token : Token}
    (h : categoryRegex version token.category token.text) (input : Chars) :
    (token.handed version input).received =
        some (.token (SyntaxToken.ofToken version token)) ∧
      (Traversal.Received.token (SyntaxToken.ofToken version token)).OfVersion version := by
  obtain ⟨category, offset, text⟩ := token
  cases category <;>
    simp [Token.handed, Handed.received, Category.type, Token.reservedKind,
      SyntaxToken.ofToken, Token.content, Traversal.Received.OfVersion]
  exact ⟨by split <;> simp, by simpa [categoryRegex, reserved, litOneOf_iff] using h⟩

/-- Moving a token's location keeps what it stands for. -/
theorem received_after (before : Chars) (handed : Handed) :
    (handed.after before).received = handed.received := rfl

/-- Moving a token's location keeps its type. -/
theorem type_after (before : Chars) (handed : Handed) :
    (handed.after before).type = handed.type := rfl

/-- The end of a token located after `before` is moved by the length of `before`. -/
theorem end_offset_after (before : Chars) (handed : Handed) :
    (handed.after before).«end».offset = before.length + handed.«end».offset := rfl

/-- The end of a token handed over is the end of its characters. -/
theorem end_offset_handed (version : Version) (input : Chars) (token : Token) :
    (token.handed version input).«end».offset = token.offset + token.text.length := rfl

/-- A token moved stands for the same syntax token. -/
theorem ofToken_moveBy (version : Version) (k : Nat) (token : Token) :
    SyntaxToken.ofToken version (token.moveBy k) = SyntaxToken.ofToken version token := by
  obtain ⟨category, offset, text⟩ := token
  cases category <;> rfl

/-! ## Characters that end with a `)` -/

/-- The location of an offset within characters is its location in any longer input. -/
theorem handed_append {version : Version} {input more : Chars} {token : Token}
    (h : token.offset + token.text.length ≤ input.length) :
    token.handed version (input ++ more) = token.handed version input := by
  simp only [Token.handed, locate_append (show token.offset ≤ input.length by omega),
    locate_append h]

/-- A correct lexer fed characters whose tokenisation ends with a `)` at their end, followed by
anything, and then the end of the input, has handed over their tokens first. -/
theorem handed_close_prefix {feed : Version → List Chars → Bool → Fed} (h : Correct feed)
    {version : Version} {start : Chars} {tokens : List Token}
    (ht : Tokenization version start tokens) (hclose : EndsWithClose tokens start.length)
    (more : Chars) :
    ∃ rest, (feed version [start ++ more] true).handed =
      tokens.map (·.handed version (start ++ more)) ++ rest := by
  have hmax := close_handoverMaximal ht hclose
  have hv : Viable version start := viable_of_tokenization ht
  -- fed the characters alone, before the end, the lexer has handed over exactly their tokens
  obtain ⟨s, hs⟩ := exists_longestViableStart version [start].flatten
  have hss : s = start := by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hs
    exact longestViableStart_viable hs hv
  obtain ⟨tokens', hmax', he'⟩ :=
    handsOverMaximal_of_correct h (not_complete_false version [start].flatten) s hs
  rw [hss] at hmax'
  have heq := handoverMaximal_unique hv hmax' hmax
  subst heq
  have hp₁ := handed_prefix_of_correct h version [start] [more]
  have hp₂ := handed_prefix_end_of_correct h version ([start] ++ [more])
  have hf : feed version ([start] ++ [more]) true = feed version [start ++ more] true :=
    fed_eq_of_flatten h true (by simp)
  obtain ⟨rest, hrest⟩ := hp₁.trans hp₂
  refine ⟨rest, ?_⟩
  rw [← hf, ← hrest, he']
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_cancel_right_eq]
  refine List.map_congr_left fun token htoken => ?_
  exact (handed_append (handoverReady_within hv hmax.1 token htoken)).symm

/-- A correct lexer fed a whole input that has a tokenisation, and then the end of the input,
has handed over its tokens and the end of the file, and has not failed. -/
theorem fed_complete {feed : Version → List Chars → Bool → Fed} (h : Correct feed)
    {version : Version} {input : Chars} {tokens : List Token}
    (ht : Tokenization version input tokens) :
    feed version [input] true =
      ⟨tokens.map (·.handed version input) ++ [endOfFile input], false⟩ := by
  have hw := wholeInputCorrect_of_correct h version [input]
    (tokens.map (·.handed version input) ++ [endOfFile input])
  simp only [WholeInputCorrect, List.flatten_cons, List.flatten_nil, List.append_nil] at hw
  obtain ⟨hnf, he⟩ := hw.mpr ⟨tokens, ht, rfl⟩
  cases hfeed : feed version [input] true
  rw [hfeed] at hnf he
  simp_all

/-! ## What a lexer has handed over -/

/--
The tokens are the start of a tokenisation of an input that agrees with `input` up to an offset
at or after the end of each of them.
-/
def Readout (version : Version) (input : Chars) (tokens : List Token) : Prop :=
  ∃ other all n, Tokenization version other all ∧ tokens <+: all ∧
    input.take n = other.take n ∧ ∀ token ∈ tokens, token.offset + token.text.length ≤ n

/-- The tokens of a tokenisation end within its input. -/
theorem tokenizationFrom_within {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} (h : Tokenization.From version offset input tokens) :
    ∀ token ∈ tokens, token.offset + token.text.length ≤ offset + input.length := by
  induction h with
  | done => simp
  | token _ _ _ _ ih =>
    intro token htoken
    rcases List.mem_cons.mp htoken with rfl | htoken
    · simp only [List.length_append]
      omega
    · have := ih token htoken
      simp only [List.length_append]
      omega

/--
What a correct lexer fed an input and then the end of the input has handed over: tokens that are
the start of a tokenisation of an input that agrees with the input up to their end, and, only if
they are the tokenisation of the input, the end of the file after them.
-/
theorem fed_readout {feed : Version → List Chars → Bool → Fed} (h : Correct feed)
    (version : Version) (input : Chars) :
    ∃ tokens, Readout version input tokens ∧
      ((feed version [input] true).handed = tokens.map (·.handed version input) ∨
        (Tokenization version input tokens ∧
          (feed version [input] true).handed =
            tokens.map (·.handed version input) ++ [endOfFile input])) := by
  by_cases hc : Complete version [input].flatten true
  · obtain ⟨tokens, ht, he⟩ := handsOverAll_of_correct h hc
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at ht he
    exact ⟨tokens, ⟨input, tokens, input.length, ht, List.prefix_refl _, rfl,
      fun token htoken => by simpa using tokenizationFrom_within ht token htoken⟩,
      Or.inr ⟨ht, he⟩⟩
  · obtain ⟨s, hs⟩ := exists_longestViableStart version [input].flatten
    obtain ⟨tokens, hmax, he⟩ := handsOverMaximal_of_correct h hc s hs
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hs he
    obtain ⟨rest, all, hall⟩ := hs.2.1
    refine ⟨tokens, ⟨s ++ rest, all, s.length, hall, determined_prefix hmax.1.1 hall, ?_,
      handoverReady_within hs.2.1 hmax.1⟩, Or.inl he⟩
    rw [List.prefix_iff_eq_take.mp hs.1]
    simp

end BSmtLibSpec.Facts.Proofs.Reader.Lexing
