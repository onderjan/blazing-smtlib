import BSmtLib.Proofs.VNaive.Complete
import BSmtLib.Proofs.VNaive.Reserved

/-!
# The naive lexer is correct

`lex_correct`: the naive lexer as the adapter runs it, `handed VNaive.ops`, has the property
`Spec.Lexer.WholeInputCorrect` on every version and every input. It gives what the pure run of
the whole input gives (`handed_eq_run`); the pure run finishes exactly the inputs that have a
tokenisation (`run_sound`, `run_complete`), with the lexemes of its tokens; and the consumer
records the lexeme of a token as the spec hands the token over (`lexemeHanded_token`).
-/

namespace BSmtLib.Proofs.Lexer.VNaive

open BSmtLib.Proofs.Adapter BSmtLib.Spec.Lexicon BSmtLib.SpecChecks.Lexicon
open BSmtLib.Proofs.Simulation (byteArray_toList toByteArray_toByteSlice)

/-! ## What the consumer records of a lexeme -/

/-- The kind of reserved word the consumer records for a lexeme of the category with the
content, under the version. -/
def lexemeReserved (version : Version) (category : TokenCategory) (content : ByteArray) :
    Option Spec.Lexer.ReservedKind :=
  match category with
  | .unquotedSymbol => (Reserved.fromBytes? content.toByteSlice version).map reservedKindOf
  | _ => none

/-- What the consumer records of a lexeme, field by field. -/
theorem lexemeHanded_eq (version : Version) (l : Lexeme) :
    lexemeHanded version l = (toTokenType l.category).map fun type =>
      { type, start := toLocation l.start, «end» := toLocation l.end,
        reserved := lexemeReserved version l.category l.content,
        content := l.content.data.toList } := by
  unfold lexemeHanded
  simp only [toContent, toByteArray_toByteSlice, byteArray_toList]
  cases hc : l.category <;> simp [lexemeReserved] <;> rfl


/-! ## What the consumer records of the tokens of a tokenisation -/

/-- Every token of a tokenisation is a token of its kind, within the input. -/
theorem tokenizationFrom_tokens {version : Spec.Lexicon.Version} {offset : Nat} {input : Chars}
    {tokens : List Spec.Lexicon.Token} (h : TokenizationFrom version offset input tokens) :
    ∀ token ∈ tokens, categoryRegex version token.category token.text ∧
      offset ≤ token.offset ∧ token.offset + token.text.length ≤ offset + input.length := by
  induction h with
  | done => simp
  | token hw hs hd hrest ih =>
    rename_i offset w category s rest tokens
    intro token htoken
    rcases List.mem_cons.mp htoken with rfl | htoken
    · refine ⟨hs, by simp, ?_⟩
      simp only [List.length_append]
      omega
    · obtain ⟨hr, h1, h2⟩ := ih token htoken
      refine ⟨hr, by omega, ?_⟩
      simp only [List.length_append] at h2 ⊢
      omega

theorem toLocation_take {input : Chars} {n : Nat} (h : n ≤ input.length) :
    toLocation (locAfter (input.take n)) = Spec.Lexer.locate input n := by
  have := toLocation_locAfter_append (input.take n) (input.drop n)
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left h] at this
  exact this

theorem toTokenType_lexCategory (category : Category) :
    toTokenType (lexCategory category) = some category.type := by
  cases category <;> rfl

/-- The consumer records the lexeme of a token of the input as the spec hands it over. -/
theorem lexemeHanded_token {version : Spec.Lexicon.Version} {input : Chars}
    {token : Spec.Lexicon.Token} (hr : categoryRegex version token.category token.text)
    (hb : token.offset + token.text.length ≤ input.length) :
    lexemeHanded (toVersion version) (lexemeOf version input token) =
      some (token.handed version input) := by
  rw [lexemeHanded_eq]
  simp only [lexemeOf, toTokenType_lexCategory, Option.map_some, Option.some.injEq,
    Spec.Lexicon.Token.handed]
  obtain ⟨category, offset, text⟩ := token
  simp only at hr hb ⊢
  rw [toLocation_take (by omega), toLocation_take hb]
  congr 1
  cases category <;> simp only [lexCategory, lexemeReserved, Spec.Lexicon.Token.reservedKind]
  case simpleSymbol =>
    rw [fromBytes_kind]
    obtain ⟨-, -, -, -, hnot⟩ := simpleSymbol_inv hr
    simp only [reservedWords, List.map_append, List.mem_append, not_or] at hnot
    simp [specReservedKind, Spec.Lexicon.Token.content, hnot.2]
  case reserved =>
    rw [fromBytes_kind]
    have hmem := litOneOf_iff.mp hr
    simp only [List.map_append, List.mem_append] at hmem
    simp only [specReservedKind, Spec.Lexicon.Token.content, ne_eq, not_true_eq_false,
      ↓reduceIte]
    by_cases hbasic : text ∈ (basicReservedWords version).map chars
    · have : ∃ w ∈ basicReservedWords version, text = chars w := by
        obtain ⟨w, hw, e⟩ := List.mem_map.mp hbasic
        exact ⟨w, hw, e.symm⟩
      simp [hbasic, this]
    · have : ¬ ∃ w ∈ basicReservedWords version, text = chars w := by
        rintro ⟨w, hw, rfl⟩
        exact hbasic (List.mem_map_of_mem hw)
      have hcmd : text ∈ (commandNames version).map chars := hmem.resolve_left hbasic
      simp [hbasic, this, hcmd]
  all_goals simp

theorem lexemeHanded_eof (version : Version) (input : Chars) :
    lexemeHanded version (eofLexeme (locAfter input)) = some (Spec.Lexer.endOfFile input) := by
  rw [lexemeHanded_eq]
  simp only [eofLexeme, toTokenType, Option.map_some, toLocation_locAfter, lexemeReserved]
  rfl

/-- The consumer records the lexemes of tokens of the input and the end-of-file lexeme as the
spec hands them over. -/
theorem handedAll_of {version : Spec.Lexicon.Version} {input : Chars}
    (tokens : List Spec.Lexicon.Token)
    (h : ∀ token ∈ tokens, categoryRegex version token.category token.text ∧
      token.offset + token.text.length ≤ input.length) :
    handedAll (toVersion version)
        (tokens.map (lexemeOf version input) ++ [eofLexeme (locAfter input)]) =
      some (tokens.map (·.handed version input) ++ [Spec.Lexer.endOfFile input]) := by
  induction tokens with
  | nil => simp [handedAll, lexemeHanded_eof]
  | cons token tokens ih =>
    obtain ⟨hr, hb⟩ := h token (by simp)
    have ih' := ih fun t ht => h t (by simp [ht])
    unfold handedAll at ih' ⊢
    simp [List.mapM_cons, lexemeHanded_token hr hb, ih']

/-- The consumer records the lexemes of the tokens of a tokenisation and the end-of-file
lexeme as the spec hands them over. -/
theorem handedAll_tokens {version : Spec.Lexicon.Version} {input : Chars}
    {tokens : List Spec.Lexicon.Token} (h : Tokenization version input tokens) :
    handedAll (toVersion version)
        (tokens.map (lexemeOf version input) ++ [eofLexeme (locAfter input)]) =
      some (tokens.map (·.handed version input) ++ [Spec.Lexer.endOfFile input]) :=
  handedAll_of tokens fun token htoken => by
    obtain ⟨hr, -, hb⟩ := tokenizationFrom_tokens h token htoken
    exact ⟨hr, by simpa using hb⟩

/-! ## The lexer -/

/-- `handed VNaive.ops` hands over the tokens of the tokenisation of the input and the
end-of-file token exactly when the input has a tokenisation. -/
theorem lex_correct :
    ∀ version slices handed',
      Spec.Lexer.WholeInputCorrect (handed VNaive.ops) version slices handed' := by
  intro version slices handed'
  simp only [Spec.Lexer.WholeInputCorrect]
  rw [handed_eq_run]
  constructor
  · intro h
    obtain ⟨ls, hrun, hh⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tokens, ht, hm⟩ := run_sound hrun
    refine ⟨tokens, ht, ?_⟩
    rw [hm, handedAll_tokens ht] at hh
    exact (Option.some.inj hh).symm
  · rintro ⟨tokens, ht, rfl⟩
    rw [run_complete ht, Option.bind_some, handedAll_tokens ht]

end BSmtLib.Proofs.Lexer.VNaive
