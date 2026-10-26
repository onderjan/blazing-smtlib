module

public import BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix
public import BSmtLibSpec.Facts.Proofs.Lexer.StreamingFacts

@[expose] public section

/-!
# The naive lexer is correct

`fedRun_correct`: what the pure run of the naive lexer hands over after the slices and then, if
the input has ended, the end of the input (`fedRun`), has the property `BSmtLibSpec.Lexer.Correct`.

`fedRun` is what the pure run over the bytes of the slices and then the end of the input gives,
also up to an error (`fedRun_eq_run`, `fedOf_isSome`), and the lexeme of a token is in the form
in which the specification formalism (`BSmtLibSpec`) hands the token over (`lexemeHanded_token`).

Before the end of the input (`correct_unended`): when the run gets through the bytes, they are
viable, as some bytes complete them to an input that the run finishes (`runFrom_completes`),
and the lexemes it has finished are the tokens maximal to hand over on them (`reached`): those
of the tokenisation of every completion that end before a byte the run has read, as the run is
the same over the bytes whatever follows them. When the run fails at a byte, the bytes before
it are the longest viable start, and the run has finished their tokens maximal to hand over.

After the end of the input (`correct_ended`): the end of the input after the bytes finishes the
run exactly when the input has a tokenisation (`run_sound`, `run_complete`), with the lexemes of
its tokens and the end-of-file lexeme. Otherwise the lexer has failed, and has handed over
nothing that it had not handed over before the end.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaive.Streaming

open BSmtLib.Facts.Lexer.Adapters BSmtLibSpec.Lexicon
open BSmtLibSpec.Lexicon.Properties
open BSmtLibSpec.Regex (Chars chars)
open BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes (byteArray_toList toByteArray_toByteSlice)
open BSmtLibSpec.Facts.Proofs.Lexer.StreamingFacts
    (handoverReady_within viable_of_prefix longestViableStart_unique longestViableStart_viable
    viable_of_tokenization not_complete_false)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Complete BSmtLib.Facts.Proofs.Lexer.VNaive.Facts
open BSmtLib.Facts.Proofs.Lexer.VNaive.Modes BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix
open BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix.Lexeme BSmtLib.Facts.Proofs.Lexer.VNaive.Reserved
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaive.Sound
open BSmtLib.Lexer.Internal.VNaive BSmtLibSpec.Facts.Proofs.Lexicon.Lemmas
open BSmtLibSpec.Facts.Proofs.Lexicon.Unique

/-! ## What the consumer records of a lexeme -/

/-- The kind of reserved word the consumer records for a lexeme of the category with the
content, under the version. -/
def lexemeReserved (version : Version) (category : Token.TokenCategory)
    (content : ByteArray) :
    Option BSmtLibSpec.Lexer.ReservedKind :=
  match category with
  | .unquotedSymbol => (Token.Reserved.fromBytes? content.toByteSlice version).map reservedKindOf
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
theorem tokenizationFrom_tokens {version : BSmtLibSpec.Lexicon.Version} {offset : Nat}
    {input : Chars}
    {tokens : List BSmtLibSpec.Lexicon.Token} (h : Tokenization.From version offset input tokens) :
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
    toLocation (locAfter (input.take n)) = BSmtLibSpec.Lexer.locate input n := by
  have := toLocation_locAfter_append (input.take n) (input.drop n)
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left h] at this
  exact this

theorem toTokenType_lexCategory (category : Category) :
    toTokenType (lexCategory category) = some category.type := by
  cases category <;> rfl

/-- The consumer records the lexeme of a token of the input as the formalism hands it over. -/
theorem lexemeHanded_token {version : BSmtLibSpec.Lexicon.Version} {input : Chars}
    {token : BSmtLibSpec.Lexicon.Token} (hr : categoryRegex version token.category token.text)
    (hb : token.offset + token.text.length ≤ input.length) :
    lexemeHanded (toVersion version) (lexemeOf version input token) =
      some (token.handed version input) := by
  rw [lexemeHanded_eq]
  simp only [lexemeOf, toTokenType_lexCategory, Option.map_some, Option.some.injEq,
    BSmtLibSpec.Lexicon.Token.handed]
  obtain ⟨category, offset, text⟩ := token
  simp only at hr hb ⊢
  rw [toLocation_take (by omega), toLocation_take hb]
  congr 1
  cases category <;> simp only [lexCategory, lexemeReserved, BSmtLibSpec.Lexicon.Token.reservedKind]
  case simpleSymbol =>
    rw [fromBytes_kind]
    obtain ⟨-, -, -, -, hnot⟩ := simpleSymbol_inv hr
    simp only [reservedWords, List.map_append, List.mem_append, not_or] at hnot
    simp [specReservedKind, BSmtLibSpec.Lexicon.Token.content, hnot.2]
  case reserved =>
    rw [fromBytes_kind]
    have hmem := litOneOf_iff.mp hr
    simp only [List.map_append, List.mem_append] at hmem
    simp only [specReservedKind, BSmtLibSpec.Lexicon.Token.content, ne_eq, not_true_eq_false,
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
    lexemeHanded version (eofLexeme (locAfter input)) = some
        (BSmtLibSpec.Lexer.endOfFile input) := by
  rw [lexemeHanded_eq]
  simp only [eofLexeme, toTokenType, Option.map_some, toLocation_locAfter, lexemeReserved]
  rfl

/-- The consumer records the lexemes of tokens of the input and the end-of-file lexeme as the
formalism hands them over. -/
theorem handedAll_of {version : BSmtLibSpec.Lexicon.Version} {input : Chars}
    (tokens : List BSmtLibSpec.Lexicon.Token)
    (h : ∀ token ∈ tokens, categoryRegex version token.category token.text ∧
      token.offset + token.text.length ≤ input.length) :
    handedAll (toVersion version)
        (tokens.map (lexemeOf version input) ++ [eofLexeme (locAfter input)]) =
      some (tokens.map (·.handed version input) ++ [BSmtLibSpec.Lexer.endOfFile input]) := by
  induction tokens with
  | nil => simp [handedAll, lexemeHanded_eof]
  | cons token tokens ih =>
    obtain ⟨hr, hb⟩ := h token (by simp)
    have ih' := ih fun t ht => h t (by simp [ht])
    unfold handedAll at ih' ⊢
    simp [List.mapM_cons, lexemeHanded_token hr hb, ih']

/-- The consumer records the lexemes of the tokens of a tokenisation and the end-of-file
lexeme as the formalism hands them over. -/
theorem handedAll_tokens {version : BSmtLibSpec.Lexicon.Version} {input : Chars}
    {tokens : List BSmtLibSpec.Lexicon.Token} (h : Tokenization version input tokens) :
    handedAll (toVersion version)
        (tokens.map (lexemeOf version input) ++ [eofLexeme (locAfter input)]) =
      some (tokens.map (·.handed version input) ++ [BSmtLibSpec.Lexer.endOfFile input]) :=
  handedAll_of tokens fun token htoken => by
    obtain ⟨hr, -, hb⟩ := tokenizationFrom_tokens h token htoken
    exact ⟨hr, by simpa using hb⟩

/-! ## The lexemes of tokens -/

theorem locAfter_offset (bytes : List UInt8) : (locAfter bytes).offset = bytes.length := by
  simp only [locAfter, advanceLoc_offset, Span.Location.initial,
    Span.Location.Internal.offset_new, Nat.zero_add]

theorem lexemeOf_start {version : BSmtLibSpec.Lexicon.Version} {input : Chars}
    {token : BSmtLibSpec.Lexicon.Token} (h : token.offset ≤ input.length) :
    (lexemeOf version input token).start.offset = token.offset := by
  show (locAfter (input.take token.offset)).offset = _
  rw [locAfter_offset, List.length_take]
  omega

theorem lexemeOf_end {version : BSmtLibSpec.Lexicon.Version} {input : Chars}
    {token : BSmtLibSpec.Lexicon.Token} (h : token.offset + token.text.length ≤ input.length) :
    (lexemeOf version input token).end.offset = token.offset + token.text.length := by
  show (locAfter (input.take (token.offset + token.text.length))).offset = _
  rw [locAfter_offset, List.length_take]
  omega

theorem lexemeOf_paren {version : BSmtLibSpec.Lexicon.Version} {input : Chars}
    {token : BSmtLibSpec.Lexicon.Token} :
    (IsParen (lexemeOf version input token)) ↔
      token.category = .parenOpen ∨ token.category = .parenClose := by
  simp only [Lexeme.IsParen, lexemeOf]
  cases token.category <;> simp [lexCategory]

/-- The characters of a token of a tokenisation are those of the input at its offset. -/
theorem tokenizationFrom_text {version : BSmtLibSpec.Lexicon.Version} {offset : Nat} {input : Chars}
    {tokens : List BSmtLibSpec.Lexicon.Token} (h : Tokenization.From version offset input tokens) :
    ∀ token ∈ tokens, (input.drop (token.offset - offset)).take token.text.length = token.text := by
  induction h with
  | done => simp
  | @token w category s rest offset tokens _ _ _ hrest ih =>
    intro token htoken
    rcases List.mem_cons.mp htoken with rfl | htoken
    · simp
    · have hle := (tokenizationFrom_tokens hrest token htoken).2.1
      have e : (w ++ s ++ rest).drop (token.offset - offset) =
          rest.drop (token.offset - (offset + w.length + s.length)) := by
        rw [show token.offset - offset =
          (w ++ s).length + (token.offset - (offset + w.length + s.length)) by
            simp only [List.length_append]; omega]
        rw [List.drop_append]
        simp
      rw [e]
      exact ih token htoken

/-- Two categories of the lexer's kind are the same kind if a token's characters are of both. -/
theorem category_eq {version : BSmtLibSpec.Lexicon.Version} {c₁ c₂ : Category} {text : Chars}
    (h : lexCategory c₁ = lexCategory c₂) (h₁ : categoryRegex version c₁ text)
    (h₂ : categoryRegex version c₂ text) : c₁ = c₂ := by
  have hsym : ∀ {text : Chars}, categoryRegex version .simpleSymbol text →
      categoryRegex version .reserved text → False := by
    intro text hs hr
    obtain ⟨_, _, -, -, -, hnot⟩ := simpleSymbol_inv hs
    exact hnot (by simpa [reservedWords] using litOneOf_iff.mp hr)
  cases c₁ <;> cases c₂ <;> simp only [lexCategory, reduceCtorEq] at h <;> first
    | rfl
    | exact (hsym h₁ h₂).elim
    | exact (hsym h₂ h₁).elim

/-- A token of one tokenisation and a token of another, of inputs that start with the same
characters, that end within those characters and have the same lexeme, are the same. -/
theorem token_eq_of_lexemeOf {version : BSmtLibSpec.Lexicon.Version} {input input' start : Chars}
    {tokens tokens' : List BSmtLibSpec.Lexicon.Token} {token token' : BSmtLibSpec.Lexicon.Token}
    (h : Tokenization version input tokens) (h' : Tokenization version input' tokens')
    (ht : token ∈ tokens) (ht' : token' ∈ tokens') (hs : start <+: input) (hs' : start <+: input')
    (hw : token.offset + token.text.length ≤ start.length)
    (he : lexemeOf version input token = lexemeOf version input' token') : token = token' := by
  obtain ⟨hr, -, hb⟩ := tokenizationFrom_tokens h token ht
  obtain ⟨hr', -, hb'⟩ := tokenizationFrom_tokens h' token' ht'
  simp only [Nat.zero_add] at hb hb'
  have ho : token.offset = token'.offset := by
    have := congrArg (fun l => l.start.offset) he
    rwa [lexemeOf_start (by omega), lexemeOf_start (by omega)] at this
  have hl : token.text.length = token'.text.length := by
    have := congrArg (fun l => l.end.offset) he
    rw [lexemeOf_end hb, lexemeOf_end hb'] at this
    omega
  have htext : token.text = token'.text := by
    have e := tokenizationFrom_text h token ht
    have e' := tokenizationFrom_text h' token' ht'
    simp only [Nat.sub_zero] at e e'
    obtain ⟨d, rfl⟩ := hs
    obtain ⟨d', rfl⟩ := hs'
    rw [← e, ← e', ← ho, ← hl, List.drop_append_of_le_length (by omega),
      List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega),
      List.take_append_of_le_length (by simp; omega)]
  have hc : token.category = token'.category := by
    have := congrArg (·.category) he
    simp only [lexemeOf] at this
    exact category_eq this hr (htext ▸ hr')
  cases token
  cases token'
  simp_all

/-! ## What the consumer records of the tokens -/

/-- A token that ends within the start of an input is handed over alike in every input that
starts with it. -/
theorem handed_append {version : BSmtLibSpec.Lexicon.Version} {start more : Chars}
    {token : BSmtLibSpec.Lexicon.Token} (h : token.offset + token.text.length ≤ start.length) :
    token.handed version (start ++ more) = token.handed version start := by
  simp only [BSmtLibSpec.Lexicon.Token.handed,
    BSmtLibSpec.Facts.Proofs.Lexer.StreamingFacts.locate_append
        (show token.offset ≤ start.length by omega),
    BSmtLibSpec.Facts.Proofs.Lexer.StreamingFacts.locate_append h]

/-- The consumer records the lexemes of tokens of the input as the formalism hands them over. -/
theorem handedAll_map {version : BSmtLibSpec.Lexicon.Version} {input : Chars}
    (tokens : List BSmtLibSpec.Lexicon.Token)
    (h : ∀ token ∈ tokens, categoryRegex version token.category token.text ∧
      token.offset + token.text.length ≤ input.length) :
    handedAll (toVersion version) (tokens.map (lexemeOf version input)) =
      some (tokens.map (·.handed version input)) := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    obtain ⟨hr, hb⟩ := h token (by simp)
    rw [List.map_cons, handedAll_cons_some (lexemeHanded_token hr hb),
      ih fun t ht => h t (by simp [ht])]
    rfl

/-! ## The bytes that the run gets through -/

/-- Bytes that the pure run gets through from the start are viable, and the lexemes it has
finished are the tokens maximal to hand over on them, as the consumer records them in every
input that starts with the bytes. -/
theorem reached {version : BSmtLibSpec.Lexicon.Version} {start : Chars} {st : St}
    {location : Span.Location}
    {ls : List Lexeme}
    (h : feedBytes (toVersion version) .idle Span.Location.initial start = some (st, location, ls))
    :
    Viable version start ∧ ∃ tokens, BSmtLibSpec.Lexer.HandoverMaximal version start tokens ∧
      ∀ input, start <+: input →
        handedAll (toVersion version) ls = some (tokens.map (·.handed version input)) := by
  have hloc : location.offset = start.length := by
    rw [feedBytes_location h, advanceLoc_offset]
    simp [Span.Location.initial]
  obtain ⟨rest, ls₂, hr⟩ := runFrom_completes (toVersion version) st location
  have hrun : run (toVersion version) (start ++ rest) = some (ls ++ ls₂) := by
    rw [run, runFrom_append, h]
    simp [hr]
  obtain ⟨all, hall, hm⟩ := run_sound hrun
  simp only [Matches] at hm
  -- the lexemes the run has finished are those of the first tokens
  have hne := runFrom_ne_nil hr
  have hn : ls.length ≤ all.length := by
    have := congrArg List.length hm
    simp only [List.length_append, List.length_map, List.length_singleton] at this
    have : ls₂.length ≠ 0 := fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
    omega
  have hls : ls = (all.take ls.length).map (lexemeOf version (start ++ rest)) := by
    have := congrArg (List.take ls.length) hm
    rwa [List.take_left, List.take_append_of_le_length (by simpa using hn),
      ← List.map_take] at this
  have hls₂ : ls₂ = (all.drop ls.length).map (lexemeOf version (start ++ rest)) ++
      [eofLexeme (locAfter (start ++ rest))] := by
    have := congrArg (List.drop ls.length) hm
    rwa [List.drop_left, List.drop_append_of_le_length (by simpa using hn),
      ← List.map_drop] at this
  -- the first tokens end within the bytes, before the byte after them unless parentheses
  have hwithin : ∀ token ∈ all.take ls.length, token.offset + token.text.length ≤ start.length ∧
      (¬ (token.category = .parenOpen ∨ token.category = .parenClose) →
        token.offset + token.text.length < start.length) := by
    intro token htoken
    have hb := (tokenizationFrom_tokens hall token (List.mem_of_mem_take htoken)).2.2
    simp only [Nat.zero_add] at hb
    have hl : lexemeOf version (start ++ rest) token ∈ ls := by
      rw [hls]; exact List.mem_map_of_mem htoken
    have := feedBytes_ends _ h _ hl
    rw [lexemeOf_end hb, hloc] at this
    exact ⟨this.1, fun hn => this.2 (fun hp => hn (lexemeOf_paren.mp hp))⟩
  have hdet : Determined version start (all.take ls.length) := by
    intro rest' all' hall'
    have hrun' := run_complete hall'
    rw [run, runFrom_append, h, Option.bind_some] at hrun'
    obtain ⟨ls₃, hr', he⟩ := Option.map_eq_some_iff.mp hrun'
    have hne' := runFrom_ne_nil hr'
    have hn' : ls.length ≤ all'.length := by
      have := congrArg List.length he
      simp only [List.length_append, List.length_map, List.length_singleton] at this
      have : ls₃.length ≠ 0 := fun h0 => hne' (List.eq_nil_of_length_eq_zero h0)
      omega
    have hls' : ls = (all'.take ls.length).map (lexemeOf version (start ++ rest')) := by
      have := congrArg (List.take ls.length) he
      rwa [List.take_left, List.take_append_of_le_length (by simpa using hn'),
        ← List.map_take] at this
    have htake : all'.take ls.length = all.take ls.length := by
      refine List.ext_getElem (by simp; omega) fun i hi' hi => ?_
      have hmap := congrArg (fun l => l[i]?) (hls.symm.trans hls')
      simp only [List.getElem?_map] at hmap
      rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at hmap
      simp only [Option.map_some, Option.some.injEq] at hmap
      exact (token_eq_of_lexemeOf hall hall' (List.mem_of_mem_take (List.getElem_mem hi))
        (List.mem_of_mem_take (List.getElem_mem hi')) (List.prefix_append _ _)
        (List.prefix_append _ _) (hwithin _ (List.getElem_mem hi)).1 hmap).symm
    refine ⟨all'.drop ls.length, ?_⟩
    rw [← htake]
    exact (List.take_append_drop _ _).symm
  have hready : BSmtLibSpec.Lexer.HandoverReady version start (all.take ls.length) := by
    refine ⟨hdet, fun token htoken => ?_⟩
    by_cases hp : token.category = .parenOpen ∨ token.category = .parenClose
    · rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr ((hwithin token htoken).2 hp))
  refine ⟨⟨rest, all, hall⟩, all.take ls.length, ⟨hready, ?_⟩, ?_⟩
  · -- no longer list is ready: the next token is finished after the bytes
    intro tokens' hready'
    obtain ⟨more, hmore⟩ := determined_prefix hready'.1 hall
    refine Nat.le_of_not_lt fun hlt => ?_
    have hlt' : ls.length < all.length := by
      have := congrArg List.length hmore
      simp only [List.length_append] at this
      rw [List.length_take] at hlt
      omega
    have hmem : all[ls.length] ∈ tokens' := by
      have : all[ls.length] = tokens'[ls.length]'(by rw [List.length_take] at hlt; omega) := by
        subst hmore
        exact List.getElem_append_left _
      rw [this]
      exact List.getElem_mem _
    have hw := handoverReady_within ⟨rest, all, hall⟩ hready' _ hmem
    have hb := (tokenizationFrom_tokens hall _ (List.getElem_mem hlt')).2.2
    simp only [Nat.zero_add] at hb
    have hl : lexemeOf version (start ++ rest) all[ls.length] ∈ ls₂ := by
      rw [hls₂]
      refine List.mem_append_left _ (List.mem_map_of_mem ?_)
      exact List.mem_iff_getElem.mpr ⟨0, by simp; omega, by simp⟩
    have := runFrom_ends _ hr _ hl
    rw [lexemeOf_end hb, hloc] at this
    rcases hready'.2 _ hmem with hp | hp | hp
    · exact absurd (this.2 (lexemeOf_paren.mpr (Or.inl hp))) (by omega)
    · exact absurd (this.2 (lexemeOf_paren.mpr (Or.inr hp))) (by omega)
    · omega
  · intro input hinput
    have hh := handedAll_map (version := version) (input := start ++ rest) (all.take ls.length)
      fun token htoken => ⟨(tokenizationFrom_tokens hall token (List.mem_of_mem_take htoken)).1,
        by have := (hwithin token htoken).1; simp only [List.length_append]; omega⟩
    rw [← hls] at hh
    rw [hh]
    congr 1
    refine List.map_congr_left fun token htoken => ?_
    have hw := (hwithin token htoken).1
    obtain ⟨d, rfl⟩ := hinput
    rw [handed_append hw, handed_append hw]

/-! ## The byte that the run fails at -/

/-- A run that fails gets through the bytes before the byte it fails at, and has finished the
lexemes before it. -/
theorem lexBytes_error {version : Version} (bytes : List UInt8) :
    ∀ {st : St} {location : Span.Location} {ls : List Lexeme},
      lexBytes version st location bytes = .error ls →
      ∃ before c after st' location' ls', bytes = before ++ c :: after ∧
        feedBytes version st location before = some (st', location', ls') ∧
        byteStep version st' location' c = none ∧ ls = ls' ++ failedBefore st' location' c := by
  induction bytes with
  | nil => intro st location ls h; cases h
  | cons c bytes ih =>
    intro st location ls h
    simp only [lexBytes] at h
    cases hb : byteStep version st location c with
    | none =>
      rw [hb] at h
      cases h
      exact ⟨[], c, bytes, st, location, [], rfl, rfl, hb, rfl⟩
    | some r =>
      obtain ⟨st₁, ls₁⟩ := r
      rw [hb] at h
      simp only at h
      cases e : lexBytes version st₁ (location.afterByte c) bytes with
      | ok r => rw [e] at h; obtain ⟨_, _, _⟩ := r; simp [withBefore] at h
      | error ls₂ =>
        rw [e] at h
        simp only [withBefore, Except.error.injEq] at h
        subst h
        obtain ⟨before, c', after, st', location', ls', rfl, hf, hb', rfl⟩ := ih e
        refine ⟨c :: before, c', after, st', location', ls₁ ++ ls', rfl, ?_, hb',
          (List.append_assoc _ _ _).symm⟩
        simp [feedBytes, hb, hf]

theorem lexBytes_of_feedBytes {version : Version} {st st' : St}
    {location location' : Span.Location}
    {bytes : List UInt8} {ls : List Lexeme}
    (h : feedBytes version st location bytes = some (st', location', ls)) :
    lexBytes version st location bytes = .ok (st', location', ls) := by
  rw [← lexBytes_toOption] at h
  cases e : lexBytes version st location bytes with
  | ok r => rw [e] at h; cases h; rfl
  | error _ => rw [e] at h; cases h

/-! ## The lexer -/

/-- `fedRun` gives what the pure run of the bytes of the slices and then, if the input has ended,
the end of the input give, also up to an error. -/
theorem fedOf_fedRun (version : BSmtLibSpec.Lexicon.Version) (slices : List BSmtLibSpec.Regex.Chars)
    (ended : Bool) :
    fedOf (toVersion version) ended (lexBytes (toVersion version) .idle Span.Location.initial
      slices.flatten) =
      some ((fedRun version slices ended).handed,
        (fedRun version slices ended).failed) := by
  obtain ⟨⟨hs, failed⟩, hf⟩ := fedOf_isSome (toVersion version) ended slices.flatten
  rw [hf, fedRun_eq_run version slices ended hs failed hf]

/-- The naive lexer fed slices, before the end of the input, fails exactly when the input is not
viable, and hands over the tokens maximal to hand over on the longest viable start. -/
theorem correct_unended (version : BSmtLibSpec.Lexicon.Version)
    (slices : List BSmtLibSpec.Regex.Chars)
    (start : Chars) :
    BSmtLibSpec.Lexer.FailsCorrectly fedRun version slices false ∧
      BSmtLibSpec.Lexer.HandsOverMaximal fedRun version slices false start := by
  have hf := fedOf_fedRun version slices false
  simp only [BSmtLibSpec.Lexer.FailsCorrectly, BSmtLibSpec.Lexer.HandsOverMaximal,
      Bool.false_eq_true,
    ↓reduceIte]
  generalize fedRun version slices false = r at hf ⊢
  obtain ⟨hs, failed⟩ := r
  simp only at hf ⊢
  cases e : lexBytes (toVersion version) .idle Span.Location.initial slices.flatten with
  | ok r =>
    obtain ⟨st, location, ls⟩ := r
    rw [e] at hf
    cases hls : handedAll (toVersion version) ls with
    | none => simp [fedOf, hls] at hf
    | some hs' =>
      simp only [fedOf, Bool.false_eq_true, ↓reduceIte, hls, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      have hfb : feedBytes (toVersion version) .idle Span.Location.initial slices.flatten =
          some (st, location, ls) := by
        rw [← lexBytes_toOption, e]; rfl
      obtain ⟨hv, tokens, hmax, hh⟩ := reached hfb
      refine ⟨⟨fun h => (by cases h), fun h => absurd hv h⟩, fun hstart => ?_⟩
      rw [longestViableStart_viable hstart hv]
      refine ⟨tokens, hmax, ?_⟩
      have := hh _ (List.prefix_refl _)
      rw [hls] at this
      exact Option.some.inj this
  | error ls =>
    rw [e] at hf
    cases hls : handedAll (toVersion version) ls with
    | none => simp [fedOf, hls] at hf
    | some hs' =>
      simp only [fedOf, hls, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      obtain ⟨before, c, after, st, location, ls', hsplit, hfb, hb, rfl⟩ := lexBytes_error _ e
      have htaken := lexBytes_taken (version := toVersion version)
          (location := Span.Location.initial)
        before (st := .idle) trivial
      rw [lexBytes_of_feedBytes hfb] at htaken
      rw [failedBefore_nil hb htaken.1, List.append_nil] at hls
      obtain ⟨hv, tokens, hmax, hh⟩ := reached hfb
      -- the bytes with the one the run fails at are not viable
      have hnv : ¬ Viable version (before ++ [c]) := by
        rintro ⟨rest, all, hall⟩
        have := run_complete hall
        rw [run, List.append_assoc, List.singleton_append, runFrom_append, hfb,
          Option.bind_some] at this
        simp only at this
        rw [runFrom_cons, hb] at this
        cases this
      have hpre : before ++ [c] <+: slices.flatten := by
        rw [hsplit]; exact ⟨after, by simp⟩
      have hbefore : before <+: slices.flatten := by
        rw [hsplit]; exact List.prefix_append _ _
      refine ⟨⟨fun _ hv' => hnv (viable_of_prefix hpre hv'), fun _ => rfl⟩, fun hstart => ?_⟩
      -- the bytes before the one the run fails at are the longest viable start
      have hA : BSmtLibSpec.Lexer.LongestViableStart version slices.flatten before := by
        refine ⟨hbefore, hv, fun longer hp hvl => Nat.le_of_not_lt fun hlt => hnv ?_⟩
        exact viable_of_prefix
          (List.prefix_of_prefix_length_le hpre hp (by simp only [List.length_append]; simp; omega))
          hvl
      rw [longestViableStart_unique hstart hA]
      refine ⟨tokens, hmax, ?_⟩
      have := hh _ hbefore
      rw [hls] at this
      exact Option.some.inj this

/-- A lexer that has failed at the end of an input with no tokenisation, and has handed over
then what it had before the end, is correct there if it was before the end. -/
theorem correct_ended_of_unended
    {feed : BSmtLibSpec.Lexicon.Version → List Chars → Bool → BSmtLibSpec.Lexer.Fed}
    {version : BSmtLibSpec.Lexicon.Version} {slices : List Chars} {start : Chars}
    (hnt : ¬ ∃ tokens, Tokenization version slices.flatten tokens)
    (hft : (feed version slices true).failed = true)
    (hh : (feed version slices true).handed = (feed version slices false).handed)
    (hu : BSmtLibSpec.Lexer.HandsOverMaximal feed version slices false start) :
    BSmtLibSpec.Lexer.FailsCorrectly feed version slices true ∧
      BSmtLibSpec.Lexer.HandsOverCorrectly feed version slices true start := by
  refine ⟨by simp only [BSmtLibSpec.Lexer.FailsCorrectly, ↓reduceIte, hft, true_iff]; exact hnt, ?_⟩
  have hc : ¬ BSmtLibSpec.Lexer.Complete version slices.flatten true := fun h => hnt h.2
  unfold BSmtLibSpec.Lexer.HandsOverCorrectly
  rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
  unfold BSmtLibSpec.Lexer.HandsOverMaximal at hu ⊢
  rw [hh]
  exact hu

/-- Lexer results that are recorded alike are equal. -/
theorem fed_eq_of {a b : BSmtLibSpec.Lexer.Fed}
    (h : some (a.handed, a.failed) = some (b.handed, b.failed)) : a = b := by
  obtain ⟨ah, af⟩ := a
  obtain ⟨bh, bf⟩ := b
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [h.1, h.2]

/-- The naive lexer fed slices and then the end of the input fails exactly when the input has
no tokenisation, hands over its tokens and the end-of-file token when it has one, and otherwise
what it had handed over before the end of the input. -/
theorem correct_ended (version : BSmtLibSpec.Lexicon.Version)
    (slices : List BSmtLibSpec.Regex.Chars)
    (start : Chars) :
    BSmtLibSpec.Lexer.FailsCorrectly fedRun version slices true ∧
      BSmtLibSpec.Lexer.HandsOverCorrectly fedRun version slices true start := by
  have hu := correct_unended version slices start
  have hf := fedOf_fedRun version slices true
  have hf' := fedOf_fedRun version slices false
  cases e : lexBytes (toVersion version) .idle Span.Location.initial slices.flatten with
  | error ls =>
    -- the run has failed before the end: the end changes nothing
    rw [e] at hf hf'
    simp only [fedOf] at hf hf'
    have heq := fed_eq_of (hf.symm.trans hf')
    have hft : (fedRun version slices false).failed = true := by
      cases hls : handedAll (toVersion version) ls with
      | none => rw [hls] at hf'; cases hf'
      | some hs =>
        rw [hls] at hf'
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf'
        exact hf'.2.symm
    have hnv : ¬ Viable version slices.flatten := by
      have := hu.1
      simp only [BSmtLibSpec.Lexer.FailsCorrectly, Bool.false_eq_true, ↓reduceIte] at this
      exact this.mp hft
    exact correct_ended_of_unended (fun ⟨_, ht⟩ => hnv (viable_of_tokenization ht))
      (by rw [heq]; exact hft) (by rw [heq]) hu.2
  | ok r =>
    obtain ⟨st, location, ls⟩ := r
    rw [e] at hf hf'
    have hfb : feedBytes (toVersion version) .idle Span.Location.initial slices.flatten =
        some (st, location, ls) := by
      rw [← lexBytes_toOption, e]; rfl
    simp only [fedOf, ↓reduceIte, Bool.false_eq_true] at hf hf'
    cases hend : endStep st location with
    | none =>
      -- the end of the input fails: the input has no tokenisation
      rw [hend] at hf
      dsimp only at hf
      have hnt : ¬ ∃ tokens, Tokenization version slices.flatten tokens := by
        rintro ⟨tokens, ht⟩
        have := run_complete ht
        rw [run, runFrom, hfb, Option.bind_some] at this
        dsimp only at this
        rw [hend] at this
        cases this
      cases hls : handedAll (toVersion version) ls with
      | none => rw [hls] at hf; cases hf
      | some hs =>
        rw [hls] at hf hf'
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf hf'
        exact correct_ended_of_unended hnt hf.2.symm (by rw [← hf.1, ← hf'.1]) hu.2
    | some ls' =>
      -- the end of the input finishes the run: the input has a tokenisation
      rw [hend] at hf
      dsimp only at hf
      have hrun : run (toVersion version) slices.flatten = some (ls ++ ls') := by
        rw [run, runFrom, hfb, Option.bind_some]
        dsimp only
        rw [hend]
        rfl
      obtain ⟨tokens, ht, hm⟩ := run_sound hrun
      simp only [Matches] at hm
      rw [hm, handedAll_tokens ht] at hf
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      have hc : BSmtLibSpec.Lexer.Complete version slices.flatten true := ⟨rfl, tokens, ht⟩
      refine ⟨?_, ?_⟩
      · unfold BSmtLibSpec.Lexer.FailsCorrectly
        rw [← hf.2]
        simp only [↓reduceIte, Bool.false_eq_true, false_iff]
        exact fun h => h ⟨tokens, ht⟩
      · unfold BSmtLibSpec.Lexer.HandsOverCorrectly
        rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
        exact ⟨tokens, ht, hf.1.symm⟩

/-- The pure run of the naive lexer, over the slices and then, if the input has ended, the end
of the input, is correct. -/
theorem fedRun_correct : BSmtLibSpec.Lexer.Correct fedRun := by
  intro version slices ended start
  cases ended with
  | false =>
    have hu := correct_unended version slices start
    refine ⟨hu.1, ?_⟩
    unfold BSmtLibSpec.Lexer.HandsOverCorrectly
    rw [ite_eq_right_of_eq_false _ _ (eq_false (not_complete_false version slices.flatten))]
    exact hu.2
  | true => exact correct_ended version slices start

end BSmtLib.Facts.Proofs.Lexer.VNaive.Streaming
