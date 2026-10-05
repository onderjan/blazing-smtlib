import BSmtLib.Proofs.V1Naive.Modes

/-!
# What the naive lexer finishes is a tokenisation

`run_sound`: when the pure run of the naive lexer finishes an input, the lexemes it gives are
the tokens of a tokenisation of the input, followed by the end-of-file lexeme.
-/

namespace BSmtLib.Proofs.Lexer.V1Naive

open BSmtLib.Spec.Lexicon BSmtLib.Spec.Lexicon.Regex BSmtLib.SpecChecks.Lexicon

/-! ## The lexemes of tokens -/

/-- The lexeme of the token of the input. -/
def lexemeOf (version : Spec.Lexicon.Version) (input : Chars) (token : Spec.Lexicon.Token) :
    Lexeme :=
  { category := lexCategory token.category
    content := ⟨(Spec.Lexicon.Token.content version token).toArray⟩
    start := locAfter (input.take token.offset)
    «end» := locAfter (input.take (token.offset + token.text.length)) }

theorem lexemeIs_eq {version : Spec.Lexicon.Version} {category : Category}
    {start «end» : Location} {text : Chars} {l : Lexeme}
    (h : LexemeIs version category start «end» text l) :
    l = { category := lexCategory category,
          content := ⟨(Spec.Lexicon.Token.content version ⟨category, 0, text⟩).toArray⟩,
          start, «end» } := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨cat, ⟨data⟩, s, e⟩ := l
  simp only at h1 h2 h3 h4
  subst h1 h3 h4
  rw [← h2, Array.toArray_toList]

/-- The lexemes `ls` are the lexemes of the tokens of the input and then the end-of-file
lexeme. -/
def Matches (version : Spec.Lexicon.Version) (input : Chars) (tokens : List Spec.Lexicon.Token)
    (ls : List Lexeme) : Prop :=
  ls = tokens.map (lexemeOf version input) ++ [eofLexeme (locAfter input)]

/-- The lexemes `ls` are the tokens of a tokenisation of `input`, which follows `before`. -/
def Sound (version : Spec.Lexicon.Version) (before input : Chars) (ls : List Lexeme) : Prop :=
  ∃ tokens, TokenizationFrom version before.length input tokens ∧
    Matches version (before ++ input) tokens ls

/-! ## Tokenisations -/

theorem star_append {r : Regex} {a b : Chars} (ha : star r a) (hb : star r b) :
    star r (a ++ b) := by
  obtain ⟨pa, rfl, hpa⟩ := ha
  obtain ⟨pb, rfl, hpb⟩ := hb
  refine ⟨pa ++ pb, by simp, fun p hp => ?_⟩
  rcases List.mem_append.mp hp with hp | hp
  · exact hpa p hp
  · exact hpb p hp

/-- Whitespace before a tokenisation. -/
theorem tokenizationFrom_ws {version : Spec.Lexicon.Version} {offset : Nat} {w r : Chars}
    {tokens : List Spec.Lexicon.Token} (hw : whitespace w)
    (h : TokenizationFrom version (offset + w.length) r tokens) :
    TokenizationFrom version offset (w ++ r) tokens := by
  cases h with
  | done he =>
    obtain ⟨w', z, rfl, hw', hz⟩ := he
    exact .done ⟨w ++ w', z, by simp, star_append hw hw', hz⟩
  | token hw' hs hd hrest =>
    rename_i w' category s rest tokens'
    have e : offset + w.length + w'.length = offset + (w ++ w').length := by
      simp [Nat.add_assoc]
    rw [e] at hrest ⊢
    have := TokenizationFrom.token (offset := offset) (star_append hw hw') hs hd hrest
    simpa [List.append_assoc] using this

theorem sound_ws {version : Spec.Lexicon.Version} {before w rest : Chars} {ls : List Lexeme}
    (hw : whitespace w) (h : Sound version (before ++ w) rest ls) :
    Sound version before (w ++ rest) ls := by
  obtain ⟨tokens, ht, hm⟩ := h
  exact ⟨tokens, tokenizationFrom_ws hw (by simpa using ht), by simpa using hm⟩

theorem sound_token {version : Spec.Lexicon.Version} {before s rest : Chars}
    {ls : List Lexeme} {l : Lexeme} {category : Category}
    (hs : categoryRegex version category s) (hd : Delimited category rest)
    (hl : LexemeIs version category (locAfter before) (locAfter (before ++ s)) s l)
    (h : Sound version (before ++ s) rest ls) : Sound version before (s ++ rest) (l :: ls) := by
  obtain ⟨tokens, ht, hm⟩ := h
  refine ⟨⟨category, before.length, s⟩ :: tokens, ?_, ?_⟩
  · have := TokenizationFrom.token (offset := before.length) (w := []) whitespace_nil hs hd
      (by simpa using ht)
    simpa using this
  · rw [Matches] at hm ⊢
    rw [hm, lexemeIs_eq hl]
    simp [lexemeOf, List.take_append]
    exact ⟨rfl, by rw [List.take_of_length_le (by simp)]⟩

theorem whitespace_char {c : UInt8} (h : whiteSpaceChar [c]) : whitespace [c] :=
  star_parts [[c]] fun p hp => by rw [List.mem_singleton.mp hp]; exact Or.inl h

theorem whitespace_comment {t : Chars} (h : comment t) : whitespace t := by
  have := star_parts (r := alt whiteSpaceChar comment) [t] fun p hp => by
    rw [List.mem_singleton.mp hp]; exact Or.inr h
  have e : [t].flatten = t := by simp
  rw [e] at this
  exact this


theorem delimited_of_delim {category : Category} {c : UInt8} {r : Chars} (h : Delim c.toNat) :
    Delimited category (c :: r) := by
  refine delimited_by ?_
  simp only [Delim] at h
  rcases h with h | h | h | h | h | h | h
  all_goals first
    | exact Or.inl (whiteSpaceChar_one.mpr (by omega))
    | (refine Or.inr (oneOf_one.mpr ?_)
       have e : chars "();" = [40, 41, 59] := rfl
       rw [e]
       have hc : c = UInt8.ofNat c.toNat := by simp
       rw [hc, h]
       decide)

theorem delimited_end {category : Category} : Delimited category [] :=
  Or.inr (Or.inr (Or.inl rfl))

/-! ## The pure run -/

/-- The state of the pure run, after the input `before` and the characters `text` of the
token in progress. -/
def StInv (version : Spec.Lexicon.Version) : St → Chars → Chars → Prop
  | .idle, _, text => text = []
  | .token p, before, text =>
    p.start = locAfter before ∧ ModeInv version p.mode text p.content.data.toList

theorem runFrom_nil (version : Version) (st : St) (location : Location) :
    runFrom version st location [] = endStep st location := by
  simp only [runFrom, feedBytes, Option.bind_some]
  cases endStep st location <;> rfl

theorem runFrom_cons (version : Version) (st : St) (location : Location) (c : UInt8)
    (r : List UInt8) :
    runFrom version st location (c :: r) =
      (byteStep version st location c).bind fun (st', ls) =>
        (runFrom version st' (location.afterByte c) r).map (ls ++ ·) := by
  simp only [runFrom, feedBytes]
  cases byteStep version st location c with
  | none => rfl
  | some e =>
    obtain ⟨st', ls⟩ := e
    simp only [Option.bind_some]
    cases feedBytes version st' (location.afterByte c) r with
    | none => rfl
    | some e' =>
      obtain ⟨st'', location'', ls'⟩ := e'
      simp only [Option.map_some, Option.bind_some]
      cases endStep st'' location'' <;> simp

theorem eof_sound {version : Spec.Lexicon.Version} (before : Chars) :
    Sound version before [] [eofLexeme (locAfter before)] :=
  ⟨[], .done ⟨[], [], rfl, whitespace_nil, Or.inl rfl⟩, by simp [Matches]⟩

/-- The pure run is sound from a state with no token in progress, once it is sound after the
first byte. -/
theorem idle_sound {version : Spec.Lexicon.Version} {c : UInt8} {r : Chars}
    (ih : ∀ (st : St) (before text : Chars) (ls : List Lexeme), StInv version st before text →
      runFrom (V1Spec.toVersion version) st (locAfter (before ++ text)) r = some ls →
      Sound version before (text ++ r) ls)
    (before : Chars) (ls : List Lexeme)
    (h : runFrom (V1Spec.toVersion version) .idle (locAfter before) (c :: r) = some ls) :
    Sound version before (c :: r) ls := by
  rw [runFrom_cons] at h
  have hs := start_sound version (locAfter before) c
  simp only [byteStep, startStep] at h
  cases hst : start (V1Spec.toVersion version) false (locAfter before) c with
  | idle =>
    rw [hst] at h hs
    simp only [Option.bind_some, List.nil_append, Option.map_id_fun', id_eq] at h
    rw [← locAfter_concat] at h
    have := ih .idle (before ++ [c]) [] ls rfl (by simpa using h)
    exact sound_ws (w := [c]) (whitespace_char hs) (by simpa using this)
  | pending p =>
    rw [hst] at h hs
    simp only [Option.bind_some, List.nil_append, Option.map_id_fun', id_eq] at h
    rw [← locAfter_concat] at h
    exact ih (.token p) before [c] ls hs h
  | token l =>
    rw [hst] at h hs
    simp only [Option.bind_some] at h
    obtain ⟨ls', h', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [← locAfter_concat] at h'
    obtain ⟨category, hparen, hr, hl⟩ := hs
    have := ih .idle (before ++ [c]) [] ls' rfl (by simpa using h')
    refine sound_token (s := [c]) hr ?_ (by rw [locAfter_concat]; exact hl) (by simpa using this)
    rcases hparen with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  | error f =>
    rw [hst] at h
    simp at h

/-- The pure run is sound from any state that keeps `StInv`. -/
theorem runFrom_sound (version : Spec.Lexicon.Version) (r : Chars) :
    ∀ (st : St) (before text : Chars) (ls : List Lexeme), StInv version st before text →
      runFrom (V1Spec.toVersion version) st (locAfter (before ++ text)) r = some ls →
      Sound version before (text ++ r) ls := by
  induction r with
  | nil =>
    intro st before text ls hst h
    rw [runFrom_nil] at h
    cases st with
    | idle =>
      simp only [StInv] at hst
      subst hst
      simp only [endStep, Option.some.injEq] at h
      subst h
      simpa using eof_sound before
    | token p =>
      obtain ⟨hstart, hmode⟩ := hst
      have hf := finish_sound (locAfter (before ++ text)) hmode
      simp only [endStep] at h
      cases hfin : finish false p (locAfter (before ++ text)) with
      | none =>
        rw [hfin] at h hf
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨[], .done ⟨[], text, by simp, whitespace_nil, Or.inr hf⟩, by simp [Matches]⟩
      | token l =>
        rw [hfin] at h hf
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨category, hr, hl⟩ := hf
        rw [hstart] at hl
        simpa using sound_token (rest := []) hr delimited_end hl (eof_sound (before ++ text))
      | error f =>
        rw [hfin] at h
        simp at h
  | cons c r ih =>
    intro st before text ls hst h
    cases st with
    | idle =>
      simp only [StInv] at hst
      subst hst
      exact idle_sound ih before ls (by simpa using h)
    | token p =>
      obtain ⟨hstart, hmode⟩ := hst
      have ha := advance_sound (locAfter (before ++ text)) c hmode
      rw [runFrom_cons] at h
      simp only [byteStep] at h
      cases hadv : advance false p (locAfter (before ++ text)) c with
      | pending p' =>
        rw [hadv] at h ha
        simp only [Option.bind_some, List.nil_append, Option.map_id_fun', id_eq] at h
        rw [← locAfter_concat] at h
        obtain ⟨hs', hm'⟩ := ha
        have := ih (.token p') before (text ++ [c]) ls ⟨hs'.trans hstart, hm'⟩
          (by simpa using h)
        simpa using this
      | idle =>
        rw [hadv] at h ha
        simp only [Option.bind_some, List.nil_append, Option.map_id_fun', id_eq] at h
        rw [← locAfter_concat] at h
        have := ih .idle (before ++ (text ++ [c])) [] ls rfl (by simpa using h)
        have := sound_ws (whitespace_comment ha) (by simpa using this)
        simpa using this
      | tokenWith l =>
        rw [hadv] at ha
        exact ha.elim
      | tokenBefore l =>
        rw [hadv] at h ha
        obtain ⟨hdelim, category, hr, hl⟩ := ha
        have hidle : runFrom (V1Spec.toVersion version) .idle (locAfter (before ++ text))
            (c :: r) = (startStep (V1Spec.toVersion version) (locAfter (before ++ text)) c).bind
              fun (st', ls) => (runFrom (V1Spec.toVersion version) st'
                ((locAfter (before ++ text)).afterByte c) r).map (ls ++ ·) := by
          rw [runFrom_cons]; rfl
        cases hss : startStep (V1Spec.toVersion version) (locAfter (before ++ text)) c with
        | none =>
          rw [hss] at h
          simp at h
        | some e =>
          rw [hss] at h hidle
          obtain ⟨st', ls1⟩ := e
          simp only [Option.map_some, Option.bind_some] at h hidle
          obtain ⟨ls', h', rfl⟩ := Option.map_eq_some_iff.mp h
          have hsound := idle_sound ih (before ++ text) (ls1 ++ ls')
            (by rw [hidle, h']; rfl)
          rw [hstart] at hl
          simpa using sound_token hr (delimited_of_delim hdelim) hl hsound
      | error f =>
        rw [hadv] at h
        simp at h

/-- When the pure run finishes an input, its lexemes are the tokens of a tokenisation of the
input and then the end-of-file lexeme. -/
theorem run_sound {version : Spec.Lexicon.Version} {input : Chars} {ls : List Lexeme}
    (h : run (V1Spec.toVersion version) input = some ls) :
    ∃ tokens, Tokenization version input tokens ∧ Matches version input tokens ls := by
  have := runFrom_sound version input .idle [] [] ls rfl h
  obtain ⟨tokens, ht, hm⟩ := this
  exact ⟨tokens, ht, by simpa using hm⟩

end BSmtLib.Proofs.Lexer.V1Naive
