import BSmtLib.Proofs.VNaive.Complete
import BSmtLib.Proofs.VNaive.Reserved

/-!
# The pure run over a start of the input

Facts about the naive lexer's pure run over the bytes fed so far, for `VNaive.Streaming`:

- the consumer takes every lexeme the run and the end of the input finish, as the run never
  starts whitespace (`St.Taken`, `lexBytes_taken`, `endStep_taken`), and a byte that fails
  finishes no lexeme before it (`failedBefore_nil`);
- where the lexemes end: a parenthesis just after its byte, any other lexeme at the byte that
  delimits it or at the end of the input (`feedBytes_ends`, `runFrom_ends`);
- every state of the run can be completed to a whole input that the run finishes
  (`runFrom_completes`).
-/

namespace BSmtLib.Proofs.Lexer.VNaive

open BSmtLib.Proofs.Adapter

/-! ## Lexemes the consumer takes -/

/-- The token in progress is not whitespace, which the consumer does not take. -/
def St.Taken : St → Prop
  | .idle => True
  | .token p => p.mode ≠ .whitespace

/-- The consumer takes the lexeme: it is not whitespace or a comment. -/
def Lexeme.Taken (l : Lexeme) : Prop :=
  (toTokenType l.category).isSome = true

/-- The lexeme is a parenthesis. -/
def Lexeme.IsParen (l : Lexeme) : Prop :=
  l.category = .parenOpen ∨ l.category = .parenClose

theorem radix_taken (r : Radix) : (toTokenType r.category).isSome = true := by
  cases r <;> rfl

theorem radix_ne_open (r : Radix) : r.category ≠ .parenOpen := by
  cases r <;> nofun

theorem radix_ne_close (r : Radix) : r.category ≠ .parenClose := by
  cases r <;> nofun

/-- A byte with no token in progress starts no whitespace. -/
theorem start_taken {version : Version} {location : Location} {c : UInt8} {p : Pending}
    (h : start version false location c = .pending p) : p.mode ≠ .whitespace := by
  simp only [start] at h
  repeat' split at h
  all_goals (cases h <;> simp_all)

/-- A byte with no token in progress is a token by itself only as a parenthesis. -/
theorem start_paren {version : Version} {location : Location} {c : UInt8} {l : Lexeme}
    (h : start version false location c = .token l) : l.Taken ∧ l.IsParen := by
  simp only [start] at h
  repeat' split at h
  all_goals (cases h <;> first | exact ⟨rfl, Or.inl rfl⟩ | exact ⟨rfl, Or.inr rfl⟩)

/-- A delimiter starts no error. -/
theorem start_delimiter {version : Version} {location : Location} {c : UInt8}
    (hc : isDelimiter c = true) (f : LexFailure) : start version false location c ≠ .error f := by
  intro h
  simp only [start] at h
  repeat' split at h
  all_goals (cases h <;> simp_all [isDelimiter, isWhitespace])

/-- A token goes on without becoming whitespace. -/
theorem advance_taken {p p' : Pending} {location : Location} {c : UInt8}
    (h : advance false p location c = .pending p') (hp : p.mode ≠ .whitespace) :
    p'.mode ≠ .whitespace := by
  simp only [advance, legacyStringByte] at h
  repeat' split at h
  all_goals (cases h <;> simp_all)

/-- With a consumer that does not take comments, no token ends with a byte. -/
theorem advance_not_tokenWith {p : Pending} {location : Location} {c : UInt8} {l : Lexeme}
    (h : advance false p location c = .tokenWith l) : False := by
  simp only [advance, legacyStringByte] at h
  repeat' split at h
  all_goals (cases h <;> simp_all)

/-- A token that ends before a byte is not a parenthesis. -/
theorem advance_tokenBefore_paren {p : Pending} {location : Location} {c : UInt8} {l : Lexeme}
    (h : advance false p location c = .tokenBefore l) : ¬ l.IsParen := by
  simp only [advance, legacyStringByte] at h
  repeat' split at h
  all_goals (cases h <;> simp [Lexeme.IsParen, radix_ne_open, radix_ne_close])

/-- A token that is not whitespace ends before a byte only if the byte delimits it, and the
consumer takes it. -/
theorem advance_tokenBefore_taken {p : Pending} {location : Location} {c : UInt8} {l : Lexeme}
    (h : advance false p location c = .tokenBefore l) (hp : p.mode ≠ .whitespace) :
    isDelimiter c = true ∧ l.Taken := by
  simp only [advance, legacyStringByte] at h
  repeat' split at h
  all_goals (cases h <;> first
    | exact ⟨by assumption, radix_taken _⟩
    | exact ⟨by assumption, rfl⟩
    | simp_all)

/-- A token that the end of the input ends is not a parenthesis. -/
theorem finish_paren {p : Pending} {location : Location} {l : Lexeme}
    (h : finish false p location = .token l) : ¬ l.IsParen := by
  simp only [finish] at h
  repeat' split at h
  all_goals (cases h <;> simp [Lexeme.IsParen, radix_ne_open, radix_ne_close])

/-- A byte keeps the state taken, and the consumer takes the lexemes it finishes. -/
theorem byteStep_taken {version : Version} {st st' : St} {location : Location} {c : UInt8}
    {ls : List Lexeme} (h : byteStep version st location c = some (st', ls)) (hst : st.Taken) :
    st'.Taken ∧ ∀ l ∈ ls, l.Taken := by
  have hstart : ∀ {st' ls}, startStep version location c = some (st', ls) →
      st'.Taken ∧ ∀ l ∈ ls, l.Taken := by
    intro st' ls h
    simp only [startStep] at h
    split at h
    · cases h; exact ⟨trivial, by simp⟩
    · cases h; exact ⟨start_taken ‹_›, by simp⟩
    · cases h
      exact ⟨trivial, by simpa using (start_paren ‹_›).1⟩
    · cases h
  cases st with
  | idle => exact hstart h
  | token p =>
    simp only [byteStep] at h
    split at h
    · cases h; exact ⟨advance_taken ‹_› hst, by simp⟩
    · cases h; exact ⟨trivial, by simp⟩
    · exact (advance_not_tokenWith ‹_›).elim
    · obtain ⟨⟨st'', ls'⟩, hs, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      obtain ⟨h1, h2⟩ := hstart hs
      refine ⟨h1, fun l hl => ?_⟩
      rcases List.mem_cons.mp hl with rfl | hl
      · exact (advance_tokenBefore_taken ‹_› hst).2
      · exact h2 l hl
    · cases h

/-- In a taken state, a byte that fails finishes no lexeme before it. -/
theorem failedBefore_nil {version : Version} {st : St} {location : Location} {c : UInt8}
    (h : byteStep version st location c = none) (hst : st.Taken) :
    failedBefore st location c = [] := by
  cases st with
  | idle => rfl
  | token p =>
    simp only [failedBefore]
    split
    · rename_i l hadv
      have hd := (advance_tokenBefore_taken hadv hst).1
      simp only [byteStep, hadv, startStep] at h
      cases hs : start version false location c with
      | error f => exact absurd hs (start_delimiter hd f)
      | _ => simp [hs] at h
    · rfl

/-- From a taken state, the run keeps the state taken, and the consumer takes the lexemes it
finishes, also up to an error. -/
theorem lexBytes_taken {version : Version} (bytes : List UInt8) :
    ∀ {st : St} {location : Location}, st.Taken →
      match lexBytes version st location bytes with
      | .ok (st', _, ls) => st'.Taken ∧ ∀ l ∈ ls, l.Taken
      | .error ls => ∀ l ∈ ls, l.Taken := by
  induction bytes with
  | nil => intro st location hst; exact ⟨hst, by simp⟩
  | cons c bytes ih =>
    intro st location hst
    simp only [lexBytes]
    cases hb : byteStep version st location c with
    | none => simp [failedBefore_nil hb hst]
    | some r =>
      obtain ⟨st', ls⟩ := r
      obtain ⟨h1, h2⟩ := byteStep_taken hb hst
      have := ih (location := location.afterByte c) h1
      simp only
      cases e : lexBytes version st' (location.afterByte c) bytes with
      | ok r' =>
        obtain ⟨st'', location'', ls'⟩ := r'
        rw [e] at this
        refine ⟨this.1, fun l hl => ?_⟩
        rcases List.mem_append.mp hl with hl | hl
        · exact h2 l hl
        · exact this.2 l hl
      | error ls' =>
        rw [e] at this
        intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact h2 l hl
        · exact this l hl

/-- The consumer records the lexemes it takes. -/
theorem handedAll_taken (version : Version) (ls : List Lexeme) (h : ∀ l ∈ ls, l.Taken) :
    ∃ hs, handedAll version ls = some hs := by
  induction ls with
  | nil => exact ⟨[], rfl⟩
  | cons l ls ih =>
    obtain ⟨hs, hhs⟩ := ih fun l' hl' => h l' (by simp [hl'])
    have hl := h l (by simp)
    unfold Lexeme.Taken at hl
    cases ht : toTokenType l.category with
    | none => rw [ht] at hl; cases hl
    | some type =>
      obtain ⟨x, hx⟩ : ∃ x, lexemeHanded version l = some x := by
        simp only [lexemeHanded, ht, Option.map_some]
        exact ⟨_, rfl⟩
      exact ⟨_, by rw [handedAll_cons_some hx, hhs]; rfl⟩

/-- The end of the input from a state whose token in progress the consumer takes finishes
lexemes that the consumer takes. -/
theorem endStep_taken {st : St} {location : Location} {ls : List Lexeme}
    (h : endStep st location = some ls) (hst : st.Taken) : ∀ l ∈ ls, l.Taken := by
  have heof : (eofLexeme location).Taken := rfl
  cases st with
  | idle =>
    simp only [endStep, Option.some.injEq] at h
    subst h
    simpa using heof
  | token p =>
    simp only [St.Taken] at hst
    simp only [endStep] at h
    cases hf : finish false p location with
    | none =>
      rw [hf] at h
      simp only [Option.some.injEq] at h
      subst h
      simpa using heof
    | token l =>
      rw [hf] at h
      simp only [Option.some.injEq] at h
      subst h
      have hl : l.Taken := by
        unfold finish at hf
        cases hm : p.mode <;> simp only [hm] at hf hst <;> (repeat' split at hf) <;>
          cases hf <;> first | rfl | exact radix_taken _ | contradiction
      intro l' hl'
      rcases List.mem_cons.mp hl' with rfl | hl'
      · exact hl
      · simp only [List.mem_singleton] at hl'
        subst hl'
        exact heof
    | error _ =>
      rw [hf] at h
      cases h

/-- The pure run fed bytes from the start, also up to an error, and then, if the input has
ended, the end of the input, as the consumer records it. -/
theorem fedOf_isSome (version : Version) (ended : Bool) (bytes : List UInt8) :
    ∃ r, fedOf version ended (lexBytes version .idle Location.initial bytes) = some r := by
  have h := lexBytes_taken (version := version) (location := Location.initial) bytes
    (st := .idle) trivial
  cases e : lexBytes version .idle Location.initial bytes with
  | ok r =>
    obtain ⟨st, location, ls⟩ := r
    rw [e] at h
    obtain ⟨hs, hhs⟩ := handedAll_taken version ls h.2
    cases ended with
    | false => exact ⟨(hs, false), by simp [fedOf, hhs]⟩
    | true =>
      cases hend : endStep st location with
      | none => exact ⟨(hs, true), by simp [fedOf, hend, hhs]⟩
      | some ls' =>
        obtain ⟨hs', hhs'⟩ := handedAll_taken version (ls ++ ls') fun l hl => by
          rcases List.mem_append.mp hl with hl | hl
          · exact h.2 l hl
          · exact endStep_taken hend h.1 l hl
        exact ⟨(hs', false), by simp [fedOf, hend, hhs']⟩
  | error ls =>
    rw [e] at h
    obtain ⟨hs, hhs⟩ := handedAll_taken version ls h
    exact ⟨(hs, true), by simp [fedOf, hhs]⟩

/-! ## Where the lexemes end -/

/-- A parenthesis ends just after its byte; any other lexeme a byte finishes ends at it. -/
theorem byteStep_ends {version : Version} {st st' : St} {location : Location} {c : UInt8}
    {ls : List Lexeme} (h : byteStep version st location c = some (st', ls)) :
    ∀ l ∈ ls, (l.IsParen → l.end.offset = location.offset + 1) ∧
      (¬ l.IsParen → l.end.offset = location.offset) := by
  have hstart : ∀ {st' ls}, startStep version location c = some (st', ls) →
      ∀ l ∈ ls, (l.IsParen → l.end.offset = location.offset + 1) ∧
        (¬ l.IsParen → l.end.offset = location.offset) := by
    intro st' ls h l hl
    simp only [startStep] at h
    split at h
    · cases h; simp at hl
    · cases h; simp at hl
    · rename_i l' hs
      cases h
      simp only [List.mem_singleton] at hl
      subst hl
      refine ⟨fun _ => ?_, fun hn => absurd (start_paren hs).2 hn⟩
      rw [(start_token_span hs).2, afterByte_offset]
    · cases h
  cases st with
  | idle => exact hstart h
  | token p =>
    simp only [byteStep] at h
    split at h
    · cases h; simp
    · cases h; simp
    · exact (advance_not_tokenWith ‹_›).elim
    · rename_i l' hadv
      obtain ⟨⟨st'', ls'⟩, hs, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact ⟨fun hp => absurd hp (advance_tokenBefore_paren hadv),
          fun _ => by rw [(advance_tokenBefore hadv).2]⟩
      · exact hstart hs l hl
    · cases h

/-- The end of the input finishes no parenthesis, and its lexemes end at it. -/
theorem endStep_ends {st : St} {location : Location} {ls : List Lexeme}
    (h : endStep st location = some ls) :
    ∀ l ∈ ls, ¬ l.IsParen ∧ l.end.offset = location.offset := by
  have heof : ¬ (eofLexeme location).IsParen ∧ (eofLexeme location).end.offset =
      location.offset := ⟨by simp [Lexeme.IsParen, eofLexeme], rfl⟩
  cases st with
  | idle =>
    simp only [endStep, Option.some.injEq] at h
    subst h
    simpa using heof
  | token p =>
    simp only [endStep] at h
    split at h
    · cases h; simpa using heof
    · rename_i l hf
      cases h
      intro l' hl'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
      rcases hl' with rfl | rfl
      · exact ⟨finish_paren hf, by rw [(finish_token hf).2]⟩
      · exact heof
    · cases h

/-- Each byte moves the location on by one. -/
theorem advanceLoc_offset (location : Location) (bytes : List UInt8) :
    (advanceLoc location bytes).offset = location.offset + bytes.length := by
  induction bytes generalizing location with
  | nil => rfl
  | cons c bytes ih =>
    show (advanceLoc (location.afterByte c) bytes).offset = _
    rw [ih, afterByte_offset, List.length_cons]
    omega

/-- The lexemes that the run finishes over bytes end before the location after them, except a
parenthesis, which may end at it. -/
theorem feedBytes_ends {version : Version} (bytes : List UInt8) :
    ∀ {st st' : St} {location location' : Location} {ls : List Lexeme},
      feedBytes version st location bytes = some (st', location', ls) →
      ∀ l ∈ ls, l.end.offset ≤ location'.offset ∧
        (¬ l.IsParen → l.end.offset < location'.offset) := by
  induction bytes with
  | nil =>
    intro st st' location location' ls h
    simp only [feedBytes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    simp
  | cons c bytes ih =>
    intro st st' location location' ls h
    simp only [feedBytes] at h
    split at h
    · cases h
    · rename_i st₁ ls₁ hb
      obtain ⟨⟨st₂, location₂, ls₂⟩, hf, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      have hle : location.offset + 1 ≤ location₂.offset := by
        rw [feedBytes_location hf, advanceLoc_offset, afterByte_offset]
        omega
      dsimp only
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · have := byteStep_ends hb l hl
        by_cases hp : l.IsParen
        · exact ⟨by rw [this.1 hp]; exact hle, fun hn => absurd hp hn⟩
        · rw [this.2 hp]; exact ⟨by omega, fun _ => by omega⟩
      · exact ih hf l hl

/-- The lexemes that the run finishes from `location` on, up to the end of the input, end at or
after it, and a parenthesis after it. -/
theorem runFrom_ends {version : Version} (bytes : List UInt8) :
    ∀ {st : St} {location : Location} {ls : List Lexeme},
      runFrom version st location bytes = some ls →
      ∀ l ∈ ls, location.offset ≤ l.end.offset ∧ (l.IsParen → location.offset < l.end.offset) := by
  induction bytes with
  | nil =>
    intro st location ls h l hl
    rw [runFrom_nil] at h
    have := endStep_ends h l hl
    exact ⟨by omega, fun hp => absurd hp this.1⟩
  | cons c bytes ih =>
    intro st location ls h l hl
    rw [runFrom_cons] at h
    obtain ⟨⟨st', ls₁⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ls₂, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases List.mem_append.mp hl with hl | hl
    · have := byteStep_ends hb l hl
      by_cases hp : l.IsParen
      · rw [this.1 hp]; exact ⟨by omega, fun _ => by omega⟩
      · rw [this.2 hp]; exact ⟨by omega, fun hp' => absurd hp' hp⟩
    · have := ih hr l hl
      rw [afterByte_offset] at this
      exact ⟨by omega, fun hp => by have := this.2 hp; omega⟩

/-- The run up to the end of the input finishes at least the end-of-file lexeme. -/
theorem runFrom_ne_nil {version : Version} {st : St} {location : Location} {bytes : List UInt8}
    {ls : List Lexeme} (h : runFrom version st location bytes = some ls) : ls ≠ [] := by
  simp only [runFrom] at h
  obtain ⟨⟨st', location', ls₁⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ls₂, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have : ls₂ ≠ [] := by
    cases st' with
    | idle => simp only [endStep, Option.some.injEq] at he; subst he; simp
    | token p =>
      simp only [endStep] at he
      split at he <;> (try cases he) <;> simp
  simp [this]

/-! ## Completing the input -/

theorem push_not_isEmpty (a : ByteArray) (c : UInt8) : (a.push c).isEmpty = false := by
  cases h : (a.push c).isEmpty
  · rfl
  · rw [isEmpty_iff, toList_push] at h
    simp at h

/-- From every state, some bytes complete the input to one that the run finishes. -/
theorem runFrom_completes (version : Version) (st : St) (location : Location) :
    ∃ rest ls, runFrom version st location rest = some ls := by
  cases st with
  | idle => exact ⟨[], _, rfl⟩
  | token p =>
    obtain ⟨mode, start, content⟩ := p
    cases mode with
    | numeral zero => exact ⟨[], _, rfl⟩
    | fraction digits =>
      refine ⟨[48], ?_⟩
      simp [runFrom, feedBytes, byteStep, advance, endStep, finish, isDigit]
    | hash =>
      refine ⟨[120, 48], ?_⟩
      simp [runFrom, feedBytes, byteStep, advance, endStep, finish, Radix.allows, isHexDigit,
        isDigit, push_not_isEmpty]
    | digits radix =>
      refine ⟨[48], ?_⟩
      cases radix <;>
        simp [runFrom, feedBytes, byteStep, advance, endStep, finish, Radix.allows, isHexDigit,
          isBinaryDigit, isDigit, push_not_isEmpty]
    | keyword =>
      refine ⟨[97], ?_⟩
      simp [runFrom, feedBytes, byteStep, advance, endStep, finish, isSymbolByte, isLetter,
        push_not_isEmpty]
    | simpleSymbol => exact ⟨[], _, rfl⟩
    | quotedSymbol =>
      refine ⟨[124], ?_⟩
      simp [runFrom, feedBytes, byteStep, advance, endStep, finish]
    | quotedSymbolClosed => exact ⟨[], _, rfl⟩
    | string =>
      refine ⟨[34], ?_⟩
      simp [runFrom, feedBytes, byteStep, advance, endStep, finish]
    | stringQuote => exact ⟨[], _, rfl⟩
    | legacyString =>
      refine ⟨[34], ?_⟩
      simp [runFrom, feedBytes, byteStep, advance, legacyStringByte, endStep, finish]
    | legacyEscape =>
      refine ⟨[34, 34], ?_⟩
      simp [runFrom, feedBytes, byteStep, advance, legacyStringByte, endStep, finish]
    | legacyQuote => exact ⟨[], _, rfl⟩
    | comment => exact ⟨[], _, rfl⟩
    | whitespace => exact ⟨[], _, rfl⟩

end BSmtLib.Proofs.Lexer.VNaive
