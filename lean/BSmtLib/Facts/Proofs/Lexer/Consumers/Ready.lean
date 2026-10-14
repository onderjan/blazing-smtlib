module

public import BSmtLib.Facts.Proofs.Lexer.Consumers.VHold
import all BSmtLib.Token

@[expose] public section

/-!
# The entries ready from a boundary

What the spec says is ready for a consumer from a boundary of the input
(`BSmtLibSpec.Lexer.readyFrom`): the tokens of the pure run from the boundary on, read on its own,
and for a consumer that takes whitespace and comments also the layout the spec gives around them, is
what the run from the boundary with whitespace and comments hands over as the consumer is handed
it (`ready_stream`). After a lexeme other than the end of file, the run goes on as the run from
the boundary at its end (`stream_restart`); the end of file is the run's last lexeme, at the end
of the input (`stream_eof_head`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.Ready

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Boundary BSmtLib.Facts.Proofs.Lexer.Consumers.Pure
open BSmtLib.Facts.Proofs.Lexer.Consumers.Stream BSmtLib.Facts.Proofs.Lexer.Consumers.VHold
open BSmtLib.Facts.Proofs.Lexer.VNaive.Facts BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix
open BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix.Lexeme BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Facts.Proofs.Lexer.VNaive.Streaming BSmtLib.Lexer.Internal.VNaive

/-- Whether no lexeme of the list is the end of file. -/
def NoEof (ls : List Lexeme) : Prop := ∀ l ∈ ls, (l.category == .endOfFile) = false

theorem byteStepW_noEof {version : Token.Version} {ws : Bool} {st st' : St}
    {location : Span.Location}
    {c : UInt8} {ls : List Lexeme} (h : byteStepW version ws st location c = some (st', ls)) :
    NoEof ls := by
  have hstart : ∀ {st' ls}, startStepW version ws location c = some (st', ls) → NoEof ls := by
    intro st' ls h
    simp only [startStepW] at h
    split at h <;> cases h
    · simp [NoEof]
    · simp [NoEof]
    · rename_i l hs
      simpa [NoEof] using start_token_ne_eof hs
  cases st with
  | idle => exact hstart h
  | token p =>
    simp only [byteStepW] at h
    split at h
    · cases h; simp [NoEof]
    · cases h; simp [NoEof]
    · cases h; simpa [NoEof] using advance_lexeme_ne_eof (.inl ‹_›)
    · obtain ⟨⟨st'', ls''⟩, hs, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact advance_lexeme_ne_eof (.inr ‹_›)
      · exact hstart hs l hl
    · cases h

theorem failedBeforeW_noEof (ws : Bool) (st : St) (location : Span.Location) (c : UInt8) :
    NoEof (failedBeforeW ws st location c) := by
  cases st with
  | idle => simp [failedBeforeW, NoEof]
  | token p =>
    simp only [failedBeforeW]
    split
    · simpa [NoEof] using advance_lexeme_ne_eof (.inr ‹_›)
    · simp [NoEof]

/-- The lexemes of the outcome of a run. -/
def lexemesOf : Except (List Lexeme) (St × Span.Location × List Lexeme) → List Lexeme
  | .ok (_, _, ls) => ls
  | .error ls => ls

theorem lexemesOf_withBefore (ls : List Lexeme)
    (r : Except (List Lexeme) (St × Span.Location × List Lexeme)) :
    lexemesOf (withBefore ls r) = ls ++ lexemesOf r := by
  cases r with
  | ok x => obtain ⟨_, _, _⟩ := x; rfl
  | error _ => rfl

theorem lexBytesW_noEof (version : Token.Version) (ws : Bool) (bytes : List UInt8) :
    ∀ (st : St) (location : Span.Location),
      NoEof (lexemesOf (lexBytesW version ws st location bytes)) := by
  induction bytes with
  | nil => intro st location; simp [lexBytesW, lexemesOf, NoEof]
  | cons c bytes ih =>
    intro st location
    simp only [lexBytesW]
    cases hb : byteStepW version ws st location c with
    | none => exact failedBeforeW_noEof ws st location c
    | some r =>
      obtain ⟨st', ls⟩ := r
      dsimp only
      rw [lexemesOf_withBefore]
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact byteStepW_noEof hb l hl
      · exact ih st' (location.afterByte c) l hl

theorem lexemeHanded_some {version : Token.Version} {l : Lexeme} {hd : Handed}
    (h : lexemeHanded version l = some hd) :
    hd.start = toLocation l.start ∧ hd.end = toLocation l.end ∧
      (hd.type = .endOfFile ↔ (l.category == .endOfFile) = true) := by
  unfold lexemeHanded at h
  cases ht : toTokenType l.category with
  | none => simp [ht] at h
  | some t =>
    simp only [ht, Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨rfl, rfl, ?_⟩
    cases hc : l.category <;> simp only [hc, toTokenType, Option.some.injEq] at ht <;>
      (try cases ht) <;> (try subst ht) <;>
      (dsimp only; decide)

theorem lexemeHanded_of_taken {version : Token.Version} {l : Lexeme} (h : (Taken l)) :
    ∃ hd, lexemeHanded version l = some hd := by
  unfold Lexeme.Taken at h
  unfold lexemeHanded
  cases ht : toTokenType l.category with
  | none => rw [ht] at h; cases h
  | some t => exact ⟨_, rfl⟩

theorem lexemeHanded_none_of_not_taken {version : Token.Version} {l : Lexeme} (h : ¬ (Taken l)) :
    lexemeHanded version l = none := by
  unfold Lexeme.Taken at h
  unfold lexemeHanded
  cases ht : toTokenType l.category with
  | none => rfl
  | some t => rw [ht] at h; exact absurd rfl h

/-- The entries of the lexemes, as the consumer is handed them. -/
def entriesOf (concrete : Bool) (version : Token.Version) (ls : List Lexeme) : List Handed :=
  ls.filterMap (lexemeEntry concrete version)

theorem entriesOf_false (version : Token.Version) (ls : List Lexeme) :
    entriesOf false version ls = handedOf version ls := by
  unfold entriesOf handedOf
  congr 1
  funext l
  unfold lexemeEntry
  cases lexemeHanded version l <;> rfl

theorem lexemeEntry_of_handed {concrete : Bool} {version : Token.Version} {l : Lexeme} {hd : Handed}
    (h : lexemeHanded version l = some hd) : lexemeEntry concrete version l = some hd := by
  simp [lexemeEntry, h]

theorem lexemeEntry_of_not_taken {version : Token.Version} {l : Lexeme} (h : ¬ (Taken l)) :
    lexemeEntry true version l = some (lexemeLayout l) := by
  simp [lexemeEntry, lexemeHanded_none_of_not_taken h]

/-- After a lexeme other than the end of file, the run from a boundary goes on as the run from
the boundary at the end of the lexeme, which is after the boundary. -/
theorem stream_restart {version : Token.Version} {ws : Bool} {input : List UInt8} {ended : Bool}
    {o : Nat} {l : Lexeme} {rest : List Lexeme}
    (h : (stream version ws input ended o).1 = l :: rest) (hl : l.category ≠ .endOfFile)
    (ho : o ≤ input.length) :
    o < (toLocation l.end).offset ∧ (toLocation l.end).offset ≤ input.length ∧
      stream version ws input ended (toLocation l.end).offset =
        (rest, (stream version ws input ended o).2) := by
  obtain ⟨k, hk, he, hs⟩ := streamFrom_restart (pre := []) h hl
  have hk' : k ≤ input.length - o := by simpa using hk
  have hoff : (toLocation l.end).offset = o + k := by
    rw [he, ← locAfter_take_add (piece := (input.drop o).take k) (more := (input.drop o).drop k)
      (by rw [List.take_append_drop])]
    rw [toLocation_take (by simp; omega)]
    simp [BSmtLibSpec.Lexer.locate]
    omega
  have hst :
      stream version ws input ended (o + k) = (rest, (stream version ws input ended o).2) := by
    unfold stream
    have hl1 : (input.drop o).take k ++ (input.drop o).drop k = input.drop o :=
      List.take_append_drop _ _
    rw [← List.drop_drop, ← hs, he]
    congr 1
    rw [← locAfter_take_add (piece := (input.drop o).take k) (more := (input.drop o).drop k)
      hl1.symm]
    congr 2
    simp
    omega
  rw [hoff]
  refine ⟨?_, by omega, hst⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · exfalso
    subst hk0
    have h2 := congrArg Prod.fst hst
    simp only [Nat.add_zero] at h2
    rw [h] at h2
    exact List.cons_ne_self l rest h2
  · omega

/-- The end of file is the last lexeme of the run from a boundary, at the end of the input. -/
theorem stream_eof_head {version : Token.Version} {ws : Bool} {input : List UInt8} {ended : Bool}
    {o : Nat} {l : Lexeme} {rest : List Lexeme}
    (h : (stream version ws input ended o).1 = l :: rest)
    (hl : (l.category == .endOfFile) = true) :
    rest = [] ∧ (toLocation l.end).offset = input.length := by
  unfold stream streamFrom at h
  have hno := lexBytesW_noEof version ws (input.drop o) .idle (locAfter (input.take o))
  revert h hno
  cases hr : lexBytesW version ws .idle (locAfter (input.take o)) (input.drop o) with
  | error ls =>
    intro h hno
    simp only [lexemesOf] at hno h
    rw [h] at hno
    rw [hno l (by simp)] at hl
    cases hl
  | ok x =>
    obtain ⟨st, loc', ls⟩ := x
    intro h hno
    simp only [lexemesOf] at hno h
    have hloc := lexBytesW_location (input.drop o) hr
    cases ls with
    | cons l' ls =>
      exfalso
      cases ended with
      | false =>
        simp only [Bool.false_eq_true, ite_false, List.cons.injEq] at h
        rw [← h.1, hno l' (by simp)] at hl
        cases hl
      | true =>
        simp only [ite_true] at h
        split at h
        all_goals
          simp only [List.cons_append, List.cons.injEq] at h
          rw [← h.1, hno l' (by simp)] at hl
          cases hl
    | nil =>
      cases ended with
      | false => simp at h
      | true =>
        simp only [ite_true] at h
        split at h
        · rename_i ls' hend
          simp only [List.nil_append] at h
          rcases endStepW_cases hend with h1 | ⟨t, h1, -⟩
          · rw [h1] at h
            simp only [List.cons.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨rfl, ?_⟩
            simp only [eofLexeme, hloc]
            rw [← locAfter_append, List.take_append_drop, toLocation_locAfter]
            simp [BSmtLibSpec.Lexer.locate]
          · exfalso
            rw [h1] at h hend
            simp only [List.cons.injEq] at h
            obtain ⟨rfl, -⟩ := h
            cases st with
            | idle => simp [endStepW] at hend
            | token p =>
              simp only [endStepW] at hend
              split at hend
              · simp at hend
              · rename_i l2 hf
                simp only [Option.some.injEq, List.cons.injEq] at hend
                rw [← hend.1, finish_token_ne_eof hf] at hl
                cases hl
              · simp at hend
        · simp at h

/-- For a consumer that takes whitespace and comments, the entries ready from a boundary are the
lexemes of the run from it. -/
theorem ready_stream_true (version : Token.Version) (input : List UInt8) (ended : Bool) :
    ∀ n o, input.length - o < n → o ≤ input.length →
      (BSmtLibSpec.Lexer.withLayout true input ended o
          (BSmtLibSpec.Lexer.segment fedRun (fromVersion version) input ended o)).handed =
        entriesOf true version (stream version true input ended o).1 := by
  intro n
  induction n with
  | zero => intro o h; omega
  | succ n ih =>
    intro o hn ho
    rw [segment_stream version true input ended o]
    simp only [BSmtLibSpec.Lexer.withLayout, ite_true]
    rcases stream_layout version input ended o with ⟨hlay, hhead⟩ |
      ⟨l, rest, hs, ht, hlt, hlay⟩ | ⟨hlay, hs⟩
    · rw [hlay, List.nil_append]
      generalize hS : stream version true input ended o = S at hhead
      obtain ⟨L, fl⟩ := S
      cases L with
      | nil => rfl
      | cons l rest =>
        have htk := hhead l (by simp)
        obtain ⟨hd, hhd⟩ := lexemeHanded_of_taken (version := version) htk
        obtain ⟨-, hdend, htype⟩ := lexemeHanded_some hhd
        have hh : handedOf version (l :: rest) = hd :: handedOf version rest := by
          simp [handedOf, hhd]
        have he : entriesOf true version (l :: rest) = hd :: entriesOf true version rest := by
          simp [entriesOf, lexemeEntry_of_handed hhd]
        simp only
        rw [hh, he, List.flatMap_cons, List.cons_append]
        congr 1
        cases hcat : l.category == .endOfFile with
        | true =>
          obtain ⟨rfl, hend⟩ := stream_eof_head (by rw [hS]) hcat
          rw [hdend, hend, layoutFrom_nil (by simp)]
          rfl
        | false =>
          obtain ⟨hlt, hle, hst⟩ := stream_restart (by rw [hS])
            (by intro hc; rw [hc] at hcat; cases hcat) ho
          have := ih _ (by omega) hle
          rw [segment_stream version true input ended _, hst] at this
          simp only [BSmtLibSpec.Lexer.withLayout, ite_true] at this
          rw [hdend, ← this]
    · have hne : (l.category == .endOfFile) = false := by
        cases hc : l.category == .endOfFile with
        | false => rfl
        | true =>
          exfalso
          apply ht
          have hc' : l.category = .endOfFile := by
            revert hc; cases l.category <;> intro h <;> first | rfl | cases h
          simp [Lexeme.Taken, hc', toTokenType]
      obtain ⟨hlt', hle, hst⟩ := stream_restart hs (by intro hc; rw [hc] at hne; cases hne) ho
      have := ih _ (by omega) hle
      rw [segment_stream version true input ended _, hst] at this
      simp only [BSmtLibSpec.Lexer.withLayout, ite_true] at this
      have hh : handedOf version (l :: rest) = handedOf version rest := by
        simp [handedOf, lexemeHanded_none_of_not_taken ht]
      have he : entriesOf true version (l :: rest) =
          lexemeLayout l :: entriesOf true version rest := by
        simp [entriesOf, lexemeEntry_of_not_taken ht]
      rw [hs, hh, he, hlay, List.cons_append, ← this]
    · rw [hlay, hs]
      rfl

/-- The entries ready from a boundary are the lexemes of the run from it, as the consumer is
handed them. -/
theorem ready_stream (concrete : Bool) (version : Token.Version) (input : List UInt8) (ended : Bool)
    (o : Nat) (ho : o ≤ input.length) :
    BSmtLibSpec.Lexer.readyFrom fedRun concrete (fromVersion version) input ended o =
      { handed := entriesOf concrete version (stream version concrete input ended o).1
        failed := (stream version concrete input ended o).2 } := by
  cases concrete with
  | false =>
    rw [entriesOf_false]
    exact segment_stream version false input ended o
  | true =>
    have h := ready_stream_true version input ended _ o (Nat.lt_succ_self _) ho
    unfold BSmtLibSpec.Lexer.readyFrom
    rw [← h]
    simp only [BSmtLibSpec.Lexer.withLayout, ite_true]
    rw [segment_stream version true input ended o]


/-- For a consumer that does not take whitespace and comments, the entries ready from an offset
are the tokens of the input from there, read on its own. -/
theorem readyFrom_plain (feed : BSmtLibSpec.Lexicon.Version → List BSmtLibSpec.Regex.Chars → Bool →
      BSmtLibSpec.Lexer.Fed) (version : BSmtLibSpec.Lexicon.Version) (input : List UInt8)
          (ended : Bool)
    (o : Nat) :
    BSmtLibSpec.Lexer.readyFrom feed false version input ended o =
      BSmtLibSpec.Lexer.segment feed version input ended o := by
  simp [BSmtLibSpec.Lexer.readyFrom, BSmtLibSpec.Lexer.withLayout]
end BSmtLib.Facts.Proofs.Lexer.Consumers.Ready
