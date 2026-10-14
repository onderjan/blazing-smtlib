module

public import BSmtLib.Facts.Proofs.Lexer.Consumers.Stream
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Token

@[expose] public section

/-!
# What follows a boundary

The run from a boundary for a consumer that takes whitespace and comments, and the layout the spec
gives there (`BSmtLibSpec.Lexer.layoutFrom`, `stream_layout`): either the spec gives none, and the
first lexeme of the run, if any, is a token; or the first lexeme is whitespace or a comment from the
boundary, which is the first piece the spec gives; or the layout there is not complete yet, and
the run has finished nothing and not failed.
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.Boundary

open BSmtLib.Facts.Lexer.Adapters BSmtLibSpec.Lexicon BSmtLibSpec.Facts.Proofs.Lexicon.Unique
open BSmtLibSpec.Regex (chars)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Layout BSmtLib.Facts.Proofs.Lexer.Consumers.Pure
open BSmtLib.Facts.Proofs.Lexer.Consumers.Stream BSmtLib.Facts.Proofs.Lexer.VNaive.Facts
open BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix.Lexeme
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaive.Streaming
open BSmtLib.Lexer.Internal.VNaive

/-- The whitespace lexeme in progress `p` that ends at `location`. -/
def wsLexeme (p : Pending) (location : Span.Location) : Lexeme :=
  { category := .whitespace, content := p.content, start := p.start, «end» := location }

/-- Whitespace in progress goes on over whitespace, which it takes into its content. -/
theorem lexBytesW_whitespace (version : Token.Version) (bytes : List UInt8)
    (hbytes : ∀ b ∈ bytes, isWhitespace b = true) :
    ∀ {p : Pending} {location : Span.Location}, p.mode = .whitespace →
      ∃ p', p'.mode = .whitespace ∧ p'.start = p.start ∧
        p'.content = bytes.foldl ByteArray.push p.content ∧
        lexBytesW version true (.token p) location bytes =
          .ok (.token p', advanceLoc location bytes, []) := by
  induction bytes with
  | nil => intro p location hp; exact ⟨p, hp, rfl, rfl, rfl⟩
  | cons b bytes ih =>
    intro p location hp
    have hb := hbytes b (by simp)
    obtain ⟨p', h1, h2, hc, h3⟩ := ih (fun x hx => hbytes x (by simp [hx]))
      (p := { p with mode := .whitespace, content := p.content.push b })
      (location := location.afterByte b) rfl
    refine ⟨p', h1, h2, hc, ?_⟩
    simp only [lexBytesW, byteStepW, advance, hp, hb, ite_true]
    rw [h3]
    rfl

/-- Whitespace in progress ends before a byte that is not whitespace, which is lexed again with
nothing in progress. -/
theorem byteStepW_whitespace_end (version : Token.Version) {p : Pending} {location : Span.Location}
    {c : UInt8} (hp : p.mode = .whitespace) (hc : isWhitespace c = false) :
    byteStepW version true (.token p) location c =
        (startStepW version true location c).map (fun (st, ls) => (st, wsLexeme p location :: ls)) ∧
      failedBeforeW true (.token p) location c = [wsLexeme p location] := by
  simp only [byteStepW, failedBeforeW, advance, hp, hc, Bool.false_eq_true, ite_false]
  exact ⟨rfl, rfl⟩

/-- A comment in progress goes on over bytes that are not line breaks, which it takes into its
content. -/
theorem lexBytesW_comment (version : Token.Version) (bytes : List UInt8)
    (hbytes : ∀ b ∈ bytes, ((b == 10) || (b == 13)) = false) :
    ∀ {p : Pending} {location : Span.Location}, p.mode = .comment →
      ∃ p', p'.mode = .comment ∧ p'.start = p.start ∧
        p'.content = bytes.foldl ByteArray.push p.content ∧
        lexBytesW version true (.token p) location bytes =
          .ok (.token p', advanceLoc location bytes, []) := by
  induction bytes with
  | nil => intro p location hp; exact ⟨p, hp, rfl, rfl, rfl⟩
  | cons b bytes ih =>
    intro p location hp
    have hb := hbytes b (by simp)
    obtain ⟨p', h1, h2, hc, h3⟩ := ih (fun x hx => hbytes x (by simp [hx]))
      (p := { p with mode := .comment, content := p.content.push b })
      (location := location.afterByte b) rfl
    refine ⟨p', h1, h2, hc, ?_⟩
    have hb' : (b == byte! '\n' || b == byte! '\r') = false := hb
    simp only [lexBytesW, byteStepW, advance, hp, hb', Bool.false_eq_true, ite_false]
    rw [h3]
    rfl

/-- A line break ends the comment in progress, with the line break. -/
theorem byteStepW_comment_end (version : Token.Version) {p : Pending} {location : Span.Location}
    {c : UInt8} (hp : p.mode = .comment) (hc : ((c == 10) || (c == 13)) = true) :
    byteStepW version true (.token p) location c = some (.idle, [commentLexeme p location c]) := by
  have hc' : (c == byte! '\n' || c == byte! '\r') = true := hc
  simp only [byteStepW, advance, hp, hc', ite_true]
  rfl

/-- A token goes on without becoming a comment. -/
theorem advance_not_comment {p p' : Pending} {location : Span.Location} {c : UInt8}
    (h : advance false p location c = .pending p') (hp : p.mode ≠ .comment) :
    p'.mode ≠ .comment := by
  simp only [advance, legacyStringByte] at h
  repeat' split at h
  all_goals (cases h <;> simp_all)

/-- A token in progress that is neither whitespace nor a comment. -/
def St.NonLayout : St → Prop
  | .idle => False
  | .token q => q.mode ≠ .whitespace ∧ q.mode ≠ .comment

/-- From a token in progress that is neither whitespace nor a comment, the first lexeme the run
finishes, if any, is one that a consumer that does not take whitespace and comments takes. -/
theorem lexBytesW_head_taken (version : Token.Version) (bytes : List UInt8) :
    ∀ {st : St} {location : Span.Location}, (St.NonLayout st) →
      match lexBytesW version true st location bytes with
      | .ok (st', _, ls) => (ls = [] → (St.NonLayout st')) ∧ ∀ l ∈ ls.head?, (Taken l)
      | .error ls => ∀ l ∈ ls.head?, (Taken l) := by
  induction bytes with
  | nil => intro st location h; exact ⟨fun _ => h, by simp⟩
  | cons b bytes ih =>
    intro st location h
    cases st with
    | idle => exact h.elim
    | token q =>
      obtain ⟨hw, hc⟩ := h
      simp only [lexBytesW, byteStepW, failedBeforeW, advance_ws_eq hc]
      cases ha : advance false q location b with
      | pending q' =>
        have := ih (st := .token q') (location := location.afterByte b)
          ⟨advance_taken ha hw, advance_not_comment ha hc⟩
        simp only [withBefore_nil]
        exact this
      | idle =>
        exfalso
        simp only [advance, legacyStringByte] at ha
        cases hm : q.mode <;> simp only [hm] at ha hc <;> (repeat' split at ha) <;> simp_all
      | tokenWith l => exact (advance_not_tokenWith ha).elim
      | tokenBefore l =>
        have hl := (advance_tokenBefore_taken ha hw).2
        cases hs : startStepW version true location b with
        | none => simp [hl]
        | some r =>
          obtain ⟨st1, ls1⟩ := r
          simp only [Option.map_some]
          cases lexBytesW version true st1 (location.afterByte b) bytes with
          | ok r' => obtain ⟨_, _, _⟩ := r'; simp [withBefore, hl]
          | error _ => simp [withBefore, hl]
      | error f => simp

/-- A list either satisfies the test throughout or has a first element that fails it. -/
theorem list_split_first (p : UInt8 → Bool) (l : List UInt8) :
    (∀ x ∈ l, p x = true) ∨ ∃ a d t, l = a ++ d :: t ∧ (∀ x ∈ a, p x = true) ∧ p d = false := by
  induction l with
  | nil => exact .inl (by simp)
  | cons x l ih =>
    cases hx : p x with
    | false => exact .inr ⟨[], x, l, rfl, by simp, hx⟩
    | true =>
      rcases ih with h | ⟨a, d, t, rfl, ha, hd⟩
      · exact .inl (by simp [hx]; exact fun y hy => h y hy)
      · exact .inr ⟨x :: a, d, t, rfl, by simp [hx]; exact fun y hy => ha y hy, hd⟩

theorem chars_semicolon : chars ";" = [59] := rfl

theorem start_not_comment {version : Token.Version} {location : Span.Location} {c : UInt8}
    {p : Pending}
    (h : start version false location c = .pending p) (hc : c ≠ 59) : p.mode ≠ .comment := by
  simp only [start] at h
  repeat' split at h
  all_goals (cases h <;> simp_all)

/-- A run whose lexemes begin with `l`, before the end of the input. -/
def HeadIs (l : Lexeme) : Except (List Lexeme) (St × Span.Location × List Lexeme) → Prop
  | .ok (_, _, ls) => ∃ rest, ls = l :: rest
  | .error ls => ∃ rest, ls = l :: rest

theorem headIs_withBefore {l : Lexeme} {ls : List Lexeme}
    (r : Except (List Lexeme) (St × Span.Location × List Lexeme)) :
    HeadIs l (withBefore (l :: ls) r) := by
  cases r with
  | ok x => obtain ⟨_, _, _⟩ := x; exact ⟨_, rfl⟩
  | error _ => exact ⟨_, rfl⟩

theorem headIs_withBefore_nil {l : Lexeme}
    {r : Except (List Lexeme) (St × Span.Location × List Lexeme)} (h : HeadIs l r) :
    HeadIs l (withBefore [] r) := by
  rw [withBefore_nil]; exact h

theorem streamFrom_head {version : Token.Version} {ws ended : Bool} {location : Span.Location}
    {bytes : List UInt8} {l : Lexeme} (h : HeadIs l (lexBytesW version ws .idle location bytes)) :
    ∃ rest, (streamFrom version ws ended location bytes).1 = l :: rest := by
  unfold streamFrom
  revert h
  cases lexBytesW version ws .idle location bytes with
  | error ls => rintro ⟨rest, rfl⟩; exact ⟨rest, rfl⟩
  | ok x =>
    obtain ⟨st, location', ls⟩ := x
    rintro ⟨rest, rfl⟩
    dsimp only
    cases ended with
    | false => exact ⟨rest, rfl⟩
    | true =>
      simp only [ite_true]
      cases endStepW ws st location' with
      | none => exact ⟨rest, rfl⟩
      | some ls' => exact ⟨rest ++ ls', rfl⟩

/-- The lexeme ends before the byte `d`, which ends the whitespace in progress: the run over
`d` and the bytes after it begins with the whitespace. -/
theorem headIs_whitespace_end (version : Token.Version) {p : Pending} {location : Span.Location}
    {d : UInt8} (t : List UInt8) (hp : p.mode = .whitespace) (hd : isWhitespace d = false) :
    HeadIs (wsLexeme p location) (lexBytesW version true (.token p) location (d :: t)) := by
  obtain ⟨h1, h2⟩ := byteStepW_whitespace_end version (location := location) hp hd
  simp only [lexBytesW, h1, h2]
  cases startStepW version true location d with
  | none => exact ⟨[], rfl⟩
  | some x => obtain ⟨st, ls⟩ := x; exact headIs_withBefore _


/-! ## The layout after a boundary, as the spec gives it -/

/-- The test for a byte that is no line break. -/
def notLineBreak (x : UInt8) : Bool := !((x == 10) || (x == 13))

open Classical in
theorem decide_whiteSpaceChar :
    (fun d : UInt8 => decide (whiteSpaceChar [d])) = isWhitespace := by
  funext d
  cases h : isWhitespace d
  · have : ¬ whiteSpaceChar [d] := fun h' => by rw [← whitespace_iff] at h'; simp_all
    simp [this]
  · simp [(whitespace_iff d).mp h]

theorem lineBreak_bool (x : UInt8) : lineBreak [x] ↔ ((x == 10) || (x == 13)) = true := by
  rw [lineBreak_one, lineBreak_iff]

open Classical in
theorem decide_notLineBreak :
    (fun d : UInt8 => !decide (lineBreak [d])) = notLineBreak := by
  funext d
  unfold notLineBreak
  cases h : ((d == 10) || (d == 13))
  · have : ¬ lineBreak [d] := fun h' => by rw [lineBreak_bool] at h'; simp_all
    simp [this]
  · simp [(lineBreak_bool d).mpr h]

theorem layoutFrom_ws {input : List UInt8} {ended : Bool} {o : Nat} {c : UInt8}
    {rest : List UInt8} (h : input.drop o = c :: rest) (hw : isWhitespace c = true) :
    BSmtLibSpec.Lexer.layoutFrom input ended o =
      if ended = true ∨ o + (c :: rest.takeWhile isWhitespace).length < input.length then
        BSmtLibSpec.Lexer.layoutEntry input .whitespace o (c :: rest.takeWhile isWhitespace).length
            (c :: rest.takeWhile isWhitespace) ::
          BSmtLibSpec.Lexer.layoutFrom input ended (o + (c :: rest.takeWhile isWhitespace).length)
      else [] := by
  rw [BSmtLibSpec.Lexer.layoutFrom]
  split
  · rename_i h'; rw [h] at h'; cases h'
  · rename_i c' rest' h'
    rw [h] at h'
    cases h'
    rw [ite_eq_left ((whitespace_iff c).mp hw), decide_whiteSpaceChar]

theorem layoutFrom_semi {input : List UInt8} {ended : Bool} {o : Nat} {rest : List UInt8}
    (h : input.drop o = 59 :: rest) :
    BSmtLibSpec.Lexer.layoutFrom input ended o =
      match rest.dropWhile notLineBreak with
      | lb :: _ =>
        BSmtLibSpec.Lexer.layoutEntry input .comment o ((rest.takeWhile notLineBreak).length + 2)
            (rest.takeWhile notLineBreak ++ [lb]) ::
          BSmtLibSpec.Lexer.layoutFrom input ended (o + ((rest.takeWhile notLineBreak).length + 2))
      | [] =>
        if ended then
          [BSmtLibSpec.Lexer.layoutEntry input .comment o ((rest.takeWhile notLineBreak).length + 1)
            (rest.takeWhile notLineBreak)]
        else [] := by
  rw [BSmtLibSpec.Lexer.layoutFrom]
  split
  · rename_i h'; rw [h] at h'; cases h'
  · rename_i c' rest' h'
    rw [h] at h'
    cases h'
    have hw : ¬ whiteSpaceChar [(59 : UInt8)] := fun h' => by
      rw [← whitespace_iff] at h'; exact absurd h' (by decide)
    rw [ite_eq_right hw, ite_eq_left (by rw [chars_semicolon]), decide_notLineBreak]
    rfl

theorem layoutFrom_other {input : List UInt8} {ended : Bool} {o : Nat} {c : UInt8}
    {rest : List UInt8} (h : input.drop o = c :: rest) (hw : isWhitespace c = false)
    (hc : c ≠ 59) : BSmtLibSpec.Lexer.layoutFrom input ended o = [] := by
  rw [BSmtLibSpec.Lexer.layoutFrom]
  split
  · rfl
  · rename_i c' rest' h'
    rw [h] at h'
    cases h'
    have hw' : ¬ whiteSpaceChar [c] := fun h' => by rw [← whitespace_iff] at h'; simp_all
    have hc' : ¬ [c] = chars ";" := fun h' => by rw [chars_semicolon] at h'; simp_all
    rw [ite_eq_right hw', ite_eq_right hc']

theorem layoutFrom_nil {input : List UInt8} {ended : Bool} {o : Nat} (h : input.drop o = []) :
    BSmtLibSpec.Lexer.layoutFrom input ended o = [] := by
  rw [BSmtLibSpec.Lexer.layoutFrom]
  split
  · rfl
  · rename_i c' rest' h'; rw [h] at h'; cases h'

theorem toList_foldl_push (bytes : List UInt8) (b : ByteArray) :
    (bytes.foldl ByteArray.push b).toList = b.toList ++ bytes := by
  induction bytes generalizing b with
  | nil => simp
  | cons x bytes ih =>
    rw [List.foldl_cons, ih]
    simp [Simulation.Bytes.byteArray_toList, ByteArray.push]

theorem toList_byteArray_empty : ByteArray.empty.toList = [] := by
  rw [Simulation.Bytes.byteArray_toList]; rfl

theorem toList_empty_push (c : UInt8) : (ByteArray.empty.push c).toList = [c] := by
  simp [Simulation.Bytes.byteArray_toList, ByteArray.push, ByteArray.empty,
      ByteArray.emptyWithCapacity]
  rfl

theorem toContent_toByteSlice (b : ByteArray) : toContent b.toByteSlice = b.toList := by
  simp [toContent, Simulation.Bytes.toByteArray_toByteSlice]

theorem locAfter_take_add {input : List UInt8} {o : Nat} {piece more : List UInt8}
    (h : input.drop o = piece ++ more) :
    locAfter (input.take (o + piece.length)) = advanceLoc (locAfter (input.take o)) piece := by
  rw [List.take_add, h, List.take_left, locAfter_append]

theorem drop_length_le {input : List UInt8} {o : Nat} {piece more : List UInt8}
    (h : input.drop o = piece ++ more) (hp : piece ≠ []) :
    o + piece.length + more.length = input.length := by
  have hl := congrArg List.length h
  simp only [List.length_drop, List.length_append] at hl
  by_cases ho : o ≤ input.length
  · omega
  · have : input.drop o = [] := List.drop_eq_nil_of_le (by omega)
    rw [this] at h
    cases piece with
    | nil => exact absurd rfl hp
    | cons _ _ => cases h

/-- A lexeme that spans the piece after the offset is the piece of layout the spec gives there,
and ends after it. -/
theorem lexemeLayout_eq {input : List UInt8} {o : Nat} {piece more : List UInt8}
    (h : input.drop o = piece ++ more) (hp : piece ≠ []) {l : Lexeme}
    {type : BSmtLibSpec.Lexer.TokenType}
    (hcat : (if l.category == .comment then BSmtLibSpec.Lexer.TokenType.comment else .whitespace) =
    type)
    (hs : l.start = locAfter (input.take o))
    (he : l.end = advanceLoc (locAfter (input.take o)) piece)
    {content : List UInt8} (hc : l.content.toList = content) :
    lexemeLayout l = BSmtLibSpec.Lexer.layoutEntry input type o piece.length content ∧
      (toLocation l.end).offset = o + piece.length := by
  have hlen := drop_length_le h hp
  have hend : toLocation l.end = BSmtLibSpec.Lexer.locate input (o + piece.length) := by
    rw [he, ← locAfter_take_add h, toLocation_take (by omega)]
  refine ⟨?_, by rw [hend]; rfl⟩
  unfold lexemeLayout BSmtLibSpec.Lexer.layoutEntry
  rw [hcat, hs, toLocation_take (by omega), hend, toContent_toByteSlice, hc]

theorem takeWhile_all {p : UInt8 → Bool} {l : List UInt8} (h : ∀ x ∈ l, p x = true) :
    l.takeWhile p = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [h x (by simp), ih fun y hy => h y (by simp [hy])]

theorem takeWhile_split {p : UInt8 → Bool} {a t : List UInt8} {d : UInt8}
    (ha : ∀ x ∈ a, p x = true) (hd : p d = false) : (a ++ d :: t).takeWhile p = a := by
  induction a with
  | nil => simp [hd]
  | cons x a ih => simp [ha x (by simp), ih fun y hy => ha y (by simp [hy])]

theorem dropWhile_all {p : UInt8 → Bool} {l : List UInt8} (h : ∀ x ∈ l, p x = true) :
    l.dropWhile p = [] := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [h x (by simp), ih fun y hy => h y (by simp [hy])]

theorem dropWhile_split {p : UInt8 → Bool} {a t : List UInt8} {d : UInt8}
    (ha : ∀ x ∈ a, p x = true) (hd : p d = false) : (a ++ d :: t).dropWhile p = d :: t := by
  induction a with
  | nil => simp [hd]
  | cons x a ih => simp [ha x (by simp), ih fun y hy => ha y (by simp [hy])]

/-- The run from a boundary for a consumer that takes whitespace and comments, and the layout
the spec gives there: either the spec gives none, and the first lexeme of the run, if any, is a
token; or the first lexeme is whitespace or a comment, the first piece the spec gives, after
which the spec goes on from its end; or the layout there is not complete yet, and the run has
finished nothing and not failed. -/
theorem stream_layout (version : Token.Version) (input : List UInt8) (ended : Bool) (o : Nat) :
    (BSmtLibSpec.Lexer.layoutFrom input ended o = [] ∧
      ∀ l ∈ (stream version true input ended o).1.head?, (Taken l)) ∨
    (∃ l rest, (stream version true input ended o).1 = l :: rest ∧ ¬ (Taken l) ∧
      o < (toLocation l.end).offset ∧
      BSmtLibSpec.Lexer.layoutFrom input ended o =
        lexemeLayout l :: BSmtLibSpec.Lexer.layoutFrom input ended (toLocation l.end).offset) ∨
    (BSmtLibSpec.Lexer.layoutFrom input ended o = [] ∧
      stream version true input ended o = ([], false)) := by
  unfold stream
  generalize hloc : locAfter (input.take o) = loc
  generalize hb : input.drop o = bytes
  cases bytes with
  | nil =>
    left
    refine ⟨layoutFrom_nil hb, ?_⟩
    simp only [streamFrom, lexBytesW]
    cases ended <;> simp [endStepW, eofLexeme, Lexeme.Taken, toTokenType]
  | cons c rest =>
    by_cases hw : isWhitespace c = true
    · -- whitespace: it goes on up to a byte that is not whitespace
      rw [layoutFrom_ws hb hw]
      let p0 : Pending := { mode := .whitespace, start := loc, content := ByteArray.empty.push c }
      have h0 : lexBytesW version true .idle loc (c :: rest) =
          lexBytesW version true (.token p0) (loc.afterByte c) rest := by
        simp only [lexBytesW, byteStepW, startStepW, start, hw, ite_true, withBefore_nil]
        rfl
      rcases list_split_first isWhitespace rest with hall | ⟨a, d, t, rfl, ha, hd⟩
      · obtain ⟨p', hm, hs, hc, hrun⟩ := lexBytesW_whitespace version rest hall (p := p0)
          (location := loc.afterByte c) rfl
        rw [takeWhile_all hall]
        have hlen := drop_length_le (piece := c :: rest) (more := []) (by simpa using hb)
          (by simp)
        simp only [List.length_cons, List.length_nil] at hlen
        cases ended with
        | false =>
          right; right
          rw [ite_eq_right (by simp; omega)]
          exact ⟨rfl, by simp only [streamFrom, h0, hrun, Bool.false_eq_true, ite_false]⟩
        | true =>
          right; left
          rw [ite_eq_left (.inl rfl)]
          let l : Lexeme := { category := .whitespace, content := p'.content, start := p'.start
                              «end» := advanceLoc (loc.afterByte c) rest }
          obtain ⟨hl1, hl2⟩ := lexemeLayout_eq (l := l) (type := .whitespace)
            (piece := c :: rest) (more := []) (by simpa using hb) (by simp) rfl
            (by rw [hloc]; exact hs) (by rw [hloc]; try rfl)
            (by
              show p'.content.toList = c :: rest
              simp only [hc, p0, toList_foldl_push, toList_empty_push, List.singleton_append])
          refine ⟨l, [eofLexeme (advanceLoc (loc.afterByte c) rest)], ?_,
            by simp [l, Lexeme.Taken, toTokenType], by rw [hl2]; simp, ?_⟩
          · simp only [streamFrom, h0, hrun, ite_true, endStepW, finish, hm, List.nil_append]
            rfl
          · rw [hl1, hl2]
      · obtain ⟨p', hm, hs, hc, hrun⟩ := lexBytesW_whitespace version a ha (p := p0)
          (location := loc.afterByte c) rfl
        rw [takeWhile_split ha hd]
        have hlen := drop_length_le (piece := c :: a) (more := d :: t) (by simpa using hb)
          (by simp)
        simp only [List.length_cons] at hlen
        right; left
        rw [ite_eq_left (.inr (by simp; omega))]
        have hh : HeadIs (wsLexeme p' (advanceLoc (loc.afterByte c) a))
            (lexBytesW version true .idle loc (c :: (a ++ d :: t))) := by
          rw [h0, lexBytesW_append, hrun]
          exact headIs_withBefore_nil (headIs_whitespace_end version t hm hd)
        obtain ⟨r, hr⟩ := streamFrom_head (ended := ended) hh
        obtain ⟨hl1, hl2⟩ := lexemeLayout_eq (l := wsLexeme p' (advanceLoc (loc.afterByte c) a))
          (type := .whitespace) (piece := c :: a) (more := d :: t) (by simpa using hb) (by simp)
          rfl (by rw [hloc]; exact hs) (by rw [hloc]; try rfl)
          (by
            show p'.content.toList = c :: a
            simp only [hc, p0, toList_foldl_push, toList_empty_push, List.singleton_append])
        refine ⟨_, r, hr, by simp [Lexeme.Taken, wsLexeme, toTokenType], by rw [hl2]; simp, ?_⟩
        rw [hl1, hl2]
    · have hw' : isWhitespace c = false := by simpa using hw
      by_cases hc : c = 59
      · -- a comment: it goes on up to a line break
        subst hc
        rw [layoutFrom_semi hb]
        let p0 : Pending := { mode := .comment, start := loc, content := .empty }
        have h0 : lexBytesW version true .idle loc (59 :: rest) =
            lexBytesW version true (.token p0) (loc.afterByte 59) rest := by
          simp only [lexBytesW, byteStepW, startStepW, start, hw', Bool.false_eq_true,
            show ((59 : UInt8) == 40) = false from rfl, show ((59 : UInt8) == 41) = false from rfl,
            show ((59 : UInt8) == 59) = true from rfl, ite_true, withBefore_nil,
            ite_false]
          rfl
        rcases list_split_first notLineBreak rest with hall | ⟨a, d, t, rfl, ha, hd⟩
        · have hall' : ∀ x ∈ rest, ((x == 10) || (x == 13)) = false := fun x hx => by
            simpa [notLineBreak] using hall x hx
          obtain ⟨p', hm, hs, hcont, hrun⟩ := lexBytesW_comment version rest hall' (p := p0)
            (location := loc.afterByte 59) rfl
          rw [dropWhile_all hall, takeWhile_all hall]
          cases ended with
          | false =>
            right; right
            exact ⟨rfl, by simp only [streamFrom, h0, hrun, Bool.false_eq_true, ite_false]⟩
          | true =>
            right; left
            let l : Lexeme := { category := .comment, content := p'.content, start := p'.start
                                «end» := advanceLoc (loc.afterByte 59) rest }
            obtain ⟨hl1, hl2⟩ := lexemeLayout_eq (l := l) (type := .comment)
              (piece := 59 :: rest) (more := []) (by simpa using hb) (by simp) rfl
              (by rw [hloc]; exact hs) (by rw [hloc]; try rfl)
              (by
                show p'.content.toList = rest
                simp only [hcont, p0, toList_foldl_push, toList_byteArray_empty, List.nil_append])
            refine ⟨l, [eofLexeme (advanceLoc (loc.afterByte 59) rest)], ?_,
              by simp [l, Lexeme.Taken, toTokenType], by rw [hl2]; simp, ?_⟩
            · simp only [streamFrom, h0, hrun, ite_true, endStepW, finish, hm, List.nil_append]
              rfl
            · simp only [ite_true]
              rw [hl1, hl2]
              have hlen := drop_length_le (piece := 59 :: rest) (more := []) (by simpa using hb)
                (by simp)
              simp only [List.length_cons, List.length_nil] at hlen
              rw [layoutFrom_nil (by rw [List.drop_eq_nil_iff]; simp; omega)]
              rfl
        · have ha' : ∀ x ∈ a, ((x == 10) || (x == 13)) = false := fun x hx => by
            simpa [notLineBreak] using ha x hx
          have hd' : ((d == 10) || (d == 13)) = true := by
            unfold notLineBreak at hd; cases h : ((d == 10) || (d == 13)) <;> simp_all
          obtain ⟨p', hm, hs, hcont, hrun⟩ := lexBytesW_comment version a ha' (p := p0)
            (location := loc.afterByte 59) rfl
          rw [dropWhile_split ha hd, takeWhile_split ha hd]
          right; left
          have hh : HeadIs (commentLexeme p' (advanceLoc (loc.afterByte 59) a) d)
              (lexBytesW version true .idle loc (59 :: (a ++ d :: t))) := by
            rw [h0, lexBytesW_append, hrun]
            simp only [withBefore_nil, lexBytesW, byteStepW_comment_end version hm hd']
            exact headIs_withBefore _
          obtain ⟨r, hr⟩ := streamFrom_head (ended := ended) hh
          obtain ⟨hl1, hl2⟩ := lexemeLayout_eq
            (l := commentLexeme p' (advanceLoc (loc.afterByte 59) a) d) (type := .comment)
            (piece := 59 :: (a ++ [d])) (more := t) (by simpa using hb) (by simp) rfl
            (by rw [hloc]; exact hs) (by rw [hloc]; simp [commentLexeme, advanceLoc])
            (by
              show (p'.content.push d).toList = a ++ [d]
              rw [show p'.content.push d = (a ++ [d]).foldl ByteArray.push ByteArray.empty by
                rw [List.foldl_append, ← hcont]; rfl, toList_foldl_push, toList_byteArray_empty,
                List.nil_append])
          refine ⟨_, r, hr, by simp [Lexeme.Taken, commentLexeme, toTokenType],
            by rw [hl2]; simp, ?_⟩
          rw [hl1, hl2]
          simp
      · -- neither: a token, an error or nothing
        left
        refine ⟨layoutFrom_other hb hw' hc, ?_⟩
        unfold streamFrom
        simp only [lexBytesW, byteStepW, startStepW, start_ws_eq hw']
        cases hs : start version false loc c with
        | idle =>
          exfalso
          simp only [start, hw', Bool.false_eq_true, ite_false] at hs
          repeat' split at hs
          all_goals cases hs
        | error f => simp [failedBeforeW]
        | token l =>
          have hl := (start_paren hs).1
          dsimp only
          cases lexBytesW version true .idle (loc.afterByte c) rest with
          | error _ => simpa [withBefore] using hl
          | ok x =>
            obtain ⟨st', loc', ls⟩ := x
            simp only [withBefore, List.singleton_append]
            cases ended with
            | false => simpa using hl
            | true =>
              simp only [ite_true]
              cases endStepW true st' loc' <;> simpa using hl
        | pending q =>
          have hq : (St.NonLayout (St.token q)) := ⟨start_taken hs, start_not_comment hs hc⟩
          have ht := lexBytesW_head_taken version rest (location := loc.afterByte c) hq
          simp only [withBefore_nil]
          revert ht
          cases lexBytesW version true (.token q) (loc.afterByte c) rest with
          | error ls => exact id
          | ok x =>
            obtain ⟨st', loc', ls⟩ := x
            rintro ⟨hnil, hhead⟩
            dsimp only
            cases ended with
            | false => exact hhead
            | true =>
              simp only [ite_true]
              cases ls with
              | cons l ls => cases endStepW true st' loc' <;> simpa using hhead
              | nil =>
                have hst := hnil rfl
                cases st' with
                | idle => exact hst.elim
                | token q' =>
                  obtain ⟨hw2, hc2⟩ := hst
                  simp only [endStepW, finish_ws_eq hc2]
                  cases hf : finish false q' loc' with
                  | none =>
                    exfalso
                    simp only [finish] at hf
                    cases hm : q'.mode <;> simp only [hm] at hf hc2 <;>
                      (repeat' split at hf) <;> simp_all
                  | token l =>
                    have := endStep_taken (st := .token q') (location := loc')
                      (ls := [l, eofLexeme loc']) (by simp only [endStep, hf]) hw2
                    simpa using this l (by simp)
                  | error _ => simp

end BSmtLib.Facts.Proofs.Lexer.Consumers.Boundary
