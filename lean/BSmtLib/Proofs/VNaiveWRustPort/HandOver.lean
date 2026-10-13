import BSmtLib.Proofs.VNaiveWRustPort.Consume

/-!
# The Rust port's hand-overs to the adapter's consumer

The Rust port hands a cursor over to the consumer (`flushCursor`) by calling it until the cursor
is empty or the consumer stops; while it holds a result, the first token is trailing input. Over
a batch that holds lexemes, with the lexer state under the version `ver`, holding a result if
`hd`, it does what `pending` says of the lexemes the cursor yields (`flushCursor_wp`): if the
consumer goes on, it returns with the version the consumer is in; otherwise it is interrupted at
the stop (`Matches`), with the version the consumer asked for. A break at the last token of the
cursor stops it at the end of that token; a break before another token makes that token
trailing input.
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open BSmtLib.Lexer.Internal (intoBatch)
open BSmtLib.Proofs.Adapter VNaive BSmtLib.Proofs.Simulation
open BSmtLibSpec.Lexer (Handed)
open Lexer.WRustPort (callConsumer)
open Lexer.WRustPort.Rust (flushCursor)

/-! ## Lexemes and locations of the hand-overs -/

/-- The lexeme of a token with the content and the span on a line, from the offset `start` to
the offset `end`. -/
def onLine (ty : TokenCategory) (content : ByteSlice) (line lineStart start «end» : Nat) : Lexeme :=
  { category := ty, content := content.toByteArray,
    start := { offset := start, line, column := start - lineStart },
    «end» := { offset := «end», line, column := «end» - lineStart } }

/-- The bytes of the slice from `a` to `b`, as positions in its array. -/
theorem extract_input (input : ByteSlice) {a b : Nat} (hab : a ≤ b) (hb : b ≤ input.size) :
    input.start + a ≤ input.start + b ∧ input.start + b ≤ input.byteArray.size ∧
      input.byteArray.extract (input.start + a) (input.start + b) =
        (input.slice a b).toByteArray := by
  have := input.stop_le_size_byteArray
  have := input.start_le_stop
  simp only [ByteSlice.size] at hb
  refine ⟨by omega, by omega, (slice_toByteArray input (.inl hb)).symm⟩

/-- The lexeme of a token with the content on a line, from `start` to the offset `end`. -/
def borrowedLexeme (ty : TokenCategory) (content : ByteSlice) (start : Location) (line lineStart
    «end» : Nat) : Lexeme :=
  { category := ty, content := content.toByteArray, start,
    «end» := { offset := «end», line, column := «end» - lineStart } }

theorem holds_of_len_zero {T : TokenBatch} (h : T.len = 0) : Holds T [] := by
  refine ⟨h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | (rw [h]; exact Nat.zero_le _) | (intro j hj; simp at hj)

/-- The location of the index `position` of the slice in a step whose offset `low` is that of
the index `base`, on the lexer's line. -/
def stepLocation (c : WCore) (low base position : Nat) : Location :=
  { offset := low + (position - base), line := c.line,
    column := low + (position - base) - c.lineStart }

/-! ## The hand-overs -/

section

variable {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat}

/-- The interruption is the error that the entry at the location is trailing input. -/
def IsTrailingAt (location : Location) (e : Intr C floor) : Prop :=
  e.result = .error (.lexical .unexpectedTrailingToken) ∧ e.span.start = location

/-- The interruption is the one the Rust port raises at the stop. -/
def Matches : Stop C → Intr C floor → Prop
  | .trailing l, e => IsTrailingAt l.start e
  | .fail err _ _, e => e.result = .error (.consumer (some err))
  | .layout _, e => e.result = .error (.consumer none)
  | .brk r l next, e =>
    (e.result = .ok (.finished r) ∧ e.location = l.end) ∨
      ∃ l2, next = some l2 ∧ IsTrailingAt l2.start e
  | .brkX r l, e => e.result = .ok (.finished r) ∧ e.location = l.end
  | .discard r l, e => e.result = .ok (.discarded r) ∧ e.location = l.end
  | .relex l, e => e.result = .ok .relex ∧ e.location = l.end

end

section

variable {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} {low : Nat} {g : BatchTag}

/-- The call of the consumer. -/
theorem wp_callConsumer {cursor : BatchCursor g} {h : cursor.HasNext} {s : BS floor low}
    {coll : List Handed}
    {Q : (Except (Option C.Error) (ControlFlow C.Result) ×
      {c : BatchCursor g // c.Consumed cursor}) → BS floor low → List Handed → Prop}
    {QE : Intr C floor → BS floor low → List Handed → Prop}
    (hq : Q ((Answering.consume C cursor h).run coll).1 s
      ((Answering.consume C cursor h).run coll).2) :
    WP (callConsumer (H := Answering C) (m := AnswerM) (R := C.Result) (E := Option C.Error)
      (floor := floor) (low := low) cursor h) s coll Q QE := hq

/-- A postcondition holds of a state with the same value. -/
theorem q_of_val_eq {α : Type} {Q : α → BS floor low → List Handed → Prop} {a : α}
    {s s' : BS floor low} {coll : List Handed} (h : s'.val = s.val) (hq : Q a s coll) :
    Q a s' coll := by
  have : s' = s := Subtype.ext h
  subst this
  exact hq

end

section

variable {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} {low : Nat} {g : BatchTag}

/-- The state with the version. -/
def withVersion (s : BS floor low) (v : Version) : BS floor low :=
  ⟨{ s.val with version := v }, s.property⟩

/-- The state with the version, discarding from `d` if `d` is some, from where it began. -/
def withDiscards (s : BS floor low) (v : Version) (d : Option Location) : BS floor low :=
  ⟨{ s.val with version := v, discardedFrom := discardsAfter s.val.discardedFrom d }, s.property⟩

/-- The state after the stop, with the version: discarding if the stop makes the lexer discard
(`Stop.discards`), from where it began. -/
def withStop (st : Stop C) (s : BS floor low) (v : Version) : BS floor low :=
  withDiscards s v st.discards

/-- The lexemes a cursor over a batch that holds `ls` yields. -/
noncomputable def yields (c : BatchCursor g) (ls : List Lexeme) : List Lexeme :=
  (ls.take (cStop c)).drop (cNext c)

/-- What the hand-over of a cursor leaves, as `pending` says. -/
def FlushPost (C : BSmtLibSpec.Lexer.Consumer) (hd : Bool) (ver : Version) (coll : List Handed)
    (xs : List Lexeme) (s : BS floor low) (Q : Unit → BS floor low → List Handed → Prop)
    (QE : Intr C floor → BS floor low → List Handed → Prop) : Prop :=
  match pending C hd ver coll xs with
  | .cont p' => Q () (withVersion s p'.ver) p'.taken
  | .wait r l p' => ∀ e, Matches (.brk r l none) e → QE e (withVersion s p'.ver) p'.taken
  | .stop st p' => ∀ e, Matches st e → QE e (withStop st s p'.ver) p'.taken

theorem take_drop_split {α : Type} (ls : List α) {i k a : Nat} (hik : i ≤ k) (hka : k ≤ a) :
    (ls.take a).drop i = (ls.take k).drop i ++ (ls.take a).drop k := by
  rw [List.drop_take, List.drop_take, List.drop_take]
  rw [show a - i = (k - i) + (a - k) by omega, List.take_add, List.drop_drop]
  congr 3
  omega

theorem wp_stopWith {Q : Unit → BS floor low → List Handed → Prop}
    {QE : Intr C floor → BS floor low → List Handed → Prop} (c0 : BatchCursor g) (e : Intr C floor)
    (s : BS floor low) (coll : List Handed) (hrec : s.val.recovers = false) (h : QE e s coll) :
    WP (Lexer.WRustPort.Rust.stopWith (H := Answering C) (m := AnswerM) (R := C.Result)
      (E := Option C.Error) (low := low) c0 e) s coll Q QE := by
  unfold Lexer.WRustPort.Rust.stopWith
  apply wp_bind
  apply wp_getCore
  simp only [hrec, Bool.false_eq_true, ite_false]
  exact wp_throw _ h

theorem getLast?_take_drop {α : Type} (ls : List α) {i k : Nat} (hik : i < k) (hk : k ≤ ls.length) :
    ((ls.take k).drop i).getLast? = some (ls[k - 1]'(by omega)) := by
  rw [List.getLast?_eq_getElem?]
  simp only [List.length_drop, List.length_take, List.getElem?_drop, List.getElem?_take]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
  rw [List.getElem?_eq_getElem (by omega)]
  congr 2
  omega

theorem withVersion_self (s : BS floor low) : withVersion s s.val.version = s := rfl

/-- The hand-over of a cursor over a batch that holds lexemes, by a lexer that does not recover:
as `pending` says of the lexemes the cursor yields (`FlushPost`). -/
theorem flushCursor_wp : ∀ (n : Nat) (cursor : BatchCursor g), cStop cursor - cNext cursor = n →
    ∀ (ls : List Lexeme), Holds (intoBatch cursor) ls → cStop cursor ≤ ls.length →
    cursor.relexRequested = false → cursor.discardRequested = false →
    ∀ (hfloor : ∀ p, floor = some p → cursor.EndsAfter p) (s : BS floor low) (coll : List Handed)
      (Q : Unit → BS floor low → List Handed → Prop)
      (QE : Intr C floor → BS floor low → List Handed → Prop),
    s.val.recovers = false → s.val.version = cursor.version →
    FlushPost C s.val.holding cursor.version coll (yields cursor ls) s Q QE →
    WP (flushCursor (H := Answering C) (m := AnswerM) (R := C.Result) (E := Option C.Error)
      cursor hfloor) s coll Q QE := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro cursor hn ls hb hs hrel hdis hfloor s coll Q QE hrec hver hpost
  rw [flushCursor]
  apply wp_dite
  · intro h
    have hlt := (Simulation.hasNext_iff cursor).mp h
    have hj : cNext cursor < ls.length := by omega
    have hy : yields cursor ls =
        ls[cNext cursor] :: (ls.take (cStop cursor)).drop (cNext cursor + 1) :=
      take_drop_cons ls hlt hs
    apply wp_bind
    apply wp_getCore
    unfold FlushPost at hpost
    have hpost0 := hpost
    rw [hy, pending, handAll_cons] at hpost
    cases hhold : s.val.holding with
    | true =>
      simp only [ite_true]
      have hp1 : hand1 C true (.cont ⟨coll, cursor.version⟩) ls[cNext cursor] =
          .stop (.trailing ls[cNext cursor]) ⟨coll, cursor.version⟩ := by
        simp [hand1]
      rw [hhold, hp1, handAll_stop] at hpost
      dsimp only at hpost
      unfold Lexer.WRustPort.Rust.stopWith
      apply wp_bind
      apply wp_getCore
      simp only [hrec, Bool.false_eq_true, ite_false]
      apply wp_throw
      rw [← hver] at hpost
      exact q_of_val_eq rfl (hpost _ ⟨rfl, span_peek_start cursor h hb hj⟩)
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      clear hpost
      apply wp_bind
      apply wp_callConsumer
      have hc := consume_spec C _ cursor h ls rfl hb hs ⟨coll, cursor.version⟩ rfl
      generalize (Answering.consume C cursor h).run coll = R at hc ⊢
      obtain ⟨⟨answer, cursor', consumed⟩, taken'⟩ := R
      dsimp only at hc ⊢
      obtain ⟨k1, k2, k3⟩ := hc
      rw [yields, take_drop_split ls (Nat.le_of_lt k1) k2, pending_append] at hpost0
      have hend : cursor'.consumedEndOf consumed = ls[cNext cursor' - 1].end :=
        consumedEndOf_at consumed (by rw [intoBatch_eq cursor' cursor]; exact hb) (by omega)
      apply wp_bind
      apply wp_modifyCore
      unfold ConsumeSpec at k3
      have hb' : Holds (intoBatch cursor') ls := by rw [intoBatch_eq cursor' cursor]; exact hb
      have hlast := getLast?_take_drop ls k1 (by omega)
      cases hp : pending C false cursor.version coll ((ls.take (cNext cursor')).drop (cNext cursor))
        with
      | cont p' =>
        have hp' := hp
        rw [← hhold] at hp'
        rw [hp] at k3
        rw [hp'] at hpost0
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := k3
        subst a1 a2
        rw [hrel] at a5
        rw [hdis] at a6
        simp only [a5, a6, Bool.false_eq_true, ite_false]
        refine ih (cStop cursor'.resetConsumed - cNext cursor'.resetConsumed) ?_
          cursor'.resetConsumed
          rfl ls (by rw [intoBatch_eq cursor'.resetConsumed cursor]; exact hb)
          (by rw [cStop_resetConsumed, a4]; exact hs) (by rw [relex_resetConsumed, a5])
          (by rw [discard_resetConsumed, a6]) _ _ _ _ _ hrec rfl ?_
        · rw [cStop_resetConsumed, cNext_resetConsumed, a4]
          omega
        · unfold FlushPost
          rw [yields, cStop_resetConsumed, cNext_resetConsumed, a4, version_resetConsumed, a3]
          dsimp only
          rw [pending]
          exact hpost0
      | wait r l p' =>
        have hp' := hp
        rw [← hhold] at hp'
        rw [hp] at k3
        rw [hp'] at hpost0
        obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := k3
        subst a1 a2
        rw [hdis] at a6
        simp only [a6, Bool.false_eq_true, ite_false]
        rw [a0] at hlast
        cases hlast
        apply wp_dite
        · intro h'
          have hlt' := (Simulation.hasNext_iff cursor').mp h'
          rw [a4] at hlt'
          rw [take_drop_cons ls hlt' hs, handAll_cons] at hpost0
          simp only [hand1, handAll_stop] at hpost0
          apply wp_stopWith _ _ (withVersion s cursor'.version) _ hrec
          rw [a3]
          exact hpost0 _ (.inr ⟨_, rfl, ⟨rfl, span_peek_start cursor' h' hb' (by omega)⟩⟩)
        · intro h'
          have hle := cNext_le_cStop cursor'
          have hge : cStop cursor ≤ cNext cursor' := by
            rw [← a4]
            exact Nat.le_of_not_lt fun h'' => h' ((Simulation.hasNext_iff cursor').mpr h'')
          rw [List.drop_eq_nil_of_le (by simp only [List.length_take]; omega), handAll_nil]
            at hpost0
          apply wp_stopWith _ _ (withVersion s cursor'.version) _ hrec
          rw [a3]
          exact hpost0 _ (.inl ⟨rfl, hend⟩)
      | stop st p' =>
        have hp' := hp
        rw [← hhold] at hp'
        rw [hp] at k3
        rw [hp'] at hpost0
        rw [handAll_stop] at hpost0
        dsimp only at hpost0
        obtain ⟨a0, a1, a2, a3⟩ := k3
        subst a1
        rw [a0] at hlast
        have hl : st.lex = ls[cNext cursor' - 1] := Option.some.inj hlast
        rw [← a2] at hpost0
        cases st with
        | trailing l => exact a3.elim
        | brk r l next => exact a3.elim
        | fail err d l =>
          obtain ⟨b1, b2⟩ := a3
          subst b1
          rw [hdis, Bool.or_false] at b2
          simp only [b2]
          cases d with
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            apply wp_stopWith _ _ (withVersion s cursor'.version) _ hrec
            exact hpost0 _ rfl
          | true =>
            simp only [ite_true]
            apply wp_bind
            apply wp_modifyCore
            refine wp_stopWith _ _ _ _ (by exact hrec) ?_
            refine q_of_val_eq ?_ (hpost0 _ ?_)
            · simp only [withStop, withDiscards, Stop.discards, discardsAfter]
              rw [hend, ← congrArg Lexeme.end hl]; rfl
            · rfl
        | layout l =>
          dsimp only [withStop, withDiscards, Stop.discards, discardsAfter] at hpost0
          obtain ⟨b1, b2⟩ := a3
          subst b1
          rw [hdis] at b2
          simp only [b2, Bool.false_eq_true, ite_false]
          apply wp_stopWith _ _ (withVersion s cursor'.version) _ hrec
          exact hpost0 _ rfl
        | brkX r l =>
          dsimp only [withStop, withDiscards, Stop.discards, discardsAfter] at hpost0
          obtain ⟨b1, b2, b3, b4⟩ := a3
          subst b1
          rw [b4, hdis] at *
          simp only [Bool.false_eq_true, ite_false]
          apply wp_dite
          · intro h'
            have := (Simulation.hasNext_iff cursor').mp h'
            omega
          · intro _
            apply wp_stopWith _ _ (withVersion s cursor'.version) _ hrec
            exact hpost0 _ ⟨rfl, hend.trans (congrArg Lexeme.end hl.symm)⟩
        | discard ro l =>
          dsimp only [withStop, withDiscards, Stop.discards, discardsAfter] at hpost0
          obtain ⟨b1, b2⟩ := a3
          subst b1
          simp only [b2, ite_true]
          apply wp_stopWith _ _ (withVersion s cursor'.version) _ hrec
          cases ro <;> exact hpost0 _ ⟨rfl, hend.trans (congrArg Lexeme.end hl.symm)⟩
        | relex l =>
          dsimp only [withStop, withDiscards, Stop.discards, discardsAfter] at hpost0
          obtain ⟨b1, b2, b3⟩ := a3
          subst b1
          rw [b3, hdis]
          simp only [b2, Bool.false_eq_true, ite_false, ite_true]
          apply wp_stopWith _ _ (withVersion s cursor'.version) _ hrec
          exact hpost0 _ ⟨rfl, hend.trans (congrArg Lexeme.end hl.symm)⟩
  · intro h
    have hle := cNext_le_cStop cursor
    have hlt : ¬ cNext cursor < cStop cursor := fun h' => h ((Simulation.hasNext_iff cursor).mpr h')
    have hy : yields cursor ls = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [yields, List.length_drop, List.length_take]
      omega
    apply wp_bind
    apply wp_getCore
    simp only [hrec, Bool.false_eq_true, ite_false]
    apply wp_pure
    unfold FlushPost at hpost
    rw [hy, pending_nil] at hpost
    dsimp only at hpost
    rw [← hver, withVersion_self] at hpost
    exact hpost

end

section

variable {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} {low : Nat} {g : BatchTag}

/-- The interruption `e` is where the consumer stops on the lexemes, with `p` what it has done
then, and `d` where the stop makes the lexer discard from, if it does. -/
def Stops (C : BSmtLibSpec.Lexer.Consumer) (hd : Bool) (ver : Version) (coll : List Handed)
    (ls : List Lexeme) (e : Intr C floor) (p : Prog) (d : Option Location) : Prop :=
  match pending C hd ver coll ls with
  | .cont _ => False
  | .wait r l p' => p = p' ∧ d = none ∧ Matches (.brk r l none) e
  | .stop st p' => p = p' ∧ d = st.discards ∧ Matches st e

/-- A stop on lexemes is a stop on them followed by more. -/
theorem Stops.append {hd : Bool} {ver : Version} {coll : List Handed} {ls : List Lexeme}
    {e : Intr C floor} {p : Prog} {d : Option Location} (h : Stops C hd ver coll ls e p d)
    (ys : List Lexeme) : Stops C hd ver coll (ls ++ ys) e p d := by
  unfold Stops at h ⊢
  rw [pending_append]
  cases hp : pending C hd ver coll ls with
  | cont p' => rw [hp] at h; exact h.elim
  | wait r l p' =>
    rw [hp] at h
    cases ys with
    | nil => exact h
    | cons y ys =>
      rw [handAll_cons]
      simp only [hand1, handAll_stop]
      exact ⟨h.1, h.2.1, .inl (h.2.2.resolve_right fun ⟨_, h', _⟩ => nomatch h')⟩
  | stop st p' =>
    rw [hp] at h
    rw [handAll_stop]
    exact h

/-- The fields of the lexer state that its correspondence with the naive lexer's reads, all but
the batch and the depths, and of the version only whether it is 2.0, whose lexical rules differ
from those of the later versions; and the version the lexer was created with. -/
def key (c : WCore) :=
  ((c.version == .v2_0, c.initialVersion), c.state, (c.discardedFrom, c.holding), c.recovers,
    c.recoveryState, c.tokenStart, c.tokenContent, c.offset, c.base, c.line, c.lineStart)

/-- A hand-over that goes on keeps the lexical rules. -/
theorem hand1_cont {hd : Bool} {p p' : Prog} {l : Lexeme}
    (h : hand1 C hd (.cont p) l = .cont p') : (p'.ver == .v2_0) = (p.ver == .v2_0) := by
  cases hd with
  | true => simp [hand1] at h
  | false =>
    simp only [hand1, Bool.false_eq_true, ite_false] at h
    cases hx : lexemeEntry C.concrete p.ver l with
    | none => simp only [hx] at h; cases h
    | some x =>
      simp only [hx] at h
      cases ha : C.answer (p.taken ++ [x]) with
      | fail e => simp only [ha] at h; cases h
      | «break» r =>
        simp only [ha] at h
        split at h
        · cases h
        · split at h <;> cases h
      | «continue» =>
        simp only [ha] at h
        split at h
        · cases h
        · split at h
          · cases h
          · rename_i hc
            cases h
            simp only [crosses, Bool.not_eq_true, bne_eq_false_iff_eq] at hc
            exact hc.symm

theorem handAll_cont {hd : Bool} : ∀ (ls : List Lexeme) (p p' : Prog),
    handAll C hd (.cont p) ls = .cont p' → (p'.ver == .v2_0) = (p.ver == .v2_0)
  | [], p, p', h => by cases h; rfl
  | l :: ls, p, p', h => by
    rw [handAll_cons] at h
    cases h1 : hand1 C hd (.cont p) l with
    | cont p1 =>
      rw [h1] at h
      exact (handAll_cont ls p1 p' h).trans (hand1_cont h1)
    | wait r l' p1 =>
      rw [h1] at h
      cases ls with
      | nil => cases h
      | cons l2 ls =>
        rw [handAll_cons] at h
        simp only [hand1, handAll_stop] at h
        cases h
    | stop st p1 => rw [h1, handAll_stop] at h; cases h

/-- What the consumer does after lexemes it goes on through keeps the lexical rules. -/
theorem pending_cont {hd : Bool} {ver : Version} {coll : List Handed} {ls : List Lexeme}
    {p' : Prog} (h : pending C hd ver coll ls = .cont p') : (p'.ver == .v2_0) = (ver == .v2_0) :=
  handAll_cont ls _ p' h

/-- The hand-over of a cursor over a batch that holds lexemes, as two cases. -/
theorem flushCursor_wp' (cursor : BatchCursor g) (ls : List Lexeme)
    (hb : Holds (intoBatch cursor) ls) (hs : cStop cursor ≤ ls.length)
    (hrel : cursor.relexRequested = false) (hdis : cursor.discardRequested = false)
    (hfloor : ∀ p, floor = some p → cursor.EndsAfter p) (s : BS floor low) (coll : List Handed)
    {Q : Unit → BS floor low → List Handed → Prop}
    {QE : Intr C floor → BS floor low → List Handed → Prop}
    (hrec : s.val.recovers = false) (hver : s.val.version = cursor.version)
    (hok : ∀ p', pending C s.val.holding cursor.version coll (yields cursor ls) = .cont p' →
      Q () (withVersion s p'.ver) p'.taken)
    (herr : ∀ e p' d, Stops C s.val.holding cursor.version coll (yields cursor ls) e p' d →
      QE e (withDiscards s p'.ver d) p'.taken) :
    WP (flushCursor (H := Answering C) (m := AnswerM) (R := C.Result) (E := Option C.Error)
      cursor hfloor) s coll Q QE := by
  refine flushCursor_wp _ cursor rfl ls hb hs hrel hdis hfloor s coll Q QE hrec hver ?_
  unfold FlushPost
  unfold Stops at herr
  cases hp : pending C s.val.holding cursor.version coll (yields cursor ls) with
  | cont p' => exact hok p' hp
  | wait r l p' =>
    intro e he
    exact herr e p' none (by rw [hp]; exact ⟨rfl, rfl, he⟩)
  | stop st p' =>
    intro e he
    exact herr e p' st.discards (by rw [hp]; exact ⟨rfl, rfl, he⟩)

theorem yields_new (v : Version) (T : TokenBatch) (ls : List Lexeme) (hT : Holds T ls) :
    yields (BatchCursor.new v T) ls = ls := by
  rw [yields, cStop_new, cNext_new, List.drop_zero, hT.len, List.take_length]

end

end BSmtLib.Proofs.Lexer.VNaiveWRustPort
