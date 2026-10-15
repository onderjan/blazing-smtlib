module

public import BSmtLib.Facts.PublicApi.Adapters
public import BSmtLib.Facts.Proofs.Reader.Param.Flagged
public import BSmtLib.Facts.Lexer.Adapters
import all BSmtLib.Lexer
import all BSmtLib.Token

@[expose] public section

/-!
# The collector against the adapter's consumer

The collector of `Facts.PublicApi` (`Adapters.Collector`) takes one token per call. The adapter's
consumer of the lexer proofs (`Answering`), for the spec's consumer that takes every entry,
whitespace and comments included, and breaks at the end of the input (`concreteCollector`),
takes in one call every token of the cursor up to the end of the input. The lexer hands a batch
over to the two alike: the collector's calls one after another take what the other's call takes,
and the lexer reads nothing of the cursor they give back that tells them apart.
-/

namespace BSmtLib.Facts.Proofs.PublicApi.Collector

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Facts.PublicApi.Adapters
open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.HandOver
open BSmtLibSpec.Lexer (Handed TokenType)

/-- The consumer of the spec that takes every entry, whitespace and comments included, continues
on each but the end-of-file token, breaks on that, and asks for nothing. -/
def concreteCollector : BSmtLibSpec.Lexer.Consumer where
  Result := Unit
  Error := Empty
  concrete := true
  answer taken := if taken.getLast?.map (·.type) = some .endOfFile then .break () else .continue
  switchTo _ := none
  discards _ := false

/-- The library's category of a token type of the spec. -/
def categoryOf : TokenType → Token.TokenCategory
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral => .numeral
  | .decimal => .decimal
  | .hexadecimal => .hexadecimal
  | .binary => .binary
  | .string => .string
  | .keyword => .keyword
  | .unquotedSymbol => .unquotedSymbol
  | .quotedSymbol => .quotedSymbol
  | .whitespace => .whitespace
  | .comment => .comment
  | .endOfFile => .endOfFile

/-- What the collector writes down of an entry of the spec. -/
def entryOf (handed : Handed) : Entry :=
  (categoryOf handed.type, handed.start.offset, handed.«end».offset)

/-! ## The link of the two consumers -/

/-- The relator of the two consumers: from the entries of the tokens taken, related values, and
the entries of the tokens taken after, whatever the states of the consumers. -/
def relator : Relator Collector CollectM (Answering concreteCollector) AnswerM where
  rel Q x y := ∀ a b (taken : List Handed),
    Q ((x.run a).run (taken.map entryOf)).1.1 ((y.run b).run taken).1.1 ∧
      ((x.run a).run (taken.map entryOf)).2 = ((y.run b).run taken).2.map entryOf
  pure h _ _ _ := ⟨h, rfl⟩
  bind {_ _ _ _ _ _ x y f g} hx hk a b taken := by
    obtain ⟨h₁, h₂⟩ := hx a b taken
    have e₁ : ((x >>= f).run a).run (taken.map entryOf) =
        ((f ((x.run a).run (taken.map entryOf)).1.1).run
          ((x.run a).run (taken.map entryOf)).1.2).run
            ((x.run a).run (taken.map entryOf)).2 := rfl
    have e₂ : ((y >>= g).run b).run taken =
        ((g ((y.run b).run taken).1.1).run ((y.run b).run taken).1.2).run
          ((y.run b).run taken).2 := rfl
    rw [e₁, e₂, h₂]
    exact hk _ _ h₁ _ _ _
  mono hQ h a b taken := ⟨hQ _ _ (h a b taken).1, (h a b taken).2⟩

/-- The link of the two consumers. -/
def link : Link Collector CollectM Unit Empty (Answering concreteCollector) AnswerM
    concreteCollector.Result (Option concreteCollector.Error) where
  rc := relator
  rr := (· = ·)
  re _ _ := True

/-! ## The handover of a cursor, after the consumer's call -/

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] {floor : Option Nat} {low : Nat}

/-- What `flushCursor` does with the consumer's answer and the cursor it gives back. -/
def afterCall {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → cursor.EndsAfter p)
    (x : Except E (ControlFlow R) × {c : Token.BatchCursor b // c.Consumed cursor}) :
    LexM H m R E floor low (Option (Interrupted R E floor) × Token.BatchCursor b) :=
  match x with
  | (result, ⟨next, consumed⟩) =>
    let location := next.consumedEndOf consumed
    have after : ∀ p, floor = some p → p < location.offset := fun p hp =>
      consumed.lt_consumedEndOf (hfloor p hp)
    match result with
    | .ok flow =>
      if next.discardRequested then
        let held := match flow with
          | .continue => none
          | .break result => some result
        return (some {
          result := .ok (.discarded held)
          span := next.consumedSpanOf consumed
          location
          stopAfter := fun p hp _ _ => after p hp }, next)
      else
        match flow with
        | .continue =>
          if next.relexRequested then
            return (some {
              result := .ok .relex
              span := next.consumedSpanOf consumed
              location
              stopAfter := fun p hp _ _ => after p hp }, next)
          else
            Internal.flushCursor next.resetConsumed fun p hp =>
              Token.BatchCursor.endsAfter_resetConsumed (consumed.follows.endsAfter (hfloor p hp))
        | .break result =>
          if h : next.HasNext then
            return (some (Internal.trailingAt (next.span (next.peek h))), next)
          else
            return (some {
              result := .ok (.finished result)
              span := next.consumedSpanOf consumed
              location
              stopAfter := fun p hp _ _ => after p hp }, next)
    | .error err => do
      if next.discardRequested then
        Internal.modifyCore fun c => { c with discardedFrom := c.discardedFrom.or (some location) }
      return (some {
        result := .error (.consumer err)
        span := next.consumedSpanOf consumed
        location
        stopAfter := fun _ _ _ h => nomatch h }, next)

theorem flushCursor_eq {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → cursor.EndsAfter p) :
    Internal.flushCursor (H := H) (m := m) (R := R) (E := E) (low := low) cursor hfloor =
      if h : cursor.HasNext then do
        if (← Internal.getCore).holding then
          return (some (Internal.trailingAt (cursor.span (cursor.peek h))), cursor)
        else
          Internal.callConsumer cursor h >>= afterCall cursor hfloor
      else
        return (none, cursor) := by
  rw [Internal.flushCursor.eq_1]
  rfl

theorem callConsumer_run [LawfulMonad m] {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (h : cursor.HasNext) (s : {c : LexerCore // c.Bound floor low}) (handler : H) :
    ((Internal.callConsumer (m := m) (R := R) (E := E) (floor := floor) (low := low) cursor
        h).run.run s).run handler =
      (Token.ConsumeFrom.consume cursor h).run handler >>= fun r => pure ((.ok r.1, s), r.2) := by
  simp [Internal.callConsumer, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
    ExceptT.run_mk]
  rfl

theorem flushCursor_empty {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → cursor.EndsAfter p) (h : ¬ cursor.HasNext) :
    Internal.flushCursor (H := H) (m := m) (R := R) (E := E) (low := low) cursor hfloor =
      pure (none, cursor) := by
  rw [flushCursor_eq]
  simp only [h, ↓reduceDIte]

theorem flushCursor_congr {b : Token.BatchTag} {x y : Token.BatchCursor b} (hxy : x = y)
    (hx : ∀ p, floor = some p → x.EndsAfter p) (hy : ∀ p, floor = some p → y.EndsAfter p) :
    Internal.flushCursor (H := H) (m := m) (R := R) (E := E) (low := low) x hx =
      Internal.flushCursor y hy := by
  subst hxy
  rfl

/-- After the consumer continues without a request, the handover goes on with the rest. -/
theorem afterCall_continue {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → cursor.EndsAfter p) (next : Token.BatchCursor b)
    (consumed : next.Consumed cursor) (hd : next.discardRequested = false)
    (hr : next.relexRequested = false) :
    afterCall (H := H) (m := m) (R := R) (E := E) (low := low) cursor hfloor
        (.ok .continue, ⟨next, consumed⟩) =
      Internal.flushCursor next.resetConsumed fun p hp =>
        Token.BatchCursor.endsAfter_resetConsumed (consumed.follows.endsAfter (hfloor p hp)) := by
  simp only [afterCall, hd, hr, Bool.false_eq_true, ↓reduceIte]

/-- After the consumer breaks without a request, the handover stops: at trailing input if the
consumer left tokens, else with the result. -/
theorem afterCall_break {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → cursor.EndsAfter p) (next : Token.BatchCursor b)
    (consumed : next.Consumed cursor) (hd : next.discardRequested = false) (result : R) :
    afterCall (H := H) (m := m) (R := R) (E := E) (low := low) cursor hfloor
        (.ok (.break result), ⟨next, consumed⟩) =
      if h : next.HasNext then
        pure (some (Internal.trailingAt (next.span (next.peek h))), next)
      else
        pure (some {
          result := .ok (.finished result)
          span := next.consumedSpanOf consumed
          location := next.consumedEndOf consumed
          stopAfter := fun p hp _ _ => consumed.lt_consumedEndOf (hfloor p hp) }, next) := by
  simp only [afterCall, hd, Bool.false_eq_true, ↓reduceIte]


/-- While a result is held, the handover stops at the first token, as trailing input. -/
theorem flushCursor_holding [LawfulMonad m] {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → cursor.EndsAfter p) (h : cursor.HasNext)
    (s : {c : LexerCore // c.Bound floor low}) (hh : s.val.holding = true) (handler : H) :
    ((Internal.flushCursor (m := m) (R := R) (E := E) cursor hfloor).run.run s).run handler =
      pure ((.ok (some (Internal.trailingAt (cursor.span (cursor.peek h))), cursor), s),
        handler) := by
  rw [flushCursor_eq]
  simp only [h, ↓reduceDIte]
  have hg : ∀ {σ : Type} {n : Type → Type} [Monad n] (x : σ),
      (StateT.get : StateT σ n σ).run x = pure (x, x) := fun _ => rfl
  simp [Internal.getCore, ExceptT.run_bind, getThe, MonadStateOf.get, hg, StateT.run_bind, hh]
end

/-! ## Cursors that differ only in where their handover began -/

section

variable {g : Token.BatchTag}

theorem hasNext_resetConsumed (c : Token.BatchCursor g) :
    c.resetConsumed.HasNext ↔ c.HasNext := Iff.rfl

theorem peek_resetConsumed (c : Token.BatchCursor g) (h : c.HasNext) :
    c.resetConsumed.peek ((hasNext_resetConsumed c).mpr h) = c.peek h := (rfl)

theorem category_resetConsumed (c : Token.BatchCursor g) (t : Token g) :
    c.resetConsumed.category t = c.category t := (rfl)

theorem span_resetConsumed (c : Token.BatchCursor g) (t : Token g) :
    c.resetConsumed.span t = c.span t := (rfl)

theorem resetConsumed_resetConsumed (c : Token.BatchCursor g) :
    c.resetConsumed.resetConsumed = c.resetConsumed := (rfl)

theorem next_resetConsumed (c : Token.BatchCursor g) (h : c.HasNext) :
    (c.resetConsumed.next ((hasNext_resetConsumed c).mpr h)).2.1.resetConsumed =
      (c.next h).2.1.resetConsumed := (rfl)

theorem discardRequested_resetConsumed (c : Token.BatchCursor g) :
    c.resetConsumed.discardRequested = c.discardRequested := (rfl)

theorem relexRequested_resetConsumed (c : Token.BatchCursor g) :
    c.resetConsumed.relexRequested = c.relexRequested := (rfl)

theorem discardRequested_next (c : Token.BatchCursor g) (h : c.HasNext) :
    (c.next h).2.1.discardRequested = c.discardRequested := (rfl)

theorem relexRequested_next (c : Token.BatchCursor g) (h : c.HasNext) :
    (c.next h).2.1.relexRequested = c.relexRequested := (rfl)

/-- Cursors that differ only in where their handover began: the same tokens left, the same
token at the next place, the same last token consumed, and the same requests. -/
theorem same_of_resetConsumed {x y : Token.BatchCursor g}
    (hxy : x.resetConsumed = y.resetConsumed) :
    (x.HasNext ↔ y.HasNext) ∧ (∀ hx hy, x.span (x.peek hx) = y.span (y.peek hy)) ∧
      (∀ {o o' : Token.BatchCursor g} (p : x.Consumed o) (q : y.Consumed o'),
        x.consumedSpanOf p = y.consumedSpanOf q ∧ x.consumedEndOf p = y.consumedEndOf q) ∧
      x.discardRequested = y.discardRequested ∧ x.relexRequested = y.relexRequested ∧
      x.version = y.version ∧
      BSmtLib.Lexer.Internal.intoBatch x = BSmtLib.Lexer.Internal.intoBatch y ∧
      (∀ {β : Type} (init : β) (f : β → Token.TokenCategory → β),
        x.foldConsumedCategories init f = y.foldConsumedCategories init f) := by
  cases x
  cases y
  simp only [Token.BatchCursor.resetConsumed, Token.BatchCursor.mk.injEq] at hxy
  obtain ⟨rfl, rfl, -, rfl, rfl, rfl, rfl, rfl⟩ := hxy
  exact ⟨Iff.rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

end

/-! ## The two consumers' calls -/

/-- What the collector writes down of the token of the cursor. -/
def entryAt {b : Token.BatchTag} (cursor : Token.BatchCursor b) (token : Token b) : Entry :=
  (cursor.category token, (cursor.span token).start.offset, (cursor.span token).end.offset)

/-- The entry that the adapter's consumer takes for the token of the cursor, for a consumer that
takes whitespace and comments. -/
def handedAt {b : Token.BatchTag} (cursor : Token.BatchCursor b) (token : Token b) : Handed :=
  match toHanded cursor token with
  | some handed => handed
  | none => toLayout cursor token

theorem entry_concrete {b : Token.BatchTag} (cursor : Token.BatchCursor b) (token : Token b) :
    Answering.entry concreteCollector cursor token = some (handedAt cursor token) := by
  unfold Answering.entry handedAt
  cases toHanded cursor token <;> rfl

theorem entryOf_handedAt {b : Token.BatchTag} (cursor : Token.BatchCursor b) (token : Token b) :
    entryOf (handedAt cursor token) = entryAt cursor token := by
  unfold handedAt entryOf entryAt toHanded toLayout
  generalize cursor.category token = category
  cases category <;> rfl

theorem type_handedAt {b : Token.BatchTag} (cursor : Token.BatchCursor b) (token : Token b) :
    ((handedAt cursor token).type = .endOfFile) ↔ cursor.category token = .endOfFile := by
  unfold handedAt toHanded toLayout
  generalize cursor.category token = category
  cases category <;> simp [toTokenType] <;> decide

theorem collector_consume_run {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (h : cursor.HasNext) (a : Collector) (entries : List Entry) :
    ((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) cursor h).run a).run entries =
      (((.ok (if cursor.category (cursor.peek h) == .endOfFile then .break () else .continue),
          (cursor.next h).2), a), entries ++ [entryAt cursor (cursor.peek h)]) :=
  (rfl)


/-- What the adapter's consumer for the concrete collector gives on a cursor. -/
abbrev AnswerOn {g : Token.BatchTag} (c : Token.BatchCursor g) : Type :=
  (Except (Option concreteCollector.Error) (ControlFlow concreteCollector.Result) ×
    {x : Token.BatchCursor g // x.Consumed c}) ×
    List Handed

theorem answering_step {g : Token.BatchTag} (c : Token.BatchCursor g) (h : c.HasNext)
    (taken : List Handed) :
    (Answering.consume concreteCollector c h).run taken =
      ((if c.category (c.peek h) == .endOfFile then
        ((.ok (.break ()), ⟨(c.next h).2.1, (c.next h).2.2⟩), taken ++ [handedAt c (c.peek h)])
      else if h' : (c.next h).2.1.HasNext then
        let r := (Answering.consume concreteCollector (c.next h).2.1 h').run
          (taken ++ [handedAt c (c.peek h)])
        ((r.1.1, ⟨r.1.2.1, r.1.2.2.trans (c.next h).2.2⟩), r.2)
      else
        ((.ok .continue, ⟨(c.next h).2.1, (c.next h).2.2⟩), taken ++ [handedAt c (c.peek h)])) :
        AnswerOn c) := by
  have hpk : (c.next h).1 = c.peek h := (rfl)
  rw [Answering.consume]
  generalize c.next h = n at hpk ⊢
  obtain ⟨token, next, consumed⟩ := n
  dsimp only at hpk ⊢
  subst hpk
  rw [entry_concrete]
  have hreq : ∀ t, (Answering.requests concreteCollector t next).val = next := by
    intro t
    simp [Answering.requests, Answering.switched, concreteCollector]
  have hans : concreteCollector.answer (taken ++ [handedAt c (c.peek h)]) =
      if c.category (c.peek h) == .endOfFile then .break () else .continue := by
    have ht := type_handedAt c (c.peek h)
    simp only [concreteCollector, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.map_some, Option.some.injEq]
    by_cases hc : c.category (c.peek h) = .endOfFile
    · simp only [ht.mpr hc, ↓reduceIte]
      rw [hc]
      rfl
    · simp only [show ¬ (handedAt c (c.peek h)).type = .endOfFile from fun h' => hc (ht.mp h'),
        ↓reduceIte]
      cases hcat : c.category (c.peek h) <;> first | rfl | exact absurd hcat hc
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind, hans]
  cases hc : (c.category (c.peek h) == .endOfFile)
  · have hsw : concreteCollector.switchTo (taken ++ [handedAt c (c.peek h)]) = none := rfl
    have hdis : concreteCollector.discards (taken ++ [handedAt c (c.peek h)]) = false := rfl
    simp only [Bool.false_eq_true, ↓reduceIte, hsw, hdis, Option.isSome_none,
      Bool.or_false]
    split
    · simp only [StateT.run_bind, StateT.run_pure]
      rfl
    · rfl
  · simp only [ite_true, StateT.run_pure]
    exact Prod.ext (Prod.ext rfl (Subtype.ext (hreq (taken ++ [handedAt c (c.peek h)])))) rfl

/-! ## The handover of a cursor to the two consumers -/

section

variable {floor : Option Nat} {low : Nat}

theorem collector_flush_step {g : Token.BatchTag} (c : Token.BatchCursor g)
    (hf : ∀ p, floor = some p → c.EndsAfter p) (h : c.HasNext)
    (s : {core : LexerCore // core.Bound floor low}) (hhold : s.val.holding = false)
    (a : Collector) (entries : List Entry) :
    (((Internal.flushCursor (H := Collector) (m := CollectM) (R := Unit) (E := Empty)
        c hf).run.run s).run a).run entries =
      (((afterCall c hf (.ok (if c.category (c.peek h) == Token.TokenCategory.endOfFile then
          .break () else .continue),
          (c.next h).2)).run.run s).run a).run (entries ++ [entryAt c (c.peek h)]) := by
  rw [flushCursor_eq]
  simp only [h, ↓reduceDIte]
  have hg : ∀ {σ : Type} {n : Type → Type} [Monad n] (x : σ),
      (StateT.get : StateT σ n σ).run x = pure (x, x) := fun _ => rfl
  simp [Internal.getCore, ExceptT.run_bind, getThe, MonadStateOf.get, hg, StateT.run_bind,
    hhold, callConsumer_run, collector_consume_run]
  rfl

theorem answering_flush_step {g : Token.BatchTag} (c : Token.BatchCursor g)
    (hf : ∀ p, floor = some p → c.EndsAfter p) (h : c.HasNext)
    (s : {core : LexerCore // core.Bound floor low}) (hhold : s.val.holding = false)
    (b : Answering concreteCollector) (taken : List Handed) :
    (((Internal.flushCursor (H := Answering concreteCollector) (m := AnswerM)
        (R := concreteCollector.Result)
        (E := Option concreteCollector.Error) c hf).run.run s).run b).run taken =
      (((afterCall c hf ((Answering.consume concreteCollector c h).run taken).1).run.run s).run
        b).run ((Answering.consume concreteCollector c h).run taken).2 := by
  rw [flushCursor_eq]
  simp only [h, ↓reduceDIte]
  have hg : ∀ {σ : Type} {n : Type → Type} [Monad n] (x : σ),
      (StateT.get : StateT σ n σ).run x = pure (x, x) := fun _ => rfl
  simp [Internal.getCore, ExceptT.run_bind, getThe, MonadStateOf.get, hg, StateT.run_bind,
    hhold, callConsumer_run]
  rfl

/-- What the handovers of a cursor to the two consumers give: related stops, if any, and cursors
that differ only in where their handover began. -/
def FlushRel {g : Token.BatchTag} :
    Except (Interrupted Unit Empty floor) (Option (Interrupted Unit Empty floor) ×
        Token.BatchCursor g) →
      Except (Interrupted concreteCollector.Result (Option concreteCollector.Error) floor)
        (Option (Interrupted concreteCollector.Result (Option concreteCollector.Error) floor) ×
          Token.BatchCursor g) → Prop :=
  ERel (IRel link.rr link.re)
    (fun x y => ORel (IRel link.rr link.re) x.1 y.1 ∧ x.2.resetConsumed = y.2.resetConsumed)

/-- Runs of the handovers to the two consumers that are related: as `FlushRel` says, with the
same lexer state, and the entries the collector wrote down for the tokens the other took. -/
def RunRel {g : Token.BatchTag} {α : Type}
    (x : ((Except (Interrupted Unit Empty floor) (Option (Interrupted Unit Empty floor) ×
        Token.BatchCursor g) × α) × Collector) × List Entry)
    (y : ((Except (Interrupted concreteCollector.Result (Option concreteCollector.Error) floor)
        (Option (Interrupted concreteCollector.Result (Option concreteCollector.Error) floor) ×
          Token.BatchCursor g) × α) × Answering concreteCollector) × List Handed) : Prop :=
  FlushRel x.1.1.1 y.1.1.1 ∧ x.1.1.2 = y.1.1.2 ∧ x.2 = y.2.map entryOf

theorem entryAt_resetConsumed {g : Token.BatchTag} (c : Token.BatchCursor g) (h : c.HasNext) :
    entryAt c.resetConsumed (c.resetConsumed.peek ((hasNext_resetConsumed c).mpr h)) =
      entryAt c (c.peek h) := (rfl)

theorem flush_main (n : Nat) : ∀ {g : Token.BatchTag} (o c : Token.BatchCursor g)
    (hq : c.Follows o) (h : c.HasNext) (_hr : c.remaining < n)
    (_hrl : c.relexRequested = false) (_hds : c.discardRequested = false)
    (hfo : ∀ p, floor = some p → o.EndsAfter p)
    (hfc : ∀ p, floor = some p → c.resetConsumed.EndsAfter p)
    (s : {core : LexerCore // core.Bound floor low}) (_hhold : s.val.holding = false)
    (a : Collector) (b : Answering concreteCollector) (taken : List Handed),
    RunRel
      ((((Internal.flushCursor (H := Collector) (m := CollectM) (R := Unit) (E := Empty)
        c.resetConsumed hfc).run.run s).run a).run (taken.map entryOf))
      ((((afterCall (H := Answering concreteCollector) (m := AnswerM)
        (R := concreteCollector.Result) (E := Option concreteCollector.Error) o hfo
          (((Answering.consume concreteCollector c h).run taken).1.1,
            ⟨((Answering.consume concreteCollector c h).run taken).1.2.1,
              ((Answering.consume concreteCollector c h).run taken).1.2.2.trans_follows
                hq⟩)).run.run
          s).run b).run ((Answering.consume concreteCollector c h).run taken).2) := by
  induction n with
  | zero => intro _ _ _ _ _ hr; omega
  | succ n ih =>
  intro g o c hq h hr hrl hds hfo hfc s hhold a b taken
  have h' := (hasNext_resetConsumed c).mpr h
  rw [collector_flush_step c.resetConsumed hfc h' s hhold a, entryAt_resetConsumed c h,
    peek_resetConsumed c h, category_resetConsumed, answering_step c h taken]
  have hdn : (c.resetConsumed.next h').2.1.discardRequested = false := by
    rw [discardRequested_next, discardRequested_resetConsumed, hds]
  have hrn : (c.resetConsumed.next h').2.1.relexRequested = false := by
    rw [relexRequested_next, relexRequested_resetConsumed, hrl]
  have hsame := same_of_resetConsumed (next_resetConsumed c h)
  cases hcat : (c.category (c.peek h) == .endOfFile)
  · simp only [Bool.false_eq_true, ite_false]
    rw [show (c.resetConsumed.next h').2 =
      ⟨(c.resetConsumed.next h').2.1, (c.resetConsumed.next h').2.2⟩ from rfl,
      afterCall_continue _ _ _ _ hdn hrn]
    rw [flushCursor_congr (next_resetConsumed c h)]
    by_cases hn : (c.next h).2.1.HasNext
    · simp only [hn, ↓reduceDIte]
      have := ih o (c.next h).2.1 ((c.next h).2.2.follows.trans hq) hn
        (Nat.lt_of_lt_of_le (c.next h).2.2.remaining_lt (Nat.le_of_lt_succ hr))
        (by rw [relexRequested_next, hrl]) (by rw [discardRequested_next, hds]) hfo
        (fun p hp => Token.BatchCursor.endsAfter_resetConsumed
          ((c.next h).2.2.follows.endsAfter ((hq.endsAfter (hfo p hp)))))
        s hhold a b (taken ++ [handedAt c (c.peek h)])
      rw [List.map_append, List.map_singleton, entryOf_handedAt] at this
      exact this
    · simp only [hn, ↓reduceDIte]
      have hn' : ¬ (c.next h).2.1.resetConsumed.HasNext := hn
      rw [afterCall_continue _ _ _ _ (by rw [discardRequested_next, hds])
        (by rw [relexRequested_next, hrl]), flushCursor_empty _ _ hn', flushCursor_empty _ _ hn']
      refine ⟨⟨trivial, rfl⟩, rfl, ?_⟩
      show taken.map entryOf ++ [entryAt c (c.peek h)] =
        (taken ++ [handedAt c (c.peek h)]).map entryOf
      rw [List.map_append, List.map_singleton, entryOf_handedAt]
  · simp only [ite_true]
    rw [show (c.resetConsumed.next h').2 =
      ⟨(c.resetConsumed.next h').2.1, (c.resetConsumed.next h').2.2⟩ from rfl,
      afterCall_break _ _ _ _ hdn,
      afterCall_break (R := concreteCollector.Result) (E := Option concreteCollector.Error) _ _ _ _
        (by rw [discardRequested_next, hds]) (() : concreteCollector.Result)]
    obtain ⟨hhas, hspan, hcons, -⟩ := hsame
    have hentries : taken.map entryOf ++ [entryAt c (c.peek h)] =
        (taken ++ [handedAt c (c.peek h)]).map entryOf := by
      rw [List.map_append, List.map_singleton, entryOf_handedAt]
    by_cases hn : (c.next h).2.1.HasNext
    · have hnX := hhas.mpr hn
      simp only [hn, hnX, ↓reduceDIte]
      refine ⟨⟨⟨?_, hspan hnX hn, rfl⟩, next_resetConsumed c h⟩, rfl, hentries⟩
      simp only [Internal.trailingAt, hspan hnX hn]
    · have hnX : ¬ (c.resetConsumed.next h').2.1.HasNext := fun hx => hn (hhas.mp hx)
      simp only [hn, hnX, ↓reduceDIte]
      obtain ⟨hs1, hs2⟩ := hcons (c.resetConsumed.next h').2.2
        ((c.next h).2.2.trans_follows hq)
      exact ⟨⟨⟨hs2, hs1, rfl⟩, next_resetConsumed c h⟩, rfl, hentries⟩

theorem new_resetConsumed (version : Token.Version) (batch : Token.TokenBatch) :
    (Token.BatchCursor.new version batch).resetConsumed = Token.BatchCursor.new version batch :=
  (rfl)

theorem relexRequested_new (version : Token.Version) (batch : Token.TokenBatch) :
    (Token.BatchCursor.new version batch).relexRequested = false := (rfl)

theorem discardRequested_new (version : Token.Version) (batch : Token.TokenBatch) :
    (Token.BatchCursor.new version batch).discardRequested = false := (rfl)

/-- The handovers of a new cursor to the two consumers are related. -/
theorem flushNew_sim (version : Token.Version) (batch : Token.TokenBatch)
    (hf : ∀ p, floor = some p → (Token.BatchCursor.new version batch).EndsAfter p) :
    LSim link (fun x y => ORel (IRel link.rr link.re) x.1 y.1 ∧
        x.2.resetConsumed = y.2.resetConsumed)
      (Internal.flushCursor (H := Collector) (m := CollectM) (R := Unit) (E := Empty)
        (low := low) (Token.BatchCursor.new version batch) hf)
      (Internal.flushCursor (H := Answering concreteCollector) (m := AnswerM)
        (R := concreteCollector.Result) (E := Option concreteCollector.Error)
        (Token.BatchCursor.new version batch) hf) := by
  intro s a b taken
  by_cases hn : (Token.BatchCursor.new version batch).HasNext
  · by_cases hh : s.val.holding = true
    · rw [flushCursor_holding _ _ hn s hh, flushCursor_holding _ _ hn s hh]
      exact ⟨⟨⟨⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · have hhold : s.val.holding = false := by simpa using hh
      have hm := flush_main _ (Token.BatchCursor.new version batch)
        (Token.BatchCursor.new version batch) (Token.BatchCursor.Follows.refl _) hn
        (Nat.lt_succ_self _) (relexRequested_new version batch)
        (discardRequested_new version batch) hf
        (by rw [new_resetConsumed]; exact hf) s hhold a b taken
      rw [flushCursor_congr (new_resetConsumed version batch) _ hf] at hm
      rw [answering_flush_step _ hf hn s hhold b taken]
      exact ⟨⟨hm.1, hm.2.1⟩, hm.2.2⟩
  · rw [flushCursor_empty _ _ hn, flushCursor_empty _ _ hn]
    exact ⟨⟨⟨trivial, rfl⟩, rfl⟩, rfl⟩

/-- The handovers of a batch to the two consumers are related. -/
theorem handOver_link (batch : Token.TokenBatch) (bytesAfter : ByteArray)
    (hfloor : ∀ p, floor = some p → batch.EndsAfter p) :
    LSim link (· = ·)
      (Internal.handOver (H := Collector) (m := CollectM) (R := Unit) (E := Empty) (low := low)
        batch bytesAfter hfloor)
      (Internal.handOver (H := Answering concreteCollector) (m := AnswerM)
        (R := concreteCollector.Result) (E := Option concreteCollector.Error)
        batch bytesAfter hfloor) := by
  unfold Internal.handOver
  refine XSim.bind_eq getCore_sim fun core => ?_
  refine XSim.bind (flushNew_sim _ _ _) ?_
  rintro ⟨stop₁, cursor⟩ ⟨stop₂, cursor'⟩ ⟨hs, he⟩
  dsimp only at hs he
  obtain ⟨-, -, -, -, -, hver, hinto, hfold⟩ := same_of_resetConsumed he
  dsimp only
  have hF : @Token.BatchCursor.foldConsumedCategories _ Nat cursor' =
      @Token.BatchCursor.foldConsumedCategories _ Nat cursor := by
    funext init f
    exact (hfold init f).symm
  generalize cursor'.version = v' at hver ⊢
  subst hver
  generalize Internal.intoBatch cursor' = b' at hinto ⊢
  subst hinto
  generalize @Token.BatchCursor.foldConsumedCategories _ Nat cursor' = F at hF ⊢
  subst hF
  refine XSim.bind_eq getCore_sim fun core' => ?_
  match stop₁, stop₂, hs with
  | none, none, _ => lsim
  | some i₁, some i₂, hi => lsim

/-- The lexer hands a batch over to the collector and to the adapter's consumer for the concrete
collector alike. -/
theorem consumers : Consumers link :=
  ⟨rfl, fun batch bytesAfter hfloor => handOver_link batch bytesAfter hfloor⟩

end
/-! ## The collector's run against the adapter's feeding -/

/-- The collector's run on slices, by the steps of the public calls. -/
theorem collectWith_cons (lexer : BSmtLib.Lexer Collector) (slice : ByteList)
    (slices : List ByteList) :
    collectWith lexer (slice :: slices) = (do
      let r ← Internal.run lexer (Internal.lexSliceStep (Recovery.LexRecovery.abandon
        Recovery.FailFast) (Recovery.LexRecovery.recover Recovery.FailFast)
          slice.toByteArray.toByteSlice)
      match r with
      | (.ok held, l) => collectWith (Internal.withHeld l (held.or (Internal.held l))) slices
      | (.error e, _) => pure (.error e)) := by
  rw [collectWith]
  unfold BSmtLib.Lexer.lexSlice
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | _, _⟩ <;> rfl

/-- The collector's run at the end of the input, by the step of the public call. -/
theorem collectWith_nil (lexer : BSmtLib.Lexer Collector) :
    collectWith lexer [] = (do
      let r ← Internal.run lexer (Internal.lexEofStep (Recovery.LexRecovery.abandon
        Recovery.FailFast) (Recovery.LexRecovery.recover Recovery.FailFast))
      match r with
      | (.ok flow, l) => pure (.ok (eofResult (Internal.held l) flow, Internal.withHeld l none))
      | (.error e, _) => pure (.error e)) := by
  rw [collectWith]
  unfold BSmtLib.Lexer.lexEof
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro r
  rcases r with ⟨_ | _, l⟩
  · rfl
  · rfl
theorem run_collectM {α : Type} (lexer : BSmtLib.Lexer Collector)
    (step : InnerM Collector CollectM α) (entries : List Entry) :
    (BSmtLib.Lexer.Internal.run lexer step).run entries =
      let r := ((step.run (Internal.core lexer)).run (Internal.handler lexer)).run entries
      ((r.1.1.1, Internal.ofParts r.1.2 r.1.1.2 (Internal.held lexer)), r.2) := (rfl)

theorem abandon_link (l : Span.Location) :
    link.rc.rel (· = ·)
      (Recovery.LexRecovery.abandon (H := Collector) (m := CollectM) Recovery.FailFast l)
      (Recovery.LexRecovery.abandon (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast l) :=
  link.rc.pure rfl

theorem recover_link (l : Span.Location) :
    link.rc.rel (· = ·)
      (Recovery.LexRecovery.recover (H := Collector) (m := CollectM) Recovery.FailFast l)
      (Recovery.LexRecovery.recover (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast l) :=
  link.rc.pure rfl

theorem oRel_or {x u : Option (Span.Located Unit)}
    {y v : Option (Span.Located concreteCollector.Result)}
    (h₁ : ORel (LocRel link.rr) x y) (h₂ : ORel (LocRel link.rr) u v) :
    ORel (LocRel link.rr) (x.or u) (y.or v) := by
  match x, y, h₁ with
  | none, none, _ => exact h₂
  | some _, some _, h => exact h

theorem id_bind {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

/-- The collector's run and the adapter's feeding of the library's lexer with the concrete
collector, from lexers with the same state and related held results: the collector writes down
the entries the other consumer takes, and fails exactly where the feeding does. -/
theorem collect_runInput : ∀ (slices : List ByteList) (lC : BSmtLib.Lexer Collector)
    (lA : BSmtLib.Lexer (Answering concreteCollector)) (taken : List Handed),
    Internal.core lC = Internal.core lA →
    ORel (LocRel link.rr) (Internal.held lC) (Internal.held lA) →
    ((collectWith lC slices).run (taken.map entryOf)).2 =
        ((BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps.runInput (consumer := concreteCollector) lA true
          slices).run taken).2.map entryOf ∧
      (resultOf ((collectWith lC slices).run (taken.map entryOf)).1).toBool =
        !((BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps.runInput (consumer := concreteCollector) lA
          true
          slices).run taken).1.1.isFailed ∧
      (∀ r lexer, ((collectWith lC slices).run (taken.map entryOf)).1 = .ok (r, lexer) →
        Internal.core lexer = Internal.core
          ((BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps.runInput (consumer := concreteCollector) lA
            true slices).run taken).1.2)
  | [], lC, lA, taken, hcore, hheld => by
    have hsim := Reader.Param.Calls.lexEofStep_sim consumers
      (Recovery.LexRecovery.abandon (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexRecovery.recover (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexRecovery.abandon (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast)
      (Recovery.LexRecovery.recover (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast)
      abandon_link recover_link (Internal.core lC) (Internal.handler lC) (Internal.handler lA)
      taken
    obtain ⟨⟨hr, hc⟩, ht⟩ := hsim
    rw [collectWith_nil]
    simp only [LexOps.runInput, ↓reduceIte, BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps]
    simp only [StateT.run_bind, run_collectM, BSmtLib.Facts.Proofs.Reader.Param.Flagged.run_answerM]
    rw [← hcore]
    generalize StateT.run (((Internal.lexEofStep (H := Collector) (m := CollectM) (R := Unit)
      (E := Empty) (Recovery.LexRecovery.abandon Recovery.FailFast)
      (Recovery.LexRecovery.recover Recovery.FailFast)).run (Internal.core lC)).run
        (Internal.handler lC)) (taken.map entryOf) = R1 at hr hc ht ⊢
    generalize StateT.run (((Internal.lexEofStep (H := Answering concreteCollector)
      (m := AnswerM) (R := concreteCollector.Result) (E := Option concreteCollector.Error)
      (Recovery.LexRecovery.abandon Recovery.FailFast)
      (Recovery.LexRecovery.recover Recovery.FailFast)).run (Internal.core lC)).run
        (Internal.handler lA)) taken = R2 at hr hc ht ⊢
    obtain ⟨⟨⟨r1, c1⟩, h1⟩, e1⟩ := R1
    obtain ⟨⟨⟨r2, c2⟩, h2⟩, e2⟩ := R2
    dsimp only at hr hc ht ⊢
    subst ht
    rcases r1 with _ | f1 <;> rcases r2 with _ | f2 <;> try exact absurd hr id
    · refine ⟨rfl, rfl, fun _ _ heq => ?_⟩
      simp only [id_bind] at heq
      cases heq
    · simp only [id_bind]
      generalize Lexer.Adapters.eofResult (Internal.held (Internal.ofParts h2 c2
        (Internal.held lA))) f2 = o
      cases o <;> exact ⟨rfl, rfl, fun _ _ heq => by cases heq; exact hc⟩
  | slice :: slices, lC, lA, taken, hcore, hheld => by
    have hsim := Reader.Param.Calls.lexSliceStep_sim consumers
      (Recovery.LexRecovery.abandon (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexRecovery.recover (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexRecovery.abandon (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast)
      (Recovery.LexRecovery.recover (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast)
      abandon_link recover_link slice.toByteArray.toByteSlice (Internal.core lC)
      (Internal.handler lC) (Internal.handler lA) taken
    obtain ⟨⟨hr, hc⟩, ht⟩ := hsim
    rw [collectWith_cons]
    simp only [LexOps.runInput, BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps]
    simp only [StateT.run_bind, run_collectM,
      BSmtLib.Facts.Proofs.Reader.Param.Flagged.run_answerM]
    rw [← hcore]
    generalize StateT.run (((Internal.lexSliceStep (H := Collector) (m := CollectM) (R := Unit)
      (E := Empty) (Recovery.LexRecovery.abandon Recovery.FailFast)
      (Recovery.LexRecovery.recover Recovery.FailFast) slice.toByteArray.toByteSlice).run
        (Internal.core lC)).run (Internal.handler lC)) (taken.map entryOf) = R1 at hr hc ht ⊢
    generalize StateT.run (((Internal.lexSliceStep (H := Answering concreteCollector)
      (m := AnswerM) (R := concreteCollector.Result) (E := Option concreteCollector.Error)
      (Recovery.LexRecovery.abandon Recovery.FailFast)
      (Recovery.LexRecovery.recover Recovery.FailFast) slice.toByteArray.toByteSlice).run
        (Internal.core lC)).run (Internal.handler lA)) taken = R2 at hr hc ht ⊢
    obtain ⟨⟨⟨r1, c1⟩, h1⟩, e1⟩ := R1
    obtain ⟨⟨⟨r2, c2⟩, h2⟩, e2⟩ := R2
    dsimp only at hr hc ht ⊢
    subst ht
    simp only [id_bind]
    rcases r1 with _ | d1 <;> rcases r2 with _ | d2 <;> try exact absurd hr id
    · refine ⟨rfl, rfl, fun _ _ heq => ?_⟩
      cases heq
    · exact collect_runInput slices _ _ e2 hc
        (oRel_or hr (by
          simp only [BSmtLib.Facts.Proofs.Reader.Param.Flagged.held_ofParts]
          exact hheld))


/-- The collector writes down the entries that the library's lexer, as the adapter of the lexer
proofs feeds it, hands to the concrete collector of the spec, and fails exactly where that does. -/
theorem collect_lexing (version : Token.Version) (slices : List ByteList) :
    (collect version slices).2 = (BSmtLib.Facts.Lexer.Adapters.lexing
        BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps concreteCollector (fromVersion version) []
          slices true).taken.map entryOf ∧
      (collect version slices).1.toBool = !(BSmtLib.Facts.Lexer.Adapters.lexing
        BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps concreteCollector (fromVersion version) []
          slices true).outcome.isFailed := by
  have h := collect_runInput slices (BSmtLib.Lexer.new Collector.mk version)
    (BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps.new concreteCollector {} version) [] (rfl) trivial
  simp only [List.map_nil] at h
  have hv : toVersion (fromVersion version) = version := by cases version <;> rfl
  simp only [collect, BSmtLib.Facts.Lexer.Adapters.lexing, List.foldl_nil, hv, StateT.run_map]
  revert h
  generalize StateT.run (BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps.runInput
    (BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps.new concreteCollector {} version) true slices) [] = A
  obtain ⟨⟨o, l⟩, t⟩ := A
  intro h
  exact ⟨h.1, h.2.1⟩

end BSmtLib.Facts.Proofs.PublicApi.Collector
