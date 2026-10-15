module

public import BSmtLib.Facts.Proofs.Reader.ParamW.Calls
public import BSmtLib.Facts.Proofs.PublicApi.Collector
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Token

@[expose] public section

/-!
# The Rust port's handover to the collector against the adapter's consumer

The collector takes one token per call, the adapter's consumer for the concrete collector every
token of the cursor up to the end of the input. The Rust port's handover of a cursor
(`Rust.flushCursor`) calls the collector again until the cursor is spent, and the other
consumer once; the two handovers end alike, with the same lexer state, the collector writing
down the entries the other takes (`consumersW`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.CollectorW

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Token.BatchCursor.Internal (discardRequested resetConsumed remaining relexRequested
    EndsAfter consumedSpanOf Follows foldConsumedCategories consumedEndOf)
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Facts.PublicApi.Adapters
open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Facts.Proofs.PublicApi.Collector
open BSmtLib.Lexer.Internal.WRustPort
open BSmtLibSpec.Lexer (Handed)

/-! ## The handover of a cursor, after the consumer's call -/

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] {floor : Option Nat} {low : Nat}

/-- What `Rust.flushCursor` does with the consumer's answer and the cursor it gives back. -/
def afterCallW {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → EndsAfter cursor p)
    (x : Except E (ControlFlow R) × {c : Token.BatchCursor b // c.Consumed cursor}) :
    Lexer.Internal.WRustPort.LexM H m R E floor low Unit :=
  match x with
  | (result, ⟨cursor', consumed⟩) => do
    let consumedSpan := consumedSpanOf cursor' consumed
    let consumedEnd := consumedEndOf cursor' consumed
    have after : ∀ p, floor = some p → p < consumedEnd.offset := fun p hp =>
      consumed.lt_consumedEndOf (hfloor p hp)
    modifyCore fun c => { c with version := cursor'.version }
    match result with
    | .ok flow =>
      if discardRequested cursor' then
        let held := match flow with
          | .continue => none
          | .break result => some result
        Rust.stopWith cursor'
          { result := .ok (.discarded held), span := consumedSpan
            location := consumedEnd
            stopAfter := fun p hp _ _ => after p hp }
      else
        match flow with
        | .continue =>
          if relexRequested cursor' then
            Rust.stopWith cursor'
              { result := .ok .relex, span := consumedSpan
                location := consumedEnd
                stopAfter := fun p hp _ _ => after p hp }
          else
            Rust.flushCursor (resetConsumed cursor') fun p hp =>
              Token.BatchCursor.endsAfter_resetConsumed (consumed.follows.endsAfter (hfloor p hp))
        | .break result =>
          if h : cursor'.HasNext then
            Rust.stopWith cursor' (trailingAt (cursor'.span (cursor'.peek h)))
          else
            Rust.stopWith cursor'
              { result := .ok (.finished result), span := consumedSpan
                location := consumedEnd
                stopAfter := fun p hp _ _ => after p hp }
    | .error err => do
      if discardRequested cursor' then
        modifyCore fun c => { c with discardedFrom := c.discardedFrom.or (some consumedEnd) }
      Rust.stopWith cursor'
        { result := .error (.consumer err), span := consumedSpan
          location := consumedEnd
          stopAfter := fun _ _ _ h => nomatch h }

theorem flushCursor_eqW {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → EndsAfter cursor p) :
    Rust.flushCursor (H := H) (m := m) (R := R) (E := E) (low := low) cursor hfloor =
      (if h : cursor.HasNext then do
        if (← getCore).holding then
          Rust.stopWith cursor (trailingAt (cursor.span (cursor.peek h)))
        else
          callConsumer cursor h >>= afterCallW cursor hfloor
      else do
        if (← getCore).recovers then
          modifyCore fun c => { c with consumedDepth := c.lexedDepth }) := by
  rw [Rust.flushCursor.eq_1]
  rfl

end

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] {floor : Option Nat} {low : Nat}

theorem callConsumer_runW {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (h : cursor.HasNext) (s : {c : Lexer.Internal.WRustPort.LexerCore // c.Bound floor low})
    (handler : H) :
    ((callConsumer (m := m) (R := R) (E := E) (floor := floor) (low := low) cursor
        h).run.run s).run handler =
      (Token.ConsumeFrom.consume cursor h).run handler >>= fun r => pure ((.ok r.1, s), r.2) := by
  simp [callConsumer, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.run_mk]
  rfl

end

theorem collector_flush_stepW {g : Token.BatchTag} {floor : Option Nat} {low : Nat}
    (c : Token.BatchCursor g)
    (hf : ∀ p, floor = some p → EndsAfter c p) (h : c.HasNext)
    (s : {core : Lexer.Internal.WRustPort.LexerCore // core.Bound floor low})
    (hhold : s.val.holding = false) (a : Collector) (entries : List Entry) :
    (((Rust.flushCursor (H := Collector) (m := CollectM) (R := Unit) (E := Empty)
        c hf).run.run s).run a).run entries =
      (((afterCallW c hf (.ok (if c.category (c.peek h) == Token.TokenCategory.endOfFile then
          .break () else .continue),
          (c.next h).2)).run.run s).run a).run (entries ++ [entryAt c (c.peek h)]) := by
  rw [flushCursor_eqW]
  simp only [h, ↓reduceDIte]
  have hg : ∀ {σ : Type} {n : Type → Type} [Monad n] (x : σ),
      (StateT.get : StateT σ n σ).run x = pure (x, x) := fun _ => rfl
  simp [getCore, ExceptT.run_bind, getThe, MonadStateOf.get, hg, StateT.run_bind,
    hhold, callConsumer_runW, collector_consume_run]
  rfl

theorem answering_flush_stepW {g : Token.BatchTag} {floor : Option Nat} {low : Nat}
    (c : Token.BatchCursor g)
    (hf : ∀ p, floor = some p → EndsAfter c p) (h : c.HasNext)
    (s : {core : Lexer.Internal.WRustPort.LexerCore // core.Bound floor low})
    (hhold : s.val.holding = false)
    (b : Answering concreteCollector) (taken : List Handed) :
    (((Rust.flushCursor (H := Answering concreteCollector) (m := AnswerM)
        (R := concreteCollector.Result)
        (E := Option concreteCollector.Error) c hf).run.run s).run b).run taken =
      (((afterCallW c hf ((Answering.consume concreteCollector c h).run taken).1).run.run s).run
        b).run ((Answering.consume concreteCollector c h).run taken).2 := by
  rw [flushCursor_eqW]
  simp only [h, ↓reduceDIte]
  have hg : ∀ {σ : Type} {n : Type → Type} [Monad n] (x : σ),
      (StateT.get : StateT σ n σ).run x = pure (x, x) := fun _ => rfl
  simp [getCore, ExceptT.run_bind, getThe, MonadStateOf.get, hg, StateT.run_bind,
    hhold, callConsumer_runW]
  rfl

/-! ## Runs of the parts of the handover -/

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] {floor : Option Nat} {low : Nat}

/-- The parentheses open after the tokens the cursor's consumer has taken, from `depth`. -/
def depthAfterW {b : Token.BatchTag} (cursor : Token.BatchCursor b) (depth : Nat) : Nat :=
  foldConsumedCategories cursor depth fun depth category =>
    match category with
    | .parenOpen => depth + 1
    | .parenClose => depth - 1
    | _ => depth

/-- The lexer state after a stop of the handover: a recovering lexer counts the parentheses
the consumer has taken. -/
def stopState {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (s : {c : Lexer.Internal.WRustPort.LexerCore // c.Bound floor low}) :
    {c : Lexer.Internal.WRustPort.LexerCore // c.Bound floor low} :=
  if s.val.recovers then
    ⟨{ s.val with
        consumedDepth := depthAfterW cursor s.val.consumedDepth
        lexedDepth := depthAfterW cursor s.val.consumedDepth }, s.property⟩
  else s

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem stopWith_runW {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (stop : Interrupted R E floor)
    (s : {c : Lexer.Internal.WRustPort.LexerCore // c.Bound floor low}) (a : H) :
    ((Rust.stopWith (m := m) (low := low) cursor stop).run.run s).run a =
      pure ((.error stop, stopState cursor s), a) := by
  unfold Rust.stopWith stopState
  have hg : ∀ {σ : Type} {n : Type → Type} [Monad n] (x : σ),
      (StateT.get : StateT σ n σ).run x = pure (x, x) := fun _ => rfl
  by_cases hr : s.val.recovers = true
  · simp [getCore, ExceptT.run_bind, getThe, MonadStateOf.get, hg, StateT.run_bind, hr,
      modifyCore, modifyThe, MonadStateOf.modifyGet, throw, throwThe, MonadExceptOf.throw]
    rfl
  · have hr' : s.val.recovers = false := by simpa using hr
    simp [getCore, ExceptT.run_bind, getThe, MonadStateOf.get, hg, StateT.run_bind, hr',
      throw, throwThe, MonadExceptOf.throw]

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem modifyCore_bind_runW {α : Type} (f : Lexer.Internal.WRustPort.LexerCore →
    Lexer.Internal.WRustPort.LexerCore) (hf)
    (k : Unit → Lexer.Internal.WRustPort.LexM H m R E floor low α)
    (s : {c : Lexer.Internal.WRustPort.LexerCore // c.Bound floor low}) (a : H) :
    ((modifyCore f hf >>= k).run.run s).run a = ((k ()).run.run ⟨f s.val, hf _ s.property⟩).run a
      := by
  simp [modifyCore, modifyThe, MonadStateOf.modifyGet, ExceptT.run_bind, StateT.run_bind]


/-- The lexer state after the handover of a spent cursor. -/
def emptyState (s : {c : Lexer.Internal.WRustPort.LexerCore // c.Bound floor low}) :
    {c : Lexer.Internal.WRustPort.LexerCore // c.Bound floor low} :=
  if s.val.recovers then ⟨{ s.val with consumedDepth := s.val.lexedDepth }, s.property⟩ else s

theorem flushCursor_empty_runW {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → EndsAfter cursor p) (h : ¬ cursor.HasNext)
    (s : {c : Lexer.Internal.WRustPort.LexerCore // c.Bound floor low}) (a : H) :
    ((Rust.flushCursor (m := m) (R := R) (E := E) (low := low) cursor hfloor).run.run s).run a =
      pure ((.ok (), emptyState s), a) := by
  rw [flushCursor_eqW]
  simp only [h, ↓reduceDIte]
  unfold emptyState
  have hg : ∀ {σ : Type} {n : Type → Type} [Monad n] (x : σ),
      (StateT.get : StateT σ n σ).run x = pure (x, x) := fun _ => rfl
  by_cases hr : s.val.recovers = true
  · simp [getCore, ExceptT.run_bind, getThe, MonadStateOf.get, hg, StateT.run_bind, hr,
      modifyCore, modifyThe, MonadStateOf.modifyGet]
  · have hr' : s.val.recovers = false := by simpa using hr
    simp [getCore, ExceptT.run_bind, getThe, MonadStateOf.get, hg, StateT.run_bind, hr']

omit [LawfulMonad m] in
/-- After the consumer continues without a request, the handover goes on with the rest. -/
theorem afterCallW_continue {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → EndsAfter cursor p) (next : Token.BatchCursor b)
    (consumed : next.Consumed cursor) (hd : discardRequested next = false)
    (hr : relexRequested next = false) :
    afterCallW (H := H) (m := m) (R := R) (E := E) (low := low) cursor hfloor
        (.ok .continue, ⟨next, consumed⟩) =
      (modifyCore fun c => { c with version := next.version }) >>= fun _ =>
        Rust.flushCursor (resetConsumed next) fun p hp =>
          Token.BatchCursor.endsAfter_resetConsumed (consumed.follows.endsAfter (hfloor p hp)) := by
  simp only [afterCallW, hd, hr, Bool.false_eq_true, ↓reduceIte]

omit [LawfulMonad m] in
/-- After the consumer breaks without a request, the handover stops: at trailing input if the
consumer left tokens, else with the result. -/
theorem afterCallW_break {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → EndsAfter cursor p) (next : Token.BatchCursor b)
    (consumed : next.Consumed cursor) (hd : discardRequested next = false) (result : R) :
    afterCallW (H := H) (m := m) (R := R) (E := E) (low := low) cursor hfloor
        (.ok (.break result), ⟨next, consumed⟩) =
      (modifyCore fun c => { c with version := next.version }) >>= fun _ =>
        if h : next.HasNext then
          Rust.stopWith next (trailingAt (next.span (next.peek h)))
        else
          Rust.stopWith next {
            result := .ok (.finished result)
            span := consumedSpanOf next consumed
            location := consumedEndOf next consumed
            stopAfter := fun p hp _ _ => consumed.lt_consumedEndOf (hfloor p hp) } := by
  simp only [afterCallW, hd, Bool.false_eq_true, ↓reduceIte]

end

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] {floor : Option Nat} {low : Nat}

omit [LawfulMonad m] in
theorem flushCursor_congrW {b : Token.BatchTag} {x y : Token.BatchCursor b} (hxy : x = y)
    (hx : ∀ p, floor = some p → EndsAfter x p) (hy : ∀ p, floor = some p → EndsAfter y p) :
    Rust.flushCursor (H := H) (m := m) (R := R) (E := E) (low := low) x hx =
      Rust.flushCursor y hy := by
  subst hxy
  rfl

/-- The handover after a call sets the version first, so the version it starts from does not
matter. -/
theorem afterCallW_run_version {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → EndsAfter cursor p)
    (x : Except E (ControlFlow R) × {c : Token.BatchCursor b // c.Consumed cursor})
    (s : {c : Lexer.Internal.WRustPort.LexerCore // c.Bound floor low}) (v : Token.Version)
    (a : H) :
    ((afterCallW (m := m) (low := low) cursor hfloor x).run.run
        ⟨{ s.val with version := v }, s.property⟩).run a =
      ((afterCallW cursor hfloor x).run.run s).run a := by
  obtain ⟨result, next, consumed⟩ := x
  unfold afterCallW
  dsimp only
  rw [modifyCore_bind_runW, modifyCore_bind_runW]

end

/-- Runs of the Rust port's handovers to the two consumers that are related: related ends, the
same lexer state, and the entries the collector wrote down for the tokens the other took. -/
def RunRelW {floor : Option Nat} {low : Nat}
    (x : ((Except (Interrupted Unit Empty floor) Unit ×
        {c : Lexer.Internal.WRustPort.LexerCore // c.Bound floor low}) × Collector) × List Entry)
    (y : ((Except (Interrupted concreteCollector.Result (Option concreteCollector.Error) floor)
        Unit × {c : Lexer.Internal.WRustPort.LexerCore // c.Bound floor low}) ×
          Answering concreteCollector) × List Handed) : Prop :=
  ERel (IRel link.rr link.re) (· = ·) x.1.1.1 y.1.1.1 ∧ x.1.1.2 = y.1.1.2 ∧
    x.2 = y.2.map entryOf

theorem version_next {g : Token.BatchTag} (c : Token.BatchCursor g) (h : c.HasNext) :
    (c.next h).2.1.version = c.version := (rfl)

section

variable {floor : Option Nat} {low : Nat}

theorem flush_mainW (n : Nat) : ∀ {g : Token.BatchTag} (o c : Token.BatchCursor g)
    (hq : Follows c o) (h : c.HasNext) (_hr : remaining c < n)
    (_hrl : relexRequested c = false) (_hds : discardRequested c = false)
    (hfo : ∀ p, floor = some p → EndsAfter o p)
    (hfc : ∀ p, floor = some p → EndsAfter (resetConsumed c) p)
    (s : {core : Lexer.Internal.WRustPort.LexerCore // core.Bound floor low})
    (_hhold : s.val.holding = false)
    (a : Collector) (b : Answering concreteCollector) (taken : List Handed),
    RunRelW
      ((((Rust.flushCursor (H := Collector) (m := CollectM) (R := Unit) (E := Empty)
        (resetConsumed c) hfc).run.run s).run a).run (taken.map entryOf))
      ((((afterCallW (H := Answering concreteCollector) (m := AnswerM)
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
  rw [collector_flush_stepW (resetConsumed c) hfc h' s hhold a, entryAt_resetConsumed c h,
    peek_resetConsumed c h, category_resetConsumed, answering_step c h taken]
  have hdn : discardRequested ((resetConsumed c).next h').2.1 = false := by
    rw [discardRequested_next, discardRequested_resetConsumed, hds]
  have hrn : relexRequested ((resetConsumed c).next h').2.1 = false := by
    rw [relexRequested_next, relexRequested_resetConsumed, hrl]
  have hsame := same_of_resetConsumed (next_resetConsumed c h)
  have hentries : taken.map entryOf ++ [entryAt c (c.peek h)] =
      (taken ++ [handedAt c (c.peek h)]).map entryOf := by
    rw [List.map_append, List.map_singleton, entryOf_handedAt]
  cases hcat : (c.category (c.peek h) == .endOfFile)
  · simp only [Bool.false_eq_true, ite_false]
    rw [show ((resetConsumed c).next h').2 =
      ⟨((resetConsumed c).next h').2.1, ((resetConsumed c).next h').2.2⟩ from rfl,
      afterCallW_continue _ _ _ _ hdn hrn, modifyCore_bind_runW]
    rw [flushCursor_congrW (next_resetConsumed c h)]
    by_cases hn : (c.next h).2.1.HasNext
    · simp only [hn, ↓reduceDIte]
      have := ih o (c.next h).2.1 ((c.next h).2.2.follows.trans hq) hn
        (Nat.lt_of_lt_of_le (c.next h).2.2.remaining_lt (Nat.le_of_lt_succ hr))
        (by rw [relexRequested_next, hrl]) (by rw [discardRequested_next, hds]) hfo
        (fun p hp => Token.BatchCursor.endsAfter_resetConsumed
          ((c.next h).2.2.follows.endsAfter ((hq.endsAfter (hfo p hp)))))
        ⟨{ s.val with version := ((resetConsumed c).next h').2.1.version }, s.property⟩ hhold a b
        (taken ++ [handedAt c (c.peek h)])
      rw [List.map_append, List.map_singleton, entryOf_handedAt, afterCallW_run_version] at this
      exact this
    · simp only [hn, ↓reduceDIte]
      have hn' : ¬ (resetConsumed (c.next h).2.1).HasNext := hn
      rw [afterCallW_continue _ _ _ _ (by rw [discardRequested_next, hds])
        (by rw [relexRequested_next, hrl]), modifyCore_bind_runW, flushCursor_empty_runW _ _ hn',
        flushCursor_empty_runW _ _ hn']
      exact ⟨rfl, rfl, hentries⟩
  · simp only [ite_true]
    rw [show ((resetConsumed c).next h').2 =
      ⟨((resetConsumed c).next h').2.1, ((resetConsumed c).next h').2.2⟩ from rfl,
      afterCallW_break _ _ _ _ hdn,
      afterCallW_break (R := concreteCollector.Result) (E := Option concreteCollector.Error)
        _ _ _ _ (by rw [discardRequested_next, hds]) (() : concreteCollector.Result),
      modifyCore_bind_runW, modifyCore_bind_runW]
    obtain ⟨hhas, hspan, hcons, -, -, hver, -, hfold⟩ := hsame
    have hstate : ∀ x y : Token.BatchCursor g, x.version = y.version →
        (∀ init, depthAfterW x init = depthAfterW y init) →
        stopState (floor := floor) (low := low) x
            ⟨{ s.val with version := x.version }, s.property⟩ =
          stopState y ⟨{ s.val with version := y.version }, s.property⟩ := by
      intro x y hv hd
      unfold stopState
      rw [hv, hd]
    have hd : ∀ init, depthAfterW ((resetConsumed c).next h').2.1 init =
        depthAfterW (c.next h).2.1 init := fun init => hfold _ _
    by_cases hn : (c.next h).2.1.HasNext
    · have hnX := hhas.mpr hn
      simp only [hn, hnX, ↓reduceDIte]
      rw [stopWith_runW, stopWith_runW]
      refine ⟨⟨?_, hspan hnX hn, rfl⟩, hstate _ _ hver hd, hentries⟩
      simp only [trailingAt, hspan hnX hn]
    · have hnX : ¬ ((resetConsumed c).next h').2.1.HasNext := fun hx => hn (hhas.mp hx)
      simp only [hn, hnX, ↓reduceDIte]
      rw [stopWith_runW, stopWith_runW]
      obtain ⟨hs1, hs2⟩ := hcons ((resetConsumed c).next h').2.2
        ((c.next h).2.2.trans_follows hq)
      exact ⟨⟨hs2, hs1, rfl⟩, hstate _ _ hver hd, hentries⟩

end

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] {floor : Option Nat} {low : Nat}

theorem flushCursor_holding_runW {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → EndsAfter cursor p) (h : cursor.HasNext)
    (s : {c : Lexer.Internal.WRustPort.LexerCore // c.Bound floor low})
    (hh : s.val.holding = true) (handler : H) :
    ((Rust.flushCursor (m := m) (R := R) (E := E) cursor hfloor).run.run s).run handler =
      pure ((.error (trailingAt (cursor.span (cursor.peek h))), stopState cursor s), handler) := by
  rw [← stopWith_runW (m := m) cursor _ s handler, flushCursor_eqW]
  simp only [h, ↓reduceDIte]
  have hg : ∀ {σ : Type} {n : Type → Type} [Monad n] (x : σ),
      (StateT.get : StateT σ n σ).run x = pure (x, x) := fun _ => rfl
  simp [getCore, ExceptT.run_bind, getThe, MonadStateOf.get, hg, StateT.run_bind, hh]

end

section

variable {floor : Option Nat} {low : Nat}

/-- The Rust port's handovers of a new cursor to the two consumers are related. -/
theorem flushNew_simW (version : Token.Version) (batch : Token.Internal.TokenBatch)
    (hf : ∀ p, floor = some p → EndsAfter (Token.BatchCursor.Internal.new version batch) p) :
    LSim link (· = ·)
      (Rust.flushCursor (H := Collector) (m := CollectM) (R := Unit) (E := Empty)
        (low := low) (Token.BatchCursor.Internal.new version batch) hf)
      (Rust.flushCursor (H := Answering concreteCollector) (m := AnswerM)
        (R := concreteCollector.Result) (E := Option concreteCollector.Error)
        (Token.BatchCursor.Internal.new version batch) hf) := by
  intro s a b taken
  by_cases hn : (Token.BatchCursor.Internal.new version batch).HasNext
  · by_cases hh : s.val.holding = true
    · rw [flushCursor_holding_runW _ _ hn s hh, flushCursor_holding_runW _ _ hn s hh]
      exact ⟨⟨⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩
    · have hhold : s.val.holding = false := by simpa using hh
      have hm := flush_mainW _ (Token.BatchCursor.Internal.new version batch)
        (Token.BatchCursor.Internal.new version batch)
        (Token.BatchCursor.Internal.Follows.refl _) hn
        (Nat.lt_succ_self _) (relexRequested_new version batch)
        (discardRequested_new version batch) hf
        (by rw [new_resetConsumed]; exact hf) s hhold a b taken
      rw [flushCursor_congrW (new_resetConsumed version batch) _ hf] at hm
      rw [answering_flush_stepW _ hf hn s hhold b taken]
      exact ⟨⟨hm.1, hm.2.1⟩, hm.2.2⟩
  · rw [flushCursor_empty_runW _ _ hn, flushCursor_empty_runW _ _ hn]
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- The Rust port hands a batch over to the collector and to the adapter's consumer for the
concrete collector alike. -/
theorem consumersW : BSmtLib.Facts.Proofs.Reader.ParamW.HandOver.ConsumersW link :=
  ⟨rfl, fun version batch hfloor => flushNew_simW version batch hfloor⟩

end

end BSmtLib.Facts.Proofs.PublicApi.CollectorW
