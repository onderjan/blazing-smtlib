module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Slice
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Taken
import all BSmtLib.Lexer.Error
import all BSmtLib.Lexer.Internal.Helpers
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.WRustPort.Slice
import all BSmtLib.Span

@[expose] public section

/-!
# The Rust port at the end of the input, with every consumer

`lexEofInner_eof`: the end of the input, from a lexer state that is the naive lexer's pure state
at a location, gives what `EofRes` states for what the consumer does there (`eofOut`): it
finishes the token in progress by the state's own check and hands it over, and then the
end-of-file token unless a result is held. The handler that the Rust port wraps the token's
hand-over in goes on after a relex and after a request to discard, which makes the lexer discard
(`wp_tryCatch`), and passes every other interruption on. With a consumer that does not take
whitespace and comments, the end of the input does not fail with the adapter's error `none`: the
consumer is handed no whitespace or comment (`Taken`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Eof

open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix.Lexeme BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Arms
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Batch
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Push
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Slice
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Taken BSmtLib.Lexer.Internal.VNaive

section

variable {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} {low : Nat} {α : Type}

/-- A step whose interruptions are caught by the handler. -/
theorem wp_tryCatch {x : WP.M C floor low α} {h : WP.Intr C floor → WP.M C floor low α}
    {s : WP.BS floor low}
    {coll : List Handed} {Q : α → WP.BS floor low → List Handed → Prop}
    {QE : WP.Intr C floor → WP.BS floor low → List Handed → Prop}
    (hx : WP x s coll Q fun e s' coll' => WP (h e) s' coll' Q QE) :
    WP (tryCatch x h) s coll Q QE := by
  unfold WP at hx ⊢
  have e : WP.runM (tryCatch x h) s coll =
      match WP.runM x s coll with
      | ((.ok a, s'), coll') => ((.ok a, s'), coll')
      | ((.error e, s'), coll') => WP.runM (h e) s' coll' := by
    simp only [WP.runM, tryCatch, tryCatchThe, MonadExcept.tryCatch, StateT.run_bind,
      MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.run, ExceptT.mk]
    generalize ((StateT.run x s).run {}).run coll = r
    obtain ⟨⟨⟨r, s'⟩, hh⟩, coll'⟩ := r
    rw [answering_eq' hh {}]
    cases r <;> rfl
  rw [e]
  generalize WP.runM x s coll = r at hx ⊢
  obtain ⟨⟨r, s'⟩, coll'⟩ := r
  cases r with
  | ok a => exact hx
  | error err => exact hx

end

theorem eof_stepLocation' {c c' : WP.WCore} {location : Span.Location} (h : EofLoc c location)
    (hl : c'.line = c.line) (hs : c'.lineStart = c.lineStart) :
    stepLocation c' c.offset 0 0 = location := by
  obtain ⟨h1, h2, h3⟩ := h
  apply Span.Location.ext <;>
    simp only [stepLocation, Span.Location.Internal.offset_new, Span.Location.Internal.line_new,
      Span.Location.Internal.column_new] at h1 h2 h3 ⊢ <;>
    omega

/-- The fields of the lexer state that the end of the input keeps. -/
structure EofSame (c c' : WP.WCore) : Prop where
  recovers : c'.recovers = c.recovers
  holding : c'.holding = c.holding
  discardedFrom : c'.discardedFrom = c.discardedFrom
  offset : c'.offset = c.offset
  line : c'.line = c.line
  lineStart : c'.lineStart = c.lineStart
  initial : c'.initialVersion = c.initialVersion

/-- The result the end of the input gives after the interruption. -/
def intrRes {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} (location : Span.Location)
    (e : WP.Intr C floor) : Except (PFailure C.Error)
    (ControlFlow (Span.Located C.Result)) :=
  match e.result with
  | .error kind => .error (preciseFailure kind e.span)
  | .ok .relex => .ok .continue
  | .ok (.discarded none) => .ok .continue
  | .ok (.finished r) => .ok (.break (Span.Located.Internal.new r location))
  | .ok (.discarded (some r)) => .ok (.break (Span.Located.Internal.new r location))

/-- No hand-over of at most one lexeme stops at a break with a lexeme after it. -/
theorem hand1_ne_brk {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {p p' : Prog} {l l0 : Lexeme}
    {r : C.Result} {nx : Option Lexeme} : hand1 C hd (.cont p) l ≠ .stop (.brk r l0 nx) p' := by
  intro h
  simp only [hand1] at h
  repeat' split at h
  all_goals cases h

section

variable {C : BSmtLibSpec.Lexer.Consumer}

/-- What the token in progress at the end of the input leaves when it goes on: the lexemes the
end finishes are handed over. -/
def PendQ (C : BSmtLibSpec.Lexer.Consumer) (hd : Bool) (c : WP.WCore) (coll : List Handed) (st : St)
    (location : Span.Location) (s' : WP.WCore) (coll' : List Handed) : Prop :=
  ∃ ls, finishLs C.concrete st location = some ls ∧
    pending C hd s'.version coll' [] = pending C hd c.version coll ls ∧ EofSame c s'

/-- What the token in progress at the end of the input leaves when it is interrupted: finishing
it fails, or the consumer stopped at it. -/
def PendQE (C : BSmtLibSpec.Lexer.Consumer) (hd : Bool) (c : WP.WCore) (coll : List Handed)
    (st : St)
    (location : Span.Location) (e : WP.Intr C none) (s' : WP.WCore) (coll' : List Handed) : Prop :=
  (finishLs C.concrete st location = none ∧ IsLexical e ∧ s'.version = c.version ∧
    EofSame c s' ∧ coll' = coll ∧ intrFailure e = finishFail C.concrete st location) ∨
  (∃ ls p d, finishLs C.concrete st location = some ls ∧ Stops C hd c.version coll ls e p d ∧
    (∃ B, StopState c p d s' B) ∧ coll' = p.taken)

/-- A stop of the consumer, after it has done `h`, at the interruption `e`, with `p` done and the
lexer discarding from `d` if `d` is some. -/
def StopsH (h : HandOut C) (e : WP.Intr C none) (p : Prog) (d : Option Span.Location) : Prop :=
  match h with
  | .cont _ => False
  | .wait r l p' => p = p' ∧ d = none ∧ Matches (.brk r l none) e
  | .stop st p' => p = p' ∧ d = st.discards ∧ Matches st e

/-- The lexeme the consumer failed at, if it stopped failing. -/
def hFailLex : HandOut C → Option Lexeme
  | .stop (.fail _ _ l) _ => some l
  | _ => none

/-- The lexeme the consumer failed at at the end of the input, if it stopped failing there. -/
def failLex (o : Option (HandOut C × Option Span.Location)) : Option Lexeme :=
  o.bind fun x => hFailLex x.1

/-- An error of the consumer at the end of the input has the span of the lexeme it failed at. -/
def EofErrSpan {floor : Option Nat} (o : Option (HandOut C × Option Span.Location))
    (e : WP.Intr C floor) : Prop :=
  ∀ x, e.result = .error (.consumer (some x)) → ∃ l, failLex o = some l ∧ e.span = Cursor.lexSpan l

theorem eofHand_failTaken (hd : Bool) (eof : Lexeme) {h : HandOut C} (hf : FailTaken C h) :
    FailTaken C (eofHand C hd eof h).1 := by
  have hc : ∀ p, FailTaken C (if hd then .cont p else hand1 C false (.cont p) eof) := by
    intro p
    cases hd
    · exact hand1_failTaken C false (failTaken_cont C p) eof
    · exact failTaken_cont C p
  rcases h with p | ⟨r, l, p⟩ | ⟨s, p⟩
  · exact hc p
  · exact hf
  · cases s with
    | relex l => exact hc p
    | discard r l => cases r with
      | none => exact hc p
      | some r => exact hf
    | _ => exact hf

/-- Where the consumer failed at the end of the input, the last token it took is that of the
lexeme it failed at. -/
theorem eofOut_failTaken {hd ws : Bool} {ver : Version} {coll : List Handed} {st : St}
    {location : Span.Location} {l : Lexeme}
    (h : failLex (eofOut C hd ws ver coll st location) = some l) :
    ∃ e b p d, eofOut C hd ws ver coll st location = some (.stop (.fail e b l) p, d) ∧
      ∃ x, p.taken.getLast? = some x ∧ x.start = toLocation l.start ∧
        x.end = toLocation l.end := by
  unfold failLex at h
  generalize ho : eofOut C hd ws ver coll st location = o at h ⊢
  have hft : ∀ h' d', o = some (h', d') → FailTaken C h' := by
    intro h' d' hh
    rw [← ho] at hh
    unfold eofOut at hh
    cases hfin : finishLs ws st location with
    | none => rw [hfin] at hh; cases hh
    | some ls =>
      rw [hfin] at hh
      simp only [Option.map_some, Option.some.injEq] at hh
      have := eofHand_failTaken (C := C) hd (eofLexeme location)
        (handAll_failTaken C hd ls (failTaken_cont C ⟨coll, ver⟩))
      have hh' : eofHand C hd (eofLexeme location) (handAll C hd (.cont ⟨coll, ver⟩) ls) =
          (h', d') := hh
      rw [hh'] at this
      exact this
  rcases o with _ | ⟨h', d'⟩
  · cases h
  · rcases h' with p | ⟨r, l0, p⟩ | ⟨s, p⟩
    · cases h
    · cases h
    · cases s with
      | fail e b l0 =>
        simp only [Option.bind_some, hFailLex, Option.some.injEq] at h
        subst h
        exact ⟨e, b, p, d', rfl, hft _ _ rfl e b l0 p rfl⟩
      | _ => cases h

/-- A stop at an error of the consumer has the span of the lexeme it failed at. -/
theorem stopsH_errSpan {h : HandOut C} {e : WP.Intr C none} {p : Prog} {d : Option Span.Location}
    (hs : StopsH h e p d) (d' : Option Span.Location) : EofErrSpan (some (h, d')) e := by
  intro x hx
  rcases h with p' | ⟨r, l, p'⟩ | ⟨s, p'⟩
  · exact hs.elim
  · obtain ⟨-, -, hm⟩ := hs
    rcases hm with ⟨h1, -⟩ | ⟨l2, -, h1, -⟩ <;> rw [hx] at h1 <;> cases h1
  · obtain ⟨-, -, hm⟩ := hs
    cases s with
    | fail err b l => exact ⟨l, rfl, hm.2⟩
    | trailing l => have := hm.1; rw [hx] at this; cases this
    | layout l => have := hm.1; rw [hx] at this; cases this
    | brk r l nx =>
      rcases hm with ⟨h1, -⟩ | ⟨l2, -, h1, -⟩ <;> rw [hx] at h1 <;> cases h1
    | brkX r l => have := hm.1; rw [hx] at this; cases this
    | discard r l => have := hm.1; rw [hx] at this; cases this
    | relex l => have := hm.1; rw [hx] at this; cases this

theorem stops_eq {hd : Bool} {ver : Version} {coll : List Handed} {ls : List Lexeme}
    {e : WP.Intr C none} {p : Prog} {d : Option Span.Location} :
    Stops C hd ver coll ls e p d = StopsH (pending C hd ver coll ls) e p d := rfl

/-- What the end of the input gives after an interruption that is not caught, where the
consumer stopped. -/
theorem tail_of_stops {h : HandOut C} {d d0 dd : Option Span.Location} {location : Span.Location}
    {e : WP.Intr C none} {p : Prog} {c' : WP.WCore} {coll' : List Handed} (hs : StopsH h e p dd)
    (hnobrk : ∀ r l nx p', h ≠ .stop (.brk r l nx) p')
    (hv : c'.version = p.ver) (hd : c'.discardedFrom = discardsAfter (d.or d0) dd)
    (hc : coll' = p.taken) :
    EofTail C h d d0 location (intrRes location e) c'.version c'.discardedFrom coll' := by
  subst hc
  obtain ⟨result, espan, eloc, stopAfter⟩ := e
  rcases h with p' | ⟨r, l, p'⟩ | ⟨s, p'⟩
  · exact hs.elim
  · obtain ⟨rfl, -, hm⟩ := hs
    rcases hm with ⟨h1, -⟩ | ⟨l2, h1, -⟩
    · simp only at h1
      subst h1
      exact ⟨rfl, rfl⟩
    · cases h1
  · obtain ⟨rfl, rfl, hm⟩ := hs
    cases s with
    | trailing l =>
      obtain ⟨h1, h2⟩ := hm
      have h2s : espan.start = l.start := by simp only at h2; rw [h2, Cursor.lexSpan_start]
      simp only at h1
      subst h1
      refine ⟨?_, hv, hd, rfl⟩
      simp only [intrRes, preciseFailure, lexicalKey, causeFailure, failureOf, stopFailure, h2s,
        Lexer.Error.LexerError.Internal.kind_new, Lexer.Error.LexerError.Internal.span_new]
      rfl
    | fail err b l =>
      obtain ⟨hm, -⟩ := hm
      subst hm
      exact ⟨rfl, hv, hd, rfl⟩
    | layout l =>
      obtain ⟨hm, -⟩ := hm
      subst hm
      exact ⟨rfl, hv, hd, rfl⟩
    | brk r l nx => exact absurd rfl (hnobrk r l nx p)
    | brkX r l =>
      obtain ⟨h1, -⟩ := hm
      simp only at h1
      subst h1
      exact ⟨rfl, rfl⟩
    | discard r l =>
      obtain ⟨h1, -⟩ := hm
      simp only at h1
      subst h1
      cases r <;> exact ⟨rfl, rfl⟩
    | relex l =>
      obtain ⟨h1, -⟩ := hm
      simp only at h1
      subst h1
      exact ⟨rfl, rfl⟩


end

section

variable {C : BSmtLibSpec.Lexer.Consumer}

/-- What running a call from the lexer state and the tokens taken gives; the consumer itself has
no state. -/
def runIA {α : Type} (x : Lexer.Internal.WRustPort.InnerM (Answering C) AnswerM α) (c : WP.WCore)
    (coll : List Handed) : (α × WP.WCore) × List Handed :=
  ((((x.run c).run {}).run coll).1.1, (((x.run c).run {}).run coll).2)

/-- The result of the end of the input before it is located, in the formalism's form. -/
def innerRes (location : Span.Location) :
    Except (Lexer.Internal.Failure (Option C.Error)) (ControlFlow C.Result) →
      Except (PFailure C.Error) (ControlFlow (Span.Located C.Result))
  | .ok .continue => .ok .continue
  | .ok (.break r) => .ok (.break (Span.Located.Internal.new r location))
  | .error f => .error (preciseFailure f.kind f.span)

/-- The fields of the lexer state that say where it is, kept, with the version it was created
with and whether it recovers. -/
structure LocKeep (c c' : WP.WCore) : Prop where
  offset : c'.offset = c.offset
  line : c'.line = c.line
  lineStart : c'.lineStart = c.lineStart
  initial : c'.initialVersion = c.initialVersion
  recovers : c'.recovers = c.recovers

/-- What the step at the end of the input leaves: the result, the version and discarding, the
tokens taken, as `EofRes` says, and the location kept. -/
def EofFin (C : BSmtLibSpec.Lexer.Consumer) (c : WP.WCore) (coll : List Handed) (st : St)
    (location : Span.Location)
    (res : Except (PFailure C.Error) (ControlFlow (Span.Located C.Result)))
    (c' : WP.WCore)
    (coll' : List Handed) : Prop :=
  EofRes C (eofOut C c.holding C.concrete c.version coll st location) c.discardedFrom c.version
    coll location (finishFail C.concrete st location) res c'.version c'.discardedFrom coll' ∧
    LocKeep c c'

theorem run_bindA {α β : Type} (y : StateT (Answering C) AnswerM α)
    (k : α → StateT (Answering C) AnswerM β) (coll : List Handed) :
    (y >>= k) {} coll = k (y {} coll).1.1 {} (y {} coll).2 := by
  have e : (y >>= k) {} coll = (match y {} coll with | ((a, h), t) => k a h t) := rfl
  rw [e]
  generalize y {} coll = r
  obtain ⟨⟨a, h⟩, t⟩ := r
  rw [answering_eq' h {}]

theorem eofLocAt {c : WP.WCore} {location : Span.Location} (h : EofLoc c location) :
    LocAt c c.offset c.base c.base location := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [h1]; omega, h2, h3⟩

theorem finishLs_short {ws : Bool} {st : St} {location : Span.Location} {ls : List Lexeme}
    (h : finishLs ws st location = some ls) : ls = [] ∨ ∃ l, ls = [l] := by
  unfold finishLs at h
  split at h
  · cases h; exact .inl rfl
  · split at h
    · cases h; exact .inl rfl
    · cases h; exact .inr ⟨_, rfl⟩
    · cases h

set_option hygiene false in
/-- The digits of a hexadecimal or binary literal at the end of the input, in the proof of
`lexEofInner_eof`. -/
local macro "eof_digits" : tactic => `(tactic| (
  unfold Lexer.Internal.WRustPort.finishDigitRun
  apply WP.wp_bind; apply WP.wp_getCore
  dsimp only
  apply WP.wp_ite
  · intro hbad
    unfold Lexer.Internal.WRustPort.error Lexer.Internal.WRustPort.errorWith
    wp_walk
    have he : (contentBytes c.tokenContent).isEmpty = true := by
      unfold ByteArray.isEmpty; rw [size_contentBytes (token_fits hagree)]; exact hbad
    refine .inl ⟨?_, ⟨_, rfl, nofun⟩, rfl, hsame, rfl, ?_⟩
    simp [finishLs, Lexer.Internal.VNaive.finish, he]
    simp only [finishFail, Lexer.Internal.VNaive.finish, he, ↓reduceIte]
    failure_eq (eofLocAt (show EofLoc c1 location from hloc))
  · intro hgood
    refine hsink _ _ (token_fits hagree) ?_
    have he : (contentBytes c.tokenContent).isEmpty = false := by
      unfold ByteArray.isEmpty; rw [size_contentBytes (token_fits hagree)]
      exact Bool.eq_false_iff.mpr hgood
    simp [finishLs, Lexer.Internal.VNaive.finish, he]
    rfl))

set_option maxHeartbeats 800000 in
theorem lexEofInner_eof (v : Version) (c : WP.WCore) (coll : List Handed) (st : St)
    (location : Span.Location) (hrec : c.recovers = false) (hagree : StAgrees v C.concrete st c)
    (hloc : EofLoc c location) :
    EofFin C c coll st location
      (innerRes location (runIA (Lexer.Internal.WRustPort.lexEofInner (H := Answering C)
          (m := AnswerM)
        (R := C.Result) (E := Option C.Error)) c coll).1.1)
      (runIA (Lexer.Internal.WRustPort.lexEofInner (H := Answering C) (m := AnswerM)
        (R := C.Result) (E := Option C.Error)) c coll).1.2
      (runIA (Lexer.Internal.WRustPort.lexEofInner (H := Answering C) (m := AnswerM)
        (R := C.Result) (E := Option C.Error)) c coll).2 ∧
    (C.concrete = false → ∀ f, (runIA (Lexer.Internal.WRustPort.lexEofInner (H := Answering C)
      (m := AnswerM) (R := C.Result) (E := Option C.Error)) c coll).1.1 = .error f →
      f.kind ≠ .consumer none) ∧
    (∀ f, (runIA (Lexer.Internal.WRustPort.lexEofInner (H := Answering C)
      (m := AnswerM) (R := C.Result) (E := Option C.Error)) c coll).1.1 = .error f →
      ∀ x, f.kind = .consumer (some x) → ∃ l,
        failLex (eofOut C c.holding C.concrete c.version coll st location) = some l ∧
        f.span = Cursor.lexSpan l) := by
  unfold runIA Lexer.Internal.WRustPort.lexEofInner
  simp -zeta only [WP.rust_eofBatch, StateT.run]
  extract_lets c1 tokenStart offset pend step
  have hp : ∀ s : WP.BS none offset, s.val = c1 →
      WP pend s coll (fun _ s' coll' => PendQ C c.holding c coll st location s'.val coll')
        (fun e s' coll' => PendQE C c.holding c coll st location e s'.val coll') := by
    intro s hs
    obtain ⟨sv, sp⟩ := s
    simp only at hs
    subst hs
    have hsame : EofSame c c1 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    -- a token handed over at the end of the input
    have hsink : ∀ (ty : Token.TokenCategory) (h : Lexer.Internal.WRustPort.Started none offset
        tokenStart),
        Fits c.tokenContent →
        finishLs C.concrete st location =
          some [⟨ty, contentBytes c.tokenContent, c.tokenStart, location⟩] →
        WP (Lexer.Internal.WRustPort.sinkStored (H := Answering C) (m := AnswerM) (R := C.Result)
          (E := Option C.Error) ty .EOF tokenStart 0 h) ⟨c1, sp⟩ coll
          (fun _ s' coll' => PendQ C c.holding c coll st location s'.val coll')
          (fun e s' coll' => PendQE C c.holding c coll st location e s'.val coll') := by
      intro ty h hfits hfin
      have e1 : stepLocation c1 c.offset 0 0 = location := eof_stepLocation' hloc rfl rfl
      refine sinkStored_wp ty .EOF tokenStart 0 h [] ⟨c1, sp⟩ (holds_clear _ _) coll
        hrec hfits ?_ ?_
      · intro s' coll' hk hb hc
        obtain ⟨⟨k1, k1'⟩, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
        simp only [Prod.mk.injEq] at k3
        refine ⟨_, hfin, ?_, ⟨k4, k3.2, k3.1, k8, k10, k11, k1'⟩⟩
        rw [hc]
        show pending C c.holding c.version coll ([] ++ [⟨ty, contentBytes c.tokenContent,
          c.tokenStart, stepLocation c1 c.offset 0 0⟩]) = _
        rw [e1]
        rfl
      · intro e s' p d hs hss
        refine .inr ⟨_, p, d, hfin, ?_, ⟨_, ⟨hss.1, hss.2, hss.3, hss.4, hss.5, hss.6, hss.7, hss.8,
          hss.9, hss.10, hss.11⟩⟩, rfl⟩
        have hs' : Stops C c.holding c.version coll ([] ++ [⟨ty, contentBytes c.tokenContent,
          c.tokenStart, stepLocation c1 c.offset 0 0⟩]) e p d := hs
        rw [e1] at hs'
        exact hs'
    unfold pend
    cases st with
    | idle =>
      split
      next =>
        exact WP.wp_pure _ ⟨[], rfl, rfl, hsame⟩
      all_goals
        exfalso
        have h := ‹c1.state = _›
        rw [show c1.state = c.state from rfl, show c.state = .normal from hagree] at h
        cases h
    | token p =>
      split
      next =>
        exfalso
        obtain ⟨-, h⟩ := token_agrees hagree ‹c1.state = _›
        exact h
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        exact hsink _ _ (token_fits hagree) rfl
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.Internal.WRustPort.finishDecimal
        apply WP.wp_bind; apply WP.wp_getCore
        dsimp only
        apply WP.wp_ite
        · intro hbad
          have hbad' : ((lastOf (contentBytes c.tokenContent)).isNone ||
              lastOf (contentBytes c.tokenContent) == some 46) = true := by
            rw [← last?_stored (token_fits hagree)]; exact hbad
          unfold Lexer.Internal.WRustPort.error Lexer.Internal.WRustPort.errorWith
          wp_walk
          refine .inl ⟨?_, ⟨_, rfl, nofun⟩, rfl, hsame, rfl, ?_⟩
          simp only [finishLs, Lexer.Internal.VNaive.finish, hbad', Bool.not_true,
              Bool.false_eq_true,
            ↓reduceIte]
          simp only [finishFail, Lexer.Internal.VNaive.finish, hbad', Bool.not_true,
            Bool.false_eq_true, ↓reduceIte]
          failure_eq (eofLocAt (show EofLoc c1 location from hloc))
        · intro hgood
          have hgood' : ((lastOf (contentBytes c.tokenContent)).isNone ||
              lastOf (contentBytes c.tokenContent) == some 46) = false := by
            rw [← last?_stored (token_fits hagree)]; exact Bool.eq_false_iff.mpr hgood
          refine hsink _ _ (token_fits hagree) ?_
          simp only [finishLs, Lexer.Internal.VNaive.finish, hgood', Bool.not_false, ↓reduceIte]
      next =>
        obtain ⟨hps, hm, hcont, -⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        exact hsink _ _ (token_fits hagree) rfl
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        eof_digits
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        eof_digits
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.Internal.WRustPort.error Lexer.Internal.WRustPort.errorWith
        wp_walk
        refine .inl ⟨rfl, ⟨_, rfl, nofun⟩, rfl, hsame, rfl, ?_⟩
        simp only [finishFail, Lexer.Internal.VNaive.finish]
        failure_eq (eofLocAt (show EofLoc c1 location from hloc))
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.Internal.WRustPort.error Lexer.Internal.WRustPort.errorWith
        wp_walk
        refine .inl ⟨?_, ⟨_, rfl, nofun⟩, rfl, hsame, rfl, ?_⟩
        rcases Bool.eq_false_or_eq_true (v == .v2_0) with hv | hv <;>
          simp [finishLs, Lexer.Internal.VNaive.finish, hv]
        rcases Bool.eq_false_or_eq_true (v == .v2_0) with hv | hv <;>
          simp only [finishFail, Lexer.Internal.VNaive.finish, hv, Bool.false_eq_true,
            ↓reduceIte] <;>
          failure_eq (eofLocAt (show EofLoc c1 location from hloc))
      next =>
        obtain ⟨hps, -, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.Internal.WRustPort.error Lexer.Internal.WRustPort.errorWith
        wp_walk
        refine .inl ⟨rfl, ⟨_, rfl, nofun⟩, rfl, hsame, rfl, ?_⟩
        simp only [finishFail, Lexer.Internal.VNaive.finish]
        failure_eq (eofLocAt (show EofLoc c1 location from hloc))
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.Internal.WRustPort.finishStringLiteral
        exact hsink _ _ (token_fits hagree) (by
          rcases Bool.eq_false_or_eq_true (v == .v2_0) with hv | hv <;>
            simp [finishLs, Lexer.Internal.VNaive.finish, hv])
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.Internal.WRustPort.finishSimpleSymbol
        exact hsink _ _ (token_fits hagree) rfl
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.Internal.WRustPort.finishKeyword
        apply WP.wp_bind; apply WP.wp_getCore
        dsimp only
        apply WP.wp_ite
        · intro hbad
          unfold Lexer.Internal.WRustPort.error Lexer.Internal.WRustPort.errorWith
          wp_walk
          have he : (contentBytes c.tokenContent).isEmpty = true := by
            unfold ByteArray.isEmpty; rw [size_contentBytes (token_fits hagree)]; exact hbad
          refine .inl ⟨?_, ⟨_, rfl, nofun⟩, rfl, hsame, rfl, ?_⟩
          simp [finishLs, Lexer.Internal.VNaive.finish, he]
          simp only [finishFail, Lexer.Internal.VNaive.finish, he, ↓reduceIte]
          failure_eq (eofLocAt (show EofLoc c1 location from hloc))
        · intro hgood
          refine hsink _ _ (token_fits hagree) ?_
          have he : (contentBytes c.tokenContent).isEmpty = false := by
            unfold ByteArray.isEmpty; rw [size_contentBytes (token_fits hagree)]
            exact Bool.eq_false_iff.mpr hgood
          simp [finishLs, Lexer.Internal.VNaive.finish, he]
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.Internal.WRustPort.error Lexer.Internal.WRustPort.errorWith
        wp_walk
        refine .inl ⟨rfl, ⟨_, rfl, nofun⟩, rfl, hsame, rfl, ?_⟩
        simp only [finishFail, Lexer.Internal.VNaive.finish]
        failure_eq (eofLocAt (show EofLoc c1 location from hloc))
      next =>
        obtain ⟨hps, -, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        exact hsink _ _ (token_fits hagree) rfl
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm
        subst hm hps
        unfold Lexer.Internal.WRustPort.consumesWhitespaceAndComments
        apply WP.wp_bind; apply WP.wp_pure
        simp only [answering_concrete]
        by_cases hcon : C.concrete = true
        · simp only [hcon, ite_true]
          have hc := hcont hcon
          simp only at hc
          subst hc
          exact hsink _ _ (token_fits hagree) (by simp [finishLs, Lexer.Internal.VNaive.finish,
              hcon])
        · simp only [hcon, Bool.false_eq_true, ite_false]
          exact WP.wp_pure _
              ⟨[], by simp [finishLs, Lexer.Internal.VNaive.finish, hcon], rfl, hsame⟩
  -- the end-of-file token, after the token in progress
  have hrest : ∀ (s' : WP.BS none offset) (p : Prog) (d : Option Span.Location),
      s'.val.version = p.ver → s'.val.holding = c.holding → s'.val.recovers = false →
      s'.val.discardedFrom = d.or c.discardedFrom → LocKeep c s'.val →
      eofOut C c.holding C.concrete c.version coll st location =
        some (if c.holding then .cont p else hand1 C false (.cont p) (eofLexeme location), d) →
      WP (do
          let __x ← Lexer.Internal.WRustPort.startToken (H := Answering C) (m := AnswerM)
            (R := C.Result) (E := Option C.Error) (floor := none) (low := offset) offset 0 0
            ⟨Nat.le_refl _, fun _ h => nomatch h⟩
          Lexer.Internal.WRustPort.Ops.sinkEof __x.val) s' p.taken
        (fun _ s2 coll2 => EofFin C c coll st location (.ok .continue) s2.val coll2)
        (fun e s2 coll2 => EofFin C c coll st location (intrRes location e) s2.val coll2 ∧
          (C.concrete = false → e.result ≠ .error (.consumer none)) ∧
          EofErrSpan (eofOut C c.holding C.concrete c.version coll st location) e) := by
    intro s' p d hv hh hr hd hkeep ho
    unfold Lexer.Internal.WRustPort.startToken Lexer.Internal.WRustPort.modifyContent
    apply WP.wp_bind
    apply WP.wp_bind; apply WP.wp_getCore
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_bind; apply WP.wp_modifyCore
    apply WP.wp_pure
    dsimp only
    have hl : Span.Location.Internal.new (offset + (0 - 0)) s'.val.line
        (offset + (0 - 0) - s'.val.lineStart) = location := by
      obtain ⟨h1, h2, h3⟩ := hloc
      apply Span.Location.ext
      · rw [Span.Location.Internal.offset_new]; show c.offset + 0 = _; omega
      · rw [Span.Location.Internal.line_new, hkeep.line, h2]
      · rw [Span.Location.Internal.column_new]
        show c.offset + 0 - s'.val.lineStart = _
        rw [hkeep.lineStart]
        omega
    refine sinkEof_wp _ _ p.taken (by exact hr) ?_ ?_ ?_
    · intro hh'
      have hc : c.holding = true := hh.symm.trans hh'
      refine ⟨?_, ⟨hkeep.offset, hkeep.line, hkeep.lineStart, hkeep.initial, hkeep.recovers⟩⟩
      rw [ho]
      simp only [hc, ite_true]
      exact ⟨rfl, rfl⟩
    · intro hh' p' hc
      dsimp only at hc
      rw [hl] at hc
      have hc' : c.holding = false := hh.symm.trans hh'
      refine ⟨?_, ⟨hkeep.offset, hkeep.line, hkeep.lineStart, hkeep.initial, hkeep.recovers⟩⟩
      rw [ho]
      simp only [hc', Bool.false_eq_true, ite_false]
      have : hand1 C false (.cont p) (eofLexeme location) = .cont p' := by
        rw [← hc]
        simp only [pending, handAll, List.foldl, hv]
      rw [this]
      exact ⟨rfl, rfl⟩
    · intro hh' e p' d' hs
      dsimp only at hs
      rw [hl] at hs
      have hc' : c.holding = false := hh.symm.trans hh'
      rw [stops_eq] at hs
      have hs' : StopsH (hand1 C false (.cont p) (eofLexeme location)) e p' d' := by
        have e1 : pending C false s'.val.version p.taken [eofLexeme location] =
            hand1 C false (.cont p) (eofLexeme location) := by
          simp only [pending, handAll, List.foldl, hv]
        rw [← e1]
        exact hs
      refine ⟨⟨?_, ⟨hkeep.offset, hkeep.line, hkeep.lineStart, hkeep.initial, hkeep.recovers⟩⟩,
        fun _ hnone => ?_, ?_⟩
      · rw [ho]
        simp only [hc', Bool.false_eq_true, ite_false]
        exact tail_of_stops hs' (fun _ _ _ _ h => hand1_ne_brk h) rfl
          (by show discardsAfter _ d' = _; rw [hd]) rfl
      · have hone : ∀ l q, hand1 C false (.cont p) (eofLexeme location) ≠
            .stop (.layout l) q := by
          have heof : ∀ x ∈ [eofLexeme location], (Taken x) := by
            intro x hx
            simp only [List.mem_singleton] at hx
            subst hx
            rfl
          exact handAll_ne_layout false [eofLexeme location] heof (.cont p) (fun _ _ => nofun)
        generalize hand1 C false (.cont p) (eofLexeme location) = h1 at hs' hone
        rcases h1 with q | ⟨r, l, q⟩ | ⟨s, q⟩
        · exact hs'
        · obtain ⟨-, -, hm⟩ := hs'
          obtain ⟨l', hl'⟩ := matches_none hm hnone
          cases hl'
        · obtain ⟨-, -, hm⟩ := hs'
          obtain ⟨l', rfl⟩ := matches_none hm hnone
          exact hone l' q rfl
      · rw [ho]
        simp only [hc', Bool.false_eq_true, ite_false]
        exact stopsH_errSpan hs' _
  have hstep : ∀ s : WP.BS none offset, s.val = c1 →
      WP step s coll (fun _ s' coll' => EofFin C c coll st location (.ok .continue) s'.val coll')
        (fun e s' coll' => EofFin C c coll st location (intrRes location e) s'.val coll' ∧
          (C.concrete = false → e.result ≠ .error (.consumer none)) ∧
          EofErrSpan (eofOut C c.holding C.concrete c.version coll st location) e) := by
    intro s hs
    unfold step
    apply WP.wp_bind
    apply wp_tryCatch
    refine WP.wp_mono (hp s hs) (fun _ s' coll' h => ?_) (fun e s' coll' h => ?_)
    · obtain ⟨ls, hfin, hc, hsame⟩ := h
      rw [pending_nil] at hc
      refine hrest s' ⟨coll', s'.val.version⟩ none rfl hsame.holding
        (hsame.recovers.trans hrec) (by rw [hsame.discardedFrom]; rfl)
        ⟨hsame.offset, hsame.line, hsame.lineStart, hsame.initial, hsame.recovers⟩ ?_
      simp only [eofOut, hfin, Option.map_some, ← hc, eofHand]
    · rcases h with ⟨hfin, ⟨err, he, hk⟩, hv, hsame, rfl, hfl⟩ |
        ⟨ls, p, d, hfin, hs', ⟨B, hss⟩, rfl⟩
      · obtain ⟨result, espan, eloc, stopAfter⟩ := e
        simp only at he
        subst he
        apply WP.wp_throw
        refine ⟨⟨?_, ⟨hsame.offset, hsame.line, hsame.lineStart, hsame.initial, hsame.recovers⟩⟩,
          fun _ => nofun, fun x hx => by cases hx⟩
        simp only [EofRes, eofOut, hfin, Option.map_none]
        refine ⟨?_, hv, hsame.discardedFrom, trivial⟩
        rw [← hfl]
        simp only [intrRes, preciseFailure_lexical hk]
        rfl
      · rw [stops_eq] at hs'
        have hkeep : LocKeep c s'.val := ⟨hss.offset, hss.line, hss.lineStart,
            hss.initial, hss.recovers⟩
        have hshort := finishLs_short hfin
        have hnobrk : ∀ r l nx p', pending C c.holding c.version coll ls ≠
            .stop (.brk r l nx) p' := by
          intro r l nx p' h
          rcases hshort with rfl | ⟨l1, rfl⟩
          · cases h
          · exact hand1_ne_brk h
        have ho : eofOut C c.holding C.concrete c.version coll st location =
            some (eofHand C c.holding (eofLexeme location)
              (pending C c.holding c.version coll ls)) := by
          simp only [eofOut, hfin, Option.map_some]
        generalize hh1 : pending C c.holding c.version coll ls = h1 at hs' hnobrk ho
        obtain ⟨result, espan, eloc, stopAfter⟩ := e
        -- an interruption the handler passes on
        have pass : (∀ l, h1 ≠ .stop (.relex l) p) → (∀ l, h1 ≠ .stop (.discard none l) p) →
            EofFin C c coll st location (intrRes location ⟨result, espan, eloc, stopAfter⟩) s'.val
              p.taken ∧
            EofErrSpan (eofOut C c.holding C.concrete c.version coll st location)
              ⟨result, espan, eloc, stopAfter⟩ := by
          intro hn1 hn2
          have he : eofHand C c.holding (eofLexeme location) h1 = (h1, none) := by
            rcases h1 with p' | ⟨r, l, p'⟩ | ⟨s, p'⟩
            · exact hs'.elim
            · rfl
            · obtain ⟨rfl, -, -⟩ := hs'
              cases s with
              | relex l => exact absurd rfl (hn1 l)
              | discard r l =>
                cases r with
                | none => exact absurd rfl (hn2 l)
                | some r => rfl
              | _ => rfl
          refine ⟨⟨?_, hkeep⟩, ?_⟩
          · rw [ho, he]
            exact tail_of_stops hs' hnobrk hss.version (by rw [hss.discardedFrom]; rfl) rfl
          · rw [ho, he]
            exact stopsH_errSpan hs' _
        rcases h1 with p' | ⟨r, l, p'⟩ | ⟨s, p'⟩
        · exact hs'.elim
        · obtain ⟨rfl, -, hm⟩ := hs'
          rcases hm with ⟨h1, -⟩ | ⟨l2, h1, -⟩
          · simp only at h1
            subst h1
            apply WP.wp_throw
            exact ⟨(pass nofun nofun).1, fun _ => nofun, (pass nofun nofun).2⟩
          · cases h1
        · obtain ⟨rfl, hdd, hm⟩ := hs'
          cases s with
          | relex l =>
            obtain ⟨h1, h2⟩ := hm
            simp only at h1 h2
            subst h1 h2
            apply WP.wp_pure
            refine hrest s' p none hss.version (hss.holding) (hss.recovers.trans hrec)
              (by rw [hss.discardedFrom, hdd]; rfl) hkeep ?_
            rw [ho]
            rfl
          | discard r l =>
            obtain ⟨h1, h2⟩ := hm
            simp only at h1 h2
            subst h1 h2
            cases r with
            | none =>
              apply WP.wp_modifyCore
              refine hrest _ p (some l.end) hss.version (hss.holding) (hss.recovers.trans hrec)
                rfl ⟨hss.offset, hss.line, hss.lineStart, hss.initial, hss.recovers⟩ ?_
              rw [ho]
              rfl
            | some r =>
              apply WP.wp_throw
              exact ⟨(pass nofun nofun).1, fun _ => nofun, (pass nofun nofun).2⟩
          | trailing l =>
            obtain ⟨h1, -⟩ := hm
            simp only at h1
            subst h1
            apply WP.wp_throw
            exact ⟨(pass nofun nofun).1, fun _ => nofun, (pass nofun nofun).2⟩
          | fail err b l =>
            obtain ⟨hm, -⟩ := hm
            subst hm
            apply WP.wp_throw
            exact ⟨(pass nofun nofun).1, fun _ => nofun, (pass nofun nofun).2⟩
          | layout l =>
            obtain ⟨hm, -⟩ := hm
            subst hm
            apply WP.wp_throw
            refine ⟨(pass nofun nofun).1, fun hc _ => ?_, (pass nofun nofun).2⟩
            have hst := st_taken (by rw [hc] at hagree; exact hagree)
            have hls := finishLs_taken hst (by rw [hc] at hfin; exact hfin)
            exact handAll_ne_layout c.holding ls hls (.cont ⟨coll, c.version⟩)
              (fun _ _ => nofun) l p hh1
          | brk r l nx => exact absurd rfl (hnobrk r l nx p)
          | brkX r l =>
            obtain ⟨h1, -⟩ := hm
            simp only at h1
            subst h1
            apply WP.wp_throw
            exact ⟨(pass nofun nofun).1, fun _ => nofun, (pass nofun nofun).2⟩
  have hw := hstep ⟨c1, ⟨Nat.le_refl _, fun _ h => nomatch h⟩⟩ rfl
  unfold WP at hw
  simp only [WP.runM, StateT.run] at hw
  rw [run_bindA]
  generalize ExceptT.run step ⟨c1, ⟨Nat.le_refl _, fun _ h => nomatch h⟩⟩ {} coll = r at hw ⊢
  obtain ⟨⟨⟨res, s'⟩, h'⟩, coll'⟩ := r
  cases res with
  | ok u => exact ⟨hw, fun _ f hf => (by cases hf), fun f hf => by cases hf⟩
  | error e =>
    obtain ⟨result, espan, eloc, stopAfter⟩ := e
    rcases result with kind | stp
    · refine ⟨hw.1, fun hc f hf => ?_, fun f hf x hx => ?_⟩
      · cases hf
        exact fun h => hw.2.1 hc (by simp only at h ⊢; rw [h])
      · cases hf
        exact hw.2.2 x (by simp only at hx ⊢; rw [hx])
    · rcases stp with _ | r | (_ | r) <;>
        exact ⟨hw.1, fun _ f hf => (by cases hf), fun f hf => by cases hf⟩

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Eof
