module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VOut
public import BSmtLib.Facts.Proofs.Lexer.Consumers.VWalk
import all BSmtLib.Lexer.Error
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Span

@[expose] public section

/-!
# What the naive lexer does with bytes, as the outcome of the pure run says

From a lexer state that is the pure run's state, the naive lexer, fed bytes with the adapter's
consumer, does what the outcome of the pure run over them says (`vBytes_out`): the consumer
takes the lexemes of the run one after another, as `hand1` says, under the version it is in.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VBytes

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.Consumers.VHold
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSession BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps
open BSmtLib.Facts.Proofs.Lexer.Consumers.VWalk BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VHand BSmtLib.Lexer.Error
open BSmtLib.Lexer.Internal.VNaive

section

variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool}

theorem handAll_wait (r : C.Result) (l : Lexeme) (p : Prog) : ∀ ls,
    handAll C hd (.wait r l p) ls = .wait r l p ∨
      ∃ nx, handAll C hd (.wait r l p) ls = .stop (.brk r l nx) p
  | [] => .inl rfl
  | l2 :: ls => .inr ⟨some l2, handAll_stop C hd (.brk r l (some l2)) p ls⟩

/-- After a break, the consumer waits for the next lexeme, which is trailing input. -/
theorem outcome_wait (r : C.Result) (l : Lexeme) (p : Prog) (ls : List Lexeme)
    (e : RunF) :
    ∃ nx, outcome C hd (handAll C hd (.wait r l p) ls) e = .stopped (.brk r l nx) p := by
  have hf : ∀ (ls' : List Lexeme) (k : Prog → Out C), ∃ nx,
      Model.finish C (handAll C hd (handAll C hd (.wait r l p) ls) ls') k =
        .stopped (.brk r l nx) p := by
    intro ls' k
    rw [← handAll_append]
    rcases handAll_wait (hd := hd) r l p (ls ++ ls') with h | ⟨nx, h⟩
    · exact ⟨none, by rw [h]; rfl⟩
    · exact ⟨nx, by rw [h]; rfl⟩
  cases e with
  | ok e => obtain ⟨st, loc, ls'⟩ := e; exact hf ls' _
  | error r => obtain ⟨ls', f⟩ := r; exact hf ls' _

/-- A lexeme the consumer goes on after keeps the lexical rules. -/
theorem hand1_cont_legacy {p p' : Prog} {l : Lexeme} (h : hand1 C hd (.cont p) l = .cont p') :
    (p'.ver == .v2_0) = (p.ver == .v2_0) := by
  simp only [hand1] at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h
  rename_i hcr
  revert hcr
  unfold crosses
  cases (p.ver == .v2_0) <;> cases (switchedTo p.ver _ == .v2_0) <;> simp

/-- A lexeme the consumer breaks at and then waits after keeps the lexical rules. -/
theorem hand1_wait_legacy {p p' : Prog} {l l' : Lexeme} {r : C.Result}
    (h : hand1 C hd (.cont p) l = .wait r l' p') : (p'.ver == .v2_0) = (p.ver == .v2_0) := by
  simp only [hand1] at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h
  all_goals
    rename_i hcr _
    revert hcr
    unfold crosses
    cases (p.ver == .v2_0) <;> cases (switchedTo p.ver _ == .v2_0) <;> simp

/-- After a break, the lexeme handed over next is trailing input, as it is while a result is
held. -/
theorem outcome_wait_trailing {r : C.Result} {l l2 : Lexeme} {p p' : Prog}
    {e : RunF}
    (h : outcome C hd (handAll C hd (.wait r l p) []) e = .stopped (.brk r l (some l2)) p') :
    outcome C true (.cont p) e = .stopped (.trailing l2) p' := by
  have key : ∀ (ls : List Lexeme) (k : Prog → Out C),
      Model.finish C (handAll C hd (.wait r l p) ls) k = .stopped (.brk r l (some l2)) p' →
      Model.finish C (handAll C true (.cont p) ls) k = .stopped (.trailing l2) p' := by
    intro ls k hk
    cases ls with
    | nil => cases hk
    | cons l3 ls =>
      have e1 : handAll C hd (.wait r l p) (l3 :: ls) = .stop (.brk r l (some l3)) p :=
        handAll_stop C hd _ p ls
      have e2 : handAll C true (.cont p) (l3 :: ls) = .stop (.trailing l3) p :=
        handAll_stop C true _ p ls
      rw [e1] at hk
      rw [e2]
      simp only [Model.finish, Out.stopped.injEq, Stop.brk.injEq, Option.some.injEq] at hk
      obtain ⟨⟨-, -, rfl⟩, rfl⟩ := hk
      rfl
  cases e with
  | ok e => obtain ⟨st, loc, ls⟩ := e; exact key ls _ h
  | error r => obtain ⟨ls, f⟩ := r; exact key ls _ h

theorem withBefore_withBefore (a b : List Lexeme)
    (e : RunF) :
    withBeforeF a (withBeforeF b e) = withBeforeF (a ++ b) e := by
  cases e with
  | ok e => obtain ⟨st, loc, ls⟩ := e; simp [withBeforeF]
  | error r => obtain ⟨ls, f⟩ := r; simp [withBeforeF]

theorem outcome_cont_one (hd : Bool) (p : Prog) (l : Lexeme)
    (e : RunF) :
    outcome C hd (.cont p) (withBeforeF [l] e) = outcome C hd (hand1 C hd (.cont p) l) e :=
  outcome_prep C hd (.cont p) [] [l] e

end

section

variable (C : BSmtLibSpec.Lexer.Consumer) (v : Version)

theorem lexBytesW_tokenBefore {ws : Bool} {p : Pending} {location : Span.Location} {b : UInt8}
    {l : Lexeme} (rest : List UInt8) (h : advance ws p location b = .tokenBefore l) :
    lexBytesF v ws (.token p) location (b :: rest) =
      withBeforeF [l] (lexBytesF v ws .idle location (b :: rest)) := by
  simp only [lexBytesF, byteStepW, h]
  cases hs : startStepW v ws location b with
  | none => simp [failedBeforeW, failW, h, withBeforeF]
  | some e =>
    obtain ⟨st', ls'⟩ := e
    simp only [Option.map_some]
    rw [withBefore_withBefore]
    rfl

theorem lexBytesW_idle_token {ws : Bool} {location : Span.Location} {b : UInt8} {l : Lexeme}
    (rest : List UInt8) (h : start v ws location b = .token l) :
    lexBytesF v ws .idle location (b :: rest) =
      withBeforeF [l] (lexBytesF v ws .idle (location.afterByte b) rest) := by
  simp only [lexBytesF, byteStepW, startStepW, h]

theorem lexBytesW_tokenWith {ws : Bool} {p : Pending} {location : Span.Location} {b : UInt8}
    {l : Lexeme} (rest : List UInt8) (h : advance ws p location b = .tokenWith l) :
    lexBytesF v ws (.token p) location (b :: rest) =
      withBeforeF [l] (lexBytesF v ws .idle (location.afterByte b) rest) := by
  simp only [lexBytesF, byteStepW, h]

theorem kind_ne {k : LexicalErrorKind} (h : (k == .unexpectedTrailingToken) = false) :
    k ≠ .unexpectedTrailingToken := by
  intro he
  rw [he] at h
  exact absurd h (by decide)

/-- The naive lexer fed bytes from a lexer state that is the pure run's state does what the
outcome of the pure run over them says. -/
theorem vBytes_out (bs : List UInt8) : ∀ (core : Core) (st : St)
    (held : Option (Span.Located C.Result)) (taken : List Handed),
    core.activity = st.activity → (core.version == .v2_0) = (v == .v2_0) →
    VOut C core held bs taken (outcome C core.holding (.cont ⟨taken, core.version⟩)
      (lexBytesF v C.concrete st core.location bs)) := by
  induction bs with
  | nil =>
    intro core st held taken hact _
    exact ⟨core, rfl, ⟨hact, rfl, rfl, rfl⟩, rfl⟩
  | cons b rest ih =>
    -- a lexeme that ends with the byte, handed over from `X`
    have caseA : ∀ (core X : Core) (held : Option (Span.Located C.Result)) (taken : List Handed)
        (l : Lexeme) (hl : l.Valid), (core.version == .v2_0) = (v == .v2_0) →
        X.activity = .idle → X.location = core.location.afterByte b →
        X.version = core.version → X.holding = core.holding →
        X.initialVersion = core.initialVersion → l.end = core.location.afterByte b →
        vByte C core b taken = vRun C (handOverAt (H := Answering C) X l hl) taken →
        VOut C core held (b :: rest) taken (outcome C core.holding
          (hand1 C core.holding (.cont ⟨taken, core.version⟩) l)
          (lexBytesF v C.concrete .idle (core.location.afterByte b) rest)) := by
      intro core X held taken l hl hver hXa hXl hXv hXh hXi hle hv
      have hH := handOverAt_hand1 C X l hl taken
      rw [hXv, hXh] at hH
      rw [← hv] at hH
      generalize hho : hand1 C core.holding (.cont ⟨taken, core.version⟩) l = ho at hH ⊢
      cases ho with
      | cont p' =>
        obtain ⟨c', hr, hs⟩ := hH
        have hvb : vBytes C core held (b :: rest) taken = vBytes C c' held rest p'.taken := by
          simp only [vBytes, hr]
        have hleg := hand1_cont_legacy hho
        have := ih c' .idle held p'.taken (hs.activity.trans hXa)
          (by rw [hs.version, hleg]; exact hver)
        rw [hs.holding, hXh, hs.version, hs.location, hXl] at this
        exact VOut.cons _ hvb (hs.holding.trans hXh) (hs.initial.trans hXi)
          (hs.location.trans hXl) this
      | wait r0 l0 p' =>
        obtain ⟨rfl, c', hr, hs⟩ := hH
        have hvb : vBytes C core held (b :: rest) taken =
            vBytes C c' (some (Span.Located.Internal.new r0 l0.end)) rest p'.taken := by
          simp only [vBytes, hr]
        have hih := ih c' .idle (some (Span.Located.Internal.new r0 l0.end)) p'.taken
          (hs.activity.trans hXa)
          (by rw [hs.version, hand1_wait_legacy hho]; exact hver)
        rw [hs.holding, hs.version, hs.location, hXl] at hih
        obtain ⟨nx, hnx⟩ := outcome_wait (hd := core.holding) r0 l0 p' []
          (lexBytesF v C.concrete .idle (core.location.afterByte b) rest)
        rw [show outcome C core.holding (.wait r0 l0 p') _ = _ from hnx]
        refine ⟨⟨1, c', hle, hs.activity.trans hXa, hs.location.trans (hXl.trans hle.symm),
          hs.version, hs.holding, hs.initial.trans hXi, ?_⟩, fun l2 hl2 => ?_⟩
        · simp only [vBytes, hr, List.drop_succ_cons, List.drop_zero]
        · subst hl2
          rw [outcome_wait_trailing hnx] at hih
          obtain ⟨c2, e, a1, a2, a3⟩ := hih
          exact ⟨c2, hvb.trans e, a1, a2.trans (hs.initial.trans hXi), a3⟩
      | stop s p' =>
        rw [outcome_stop]
        cases s with
        | trailing l0 =>
          obtain ⟨rfl, hpv, hr⟩ := hH
          refine ⟨X, ?_, hpv.symm, hXi, by rw [hXa]; nofun⟩
          simp only [vBytes, hr]
        | fail e d l0 =>
          obtain ⟨rfl, c', hr, hs⟩ := hH
          refine ⟨c', Span.Internal.newUnchecked l0.end l0.end, l0.end, ?_,
            hs.version, hs.initial.trans hXi,
            by unfold discardedOf; rw [hs.activity, hXa]; cases d <;> rfl⟩
          simp only [vBytes, hr]
        | layout l0 =>
          obtain ⟨rfl, c', hr, hs⟩ := hH
          refine ⟨c', Span.Internal.newUnchecked l0.end l0.end, l0.end, ?_,
            hs.version, hs.initial.trans hXi,
            by rw [hs.activity, hXa]; nofun⟩
          simp only [vBytes, hr]
        | brk _ _ _ => exact hH.elim
        | brkX r0 l0 =>
          obtain ⟨rfl, c', hr, hs⟩ := hH
          refine ⟨1, c', hle, hs.activity.trans hXa, hs.location.trans (hXl.trans hle.symm),
            hs.version, hs.holding, hs.initial.trans hXi, ?_⟩
          simp only [vBytes, hr, List.drop_succ_cons, List.drop_zero]
        | discard r0 l0 =>
          obtain ⟨rfl, c', hr, hs⟩ := hH
          cases r0 with
          | none =>
            obtain ⟨c2, h2, a1, a2, a3, a4, a5⟩ := vBytes_discarding C rest c' held p'.taken
              hs.activity
            refine ⟨c2, ?_, ⟨a2, a1.trans hs.version, ?_, a5.trans (hs.initial.trans hXi)⟩,
              a3.trans (hs.location.trans (hXl.trans hle.symm)), 1, hle⟩
            · simp only [vBytes, hr, Option.map_none]
              rw [h2]
              rfl
            · rw [a4, hs.holding, hXh]
          | some r0 =>
            obtain ⟨c2, h2, a1, a2, a3, a4, a5⟩ := vBytes_discarding C rest c'
              (some (Span.Located.Internal.new r0 l0.end)) p'.taken hs.activity
            refine ⟨c2, ?_, ⟨a2, a1.trans hs.version, ?_, a5.trans (hs.initial.trans hXi)⟩,
              a3.trans (hs.location.trans (hXl.trans hle.symm)), 1, hle⟩
            · simp only [vBytes, hr, Option.map_some]
              rw [h2]
              rfl
            · rw [a4, hs.holding, hXh]
        | relex l0 =>
          obtain ⟨rfl, c', hr, hs⟩ := hH
          refine ⟨1, c', hle, hs.activity.trans hXa, hs.location.trans (hXl.trans hle.symm),
            hs.version, hs.holding.trans hXh, hs.initial.trans hXi, ?_⟩
          simp only [vBytes, hr, List.drop_succ_cons, List.drop_zero]
    -- the byte with nothing in progress
    have caseIdle : ∀ (core : Core) (held : Option (Span.Located C.Result)) (taken : List Handed),
        core.activity = .idle → (core.version == .v2_0) = (v == .v2_0) →
        VOut C core held (b :: rest) taken (outcome C core.holding (.cont ⟨taken, core.version⟩)
          (lexBytesF v C.concrete .idle core.location (b :: rest))) := by
      intro core held taken hact hver
      have hst := VOut.startStepW_legacy hver
      have hsl := VOut.start_legacy hver
      have hvb := lexByte_idle C core b taken hact
      cases hs : start v C.concrete core.location b with
      | idle =>
        obtain ⟨c', h, a1, a2, a3, a4, a5⟩ := lexStart_none C core b taken (st := .idle)
          (by rw [hst]; simp [startStepW, hs])
        have := ih c' .idle held taken a2 (by rw [a1]; exact hver)
        rw [a1, a3, a4] at this
        have he : lexBytesF v C.concrete .idle core.location (b :: rest) =
            lexBytesF v C.concrete .idle (core.location.afterByte b) rest := by
          simp only [lexBytesF, byteStepW, startStepW, hs, withBeforeF_nil]
        rw [he]
        exact VOut.cons _ (by simp only [vBytes, hvb, h]) a4 a5 a3 this
      | pending p =>
        obtain ⟨c', h, a1, a2, a3, a4, a5⟩ := lexStart_none C core b taken (st := .token p)
          (by rw [hst]; simp [startStepW, hs])
        have := ih c' (.token p) held taken a2 (by rw [a1]; exact hver)
        rw [a1, a3, a4] at this
        have he : lexBytesF v C.concrete .idle core.location (b :: rest) =
            lexBytesF v C.concrete (.token p) (core.location.afterByte b) rest := by
          simp only [lexBytesF, byteStepW, startStepW, hs, withBeforeF_nil]
        rw [he]
        exact VOut.cons _ (by simp only [vBytes, hvb, h]) a4 a5 a3 this
      | token l =>
        obtain ⟨hl, h⟩ := lexStart_token C core b taken (by rw [hsl]; exact hs)
        rw [lexBytesW_idle_token v rest hs, outcome_cont_one]
        exact caseA core (idleAfter core b) held taken l hl hver rfl rfl rfl rfl rfl
          (start_token_span hs).2 (hvb.trans h)
      | error f =>
        have h := lexStart_error' C core b taken (by rw [hsl]; exact hs)
        have he : lexBytesF v C.concrete .idle core.location (b :: rest) =
            .error ([], f) := by
          simp only [lexBytesF, byteStepW, startStepW, hs, failW, startFail]
          rfl
        rw [he]
        exact ⟨core, by simp only [vBytes, hvb, h], kind_ne
          (start_error_kind hs), rfl, rfl, by rw [hact]; nofun⟩
    -- a lexeme that ends before the byte, handed over from `idleAt core`
    have caseB : ∀ (core : Core) (held : Option (Span.Located C.Result)) (taken : List Handed)
        (p : Pending) (l : Lexeme), core.activity = .token p →
        (core.version == .v2_0) = (v == .v2_0) →
        advance C.concrete p core.location b = .tokenBefore l →
        VOut C core held (b :: rest) taken (outcome C core.holding
          (hand1 C core.holding (.cont ⟨taken, core.version⟩) l)
          (lexBytesF v C.concrete .idle core.location (b :: rest))) := by
      intro core held taken p l hact hver hadv
      have hle := (advance_tokenBefore hadv).2
      obtain ⟨hl, hv⟩ := lexByte_tokenBefore C core b taken hact hadv
      have hH := handOverAt_hand1 C (idleAt core) l hl taken
      generalize hrr : vRun C (handOverAt (H := Answering C) (idleAt core) l hl) taken = rr
        at hH
      obtain ⟨⟨res, core2⟩, taken2⟩ := rr
      have hv := hv hrr
      change HandV C (idleAt core) l ((res, core2), taken2)
        (hand1 C core.holding (.cont ⟨taken, core.version⟩) l) at hH
      generalize hho : hand1 C core.holding (.cont ⟨taken, core.version⟩) l = ho at hH ⊢
      -- a result held: the byte is lexed again from `core2`, which gives no result
      have holdStep : ∀ (located : Span.Located C.Result), res = .ok (some located) →
          core2.activity = .idle → core2.holding = true →
          vBytes C core held (b :: rest) taken =
            vBytes C core2 (some located) (b :: rest) taken2 := by
        intro located hres ha2 hh2
        subst hres
        have hn := lexStart_holding C core2 b taken2 hh2
        rw [ha2] at hv
        simp only [vBytes, hv, lexByte_idle C core2 b taken2 ha2]
        generalize vRun C (lexStart (H := Answering C) core2 b) taken2 = q at hn
        obtain ⟨⟨q1, core3⟩, taken3⟩ := q
        cases q1 with
        | error f => rfl
        | ok y =>
          cases y with
          | none => rfl
          | some y => exact absurd rfl (hn y)
      cases ho with
      | cont p' =>
        obtain ⟨c', hr, hs⟩ := hH
        simp only [Prod.mk.injEq] at hr
        obtain ⟨⟨rfl, hc⟩, rfl⟩ := hr
        subst core2
        have ha : c'.activity = .idle := hs.activity
        rw [ha] at hv
        have hvb : vBytes C core held (b :: rest) taken = vBytes C c' held (b :: rest) p'.taken :=
          by simp only [vBytes, hv, lexByte_idle C c' b p'.taken ha]
        have := caseIdle c' held p'.taken ha
          (by rw [hs.version, hand1_cont_legacy hho]; exact hver)
        rw [hs.holding, hs.version, hs.location] at this
        exact VOut.same _ hvb hs.holding hs.initial hs.location this
      | wait r0 l0 p' =>
        obtain ⟨rfl, c', hr, hs⟩ := hH
        simp only [Prod.mk.injEq] at hr
        obtain ⟨⟨rfl, hc⟩, rfl⟩ := hr
        subst core2
        have hvb := holdStep _ rfl hs.activity hs.holding
        obtain ⟨nx, hnx⟩ := outcome_wait (hd := core.holding) r0 l0 p' []
          (lexBytesF v C.concrete .idle core.location (b :: rest))
        rw [show outcome C core.holding (.wait r0 l0 p') _ = _ from hnx]
        refine ⟨⟨0, c', hle, hs.activity, hs.location.trans hle.symm, hs.version, hs.holding,
          hs.initial, hvb⟩, fun l2 hl2 => ?_⟩
        subst hl2
        have hih := caseIdle c' (some (Span.Located.Internal.new r0 l0.end)) p'.taken hs.activity
          (by rw [hs.version, hand1_wait_legacy hho]; exact hver)
        rw [hs.holding, hs.version, hs.location, show (idleAt core).location = core.location from
          rfl] at hih
        rw [outcome_wait_trailing hnx] at hih
        obtain ⟨c2, e, a1, a2, a3⟩ := hih
        exact ⟨c2, hvb.trans e, a1, a2.trans hs.initial, a3⟩
      | stop s p' =>
        rw [outcome_stop]
        cases s with
        | trailing l0 =>
          obtain ⟨rfl, hpv, hr⟩ := hH
          simp only [Prod.mk.injEq] at hr
          obtain ⟨⟨rfl, hc⟩, rfl⟩ := hr
          subst core2
          refine ⟨idleAt core, ?_, hpv.symm, rfl, by simp [idleAt]⟩
          simp only [vBytes, hv]
        | fail e d l0 =>
          obtain ⟨rfl, c', hr, hs⟩ := hH
          simp only [Prod.mk.injEq] at hr
          obtain ⟨⟨rfl, hc⟩, rfl⟩ := hr
          subst core2
          refine ⟨c', Span.Internal.newUnchecked l0.end l0.end, l0.end, ?_,
            hs.version, hs.initial,
            by unfold discardedOf; rw [hs.activity]; cases d <;> rfl⟩
          simp only [vBytes, hv]
        | layout l0 =>
          obtain ⟨rfl, c', hr, hs⟩ := hH
          simp only [Prod.mk.injEq] at hr
          obtain ⟨⟨rfl, hc⟩, rfl⟩ := hr
          subst core2
          refine ⟨c', Span.Internal.newUnchecked l0.end l0.end, l0.end, ?_,
            hs.version, hs.initial, by rw [hs.activity]; simp [idleAt]⟩
          simp only [vBytes, hv]
        | brk _ _ _ => exact hH.elim
        | brkX r0 l0 =>
          obtain ⟨rfl, c', hr, hs⟩ := hH
          simp only [Prod.mk.injEq] at hr
          obtain ⟨⟨rfl, hc⟩, rfl⟩ := hr
          subst core2
          refine ⟨0, c', hle, hs.activity, hs.location.trans hle.symm, hs.version, hs.holding,
            hs.initial, ?_⟩
          exact holdStep _ rfl hs.activity hs.holding
        | discard r0 l0 =>
          obtain ⟨rfl, c', hr, hs⟩ := hH
          simp only [Prod.mk.injEq] at hr
          obtain ⟨⟨rfl, hc⟩, rfl⟩ := hr
          subst core2
          rw [hs.activity] at hv
          have hda : (discardingAfter c' l0.end).activity = .discarding l0.end :=
            rfl
          cases r0 with
          | none =>
            obtain ⟨c2, h2, a1, a2, a3, a4, a5⟩ := vBytes_discarding C rest _ held p'.taken hda
            refine ⟨c2, ?_, ⟨a2, a1.trans hs.version, ?_, a5.trans hs.initial⟩,
              a3.trans (hs.location.trans hle.symm), 0, hle⟩
            · simp only [vBytes, hv, Option.map_none]
              rw [h2]
              rfl
            · rw [a4]
              exact hs.holding
          | some r0 =>
            obtain ⟨c2, h2, a1, a2, a3, a4, a5⟩ := vBytes_discarding C rest _
              (some (Span.Located.Internal.new r0 l0.end)) p'.taken hda
            refine ⟨c2, ?_, ⟨a2, a1.trans hs.version, ?_, a5.trans hs.initial⟩,
              a3.trans (hs.location.trans hle.symm), 0, hle⟩
            · simp only [vBytes, hv, Option.map_some]
              rw [h2]
              rfl
            · rw [a4]
              exact hs.holding
        | relex l0 =>
          obtain ⟨rfl, c', hr, hs⟩ := hH
          simp only [Prod.mk.injEq] at hr
          obtain ⟨⟨rfl, hc⟩, rfl⟩ := hr
          subst core2
          have ha : c'.activity = .idle := hs.activity
          rw [ha] at hv
          refine ⟨0, c', hle, ha, hs.location.trans hle.symm, hs.version, hs.holding,
            hs.initial, ?_⟩
          simp only [vBytes, hv, lexByte_idle C c' b p'.taken ha, List.drop_zero]
    intro core st held taken hact hver
    cases st with
    | idle => exact caseIdle core held taken hact hver
    | token p =>
      cases hadv : advance C.concrete p core.location b with
      | pending p' =>
        obtain ⟨c', h, a1, a2, a3, a4, a5⟩ := lexByte_pending C core b taken hact hadv
        have := ih c' (.token p') held taken a2 (by rw [a1]; exact hver)
        rw [a1, a3, a4] at this
        have he : lexBytesF v C.concrete (.token p) core.location (b :: rest) =
            lexBytesF v C.concrete (.token p') (core.location.afterByte b) rest := by
          simp only [lexBytesF, byteStepW, hadv, withBeforeF_nil]
        rw [he]
        exact VOut.cons _ (by simp only [vBytes, h]) a4 a5 a3 this
      | idle =>
        obtain ⟨c', h, a1, a2, a3, a4, a5⟩ := lexByte_advance_idle C core b taken hact hadv
        have := ih c' .idle held taken a2 (by rw [a1]; exact hver)
        rw [a1, a3, a4] at this
        have he : lexBytesF v C.concrete (.token p) core.location (b :: rest) =
            lexBytesF v C.concrete .idle (core.location.afterByte b) rest := by
          simp only [lexBytesF, byteStepW, hadv, withBeforeF_nil]
        rw [he]
        exact VOut.cons _ (by simp only [vBytes, h]) a4 a5 a3 this
      | tokenWith l =>
        obtain ⟨hl, h⟩ := lexByte_tokenWith C core b taken hact hadv
        rw [lexBytesW_tokenWith v rest hadv, outcome_cont_one]
        exact caseA core (idleAfter core b) held taken l hl hver rfl rfl rfl rfl rfl
          (advance_tokenWith hadv).2 h
      | tokenBefore l =>
        rw [lexBytesW_tokenBefore v rest hadv, outcome_cont_one]
        exact caseB core held taken p l hact hver hadv
      | error f =>
        have h := lexByte_advance_error C core b taken hact hadv
        have he : lexBytesF v C.concrete (.token p) core.location (b :: rest) =
            .error ([], f) := by
          simp only [lexBytesF, byteStepW, failedBeforeW, failW, hadv]
        rw [he]
        exact ⟨core, by simp only [vBytes, h], kind_ne
          (advance_error_kind hadv), rfl, rfl, by rw [hact]; nofun⟩

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VBytes
