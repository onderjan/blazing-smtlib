import BSmtLib.Proofs.VNaiveWRustPort.VBytes
import BSmtLib.Proofs.VNaiveWRustPort.EofModel

/-!
# The naive lexer at the end of the input, as `eofOut` says

`vEnd_eofRes`: the naive lexer's step at the end of the input, from a lexer state that is the
pure run's state, or that discards, gives what `EofRes` states for what the consumer does there
(`eofOut`); when it does not fail, it is reset.
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open BSmtLib.Proofs.Adapter BSmtLib.Proofs.Lexer.VNaive
open BSmtLibSpec.Lexer (Handed)

variable (C : BSmtLibSpec.Lexer.Consumer)

/-- What the naive lexer's end of the input gives after the hand-over of the end-of-file token
gave `r`. -/
def eofAfter (r : Except (Failure (Option C.Error)) (Option (Located C.Result))) (core3 : Core)
    (taken3 : List Handed) :
    VRes (Except (LexError (Option C.Error)) (ControlFlow (Located C.Result))) :=
  match r with
  | .ok none => ((.ok .continue, core3.reset), taken3)
  | .ok (some located) => ((.ok (.break located), core3.reset), taken3)
  | .error f => ((.error ⟨f.cause, f.span, none⟩, core3), taken3)

/-- The lexer state after the end of the input that did not fail is reset. -/
def ResetOk (iv : Version)
    (r : VRes (Except (LexError (Option C.Error)) (ControlFlow (Located C.Result)))) : Prop :=
  r.1.1.isOk = true → r.1.2 = Core.initial iv

theorem failureOf_trailing (l : Lexeme) :
    failureOf (ε := C.Error) ⟨.lexical .unexpectedTrailingToken, trailingSpan l, none⟩ =
      .trailing (toLocation l.start) :=
  rfl

theorem failureOf_lexical {k : LexicalErrorKind} {span : Span}
    (h : k ≠ .unexpectedTrailingToken) :
    failureOf (ε := C.Error) ⟨.lexical k, span, none⟩ = .lexical := by
  simp only [failureOf]
  have : (k == .unexpectedTrailingToken) = false := by
    cases k <;> first | rfl | exact absurd rfl h
  rw [this]
  rfl

theorem discardedOf_eq {X Y : Core} (h : Y.activity = X.activity) :
    discardedOf Y = discardedOf X := by
  unfold discardedOf
  rw [h]

/-- Where the lexer discards from after a hand-over at which the consumer failed, having the rest
discarded if `dd`. -/
theorem discardedOf_fail {X c' : Core} {dd : Bool} {l : Lexeme}
    (h : c'.activity = if dd then .discarding (X.activity.discardStart l.end) else X.activity) :
    discardedOf c' = discardsAfter (discardedOf X) (if dd then some l.end else none) := by
  unfold discardedOf discardsAfter
  rw [h]
  cases dd <;> cases hx : X.activity <;> simp [Activity.discardStart]

/-- The hand-over of the end-of-file token at the end of the input, from `X`, which holds no
result. -/
theorem eof_tail (X : Core) (tk : List Handed) (hX : X.holding = false) {d d0 : Option Location}
    (hd : discardedOf X = d.or d0) {iv : Version} (hiv : X.initialVersion = iv) (loc : Location) :
    ∀ {r core3 taken3},
      vRun C (handOverAt (H := Answering C) X (eofAt loc) (eofAt_valid _)) tk =
        ((r, core3), taken3) →
      EofTail C (hand1 C false (.cont ⟨tk, X.version⟩) (eofLexeme loc)) d d0 loc
        ((eofAfter C r core3 taken3).1.1.mapError failureOf)
        (eofAfter C r core3 taken3).1.2.version (discardedOf (eofAfter C r core3 taken3).1.2)
        (eofAfter C r core3 taken3).2 ∧
      ResetOk C iv (eofAfter C r core3 taken3) := by
  intro r core3 taken3 hr
  have hH := handOverAt_hand1 C X (eofAt loc) (eofAt_valid _) tk
  rw [hX, hr] at hH
  change HandV C X (eofAt loc) ((r, core3), taken3)
    (hand1 C false (.cont ⟨tk, X.version⟩) (eofLexeme loc)) at hH
  generalize hho : hand1 C false (.cont ⟨tk, X.version⟩) (eofLexeme loc) = ho at hH ⊢
  cases ho with
  | cont p =>
    obtain ⟨c', hr', hs⟩ := hH
    simp only [Prod.mk.injEq] at hr'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
    refine ⟨⟨rfl, rfl⟩, fun _ => ?_⟩
    show Core.reset _ = _
    rw [Core.reset, hs.initial, hiv]
  | wait r0 l0 p =>
    obtain ⟨rfl, c', hr', hs⟩ := hH
    simp only [Prod.mk.injEq] at hr'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
    refine ⟨⟨rfl, rfl⟩, fun _ => ?_⟩
    show Core.reset _ = _
    rw [Core.reset, hs.initial, hiv]
  | stop s p =>
    cases s with
    | trailing l0 =>
      obtain ⟨rfl, hpv, hr'⟩ := hH
      simp only [Prod.mk.injEq] at hr'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
      exact ⟨⟨rfl, hpv.symm, hd, rfl⟩, nofun⟩
    | fail e dd l0 =>
      obtain ⟨rfl, c', hr', hs⟩ := hH
      simp only [Prod.mk.injEq] at hr'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
      exact ⟨⟨rfl, hs.version, by
        show discardedOf core3 = _; rw [discardedOf_fail hs.activity, hd]; cases dd <;> rfl, rfl⟩,
        nofun⟩
    | layout l0 =>
      obtain ⟨rfl, c', hr', hs⟩ := hH
      simp only [Prod.mk.injEq] at hr'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
      exact ⟨⟨rfl, hs.version, (discardedOf_eq hs.activity).trans hd, rfl⟩, nofun⟩
    | brk _ _ _ => exact hH.elim
    | brkX r0 l0 =>
      obtain ⟨rfl, c', hr', hs⟩ := hH
      simp only [Prod.mk.injEq] at hr'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
      refine ⟨⟨rfl, rfl⟩, fun _ => ?_⟩
      show Core.reset _ = _
      rw [Core.reset, hs.initial, hiv]
    | discard r0 l0 =>
      obtain ⟨rfl, c', hr', hs⟩ := hH
      simp only [Prod.mk.injEq] at hr'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
      cases r0 with
      | none =>
        refine ⟨⟨rfl, rfl⟩, fun _ => ?_⟩
        show Core.reset _ = _
        rw [Core.reset, hs.initial, hiv]
      | some r0 =>
        refine ⟨⟨rfl, rfl⟩, fun _ => ?_⟩
        show Core.reset _ = _
        rw [Core.reset, hs.initial, hiv]
    | relex l0 =>
      obtain ⟨rfl, c', hr', hs⟩ := hH
      simp only [Prod.mk.injEq] at hr'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
      refine ⟨⟨rfl, rfl⟩, fun _ => ?_⟩
      show Core.reset _ = _
      rw [Core.reset, hs.initial, hiv]

theorem hand1_holding (p : Prog) (l : Lexeme) : hand1 C true (.cont p) l = .stop (.trailing l) p :=
  by simp [hand1]

/-- The naive lexer at the end of the input, from a lexer state that is the pure run's state, or
that discards, gives what `EofRes` states for what the consumer does there. -/
theorem vEnd_eofRes (core : Core) (st : St) (taken : List Handed)
    (ha : core.activity = st.activity ∨ (st = .idle ∧ ∃ s, core.activity = .discarding s)) :
    EofRes C (eofOut C core.holding C.concrete core.version taken st core.location)
      (discardedOf core) core.version taken core.location
      ((vEnd C core taken).1.1.mapError failureOf) (vEnd C core taken).1.2.version
      (discardedOf (vEnd C core taken).1.2) (vEnd C core taken).2 ∧
    ResetOk C core.initialVersion (vEnd C core taken) := by
  -- with nothing in progress, or discarding
  have idle : core.activity = .idle ∨ (∃ s, core.activity = .discarding s) →
      EofTail C (eofHand C core.holding (eofLexeme core.location) (.cont ⟨taken, core.version⟩)).1
        none (discardedOf core) core.location
        ((vEnd C core taken).1.1.mapError failureOf) (vEnd C core taken).1.2.version
        (discardedOf (vEnd C core taken).1.2) (vEnd C core taken).2 ∧
      ResetOk C core.initialVersion (vEnd C core taken) := by
    intro hid
    cases hh : core.holding with
    | true =>
      rw [vEnd_held C core taken hid hh]
      exact ⟨⟨rfl, rfl⟩, fun _ => rfl⟩
    | false =>
      generalize hr : vRun C (handOverAt (H := Answering C) core (eofAt core.location)
        (eofAt_valid _)) taken = rr
      obtain ⟨⟨r, core2⟩, taken2⟩ := rr
      rw [vEnd_eof C core taken hid hh hr]
      exact eof_tail C core taken hh rfl rfl core.location hr
  rcases ha with ha | ⟨rfl, s, ha⟩
  · cases st with
    | idle => exact idle (.inl ha)
    | token p =>
      cases hf : VNaive.finish C.concrete p core.location with
      | none =>
        have he : eofOut C core.holding C.concrete core.version taken (.token p) core.location =
            some (eofHand C core.holding (eofLexeme core.location)
              (.cont ⟨taken, core.version⟩)) := by
          simp only [eofOut, finishLs, hf, Option.map_some]
          rfl
        rw [he]
        have hdc : discardedOf core = none := by simp [discardedOf, ha, St.activity]
        obtain ⟨h1, h2⟩ := vEnd_finish_none C core taken ha hf
        cases hh : core.holding with
        | true =>
          rw [h1 hh]
          exact ⟨⟨rfl, rfl⟩, fun _ => rfl⟩
        | false =>
          generalize hr : vRun C (handOverAt (H := Answering C) (idleAt core)
            (eofAt core.location) (eofAt_valid _)) taken = rr
          obtain ⟨⟨r, core2⟩, taken2⟩ := rr
          rw [h2 hh hr]
          have := eof_tail C (idleAt core) taken hh (d := none) (d0 := discardedOf core)
            (by rw [hdc]; rfl) rfl core.location hr
          exact this
      | error f =>
        have he : eofOut C core.holding C.concrete core.version taken (.token p) core.location =
            none := by
          simp only [eofOut, finishLs, hf, Option.map_none]
        rw [he, vEnd_finish_error C core taken ha hf]
        exact ⟨⟨congrArg Except.error (failureOf_lexical C (kind_ne (finish_error_kind hf))),
          rfl, rfl, rfl⟩, nofun⟩
      | token l =>
        have he : eofOut C core.holding C.concrete core.version taken (.token p) core.location =
            some (eofHand C core.holding (eofLexeme core.location)
              (hand1 C core.holding (.cont ⟨taken, core.version⟩) l)) := by
          simp only [eofOut, finishLs, hf, Option.map_some]
          rfl
        rw [he]
        have hdc : discardedOf core = none := by simp [discardedOf, ha, St.activity]
        have hle := (finish_token hf).2
        obtain ⟨hl, k1, k2, k3⟩ := vEnd_finish_token C core taken ha hf
        have hH := handOverAt_hand1 C (idleAt core) l hl taken
        generalize hrr : vRun C (handOverAt (H := Answering C) (idleAt core) l hl) taken = rr
          at hH
        obtain ⟨⟨res, core2⟩, taken2⟩ := rr
        change HandV C (idleAt core) l ((res, core2), taken2)
          (hand1 C core.holding (.cont ⟨taken, core.version⟩) l) at hH
        -- the hand-overs that go on to the end-of-file token: the lexer holds no result
        have nohold : ∀ {p'}, (hand1 C core.holding (.cont ⟨taken, core.version⟩) l = .cont p' ∨
            hand1 C core.holding (.cont ⟨taken, core.version⟩) l = .stop (.relex l) p' ∨
            hand1 C core.holding (.cont ⟨taken, core.version⟩) l = .stop (.discard none l) p') →
            core.holding = false := by
          intro p' h
          cases hh : core.holding with
          | false => rfl
          | true =>
            rw [hh, hand1_holding] at h
            rcases h with h | h | h <;> cases h
        generalize hho : hand1 C core.holding (.cont ⟨taken, core.version⟩) l = ho at hH nohold
        cases ho with
        | cont p' =>
          have hh := nohold (.inl rfl)
          obtain ⟨c', hr', hs⟩ := hH
          simp only [Prod.mk.injEq] at hr'
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
          have hh2 : core2.holding = false := hs.holding.trans hh
          generalize hr3 : vRun C (handOverAt (H := Answering C) core2 (eofAt core.location)
            (eofAt_valid _)) p'.taken = rr3
          obtain ⟨⟨r3, core3⟩, taken3⟩ := rr3
          rw [k3 hh2 hrr hr3]
          simp only [eofHand, hh, Bool.false_eq_true, ite_false]
          have := eof_tail C core2 p'.taken hh2 (d := none) (d0 := discardedOf core)
            (by rw [hdc, discardedOf_eq hs.activity]; rfl) hs.initial core.location hr3
          rw [hs.version] at this
          exact this
        | wait r0 l0 p' =>
          obtain ⟨rfl, c', hr', hs⟩ := hH
          simp only [Prod.mk.injEq] at hr'
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
          rw [k2 hrr]
          refine ⟨⟨by rw [hle]; rfl, rfl⟩, fun _ => ?_⟩
          show Core.reset _ = _
          rw [Core.reset, hs.initial]
          rfl
        | stop s p' =>
          cases s with
          | trailing l0 =>
            obtain ⟨rfl, hpv, hr'⟩ := hH
            simp only [Prod.mk.injEq] at hr'
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
            rw [k1 hrr]
            exact ⟨⟨rfl, hpv.symm, by rw [hdc]; rfl, rfl⟩, nofun⟩
          | fail e dd l0 =>
            obtain ⟨rfl, c', hr', hs⟩ := hH
            simp only [Prod.mk.injEq] at hr'
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
            rw [k1 hrr]
            exact ⟨⟨rfl, hs.version, by
              rw [discardedOf_fail hs.activity]
              cases dd <;>
                simp [discardedOf, idleAt, discardsAfter, Stop.discards, ha, St.activity],
              rfl⟩,
              nofun⟩
          | layout l0 =>
            obtain ⟨rfl, c', hr', hs⟩ := hH
            simp only [Prod.mk.injEq] at hr'
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
            rw [k1 hrr]
            exact ⟨⟨rfl, hs.version, by rw [hdc, discardedOf_eq hs.activity]; rfl, rfl⟩, nofun⟩
          | brk _ _ _ => exact hH.elim
          | brkX r0 l0 =>
            obtain ⟨rfl, c', hr', hs⟩ := hH
            simp only [Prod.mk.injEq] at hr'
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
            rw [k2 hrr]
            refine ⟨⟨by rw [hle]; rfl, rfl⟩, fun _ => ?_⟩
            show Core.reset _ = _
            rw [Core.reset, hs.initial]
            rfl
          | discard r0 l0 =>
            cases r0 with
            | some r0 =>
              obtain ⟨rfl, c', hr', hs⟩ := hH
              simp only [Prod.mk.injEq] at hr'
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
              rw [k2 hrr]
              refine ⟨⟨by rw [hle]; rfl, rfl⟩, fun _ => ?_⟩
              show Core.reset _ = _
              rw [Core.reset, hs.initial]
              rfl
            | none =>
              obtain ⟨rfl, c', hr', hs⟩ := hH
              have hh := nohold (.inr (.inr rfl))
              simp only [Prod.mk.injEq] at hr'
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
              have hh2 : core2.holding = false := by
                rw [hs.holding]
                simp only [Option.isSome_none, Bool.false_or]
                exact hh
              generalize hr3 : vRun C (handOverAt (H := Answering C) core2 (eofAt core.location)
                (eofAt_valid _)) p'.taken = rr3
              obtain ⟨⟨r3, core3⟩, taken3⟩ := rr3
              rw [k3 hh2 hrr hr3]
              simp only [eofHand, hh, Bool.false_eq_true, ite_false]
              have := eof_tail C core2 p'.taken hh2 (d := some l0.end) (d0 := discardedOf core)
                (by rw [hdc]; simp [discardedOf, hs.activity]) hs.initial core.location hr3
              rw [hs.version] at this
              exact this
          | relex l0 =>
            obtain ⟨rfl, c', hr', hs⟩ := hH
            have hh := nohold (.inr (.inl rfl))
            simp only [Prod.mk.injEq] at hr'
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
            have hh2 : core2.holding = false := hs.holding.trans hh
            generalize hr3 : vRun C (handOverAt (H := Answering C) core2 (eofAt core.location)
              (eofAt_valid _)) p'.taken = rr3
            obtain ⟨⟨r3, core3⟩, taken3⟩ := rr3
            rw [k3 hh2 hrr hr3]
            simp only [eofHand, hh, Bool.false_eq_true, ite_false]
            have := eof_tail C core2 p'.taken hh2 (d := none) (d0 := discardedOf core)
              (by rw [hdc, discardedOf_eq hs.activity]; rfl) hs.initial core.location hr3
            rw [hs.version] at this
            exact this
  · exact idle (.inr ⟨s, ha⟩)

end BSmtLib.Proofs.Lexer.VNaiveWRustPort
