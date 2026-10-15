module

public import BSmtLib.Facts.Proofs.PublicApi.Lexing
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VEof
public import BSmtLib.Facts.Proofs.Lexer.Consumers.RunE
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Error
import all BSmtLib.Token

@[expose] public section

/-!
# The naive lexer with the concrete collector fails only at lexical errors

The concrete collector takes every lexeme and breaks only at the end-of-file token, which comes
last. So the naive lexer with it, fed from a lexer that holds no result and lexes, never holds a
result before the end of the input, never discards, and never meets trailing input: every error
it fails with is a lexical one other than trailing input (`runInputE_lexical`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.VCollector

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.PublicApi.Collector BSmtLib.Facts.Proofs.PublicApi.Lexing
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.Consumers.Ready
open BSmtLib.Facts.Proofs.Lexer.Consumers.RunE BSmtLib.Facts.Proofs.Lexer.Consumers.VHold
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSession BSmtLib.Facts.Proofs.Lexer.Consumers.VEnd
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel
open BSmtLib.Lexer.Error BSmtLib.Lexer.Internal.VNaive

/-- An error is a lexical one other than trailing input. -/
def IsLexicalNT {ε : Type} (e : LexError ε) : Prop :=
  ∃ kind, e.cause = .lexical kind ∧ kind ≠ .unexpectedTrailingToken

/-- The concrete collector goes on at a lexeme other than the end-of-file one, under the version
in force. -/
theorem hand1_cc (p : Prog) (l : Lexeme) (hl : (l.category == .endOfFile) = false) :
    ∃ p', hand1 concreteCollector false (.cont p) l = .cont p' ∧ p'.ver = p.ver := by
  obtain ⟨x, hx, -, hty⟩ := lexemeEntry_true p.ver l
  have hxt : x.type ≠ .endOfFile := fun h => by rw [hty.mp h] at hl; cases hl
  refine ⟨⟨p.taken ++ [x], p.ver⟩, ?_, rfl⟩
  have ha : concreteCollector.answer (p.taken ++ [x]) = .continue := by
    simp [concreteCollector, hxt]
  simp only [hand1, Bool.false_eq_true, ↓reduceIte, show concreteCollector.concrete = true from rfl,
    hx, ha, show concreteCollector.discards (p.taken ++ [x]) = false from rfl,
    show concreteCollector.switchTo (p.taken ++ [x]) = none from rfl, switchedTo, crosses,
    bne_self_eq_false]

/-- The concrete collector goes on at lexemes other than the end-of-file one. -/
theorem handAll_cc : ∀ (ls : List Lexeme) (p : Prog), NoEof ls →
    ∃ p', handAll concreteCollector false (.cont p) ls = .cont p' ∧ p'.ver = p.ver
  | [], p, _ => ⟨p, rfl, rfl⟩
  | l :: ls, p, h => by
    obtain ⟨p1, h1, v1⟩ := hand1_cc p l (h l (by simp))
    obtain ⟨p2, h2, v2⟩ := handAll_cc ls p1 (fun l' hl' => h l' (by simp [hl']))
    exact ⟨p2, by rw [handAll_cons, h1, h2], v2.trans v1⟩

/-- The concrete collector breaks at the end-of-file token. -/
theorem hand1_cc_eof (p : Prog) (location : Span.Location) :
    ∃ r l p', hand1 concreteCollector false (.cont p) (eofLexeme location) = .wait r l p' := by
  obtain ⟨x, hx, -, hty⟩ := lexemeEntry_true p.ver (eofLexeme location)
  have hxt : x.type = .endOfFile := hty.mpr rfl
  have ha : concreteCollector.answer (p.taken ++ [x]) = .break () := by
    simp [concreteCollector, hxt]
  refine ⟨(), eofLexeme location, ⟨p.taken ++ [x], p.ver⟩, ?_⟩
  simp only [hand1, Bool.false_eq_true, ↓reduceIte, show concreteCollector.concrete = true from rfl,
    hx, ha, show concreteCollector.discards (p.taken ++ [x]) = false from rfl,
    show concreteCollector.switchTo (p.taken ++ [x]) = none from rfl, switchedTo, crosses,
    bne_self_eq_false]

theorem lexemes_noEof (v : Token.Version) (st : St) (location : Span.Location) (bs : List UInt8) :
    match lexBytesF v true st location bs with
    | .ok (_, _, ls) => NoEof ls
    | .error (ls, _) => NoEof ls := by
  have h := lexBytesW_noEof v true bs st location
  rw [← plain_lexBytesF] at h
  revert h
  rcases lexBytesF v true st location bs with ⟨ls, f⟩ | ⟨st', loc', ls⟩ <;> exact id

/-- The naive lexer with the concrete collector, fed bytes from a lexer state that is the pure
run's state and holds no result: it goes on, holding none, in a pure state again, or fails with
a lexical error other than trailing input. -/
theorem vBytes_cc (core : Core) (st : St) (hact : core.activity = st.activity)
    (hh : core.holding = false) (bs : List UInt8) (taken : List Handed) :
    ((vBytes concreteCollector core none bs taken).1.1 = .ok none ∧
      (vBytes concreteCollector core none bs taken).1.2.holding = false ∧
      ∃ st' : St, (vBytes concreteCollector core none bs taken).1.2.activity = st'.activity) ∨
    ∃ f : LexFailure, (vBytes concreteCollector core none bs taken).1.1 =
      .error ⟨.lexical f.kind, f.span, f.location⟩ ∧ f.kind ≠ .unexpectedTrailingToken := by
  have hV := VBytes.vBytes_out concreteCollector core.version bs core st none taken hact rfl
  have hn := lexemes_noEof core.version st core.location bs
  rw [hh, show concreteCollector.concrete = true from rfl] at hV
  generalize lexBytesF core.version true st core.location bs = R at hV hn
  rcases R with ⟨ls, f⟩ | ⟨st', loc', ls⟩
  · obtain ⟨p', hp, -⟩ := handAll_cc ls ⟨taken, core.version⟩ hn
    simp only [outcome, hp, Model.finish] at hV
    obtain ⟨c', hvb, hk, -⟩ := hV
    exact .inr ⟨f, by rw [hvb], hk⟩
  · obtain ⟨p', hp, -⟩ := handAll_cc ls ⟨taken, core.version⟩ hn
    simp only [outcome, hp, Model.finish] at hV
    obtain ⟨c', hvb, ⟨a1, -, a3, -⟩, -⟩ := hV
    refine .inl ⟨by rw [hvb], by rw [hvb]; exact a3.trans hh, st', by rw [hvb]; exact a1⟩

theorem lexicalKey_some {ε : Type} {e : LexError (Option ε)} {k : LexicalErrorKind} {s : Span}
    (h : lexicalKey e.cause e.span = some (k, s)) : IsLexicalNT e := by
  unfold lexicalKey at h
  split at h
  · rename_i kind hk
    by_cases ht : (kind == .unexpectedTrailingToken) = true
    · simp only [ht, ↓reduceIte] at h; cases h
    · refine ⟨kind, hk, fun he => ht (by rw [he]; rfl)⟩
  · cases h

/-- The naive lexer with the concrete collector, at the end of the input from a lexer state that
is the pure run's state and holds no result, fails only with a lexical error other than trailing
input. -/
theorem vEnd_cc (core : Core) (st : St) (hact : core.activity = st.activity)
    (hh : core.holding = false) (taken : List Handed) :
    ∀ e, (vEnd concreteCollector core taken).1.1 = .error e → IsLexicalNT e := by
  intro e he
  have hR := (VEof.vEnd_eofRes concreteCollector core st taken (.inl hact)).1
  rw [he] at hR
  unfold EofRes at hR
  rw [hh] at hR
  cases hf : finishLs true st core.location with
  | none =>
    have ho : eofOut concreteCollector false true core.version taken st core.location = none := by
      simp only [eofOut, hf, Option.map_none]
    rw [show concreteCollector.concrete = true from rfl, ho] at hR
    obtain ⟨h1, -⟩ := hR
    simp only [Except.mapError, Except.error.injEq, preciseOf, preciseFailure,
      Prod.mk.injEq] at h1
    exact lexicalKey_some h1.2
  | some ls =>
    have hls : NoEof ls := by
      unfold finishLs at hf
      split at hf
      · cases hf; simp [NoEof]
      · split at hf
        · cases hf; simp [NoEof]
        · cases hf
          rename_i l hfl
          intro l' hl'
          simp only [List.mem_singleton] at hl'
          subst hl'
          exact finish_token_ne_eof hfl
        · cases hf
    obtain ⟨p', hp, -⟩ := handAll_cc ls ⟨taken, core.version⟩ hls
    obtain ⟨r, l, p'', hw⟩ := hand1_cc_eof p' core.location
    have ho : eofOut concreteCollector false true core.version taken st core.location =
        some (.wait r l p'', none) := by
      simp only [eofOut, hf, Option.map_some, pending, hp, eofHand, Bool.false_eq_true,
        ↓reduceIte, hw]
    rw [show concreteCollector.concrete = true from rfl, ho] at hR
    obtain ⟨h1, -⟩ := hR
    cases h1

/-- `vBytes_cc`, with what the pure run says: the failure it fails with, or the state and the
location it ends at. -/
theorem vBytes_cc_exact (core : Core) (st : St) (hact : core.activity = st.activity)
    (hh : core.holding = false) (bs : List UInt8) (taken : List Handed) :
    match lexBytesF core.version true st core.location bs with
    | .error (_, f) => (vBytes concreteCollector core none bs taken).1.1 =
        .error ⟨.lexical f.kind, f.span, f.location⟩
    | .ok (st', location', _) => (vBytes concreteCollector core none bs taken).1.1 = .ok none ∧
        (vBytes concreteCollector core none bs taken).1.2.holding = false ∧
        (vBytes concreteCollector core none bs taken).1.2.activity = st'.activity ∧
        (vBytes concreteCollector core none bs taken).1.2.location = location' ∧
        (vBytes concreteCollector core none bs taken).1.2.version = core.version := by
  have hV := VBytes.vBytes_out concreteCollector core.version bs core st none taken hact rfl
  have hn := lexemes_noEof core.version st core.location bs
  rw [hh, show concreteCollector.concrete = true from rfl] at hV
  generalize lexBytesF core.version true st core.location bs = R at hV hn ⊢
  rcases R with ⟨ls, f⟩ | ⟨st', loc', ls⟩
  · obtain ⟨p', hp, -⟩ := handAll_cc ls ⟨taken, core.version⟩ hn
    simp only [outcome, hp, Model.finish] at hV
    obtain ⟨c', hvb, -, -⟩ := hV
    dsimp only
    rw [hvb]
  · obtain ⟨p', hp, hv⟩ := handAll_cc ls ⟨taken, core.version⟩ hn
    simp only [outcome, hp, Model.finish] at hV
    obtain ⟨c', hvb, ⟨a1, a2, a3, -⟩, a5⟩ := hV
    dsimp only
    rw [hvb]
    exact ⟨rfl, a3.trans hh, a1, a5, a2.trans hv⟩

theorem lexicalKey_span {ε : Type} {c : LexErrorCause (Option ε)} {s s' : Span}
    {k : LexicalErrorKind} (h : lexicalKey c s = some (k, s')) : s' = s := by
  unfold lexicalKey at h
  split at h
  · split at h
    · cases h
    · cases h; rfl
  · cases h

/-- Where the naive lexer with the concrete collector fails at the end of the input, finishing
the token in progress fails, and the error spans as that failure. -/
theorem vEnd_cc_span (core : Core) (st : St) (hact : core.activity = st.activity)
    (hh : core.holding = false) (taken : List Handed) :
    ∀ e, (vEnd concreteCollector core taken).1.1 = .error e →
      finishLs true st core.location = none ∧
        e.span = (finishFail true st core.location).span := by
  intro e he
  have hR := (VEof.vEnd_eofRes concreteCollector core st taken (.inl hact)).1
  rw [he] at hR
  unfold EofRes at hR
  rw [hh] at hR
  cases hf : finishLs true st core.location with
  | none =>
    have ho : eofOut concreteCollector false true core.version taken st core.location = none := by
      simp only [eofOut, hf, Option.map_none]
    rw [show concreteCollector.concrete = true from rfl, ho] at hR
    obtain ⟨h1, -⟩ := hR
    simp only [Except.mapError, Except.error.injEq, preciseOf, preciseFailure,
      Prod.mk.injEq] at h1
    exact ⟨rfl, (lexicalKey_span h1.2).symm⟩
  | some ls =>
    exfalso
    have hls : NoEof ls := by
      unfold finishLs at hf
      split at hf
      · cases hf; simp [NoEof]
      · split at hf
        · cases hf; simp [NoEof]
        · cases hf
          rename_i l hfl
          intro l' hl'
          simp only [List.mem_singleton] at hl'
          subst hl'
          exact finish_token_ne_eof hfl
        · cases hf
    obtain ⟨p', hp, -⟩ := handAll_cc ls ⟨taken, core.version⟩ hls
    obtain ⟨r, l, p'', hw⟩ := hand1_cc_eof p' core.location
    have ho : eofOut concreteCollector false true core.version taken st core.location =
        some (.wait r l p'', none) := by
      simp only [eofOut, hf, Option.map_some, pending, hp, eofHand, Bool.false_eq_true,
        ↓reduceIte, hw]
    rw [show concreteCollector.concrete = true from rfl, ho] at hR
    obtain ⟨h1, -⟩ := hR
    cases h1

/-- What the naive lexer with the concrete collector keeps: it holds no result and is in a pure
state. -/
def Inv (L : VNaive.lexOps.Lexer concreteCollector) : Prop :=
  L.core.holding = false ∧ ∃ st : St, L.core.activity = st.activity

/-- The naive lexer with the concrete collector, fed from a lexer that holds no result and is in
a pure state, fails only with lexical errors other than trailing input. -/
theorem runInputE_lexical (ended : Bool) (slices : List BSmtLibSpec.Regex.Chars)
    (L : VNaive.lexOps.Lexer concreteCollector) (taken : List Handed) (h : Inv L) :
    ∀ e, ((runInputE VNaive.lexOps L ended slices).run taken).1.1 = .error e → IsLexicalNT e := by
  refine runInputE_error_inv VNaive.lexOps Inv IsLexicalNT ?_ ?_ ended slices L taken h
  · intro slice a taken ⟨hh, st, hact⟩
    rw [BSmtLib.Facts.Proofs.Lexer.Consumers.VReset.vLexer_eta a]
    have hp : (Core.Plain a.core) := by unfold Core.Plain; rw [hact]; cases st <;> trivial
    rw [BSmtLib.Facts.Proofs.Lexer.Consumers.VFlatten.lexSliceStep_ops concreteCollector a.core hp
      a.held slice taken]
    have hc := vBytes_cc a.core st hact hh slice taken
    generalize vBytes concreteCollector a.core none slice taken = R at hc
    obtain ⟨⟨res, core'⟩, taken'⟩ := R
    rcases hc with ⟨h1, h2, st', h3⟩ | ⟨f, h1, h2⟩
    · simp only at h1 h2 h3
      subst h1
      exact ⟨fun _ _ _ => ⟨h2, st', h3⟩, fun e he => by cases he⟩
    · simp only at h1
      subst h1
      exact ⟨(fun _ he => by cases he), fun e he => by cases he; exact ⟨f.kind, rfl, h2⟩⟩
  · intro a taken ⟨hh, st, hact⟩ e he
    rw [BSmtLib.Facts.Proofs.Lexer.Consumers.VReset.vLexer_eta a, lexOps_lexEofStep] at he
    have hc := vEnd_cc a.core st hact hh taken
    generalize vEnd concreteCollector a.core taken = R at hc he
    obtain ⟨⟨res, core'⟩, taken'⟩ := R
    exact hc e he

end BSmtLib.Facts.Proofs.PublicApi.VCollector
