module

public import BSmtLib.Facts.Proofs.Reader.Param.Basic
public import BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Error
import all BSmtLib.Span

@[expose] public section

/-!
# Runs of the naive lexer with two consumers

The naive lexer (`Lexer.Internal.VNaive`) is generic in its consumer and reads it only through
the consumer's call on the cursor of each lexeme it hands over (`handOver`), the consumer's
`Consume.isConcrete`, and the recovery actions it is given. So two runs of its code with two
consumers whose calls on such cursors are related, as a `Link` relates them, give related
results with the same lexer state (`lexSliceStep_sim`, `lexEofStep_sim`).
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.PublicApi.VLink

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Lexer.Internal.VNaive

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂]
  [∀ b, Token.ConsumeFrom H₁ (LexerCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (LexerCursor b) m₂]
  (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂)

/-- What the two consumers' calls on the cursor of a lexeme alone give alike: answers related
as the link says, and the same cursor back. -/
structure VConsumers : Prop where
  concrete : Token.Consume.isConcrete (H := H₁) = Token.Consume.isConcrete (H := H₂)
  consume : ∀ (version : Version) (l : Lexeme) (h : l.Valid),
    L.rc.rel (fun a b => ERel L.re (FlowRel L.rr) a.1 b.1 ∧ a.2.val = b.2.val)
      (Token.ConsumeFrom.consume (H := H₁) (m := m₁)
        (Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)) (l.hasNext h version))
      (Token.ConsumeFrom.consume (H := H₂) (m := m₂)
        (Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)) (l.hasNext h version))

/-- Results related as the link says, with the same lexer state. -/
def SameRes {α₁ α₂ : Type} (Q : α₁ → α₂ → Prop) (a : α₁ × Core) (b : α₂ × Core) : Prop :=
  Q a.1 b.1 ∧ a.2 = b.2

/-- Failures of the naive lexer with causes related and the same span and location. -/
def VFailRel {E₁ E₂ : Type} (RE : E₁ → E₂ → Prop) (a : BSmtLib.Lexer.Internal.VNaive.Failure E₁)
    (b : BSmtLib.Lexer.Internal.VNaive.Failure E₂) : Prop :=
  CauseRel RE a.cause b.cause ∧ a.span = b.span ∧ a.location = b.location

/-- The results of the steps on bytes: related results or related failures. -/
abbrev StepRes : Except (BSmtLib.Lexer.Internal.VNaive.Failure E₁) (Option (Span.Located R₁)) →
    Except (BSmtLib.Lexer.Internal.VNaive.Failure E₂) (Option (Span.Located R₂)) → Prop :=
  ERel (VFailRel L.re) (ORel (LocRel L.rr))

variable {L}

omit [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂]
  [∀ b, Token.ConsumeFrom H₁ (LexerCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (LexerCursor b) m₂] in
theorem rel_pure {α β : Type} {Q : α → β → Prop} {a : α} {b : β} (h : Q a b) :
    L.rc.rel Q (Pure.pure a : StateT H₁ m₁ α) (Pure.pure b : StateT H₂ m₂ β) :=
  L.rc.pure h

theorem handOver_sim (hc : VConsumers L) (core : Core) (l : Lexeme) (h : l.Valid) :
    L.rc.rel (fun (a : Except E₁ (ControlFlow R₁) × Bool × Core)
        (b : Except E₂ (ControlFlow R₂) × Bool × Core) =>
          ERel L.re (FlowRel L.rr) a.1 b.1 ∧ a.2 = b.2)
      (handOver (H := H₁) (m := m₁) core l h) (handOver (H := H₂) (m := m₂) core l h) := by
  unfold handOver
  refine L.rc.bind (hc.consume core.version l h) ?_
  rintro ⟨a1, after1, h1⟩ ⟨a2, after2, h2⟩ ⟨ha, hafter⟩
  dsimp only at ha hafter ⊢
  subst hafter
  exact rel_pure ⟨ha, rfl⟩

theorem handOverAt_sim (hc : VConsumers L) (core : Core) (l : Lexeme) (h : l.Valid) :
    L.rc.rel (SameRes (StepRes L))
      (handOverAt (H := H₁) (m := m₁) core l h) (handOverAt (H := H₂) (m := m₂) core l h) := by
  unfold handOverAt
  split
  · exact rel_pure ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  · refine L.rc.bind (handOver_sim hc core l h) ?_
    rintro ⟨a1, d1, c1⟩ ⟨a2, d2, c2⟩ ⟨ha, hdc⟩
    dsimp only at ha hdc ⊢
    cases hdc

    match a1, a2, ha with
    | .ok f1, .ok f2, hf =>
      match f1, f2, hf with
      | .continue, .continue, _ => exact rel_pure ⟨trivial, rfl⟩
      | .break r1, .break r2, hr => exact rel_pure ⟨⟨hr, rfl⟩, rfl⟩
    | .error e1, .error e2, he => exact rel_pure ⟨⟨he, rfl, rfl⟩, rfl⟩

theorem lexStart_sim (hc : VConsumers L) (core : Core) (c : UInt8) :
    L.rc.rel (SameRes (StepRes L))
      (lexStart (H := H₁) (m := m₁) core c) (lexStart (H := H₂) (m := m₂) core c) := by
  unfold lexStart
  simp only [hc.concrete]
  generalize startS core.version (Token.Consume.isConcrete (H := H₂)) core.location c = r
  obtain ⟨r, hr⟩ := r
  cases r with
  | idle => exact rel_pure ⟨trivial, rfl⟩
  | pending p => exact rel_pure ⟨trivial, rfl⟩
  | token l => exact handOverAt_sim hc _ l _
  | error f => exact rel_pure ⟨⟨rfl, rfl, rfl⟩, rfl⟩

theorem lexByte_sim (hc : VConsumers L) (recover₁ : Span.Location → StateT H₁ m₁ Unit)
    (recover₂ : Span.Location → StateT H₂ m₂ Unit)
    (hrec : ∀ l, L.rc.rel (· = ·) (recover₁ l) (recover₂ l)) (core : Core) (c : UInt8) :
    L.rc.rel (SameRes (StepRes L))
      (lexByte recover₁ core c) (lexByte recover₂ core c) := by
  unfold lexByte
  simp only [hc.concrete]
  generalize withEq core.activity = w
  obtain ⟨a, ha⟩ := w
  cases a with
  | discarding s => exact rel_pure ⟨trivial, rfl⟩
  | ended => exact rel_pure ⟨trivial, rfl⟩
  | recovered =>
    refine L.rc.bind (hrec _) ?_
    rintro _ _ rfl
    exact lexStart_sim hc _ c
  | skipping skip =>
    dsimp only
    generalize scan (core.version == .v2_0) skip core.depth c = sc
    cases sc with
    | skip s d => exact rel_pure ⟨trivial, rfl⟩
    | before =>
      refine L.rc.bind (hrec _) ?_
      rintro _ _ rfl
      exact lexStart_sim hc _ c
    | after =>
      refine L.rc.bind (hrec _) ?_
      rintro _ _ rfl
      exact rel_pure ⟨trivial, rfl⟩
  | idle => exact lexStart_sim hc core c
  | token p =>
    dsimp only
    generalize advanceS (Token.Consume.isConcrete (H := H₂)) p core.location c = r
    obtain ⟨r, hr⟩ := r
    cases r with
    | pending p' => exact rel_pure ⟨trivial, rfl⟩
    | idle => exact rel_pure ⟨trivial, rfl⟩
    | tokenWith l => exact handOverAt_sim hc _ l _
    | tokenBefore l =>
      refine L.rc.bind (handOverAt_sim hc _ l _) ?_
      rintro ⟨r1, c1⟩ ⟨r2, c2⟩ ⟨hres, hcore⟩
      dsimp only at hres hcore ⊢
      subst hcore
      match r1, r2, hres with
      | .ok none, .ok none, _ =>
        dsimp only
        split
        · exact rel_pure ⟨trivial, rfl⟩
        · exact lexStart_sim hc _ c
      | .ok (some x1), .ok (some x2), hx =>
        dsimp only
        split
        · exact rel_pure ⟨hx, rfl⟩
        · refine L.rc.bind (lexStart_sim hc _ c) ?_
          rintro ⟨s1, d1⟩ ⟨s2, d2⟩ ⟨hs, hd⟩
          dsimp only at hs hd ⊢
          subst hd
          refine rel_pure ⟨?_, rfl⟩
          match s1, s2, hs with
          | .ok _, .ok _, _ => exact hx
          | .error _, .error _, hf => exact hf
      | .error f1, .error f2, hf => exact rel_pure ⟨hf, rfl⟩
    | error f => exact rel_pure ⟨⟨rfl, rfl, rfl⟩, rfl⟩

theorem lexFrom_sim (hc : VConsumers L) (recover₁ : Span.Location → StateT H₁ m₁ Unit)
    (recover₂ : Span.Location → StateT H₂ m₂ Unit)
    (hrec : ∀ l, L.rc.rel (· = ·) (recover₁ l) (recover₂ l)) (slice : ByteSlice) :
    ∀ (n index : Nat), slice.size - index = n → ∀ (core : Core)
      (held₁ : Option (Span.Located R₁)) (held₂ : Option (Span.Located R₂)),
      ORel (LocRel L.rr) held₁ held₂ →
      L.rc.rel (SameRes (StepRes L))
        (Internal.VNaive.lexFrom recover₁ slice index core held₁)
        (Internal.VNaive.lexFrom recover₂ slice index core held₂) := by
  intro n
  induction n with
  | zero =>
    intro index hn core held₁ held₂ hh
    rw [Internal.VNaive.lexFrom, Internal.VNaive.lexFrom]
    split
    · omega
    · exact rel_pure ⟨hh, rfl⟩
  | succ n ih =>
  intro index hn core held₁ held₂ hh
  rw [Internal.VNaive.lexFrom, Internal.VNaive.lexFrom]
  split
  · refine L.rc.bind (lexByte_sim hc recover₁ recover₂ hrec core _) ?_
    rintro ⟨r1, c1⟩ ⟨r2, c2⟩ ⟨hres, hcore⟩
    dsimp only at hres hcore ⊢
    subst hcore
    match r1, r2, hres with
    | .ok none, .ok none, _ => exact ih _ (by omega) _ _ _ hh
    | .ok (some x1), .ok (some x2), hx => exact ih _ (by omega) _ _ _ hx
    | .error f1, .error f2, hf => exact rel_pure ⟨hf, rfl⟩
  · exact rel_pure ⟨hh, rfl⟩

omit [Token.Consume H₁ R₁ E₁] [Token.Consume H₂ R₂ E₂]
  [∀ b, Token.ConsumeFrom H₁ (LexerCursor b) m₁]
  [∀ b, Token.ConsumeFrom H₂ (LexerCursor b) m₂] in
theorem failCall_sim (abandon₁ : Span.Location → StateT H₁ m₁ Unit)
    (abandon₂ : Span.Location → StateT H₂ m₂ Unit)
    (f₁ : BSmtLib.Lexer.Internal.VNaive.Failure E₁)
    (f₂ : BSmtLib.Lexer.Internal.VNaive.Failure E₂) (hf : VFailRel L.re f₁ f₂) (atEnd : Bool)
    (core : Core) :
    L.rc.rel (SameRes (LexErrRel L.re))
      (failCall false abandon₁ f₁ atEnd core) (failCall false abandon₂ f₂ atEnd core) := by
  obtain ⟨hcause, hspan, -⟩ := hf
  unfold failCall
  exact rel_pure ⟨⟨hcause, hspan, rfl⟩, rfl⟩

theorem lexSliceStep_sim [LawfulMonad m₁] [LawfulMonad m₂] (hc : VConsumers L)
    (abandon₁ recover₁ : Span.Location → StateT H₁ m₁ Unit)
    (abandon₂ recover₂ : Span.Location → StateT H₂ m₂ Unit)
    (hrec : ∀ l, L.rc.rel (· = ·) (recover₁ l) (recover₂ l)) (slice : ByteSlice) (core : Core) :
    L.rc.rel (SameRes (ERel (LexErrRel L.re) (ORel (LocRel L.rr))))
      (lexSliceStep false abandon₁ recover₁ slice core)
      (lexSliceStep false abandon₂ recover₂ slice core) := by
  unfold lexSliceStep
  obtain ⟨v, iv, loc, act, d, sb, hold⟩ := core
  cases act
  all_goals dsimp only
  all_goals first
    | (refine L.rc.bind (hrec _) ?_; rintro _ _ rfl)
    | skip
  all_goals simp only [pure_bind]
  all_goals first
    | exact rel_pure ⟨trivial, rfl⟩
    | refine L.rc.bind (lexFrom_sim hc recover₁ recover₂ hrec slice _ 0 rfl _ none none trivial) ?_
      rintro ⟨r1, c1⟩ ⟨r2, c2⟩ ⟨hres, hcore⟩
      dsimp only at hres hcore ⊢
      subst hcore
      match r1, r2, hres with
      | .ok h1, .ok h2, hh => exact rel_pure ⟨hh, rfl⟩
      | .error f1, .error f2, hf =>
        refine L.rc.bind (failCall_sim abandon₁ abandon₂ f1 f2 hf false c1) ?_
        rintro ⟨e1, d1⟩ ⟨e2, d2⟩ ⟨he, hd⟩
        dsimp only at he hd ⊢
        subst hd
        exact rel_pure ⟨he, rfl⟩

/-- The end of the input after the token in progress is finished, from the same lexer state
and related results. -/
theorem lexEnd_tail_sim (hc : VConsumers L) (location : Span.Location)
    (r₁ : Except (BSmtLib.Lexer.Internal.VNaive.Failure E₁) (Option (Span.Located R₁)))
    (r₂ : Except (BSmtLib.Lexer.Internal.VNaive.Failure E₂) (Option (Span.Located R₂)))
    (hr : StepRes L r₁ r₂) (core : Core) :
    L.rc.rel (SameRes (ERel (VFailRel L.re) (FlowRel (LocRel L.rr))))
      (match (generalizing := false) r₁ with
        | .error failure => pure (.error failure, core)
        | .ok (some located) => pure (.ok (.break located), core)
        | .ok none =>
          if core.holding then pure (.ok .continue, core)
          else do
            let (result, core) ← handOverAt (H := H₁) (m := m₁) core
              { category := .endOfFile, content := .empty, start := location, «end» := location }
              (.inr ⟨rfl, rfl⟩)
            pure (match result with
              | .ok none => (.ok .continue, core)
              | .ok (some located) => (.ok (.break located), core)
              | .error failure => (.error failure, core)))
      (match (generalizing := false) r₂ with
        | .error failure => pure (.error failure, core)
        | .ok (some located) => pure (.ok (.break located), core)
        | .ok none =>
          if core.holding then pure (.ok .continue, core)
          else do
            let (result, core) ← handOverAt (H := H₂) (m := m₂) core
              { category := .endOfFile, content := .empty, start := location, «end» := location }
              (.inr ⟨rfl, rfl⟩)
            pure (match result with
              | .ok none => (.ok .continue, core)
              | .ok (some located) => (.ok (.break located), core)
              | .error failure => (.error failure, core))) := by
  match r₁, r₂, hr with
  | .error f1, .error f2, hf => exact rel_pure ⟨hf, rfl⟩
  | .ok (some x1), .ok (some x2), hx => exact rel_pure ⟨hx, rfl⟩
  | .ok none, .ok none, _ =>
    dsimp only
    split
    · exact rel_pure ⟨trivial, rfl⟩
    · refine L.rc.bind (handOverAt_sim hc _ _ _) ?_
      rintro ⟨s1, d1⟩ ⟨s2, d2⟩ ⟨hs, hd⟩
      dsimp only at hs hd ⊢
      subst hd
      match s1, s2, hs with
      | .ok none, .ok none, _ => exact rel_pure ⟨trivial, rfl⟩
      | .ok (some _), .ok (some _), hx => exact rel_pure ⟨hx, rfl⟩
      | .error _, .error _, hf => exact rel_pure ⟨hf, rfl⟩

theorem lexEnd_sim (hc : VConsumers L) (core : Core) :
    L.rc.rel (SameRes (ERel (VFailRel L.re) (FlowRel (LocRel L.rr))))
      (lexEnd (H := H₁) (m := m₁) core) (lexEnd (H := H₂) (m := m₂) core) := by
  unfold lexEnd
  simp only [hc.concrete]
  generalize withEq core.activity = w
  obtain ⟨a, ha⟩ := w
  cases a
  all_goals dsimp only
  case token p =>
    generalize finishS (Token.Consume.isConcrete (H := H₂)) p core.location = r
    obtain ⟨r, hr⟩ := r
    cases r with
    | token l =>
      refine L.rc.bind (handOverAt_sim hc _ l _) ?_
      rintro ⟨r1, c1⟩ ⟨r2, c2⟩ ⟨hres, hcore⟩
      dsimp only at hres hcore ⊢
      subst hcore
      exact lexEnd_tail_sim hc _ r1 r2 hres c1
    | none =>
      refine L.rc.bind (Q := SameRes (StepRes L)) ?_ ?_
      · exact rel_pure ⟨trivial, rfl⟩
      rintro ⟨r1, c1⟩ ⟨r2, c2⟩ ⟨hres, hcore⟩
      dsimp only at hres hcore ⊢
      subst hcore
      exact lexEnd_tail_sim hc _ r1 r2 hres c1
    | error f =>
      refine L.rc.bind (Q := SameRes (StepRes L)) ?_ ?_
      · exact rel_pure ⟨⟨rfl, rfl, rfl⟩, rfl⟩
      rintro ⟨r1, c1⟩ ⟨r2, c2⟩ ⟨hres, hcore⟩
      dsimp only at hres hcore ⊢
      subst hcore
      exact lexEnd_tail_sim hc _ r1 r2 hres c1
  all_goals
    refine L.rc.bind (Q := SameRes (StepRes L)) ?_ ?_
    · exact rel_pure ⟨trivial, rfl⟩
    rintro ⟨r1, c1⟩ ⟨r2, c2⟩ ⟨hres, hcore⟩
    dsimp only at hres hcore ⊢
    subst hcore
    exact lexEnd_tail_sim hc _ r1 r2 hres c1

theorem lexEofStep_sim [LawfulMonad m₁] [LawfulMonad m₂] (hc : VConsumers L)
    (abandon₁ recover₁ : Span.Location → StateT H₁ m₁ Unit)
    (abandon₂ recover₂ : Span.Location → StateT H₂ m₂ Unit)
    (hrec : ∀ l, L.rc.rel (· = ·) (recover₁ l) (recover₂ l)) (core : Core) :
    L.rc.rel (SameRes (ERel (LexErrRel L.re) (FlowRel (LocRel L.rr))))
      (lexEofStep false abandon₁ recover₁ core) (lexEofStep false abandon₂ recover₂ core) := by
  unfold lexEofStep
  obtain ⟨v, iv, loc, act, d, sb, hold⟩ := core
  cases act
  all_goals dsimp only
  all_goals first
    | (refine L.rc.bind (hrec _) ?_; rintro _ _ rfl)
    | skip
  all_goals simp only [pure_bind]
  all_goals refine L.rc.bind (lexEnd_sim hc _) ?_
  all_goals rintro ⟨r1, c1⟩ ⟨r2, c2⟩ ⟨hres, hcore⟩
  all_goals dsimp only at hres hcore ⊢
  all_goals subst hcore
  all_goals match r1, r2, hres with
    | .ok f1, .ok f2, hf => exact rel_pure ⟨hf, rfl⟩
    | .error f1, .error f2, hf =>
      first
        | exact rel_pure ⟨⟨hf.1, hf.2.1, rfl⟩, rfl⟩
        | refine L.rc.bind (failCall_sim abandon₁ abandon₂ f1 f2 hf true c1) ?_
          rintro ⟨e1, d1⟩ ⟨e2, d2⟩ ⟨he, hd⟩
          dsimp only at he hd ⊢
          subst hd
          exact rel_pure ⟨he, rfl⟩

end

end BSmtLib.Facts.Proofs.PublicApi.VLink
