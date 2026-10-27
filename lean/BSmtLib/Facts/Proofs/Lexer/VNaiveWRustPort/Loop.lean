module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Slice
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VBytes
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Taken
import all BSmtLib.Lexer.Error
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Span
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor

@[expose] public section

/-!
# The Rust port's loop over the stops in a slice, against the naive lexer

`loop`: the Rust port's loop over a slice with the consumer's stops (`lexSliceFrom`) gives what
the naive lexer fed the bytes from there gives (`LoopRel`). The loop starts from a lexer state
that is the naive lexer's pure state at an index. The two give:
- the same tokens taken;
- the same result, or failures the specification formalism (`BSmtLibSpec`) does not tell apart,
  none with the adapter's error `none` for a consumer that does not take whitespace and comments;
- lexer states that correspond (`LoopOk`).

Each run of the loop up to a stop (`sliceRun_ok`) and the naive lexer (`vBytes_out`) do what the
same outcome of the pure run says. At a relex or a break, the Rust port resumes after the lexeme,
where the naive lexer starts again (`Restarts`), and the loop goes on by induction on the bytes
left after the floor.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Loop

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.Consumers.VSession
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps BSmtLib.Facts.Proofs.Lexer.VNaive.Facts
open BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Batch
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Slice
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Taken
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VBytes BSmtLib.Lexer.Internal.VNaive

variable {C : BSmtLibSpec.Lexer.Consumer}

theorem afterByte_valid {location : Span.Location} (h : location.column ≤ location.offset)
    (c : UInt8) : (location.afterByte c).column ≤ (location.afterByte c).offset := by
  unfold Span.Location.afterByte Span.Location.afterColumn
  split
  · exact Nat.zero_le _
  · show location.column + 1 ≤ location.offset + 1
    omega

theorem advanceLoc_valid (bs : List UInt8) :
    ∀ {location : Span.Location}, location.column ≤ location.offset →
      (advanceLoc location bs).column ≤ (advanceLoc location bs).offset := by
  induction bs with
  | nil => intro location h; exact h
  | cons c bs ih => intro location h; exact ih (afterByte_valid h c)

theorem runS_bindA {α β : Type} (x : StateT (Answering C) AnswerM α)
    (k : α → StateT (Answering C) AnswerM β) (coll : List Handed) :
    runS (x >>= k) coll = runS (k (runS x coll).1) (runS x coll).2 := by
  simp only [runS, StateT.run_bind]
  generalize hr : (x.run {}).run coll = r
  obtain ⟨⟨a, h⟩, t⟩ := r
  rw [answering_eq' h {}]
  rfl

/-- The lexer state resumed at the end `location` of a lexeme handed over, after the loop stopped
there. -/
theorem resume_pre {input : ByteSlice} {iv : Version} {hd' : Bool} {p : Prog} {c : WP.WCore}
    {location : Span.Location} (resumed : Nat) (h : AfterStop hd' iv input.byteArray p none c)
    (hcol : location.column ≤ location.offset) :
    StepPre C p.ver hd' iv input .idle location [] resumed (c.resumeAt location resumed) :=
  ⟨⟨by show (c.version == .v2_0) = _; rw [h.version], h.recovers, h.discardedFrom, h.holding,
    h.recoveryState, h.initial⟩, rfl, rfl,
    ⟨by show location.offset = location.offset + (resumed - resumed); omega, rfl,
      by show location.offset - location.column + location.column = location.offset; omega⟩,
    holds_clear _ _, h.bytes⟩

/-- What the Rust port's loop over a slice and the naive lexer leave when they go on: the Rust
port's lexer state is the naive lexer's pure state at the end of the slice, or both discard from
the same location, where both lexers stand. -/
structure LoopOk (C : BSmtLibSpec.Lexer.Consumer) (c : WP.WCore) (n : Core) : Prop where
  version : c.version = n.version
  initial : c.initialVersion = n.initialVersion
  holding : c.holding = n.holding
  recovers : c.recovers = false
  recoveryState : c.recoveryState = none
  rest : (∃ st, n.activity = st.activity ∧ StAgrees n.version C.concrete st c ∧
      c.discardedFrom = none ∧ EofLoc c n.location) ∨
    (∃ s, n.activity = .discarding s ∧ c.discardedFrom = some s ∧ c.state = .normal ∧
      EofLoc c s ∧ n.location = s)

/-- The spans of a failure of the Rust port and one of the naive lexer, with the tokens taken: the
same for trailing input, and the span of the last token taken for the consumer's error. -/
abbrev SpanRel {ε : Type} (f : BSmtLib.Lexer.Internal.Failure (Option ε))
    (g : Lexer.Internal.VNaive.Failure (Option ε)) (t : List Handed) : Prop :=
  (f.kind = .lexical .unexpectedTrailingToken → f.span = g.span) ∧
    (∀ x, f.kind = .consumer (some x) → f.span = Cursor.handedSpan t)

/-- What the Rust port's loop over a slice and the naive lexer give alike: the same tokens taken,
the same version, and the same result, or failures alike as `preciseFailure` says. -/
def LoopRel (C : BSmtLibSpec.Lexer.Consumer)
    (rW : (Except (BSmtLib.Lexer.Internal.Failure (Option C.Error))
    (Option (Span.Located C.Result)) × WP.WCore) ×
      List Handed)
    (rV : VRes (Except (Lexer.Internal.VNaive.Failure (Option C.Error))
    (Option (Span.Located C.Result)))) : Prop :=
  rW.2 = rV.2 ∧ rW.1.2.version = rV.1.2.version ∧
  match rW.1.1, rV.1.1 with
  | .ok a, .ok b => a = b ∧ LoopOk C rW.1.2 rV.1.2
  | .error f, .error g => preciseFailure f.kind f.span = preciseFailure g.kind g.span ∧
      rW.1.2.discardedFrom = discardedOf rV.1.2 ∧ rW.1.2.recovers = false ∧
      (C.concrete = false → f.kind ≠ .consumer none) ∧ SpanRel f g rW.2
  | _, _ => False

theorem stAgrees_legacy {v v' : Version} {ws : Bool} {st : St} {c : WP.WCore}
    (h : (v == .v2_0) = (v' == .v2_0)) (hs : StAgrees v ws st c) : StAgrees v' ws st c := by
  have he : (v = Version.v2_0) = (v' = Version.v2_0) := by
    cases v <;> cases v' <;> first | rfl | (exfalso; revert h; decide) | simp
  cases st with
  | idle => exact hs
  | token p =>
    refine ⟨?_, hs.2⟩
    have h1 := hs.1
    unfold TokenAgrees TokenAgreesNoWs at h1 ⊢
    simp only [h, he] at h1 ⊢
    exact h1

theorem discardedOf_none {n : Core} (h : ∀ s, n.activity ≠ .discarding s) :
    discardedOf n = none := by
  unfold discardedOf
  split
  · rename_i s hs
    exact absurd hs (h s)
  · rfl

theorem causeFailure_trailing {ε : Type} {span : Span} :
    causeFailure (ε := ε) (.lexical .unexpectedTrailingToken) span =
      .trailing (toLocation span.start) := (rfl)

theorem loop (bytes : List UInt8) (initialOffset : Nat) :
    ∀ (N floor : Nat) (hfloor : initialOffset ≤ floor + 1) (position : Nat)
      (held : Option (Span.Located C.Result)) (core : WP.BS (some floor) 0) (coll : List Handed)
      (n : Core) (st : St),
      bytes.length + 1 - (floor + 1 - initialOffset) < N →
      StepPre C n.version n.holding n.initialVersion bytes.toByteArray.toByteSlice st n.location
        [] position core.val →
      core.val.version = n.version → n.activity = st.activity →
      n.location.offset = initialOffset + position → position ≤ bytes.length →
      LoopRel C
        (runS (Lexer.Internal.WRustPort.lexSliceFrom (H := Answering C) (m := AnswerM)
            (R := C.Result)
          (E := Option C.Error) bytes.toByteArray.toByteSlice initialOffset floor hfloor position
          (.ok .continue) held core) coll)
        (vBytes C n held (bytes.drop position) coll) := by
  intro N
  induction N with
  | zero => intro floor hfloor position held core coll n st hN; omega
  | succ N ih =>
  intro floor hfloor position held core coll n st hN hpre hver hact hoff hpos
  have hsize : bytes.toByteArray.toByteSlice.size = bytes.length := size_toByteSlice bytes
  -- the Rust port's loop up to a stop, and the naive lexer, as the outcome says
  have hW := sliceRun_ok n.version bytes.toByteArray.toByteSlice _ position (Nat.lt_succ_self _)
    core coll st n.location [] hpre
  have hV := vBytes_out C n.version (bytes.drop position) n st held coll hact rfl
  rw [hver] at hW
  unfold SliceOut at hW
  rw [pending_nil, feedFrom_toByteSlice n.version C.concrete bytes _ position rfl] at hW
  rw [Lexer.Internal.WRustPort.lexSliceFrom, runS_bindA]
  generalize runS (Lexer.Internal.WRustPort.lexSliceRun (H := Answering C) (m := AnswerM)
    (R := C.Result) (E := Option C.Error) bytes.toByteArray.toByteSlice position (.ok .continue)
    core) coll = rr at hW ⊢
  obtain ⟨⟨exit, c'⟩, coll'⟩ := rr
  generalize hO : outcome C n.holding (.cont ⟨coll, n.version⟩)
    (lexBytesF n.version C.concrete st n.location (bytes.drop position)) = O at hW hV
  rcases O with ⟨st', loc', p⟩ | ⟨ff, p⟩ | ⟨s, p⟩
  · obtain ⟨hex, hfix, hv', hag, hloc, hcl⟩ := hW
    simp only at hex hfix hv' hag hloc hcl
    subst hex hcl
    obtain ⟨n', hvb, ⟨a1, a2, a3, a4⟩, a5⟩ := hV
    rw [hvb]
    refine ⟨rfl, hv'.trans a2.symm, rfl, ⟨hv'.trans a2.symm, hfix.initial.trans a4.symm,
      hfix.holding.trans a3.symm, hfix.recovers, hfix.recoveryState, .inl ⟨st', a1, ?_,
      hfix.discardedFrom, by rw [a5]; exact hloc⟩⟩⟩
    exact stAgrees_legacy (by rw [a2, ← hv', hfix.version]) hag
  · obtain ⟨⟨hex, hk⟩, hst, hcl⟩ := hW
    simp only at hex hst hcl
    subst hex hcl
    obtain ⟨n', hvb, hk', a2, a3, a4⟩ := hV
    rw [hvb]
    exact ⟨rfl, hst.version.trans a2.symm, rfl,
      hst.discardedFrom.trans (discardedOf_none a4).symm,
      hst.recovers, fun _ => nofun, ⟨fun _ => rfl, fun x h => by cases h⟩⟩
  · obtain ⟨hx, hst, hcl⟩ := hW
    simp only at hx hst hcl
    subst hcl
    have hnv : n.location.column ≤ n.location.offset := by
      have := hpre.loc.2.2
      omega
    -- the Rust port resumes after the lexeme `l` the consumer stopped at, as the naive lexer
    -- starts again there
    have resume : ∀ (l : Lexeme) (k : Nat) (c'' : Core) (hold : Bool)
        (held' : Option (Span.Located C.Result)) (cR : WP.WCore),
        l.end = advanceLoc n.location ((bytes.drop position).take k) →
        c''.activity = .idle → c''.location = l.end → c''.version = p.ver →
        c''.holding = hold → c''.initialVersion = n.initialVersion →
        floor < l.end.offset →
        cR = { c'.val.resumeAt l.end (l.end.offset - initialOffset) with holding := hold } →
        hold = n.holding ∨ hold = true → c'.val.discardedFrom = none →
        ∀ (hfl : initialOffset ≤ l.end.offset + 1)
          (hb : cR.Bound (some l.end.offset) 0),
        LoopRel C
          (runS (if hres : l.end.offset - initialOffset < bytes.toByteArray.toByteSlice.size then
              Lexer.Internal.WRustPort.lexSliceFrom (H := Answering C) (m := AnswerM)
                  (R := C.Result)
                (E := Option C.Error) bytes.toByteArray.toByteSlice initialOffset l.end.offset hfl
                (l.end.offset - initialOffset) (.ok .continue) held' ⟨cR, hb⟩
            else pure (.ok held', cR)) p.taken)
          (vBytes C c'' held' ((bytes.drop position).drop k) p.taken) := by
      intro l k c'' hold held' cR hk ha'' hl'' hv'' hh'' hi'' hafter hcR hhold hdn hfl hb
      have hoffl : l.end.offset = initialOffset + position + min k (bytes.length - position) := by
        rw [hk, advanceLoc_offset, List.length_take, List.length_drop, hoff]
      have hcol : l.end.column ≤ l.end.offset := by rw [hk]; exact advanceLoc_valid _ hnv
      have hst' : AfterStop hold n.initialVersion bytes.toByteArray.toByteSlice.byteArray p none
          { c'.val with holding := hold } :=
        ⟨hst.version, hst.recovers, rfl, hdn, hst.recoveryState, hst.initial,
          hst.bytes⟩
      have hpre' := resume_pre (C := C) (l.end.offset - initialOffset) hst' hcol
      subst hcR
      by_cases hres : l.end.offset - initialOffset < bytes.toByteArray.toByteSlice.size
      · rw [dite_eq_left hres]
        rw [hsize] at hres
        have hdrop : (bytes.drop position).drop k = bytes.drop (l.end.offset - initialOffset) := by
          rw [List.drop_drop, hoffl]
          congr 1
          omega
        rw [hdrop]
        refine ih l.end.offset hfl (l.end.offset - initialOffset) held' _ p.taken c'' .idle
          (by omega) ?_ ?_ ha'' (by rw [hl'']; omega) (by omega)
        · rw [hv'', hh'', hi'', hl'']
          exact hpre'
        · show c'.val.version = c''.version
          rw [hst.version, hv'']
      · rw [dite_eq_right hres]
        rw [hsize] at hres
        have hdrop : (bytes.drop position).drop k = [] := by
          rw [List.drop_drop]
          apply List.drop_eq_nil_of_le
          omega
        rw [hdrop]
        refine ⟨rfl, ?_, rfl, ⟨?_, ?_, ?_, hst.recovers, hst.recoveryState,
          .inl ⟨.idle, ha'', rfl, hdn, ?_⟩⟩⟩
        · show c'.val.version = c''.version
          rw [hst.version, hv'']
        · show c'.val.version = c''.version
          rw [hst.version, hv'']
        · show c'.val.initialVersion = c''.initialVersion
          rw [hst.initial, hi'']
        · show hold = c''.holding
          rw [hh'']
        · show EofLoc _ c''.location
          rw [hl'']
          exact ⟨rfl, rfl, by show l.end.offset - l.end.column + l.end.column = l.end.offset; omega⟩
    cases s with
    | trailing l =>
      obtain ⟨g, rfl, hg, hsp⟩ := hx
      obtain ⟨n', hvb, a1, a2, a3⟩ := hV
      rw [hvb]
      refine ⟨rfl, hst.version.trans a1.symm, ?_,
        hst.discardedFrom.trans (discardedOf_none a3).symm,
        hst.recovers, fun _ => by rw [hg]; nofun, ⟨fun _ => by rw [hsp]; rfl,
        fun x h => by rw [hg] at h; cases h⟩⟩
      show preciseFailure g.kind g.span =
        preciseFailure (.lexical .unexpectedTrailingToken) (trailingSpan l)
      rw [hg, preciseFailure_trailing, preciseFailure_trailing, hsp]
      rfl
    | fail e d l =>
      obtain ⟨g, rfl, hg⟩ := hx
      obtain ⟨n', span', loc, hvb, a1, a2, a3⟩ := hV
      have hfs : ∀ x, g.kind = .consumer (some x) → g.span = Cursor.handedSpan p.taken := by
        intro x _
        obtain ⟨x', hx1, hx2, hx3⟩ :=
          outcome_failTaken C n.holding (failTaken_cont C _) _ e d l p hO
        rw [hg.2]
        exact (Cursor.handedSpan_eq hx1 hx2 hx3).symm
      rw [hvb]
      refine ⟨rfl, hst.version.trans a1.symm, ?_, hst.discardedFrom.trans a3.symm,
        hst.recovers, fun _ => by rw [hg.1]; nofun, ⟨fun h => (by rw [hg.1] at h; cases h), hfs⟩⟩
      show preciseFailure g.kind g.span = preciseFailure (.consumer (some e)) span'
      rw [hg.1]
      rfl
    | layout l =>
      obtain ⟨g, rfl, hg⟩ := hx
      obtain ⟨n', span', loc, hvb, a1, a2, a3⟩ := hV
      rw [hvb]
      refine ⟨rfl, hst.version.trans a1.symm, ?_,
        hst.discardedFrom.trans (discardedOf_none a3).symm,
        hst.recovers, fun hc => absurd hO (outcome_ne_layout hc
          (st_taken (by have := hpre.agrees; rwa [hc] at this)) l p),
        ⟨fun h => (by rw [hg.1] at h; cases h), fun x h => by rw [hg.1] at h; cases h⟩⟩
      show preciseFailure g.kind g.span = preciseFailure (.consumer none) span'
      rw [hg.1]
      rfl
    | brk r l nx =>
      rcases hx with ⟨a, rfl⟩ | ⟨l2, g, rfl, rfl, hg, hsp⟩
      · obtain ⟨⟨k, c'', hk, ha'', hl'', hv'', hh'', hi'', hvb⟩, -⟩ := hV
        rw [hvb]
        exact resume l k c'' true _ _ hk ha'' hl'' hv'' hh'' hi'' (a floor rfl) rfl (.inr rfl)
          hst.discardedFrom _ _
      · obtain ⟨-, ht⟩ := hV
        obtain ⟨n', hvb, a1, a2, a3⟩ := ht l2 rfl
        rw [hvb]
        refine ⟨rfl, hst.version.trans a1.symm, ?_,
          hst.discardedFrom.trans (discardedOf_none a3).symm,
        hst.recovers, fun _ => by rw [hg]; nofun, ⟨fun _ => by rw [hsp]; rfl,
          fun x h => by rw [hg] at h; cases h⟩⟩
        show preciseFailure g.kind g.span =
          preciseFailure (.lexical .unexpectedTrailingToken) (trailingSpan l2)
        rw [hg, preciseFailure_trailing, preciseFailure_trailing, hsp]
        rfl
    | brkX r l =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨k, c'', hk, ha'', hl'', hv'', hh'', hi'', hvb⟩ := hV
      rw [hvb]
      exact resume l k c'' true _ _ hk ha'' hl'' hv'' hh'' hi'' (a floor rfl) rfl (.inr rfl)
        hst.discardedFrom _ _
    | relex l =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨k, c'', hk, ha'', hl'', hv'', hh'', hi'', hvb⟩ := hV
      rw [hvb]
      have e : c'.val.resumeAt l.end (l.end.offset - initialOffset) =
          { c'.val.resumeAt l.end (l.end.offset - initialOffset) with holding := n.holding } := by
        rw [← hst.holding]
        rfl
      exact resume l k c'' n.holding held _ hk ha'' hl'' hv'' hh'' hi'' (a floor rfl) e
        (.inl rfl) hst.discardedFrom _ _
    | discard r l =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨n', hvb, ⟨a1, a2, a3, a4⟩, a5, k, hk⟩ := hV
      rw [hvb]
      have hcol : l.end.column ≤ l.end.offset := by rw [hk]; exact advanceLoc_valid _ hnv
      have hrest : EofLoc (c'.val.resumeAt l.end (l.end.offset - initialOffset)) l.end :=
        ⟨rfl, rfl, by show l.end.offset - l.end.column + l.end.column = l.end.offset; omega⟩
      cases r with
      | some r =>
        refine ⟨rfl, hst.version.trans a2.symm, rfl, ⟨hst.version.trans a2.symm,
          hst.initial.trans a4.symm, by rw [a3]; rfl, hst.recovers, hst.recoveryState,
          .inr ⟨l.end, a1, rfl, rfl, hrest, a5⟩⟩⟩
      | none =>
        refine ⟨rfl, hst.version.trans a2.symm, rfl, ⟨hst.version.trans a2.symm,
          hst.initial.trans a4.symm, by rw [a3]; exact hst.holding, hst.recovers,
          hst.recoveryState, .inr ⟨l.end, a1, rfl, rfl, hrest, a5⟩⟩⟩

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Loop
