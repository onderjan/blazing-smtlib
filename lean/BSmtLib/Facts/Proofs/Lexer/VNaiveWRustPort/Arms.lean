module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.NormalStep
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.WRustPort.Slice
import all BSmtLib.Span
import all BSmtLib.Lexer.Error

@[expose] public section

/-!
# The Rust port's steps for a token in progress

The arms of the Rust port's `lexStep` for a token in progress, each against the naive lexer's
pure run: an arm lexes on the token from the lexer's index; it may finish the token there, and
then the step goes on in the normal state (`afterStep_wp`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Arms

open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Lexer.Internal.WRustPort.Slice (get? get)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Batch
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Basic
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.NormalStep
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Push
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.StartWs
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Delimiters BSmtLib.Lexer.Internal.VNaive

section

variable {floor : Option Nat} {low : Nat}
variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Version}

/-- What an arm of `lexStep` keeps: the step's postcondition, with the lexer's index of its
offset unchanged, and the normal state if the arm consumed nothing. -/
def ArmPost (C : BSmtLibSpec.Lexer.Consumer) (v : Version) (hd : Bool) (iv : Version)
    (input : ByteSlice) (st : St) (location : Span.Location) (start : Nat) (ver : Version)
    (coll : List Handed) (held : List Lexeme) (next : Nat) (c : WP.WCore) (coll' : List Handed) :
    Prop :=
  StepPost C v hd iv input st location start ver coll held next c coll' ∧ c.base = start ∧
    (next = start → c.state = .normal)

/-- An arm followed by `afterStep`, which goes on in the normal state if the arm consumed
nothing. -/
theorem afterStep_wp (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (s : WP.BS floor low) (coll : List Handed) (st : St)
    (location : Span.Location) (held : List Lexeme)
    (arm : WP.M C floor low {next : Nat // start ≤ next})
    (harm : WP arm s coll
      (fun r s' coll' =>
        ArmPost C v hd iv input st location start s.val.version coll held r.1 s'.val coll')
      (fun e s' coll' =>
        StepFails C v hd iv input st location start s.val.version coll held e s'.val coll')) :
    WP (arm >>= fun n => Lexer.Internal.WRustPort.afterStep (H := Answering C) (m := AnswerM)
        (R := C.Result) (E := Option C.Error) input start hstart n) s coll
      (fun r s' coll' =>
        StepPost C v hd iv input st location start s.val.version coll held r.1 s'.val coll')
      (fun e s' coll' =>
        StepFails C v hd iv input st location start s.val.version coll held e s'.val coll') := by
  apply WP.wp_bind
  refine WP.wp_mono harm ?_ (fun _ _ _ h => h)
  intro n s' coll' ⟨hpost, hbase, hnormal⟩
  unfold Lexer.Internal.WRustPort.afterStep
  apply WP.wp_dite
  · intro _
    exact WP.wp_pure _ hpost
  · intro hn
    have hn' : n.1 = start := by have := n.2; omega
    obtain ⟨st', location', held', hfix, -, hagree, hloc, hholds, hbytes, heq⟩ := hpost
    have hidle : st' = .idle := by
      cases st' with
      | idle => rfl
      | token p =>
        have := hagree.1
        rw [hnormal hn'] at this
        exact this.2.elim
    subst hidle
    rw [hn'] at heq hloc
    exact wp_recurse (f := fun (r : {next : Nat // start < next}) => r.1)
      (lexNormal_wp v input start hstart s' coll' location' held'
        ⟨hfix, hbase, hagree, hloc, hholds, hbytes⟩) heq

/-- An arm that has handed the token over alone, ended at `pos`, and gone back to the normal
state: `s0` is the lexer state before the hand-over, `s2` the one after. -/
theorem armPost_finish {v : Version} {input : ByteSlice} {st : St} {location : Span.Location}
    {start : Nat} {coll : List Handed} {held : List Lexeme} {s0 s2 : WP.WCore} {ver : Version}
    {coll2 : List Handed} {pos : Nat} {l : Lexeme} {locp : Span.Location}
    (hfix : Fixed v hd iv s0) (hbase : s0.base = start) (hpos : start ≤ pos)
    (hbytes : s0.batch.bytes = input.byteArray)
    (h2 : ((s2.version == .v2_0) = (s0.version == .v2_0) ∧
        s2.initialVersion = s0.initialVersion) ∧ s2.recovers = s0.recovers ∧
      (s2.discardedFrom, s2.holding) = (s0.discardedFrom, s0.holding) ∧
      s2.recoveryState = s0.recoveryState ∧ s2.state = .normal ∧ s2.offset = s0.offset ∧
      s2.base = s0.base ∧ s2.line = s0.line ∧ s2.lineStart = s0.lineStart ∧
      s2.batch = s0.batch.clear s0.offset)
    (hlocp : LocAt s0 s0.offset s0.base pos locp)
    (hc : pending C s0.holding s2.version coll2 [] =
      pending C s0.holding s0.version coll (held ++ [l]))
    (heq : feedFrom v C.concrete input st location start =
      Prep [l] (feedFrom v C.concrete input .idle locp pos))
    (hver : s0.version = ver := by first | rfl | assumption) :
    ArmPost C v hd iv input st location start ver coll held pos s2 coll2 := by
  subst hver
  obtain ⟨⟨e1, e1'⟩, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := h2
  rw [hfix.holding] at hc
  refine ⟨⟨.idle, locp, [], ⟨e1.trans hfix.1, e2.trans hfix.2, (Prod.mk.inj e3).1.trans hfix.3,
    (Prod.mk.inj e3).2.trans hfix.4, e4.trans hfix.5, e1'.trans hfix.6⟩,
    by rw [e7, hbase]; exact hpos, e5, ?_, by rw [e10]; exact holds_clear _ _,
    by rw [e10]; exact hbytes, ?_⟩, e7.trans hbase, fun _ => e5⟩
  · obtain ⟨h1, h2, h3⟩ := hlocp
    refine ⟨?_, by rw [e8]; exact h2, by rw [e9]; exact h3⟩
    rw [e6, e7]; exact h1
  · rw [heq, outcome_pending_prep, outcome_pending_congr hc]

/-- An arm that has left the token in progress at `pos`, after `start`: `s0` is the lexer state
when the arm started, `s2` the one it leaves. -/
theorem armPost_pending {v : Version} {input : ByteSlice} {st : St} {location : Span.Location}
    {start : Nat} {coll : List Handed} {held : List Lexeme} {s0 s2 : WP.WCore} {ver : Version}
    {pos : Nat} {q : Pending} {locp : Span.Location}
    (hfix : Fixed v hd iv s0) (hbase : s0.base = start) (hpos : start < pos)
    (hholds : Holds s0.batch held) (hbytes : s0.batch.bytes = input.byteArray)
    (h2 : s2.version = s0.version ∧ s2.recovers = s0.recovers ∧
      (s2.discardedFrom, s2.holding) = (s0.discardedFrom, s0.holding) ∧
      s2.recoveryState = s0.recoveryState ∧ s2.offset = s0.offset ∧ s2.base = s0.base ∧
      s2.batch = s0.batch)
    (hagree : StAgrees v C.concrete (.token q) s2)
    (hlocp : LocAt s2 s0.offset s0.base pos locp)
    (heq : feedFrom v C.concrete input st location start =
      feedFrom v C.concrete input (.token q) locp pos)
    (hi : s2.initialVersion = s0.initialVersion := by rfl)
    (hver : s0.version = ver := by first | rfl | assumption) :
    ArmPost C v hd iv input st location start ver coll held pos s2 coll := by
  subst hver
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := h2
  refine ⟨⟨.token q, locp, held, ⟨by rw [e1]; exact hfix.1, e2.trans hfix.2,
    (Prod.mk.inj e3).1.trans hfix.3, (Prod.mk.inj e3).2.trans hfix.4,
    e4.trans hfix.5, hi.trans hfix.6⟩, by rw [e6, hbase]; exact Nat.le_of_lt hpos, hagree, ?_,
    by rw [e7]; exact hholds, by rw [e7]; exact hbytes, by rw [heq, e1]⟩, e6.trans hbase,
    fun h => absurd h (by omega)⟩
  rw [e5, e6]; exact hlocp

/-- An arm that has ended the token at `pos` without handing it over, and gone back to the
normal state: `s0` is the lexer state when the arm started, `s2` the one it leaves. -/
theorem armPost_idle {v : Version} {input : ByteSlice} {st : St} {location : Span.Location}
    {start : Nat} {coll : List Handed} {held : List Lexeme} {s0 s2 : WP.WCore} {ver : Version}
    {pos : Nat} {locp : Span.Location}
    (hfix : Fixed v hd iv s0) (hbase : s0.base = start) (hpos : start < pos)
    (hholds : Holds s0.batch held) (hbytes : s0.batch.bytes = input.byteArray)
    (h2 : s2.version = s0.version ∧ s2.recovers = s0.recovers ∧
      (s2.discardedFrom, s2.holding) = (s0.discardedFrom, s0.holding) ∧
      s2.recoveryState = s0.recoveryState ∧ s2.offset = s0.offset ∧ s2.base = s0.base ∧
      s2.batch = s0.batch ∧ s2.state = .normal)
    (hlocp : LocAt s2 s0.offset s0.base pos locp)
    (heq : feedFrom v C.concrete input st location start =
      feedFrom v C.concrete input .idle locp pos)
    (hi : s2.initialVersion = s0.initialVersion := by rfl)
    (hver : s0.version = ver := by first | rfl | assumption) :
    ArmPost C v hd iv input st location start ver coll held pos s2 coll := by
  subst hver
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := h2
  refine ⟨⟨.idle, locp, held, ⟨by rw [e1]; exact hfix.1, e2.trans hfix.2,
    (Prod.mk.inj e3).1.trans hfix.3, (Prod.mk.inj e3).2.trans hfix.4,
    e4.trans hfix.5, hi.trans hfix.6⟩, by rw [e6, hbase]; exact Nat.le_of_lt hpos, e8, ?_,
    by rw [e7]; exact hholds, by rw [e7]; exact hbytes, by rw [heq, e1]⟩, e6.trans hbase,
    fun _ => e8⟩
  rw [e5, e6]; exact hlocp


/-- The location that the hand-over of a token computes for its end at `pos`, on the line of the
location of the step's index, with no line feed after it. -/
theorem stepLocation_eq {c : WP.WCore} {low base start pos : Nat} {location : Span.Location}
    (hloc : LocAt c c.offset c.base start location) (hb : c.base = start) (hbase : base = c.base)
    (hlow : low = c.offset)
    (hpos : start ≤ pos) :
    stepLocation c low base pos = afterColumns location (pos - start) := by
  obtain ⟨h1, h2, h3⟩ := hloc
  cases location
  simp only [stepLocation, afterColumns, Span.Location.Internal.new_inj] at h1 h2 h3 ⊢
  subst hbase hlow
  refine ⟨?_, h2.symm, ?_⟩ <;> omega

/-- The location that the hand-over of a token computes for its end at `pos`, on the line of the
location of the index `j`, with no line feed between them. -/
theorem stepLocation_eq' {c : WP.WCore} {low base j pos : Nat} {location : Span.Location}
    (hloc : LocAt c c.offset c.base j location) (hbj : c.base ≤ j) (hbase : base = c.base)
    (hlow : low = c.offset) (hpos : j ≤ pos) :
    stepLocation c low base pos = afterColumns location (pos - j) := by
  obtain ⟨h1, h2, h3⟩ := hloc
  cases location
  simp only [stepLocation, afterColumns, Span.Location.Internal.new_inj] at h1 h2 h3 ⊢
  subst hbase hlow
  refine ⟨?_, h2.symm, ?_⟩ <;> omega

/-- The agreement of a token in progress, in the state of the lexer. -/
theorem token_agrees {v : Version} {c : WP.WCore} {p : Pending}
    {state : Lexer.Internal.Helpers.LexerState}
    (h : StAgrees v C.concrete (.token p) c) (hs : c.state = state) :
    TokenAgrees v C.concrete state c.tokenStart (contentBytes c.tokenContent) p := by
  rw [← hs]; exact h.1

/-- The content buffer of a token in progress fits its array. -/
theorem token_fits {v : Version} {c : WP.WCore} {p : Pending} (h : StAgrees v
    C.concrete (.token p) c) :
    Fits c.tokenContent :=
  h.2

/-- The arm of `lexStep` for a quoted symbol closed by its pipe. -/
theorem arm_quotedSymbolClosed (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Span.Location) (base : Nat)
    (h : Lexer.Internal.WRustPort.Started floor low tokenStart) (s : WP.BS floor low)
    (coll : List Handed)
    (p : Pending) (location : Span.Location) (held : List Lexeme)
    (hpre : StepPre C v hd iv input (.token p) location held start s.val)
        (hlow : low = s.val.offset)
    (hts : tokenStart = s.val.tokenStart) (hb : base = s.val.base)
    (hstate : s.val.state = .quotedSymbolClosed) :
    WP (Lexer.Internal.WRustPort.lexQuotedSymbolClosed (H := Answering C) (m := AnswerM)
        (R := C.Result)
        (E := Option C.Error)
        input start hstart tokenStart base h) s coll
      (fun r s' coll' => ArmPost C v hd iv input (.token p) location start s.val.version coll held
          r.1 s'.val coll')
      (fun e s' coll' => StepFails C v hd iv input (.token p) location start s.val.version coll held
          e s'.val coll') := by
  obtain ⟨hps, hm, hcont⟩ := token_agrees hpre.agrees hstate
  have hC := feedFrom_end v C.concrete input hstart (q := p) (location := location)
    (advance_end_quotedSymbolClosed hm)

  unfold Lexer.Internal.WRustPort.lexQuotedSymbolClosed Lexer.Internal.WRustPort.expectDelimiter
  rw [get_eq hstart]
  apply WP.wp_bind
  apply WP.wp_ite
  · intro hnd
    have hnd' : Lexer.Internal.VNaive.isDelimiter input[start] = false := by
      rw [← isDelimiter_eq]; simpa using hnd
    rw [hnd'] at hC
    unfold Lexer.Internal.WRustPort.errorAt Lexer.Internal.WRustPort.errorWith
    wp_walk
    refine stepFails_here ?_ hpre.holds
      ⟨hpre.fixed.1, hpre.fixed.2, hpre.fixed.3, hpre.fixed.4, hpre.fixed.5, hpre.fixed.6⟩ rfl
    rw [hC]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hps]
    have := hpre.base
    failure_eq hpre.loc
  · intro hd
    have hd' : Lexer.Internal.VNaive.isDelimiter input[start] = true := by
      rw [← isDelimiter_eq]; simpa using hd
    rw [hd'] at hC
    simp only [↓reduceIte] at hC
    apply WP.wp_pure
    apply WP.wp_bind
    refine sinkStored_wp .quotedSymbol (.mkAtByte start) tokenStart base h held s hpre.holds
      coll hpre.fixed.recovers (token_fits hpre.agrees) ?_ ?_
    · intro s1 coll1 hk1 hb1 hc1
      obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
      unfold Lexer.Internal.WRustPort.setNormal
      apply WP.wp_bind; apply WP.wp_modifyCore
      apply WP.wp_pure
      have hloc := hpre.loc
      refine armPost_finish hpre.fixed hpre.base (Nat.le_refl _) hpre.bytes
        ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩ hloc hc1 ?_
      rw [hC, show stepLocation s.val low base (Lexer.Internal.WRustPort.Slice.TokenEnd.mkAtByte
          start).position
        = location from (stepLocation_eq hloc hpre.base hb hlow (Nat.le_refl _)).trans
          (by rw [Nat.sub_self]; rfl), hts, ← hps, ← hcont]
    · intro e s' p d hn hss
      rw [show stepLocation s.val low base (Lexer.Internal.WRustPort.Slice.TokenEnd.mkAtByte
          start).position
        = location from (stepLocation_eq hpre.loc hpre.base hb hlow (Nat.le_refl _)).trans
          (by rw [Nat.sub_self]; rfl), hts, ← hps, ← hcont] at hn
      exact stepFails_of_stops' (hbytes := by first | assumption | exact hpre.bytes) hss hpre.fixed
          ⟨_, by rw [hC, outcome_pending_prep] <;> rfl⟩ hn

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Arms
