import BSmtLib.Proofs.V1NaiveWRustPort.NormalStep

/-!
# The Rust port's steps for a token in progress

The arms of the Rust port's `lexStep` for a token in progress, each against the naive lexer's
pure run: an arm lexes on the token from the lexer's index; it may finish the token there, and
then the step goes on in the normal state (`afterStep_wp`).
-/

namespace BSmtLib.Proofs.Lexer.V1NaiveWRustPort

open BSmtLib.Proofs.Adapter V1Naive BSmtLib.Proofs.Simulation
open Lexer.Slice (get? get)

section

variable {floor : Option Nat} {low : Nat}

/-- What an arm of `lexStep` keeps: the step's postcondition, with the lexer's index of its
offset unchanged, and the normal state if the arm consumed nothing. -/
def ArmPost (v : Version) (input : ByteSlice) (st : St) (location : Location) (start : Nat)
    (coll : Collector) (held : List Lexeme) (next : Nat) (c : WCore) (coll' : Collector) : Prop :=
  StepPost v input st location start coll held next c coll' ∧ c.base = start ∧
    (next = start → c.state = .normal)

/-- An arm followed by `afterStep`, which goes on in the normal state if the arm consumed
nothing. -/
theorem afterStep_wp (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (s : BS floor low) (coll : Collector) (st : St)
    (location : Location) (held : List Lexeme)
    (arm : M floor low {next : Nat // start ≤ next})
    (harm : WP arm s coll
      (fun r s' coll' => ArmPost v input st location start coll held r.1 s'.val coll')
      (fun _ s' coll' => StepFails v input st location start coll held s'.val coll')) :
    WP (arm >>= fun n => Lexer.WRustPort.afterStep (H := Collector) (m := Id) (R := Empty)
        (E := Unit) input start hstart n) s coll
      (fun r s' coll' => StepPost v input st location start coll held r.1 s'.val coll')
      (fun _ s' coll' => StepFails v input st location start coll held s'.val coll') := by
  apply wp_bind
  refine wp_mono harm ?_ (fun _ _ _ h => h)
  intro n s' coll' ⟨hpost, hbase, hnormal⟩
  unfold Lexer.WRustPort.afterStep
  apply wp_dite
  · intro _
    exact wp_pure _ hpost
  · intro hn
    have hn' : n.1 = start := by have := n.2; omega
    obtain ⟨st', location', held', hfix, -, hagree, hloc, hholds, hbytes, heq⟩ := hpost
    have hidle : st' = .idle := by
      cases st' with
      | idle => rfl
      | token p =>
        have := hagree.1.2
        rw [hnormal hn'] at this
        exact this.elim
    subst hidle
    rw [hn'] at heq hloc
    exact wp_recurse (f := fun (r : {next : Nat // start < next}) => r.1)
      (lexNormal_wp v input start hstart s' coll' location' held'
        ⟨hfix, hbase, hagree, hloc, hholds, hbytes⟩) heq

/-- An arm that has handed the token over alone, ended at `pos`, and gone back to the normal
state: `s0` is the lexer state before the hand-over, `s2` the one after. -/
theorem armPost_finish {v : Version} {input : ByteSlice} {st : St} {location : Location}
    {start : Nat} {coll : Collector} {held : List Lexeme} {s0 s2 : WCore} {coll2 : Collector}
    {pos : Nat} {l : Lexeme} {locp : Location}
    (hfix : Fixed v s0) (hbase : s0.base = start) (hpos : start ≤ pos)
    (hbytes : s0.batch.bytes = input.byteArray)
    (h2 : s2.version = s0.version ∧ s2.recovers = s0.recovers ∧ s2.discard = s0.discard ∧
      s2.recoveryState = s0.recoveryState ∧ s2.state = .normal ∧ s2.offset = s0.offset ∧
      s2.base = s0.base ∧ s2.line = s0.line ∧ s2.lineStart = s0.lineStart ∧
      s2.batch = s0.batch.clear s0.offset)
    (hlocp : LocAt s0 s0.offset s0.base pos locp)
    (hc : pending v coll2 [] = pending v coll (held ++ [l]))
    (heq : feedFrom v input st location start = Prep [l] (feedFrom v input .idle locp pos)) :
    ArmPost v input st location start coll held pos s2 coll2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := h2
  refine ⟨⟨.idle, locp, [], ⟨e1.trans hfix.1, e2.trans hfix.2, e3.trans hfix.3, e4.trans hfix.4⟩,
    by rw [e7, hbase]; exact hpos, e5, ?_, by rw [e10]; exact holds_clear _ _,
    by rw [e10]; exact hbytes, ?_⟩, e7.trans hbase, fun _ => e5⟩
  · obtain ⟨h1, h2, h3⟩ := hlocp
    refine ⟨?_, by rw [e8]; exact h2, by rw [e9]; exact h3⟩
    rw [e6, e7]; exact h1
  · rw [heq, outcome_prep, outcome_pending_congr hc]

/-- An arm that has left the token in progress at `pos`, after `start`: `s0` is the lexer state
when the arm started, `s2` the one it leaves. -/
theorem armPost_pending {v : Version} {input : ByteSlice} {st : St} {location : Location}
    {start : Nat} {coll : Collector} {held : List Lexeme} {s0 s2 : WCore}
    {pos : Nat} {q : Pending} {locp : Location}
    (hfix : Fixed v s0) (hbase : s0.base = start) (hpos : start < pos)
    (hholds : Holds s0.batch held) (hbytes : s0.batch.bytes = input.byteArray)
    (h2 : s2.version = s0.version ∧ s2.recovers = s0.recovers ∧ s2.discard = s0.discard ∧
      s2.recoveryState = s0.recoveryState ∧ s2.offset = s0.offset ∧ s2.base = s0.base ∧
      s2.batch = s0.batch)
    (hagree : StAgrees v (.token q) s2)
    (hlocp : LocAt s2 s0.offset s0.base pos locp)
    (heq : feedFrom v input st location start = feedFrom v input (.token q) locp pos) :
    ArmPost v input st location start coll held pos s2 coll := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := h2
  refine ⟨⟨.token q, locp, held, ⟨e1.trans hfix.1, e2.trans hfix.2, e3.trans hfix.3,
    e4.trans hfix.4⟩, by rw [e6, hbase]; exact Nat.le_of_lt hpos, hagree, ?_,
    by rw [e7]; exact hholds, by rw [e7]; exact hbytes, by rw [heq]⟩, e6.trans hbase,
    fun h => absurd h (by omega)⟩
  rw [e5, e6]; exact hlocp

/-- An arm that has ended the token at `pos` without handing it over, and gone back to the
normal state: `s0` is the lexer state when the arm started, `s2` the one it leaves. -/
theorem armPost_idle {v : Version} {input : ByteSlice} {st : St} {location : Location}
    {start : Nat} {coll : Collector} {held : List Lexeme} {s0 s2 : WCore}
    {pos : Nat} {locp : Location}
    (hfix : Fixed v s0) (hbase : s0.base = start) (hpos : start < pos)
    (hholds : Holds s0.batch held) (hbytes : s0.batch.bytes = input.byteArray)
    (h2 : s2.version = s0.version ∧ s2.recovers = s0.recovers ∧ s2.discard = s0.discard ∧
      s2.recoveryState = s0.recoveryState ∧ s2.offset = s0.offset ∧ s2.base = s0.base ∧
      s2.batch = s0.batch ∧ s2.state = .normal)
    (hlocp : LocAt s2 s0.offset s0.base pos locp)
    (heq : feedFrom v input st location start = feedFrom v input .idle locp pos) :
    ArmPost v input st location start coll held pos s2 coll := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := h2
  refine ⟨⟨.idle, locp, held, ⟨e1.trans hfix.1, e2.trans hfix.2, e3.trans hfix.3,
    e4.trans hfix.4⟩, by rw [e6, hbase]; exact Nat.le_of_lt hpos, e8, ?_,
    by rw [e7]; exact hholds, by rw [e7]; exact hbytes, by rw [heq]⟩, e6.trans hbase,
    fun _ => e8⟩
  rw [e5, e6]; exact hlocp

/-- The location that the hand-over of a token computes for its end at `pos`, on the line of the
location of the step's index, with no line feed after it. -/
theorem stepLocation_eq {c : WCore} {low base start pos : Nat} {location : Location}
    (hloc : LocAt c c.offset c.base start location) (hb : c.base = start) (hbase : base = c.base)
    (hlow : low = c.offset)
    (hpos : start ≤ pos) :
    stepLocation c low base pos = afterColumns location (pos - start) := by
  obtain ⟨h1, h2, h3⟩ := hloc
  cases location
  simp only [stepLocation, afterColumns, Location.mk.injEq] at h1 h2 h3 ⊢
  subst hbase hlow
  refine ⟨?_, h2.symm, ?_⟩ <;> omega

/-- The location that the hand-over of a token computes for its end at `pos`, on the line of the
location of the index `j`, with no line feed between them. -/
theorem stepLocation_eq' {c : WCore} {low base j pos : Nat} {location : Location}
    (hloc : LocAt c c.offset c.base j location) (hbj : c.base ≤ j) (hbase : base = c.base)
    (hlow : low = c.offset) (hpos : j ≤ pos) :
    stepLocation c low base pos = afterColumns location (pos - j) := by
  obtain ⟨h1, h2, h3⟩ := hloc
  cases location
  simp only [stepLocation, afterColumns, Location.mk.injEq] at h1 h2 h3 ⊢
  subst hbase hlow
  refine ⟨?_, h2.symm, ?_⟩ <;> omega

/-- The agreement of a token in progress, in the state of the lexer. -/
theorem token_agrees {v : Version} {c : WCore} {p : Pending} {state : Lexer.LexerState}
    (h : StAgrees v (.token p) c) (hs : c.state = state) :
    TokenAgrees v state c.tokenStart (contentBytes c.tokenContent) p := by
  rw [← hs]; exact h.1

/-- The content buffer of a token in progress fits its array. -/
theorem token_fits {v : Version} {c : WCore} {p : Pending} (h : StAgrees v (.token p) c) :
    Fits c.tokenContent :=
  h.2

/-- The arm of `lexStep` for a quoted symbol closed by its pipe. -/
theorem arm_quotedSymbolClosed (v : Version) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (tokenStart : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low tokenStart) (s : BS floor low) (coll : Collector)
    (p : Pending) (location : Location) (held : List Lexeme)
    (hpre : StepPre v input (.token p) location held start s.val) (hlow : low = s.val.offset)
    (hts : tokenStart = s.val.tokenStart) (hb : base = s.val.base)
    (hstate : s.val.state = .quotedSymbolClosed) :
    WP (Lexer.WRustPort.lexQuotedSymbolClosed (H := Collector) (m := Id) (R := Empty) (E := Unit)
        input start tokenStart base h) s coll
      (fun r s' coll' => ArmPost v input (.token p) location start coll held r.1 s'.val coll')
      (fun _ s' coll' => StepFails v input (.token p) location start coll held s'.val coll') := by
  obtain ⟨hps, hm, hcont⟩ := token_agrees hpre.agrees hstate
  have hC := feedFrom_end v input hstart (q := p) (location := location)
    (advance_end_quotedSymbolClosed hm)

  unfold Lexer.WRustPort.lexQuotedSymbolClosed Lexer.WRustPort.expectDelimiter
  rw [get_eq hstart]
  apply wp_bind
  apply wp_ite
  · intro hnd
    have hnd' : V1Naive.isDelimiter input[start] = false := by
      rw [← isDelimiter_eq]; simpa using hnd
    rw [hnd'] at hC
    unfold Lexer.WRustPort.errorAt Lexer.WRustPort.errorWith
    wp_walk
    refine stepFails_here ?_ hpre.holds hpre.fixed.1 hpre.fixed.2
    rw [hC]
    simp only [Bool.false_eq_true, ↓reduceIte]
  · intro hd
    have hd' : V1Naive.isDelimiter input[start] = true := by
      rw [← isDelimiter_eq]; simpa using hd
    rw [hd'] at hC
    simp only [↓reduceIte] at hC
    apply wp_pure
    apply wp_bind
    refine sinkStored_wp v .quotedSymbol (.mkAtByte start) tokenStart base h held s hpre.holds
      coll hpre.fixed.recovers hpre.fixed.version (token_fits hpre.agrees) ?_ ?_
    · intro s1 coll1 hk1 hb1 hc1
      obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk1
      unfold Lexer.WRustPort.setNormal
      apply wp_bind; apply wp_modifyCore
      apply wp_pure
      have hloc := hpre.loc
      refine armPost_finish hpre.fixed hpre.base (Nat.le_refl _) hpre.bytes
        ⟨k1, k4, k3, k5, rfl, k8, k9, k10, k11, hb1⟩ hloc hc1 ?_
      rw [hC, show stepLocation s.val low base (Lexer.Slice.TokenEnd.mkAtByte start).position
        = location from (stepLocation_eq hloc hpre.base hb hlow (Nat.le_refl _)).trans
          (by rw [Nat.sub_self]; rfl), hts, ← hps, ← hcont]
    · intro hn e s' coll'
      apply stepFails_of_none
      show outcome v _ _ = none
      rw [hC, outcome_prep]
      rw [show stepLocation s.val low base (Lexer.Slice.TokenEnd.mkAtByte start).position
        = location from (stepLocation_eq hpre.loc hpre.base hb hlow (Nat.le_refl _)).trans
          (by rw [Nat.sub_self]; rfl), hts, ← hps, ← hcont] at hn
      rw [hn, outcome_none_left]

end

end BSmtLib.Proofs.Lexer.V1NaiveWRustPort
