module

public import BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Steps
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Helpers
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.WRustPort.Slice

@[expose] public section

/-!
# The loop of the normal state of the library's lexer and of `X1BatchInCore`

`lexNormalFrom_sim`: the loop of the normal state of the library's lexer, from a position at or
after its base, is simulated by that of `X1BatchInCore` from the index of the position, and
leaves the base at the position it returns. The proof is by induction on the bytes left; at each
byte it follows both lexers through the same branch, relating the reads, the run scans, the
conditions on positions and the contents to those on indices (`Positions` and the lemmas below),
and the helpers to theirs (`Core` to `Steps`).

The Rust port's code that `X1BatchInCore` runs differs from the library's lexer in form only:
its locals are empty and whether the consumer takes whitespace and comments is a value, so both
are read away first; it computes whether a token of the fast path is emitted as Rust does
(`emit_eq`); it throws the errors it forms; and it reads a window of two bytes after a string
literal's run where the library's lexer reads the byte after the closing quote only once it has
found the quote, which finds the string closed alike (`closedN_window`, `closedN_none`). Where
the first lexer's code comes first in the goal and would be split first,
`Simulation.SimF.hide_left` names it, so that the second lexer's dependent match is split first.
`lexNormal_sim` is the entry to the loop from the lexer's base.
-/

namespace BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Normal

open BSmtLib.Facts.Proofs.Lexer.Simulation.Steps
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Batch
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Core
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.HandOver
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Positions
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Steps
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Whitespace BSmtLib.Lexer.Error

/-- The position past the origin, for the index past the origin's index. -/
def pastMap (slice : ByteSlice) (h : slice.stop < USize.size) {origin : USize} {origin' : Nat}
    (eo : ix slice.start origin = origin') (ho : slice.start ≤ origin.toNat)
    (r : BSmtLib.Lexer.Internal.Past (inputOf slice h) origin) :
    Lexer.Internal.WRustPort.Past slice origin' :=
  ⟨ix slice.start r.val, by
    have := r.property.1; have := r.property.2
    have hs := (inputOf_stop (h := h))
    have hsz : slice.size = slice.stop - slice.start := rfl
    subst eo
    refine ⟨by simp only [ix]; omega, fun hlt => ?_⟩
    have := r.property.2 (by simp only [ix] at hlt; omega)
    simp only [ix]; omega⟩

section Positions

variable {slice : ByteSlice} {h : slice.stop < USize.size}

/-- A position is the end of the input exactly when its index is the size of the slice. -/
theorem beq_stop {p : USize} (hp : slice.start ≤ p.toNat) :
    (p == (inputOf slice h).stop) = (ix slice.start p == slice.size) := by
  have hsz : slice.size = slice.stop - slice.start := rfl
  have := slice.start_le_stop
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq, ← USize.toNat_inj, inputOf_stop]
  simp only [ix]
  omega

/-- A position is after another exactly when its index is after the other's. -/
theorem decide_gt {p q : USize} (hp : slice.start ≤ p.toNat) (hq : slice.start ≤ q.toNat) :
    decide (p > q) = decide (ix slice.start p > ix slice.start q) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, gt_iff_lt, USize.lt_iff_toNat_lt, ix]
  omega

end Positions

/-- The index of the position after one below the end of the input. -/
theorem ix_add_one_of_lt_stop {slice : ByteSlice} (h : slice.stop < USize.size) {p : USize}
    (hp : slice.start ≤ p.toNat) (hlt : p.toNat < slice.stop) :
    ix slice.start (p + 1) = ix slice.start p + 1 := by
  have := Lexer.CharClass.toNat_add_one_of_lt (position := p) (bound := (inputOf slice h).stop)
    (by rw [inputOf_stop]; exact hlt)
  simp only [ix, this]
  omega

/-- The batch held at a position, for that held at its index, with the indices of the second
lexer given by equations. -/
def heldMap' (start : Nat) {floor : Option Nat} {offset : Nat} {base p : USize} {base' p' : Nat}
    (eb : ix start base = base') (ep : ix start p = p') (ok : PosOk start base p)
    (r : {batch : Token.TokenBatch // BSmtLib.Lexer.Internal.Held floor offset base p batch}) :
    {batch : Token.TokenBatch // Lexer.Internal.WRustPort.Held floor offset base' p' batch} :=
  ⟨r.val, by subst eb ep; rw [← ok.sub]; exact r.property.1, r.property.2⟩

/-- A run that starts at or before the size of the slice ends at or before it. -/
theorem runEndBy_le_size (stops : UInt8 → Bool) (slice : ByteSlice) (i : Nat)
    (hi : i ≤ slice.size) : Lexer.Internal.WRustPort.Slice.runEndBy stops slice i ≤ slice.size := by
  fun_induction Lexer.Internal.WRustPort.Slice.runEndBy stops slice i with
  | case1 => omega
  | case2 j hj _ ih => exact ih (by omega)
  | case3 => exact hi

/-- A run that starts at or before the end of the input ends at or before it. -/
theorem runEnd_le_stop {slice : ByteSlice} (h : slice.stop < USize.size) (p : USize)
    (hp : slice.start ≤ p.toNat) (hps : p.toNat ≤ slice.stop) (mask : UInt8) :
    (Lexer.CharClass.runEnd (inputOf slice h) p mask).toNat ≤ slice.stop := by
  obtain ⟨h1, h2⟩ := runEnd_eq (h := h) p hp mask
  have hsz : slice.size = slice.stop - slice.start := rfl
  have := runEndBy_le_size (fun c => Lexer.CharClass.endsRun c mask) slice (idx slice p)
    (by simp only [idx]; omega)
  simp only [Lexer.Internal.WRustPort.Slice.runEnd] at h2
  simp only [idx] at h2 this
  omega

/-- How the normal state of `X1BatchInCore` finds a string literal closed at the
index `p` of the slice read by `get`: by a quote there and a byte after it that is not a quote,
which it gives with the index after the quote. -/
def closedN (get : Nat → Option UInt8) (p : Nat) : Option (Nat × UInt8) :=
  match get p with
  | some quote =>
    if quote == byte! '"' then
      match get (p + 1) with
      | some next => if next != byte! '"' then some (p + 1, next) else none
      | none => none
    else
      none
  | none => none

/-- `closedN` for the library's lexer, over positions. -/
def closedU (get : USize → Option UInt8) (p : USize) : Option (USize × UInt8) :=
  match get p with
  | some quote =>
    if quote == byte! '"' then
      match get (p + 1) with
      | some next => if next != byte! '"' then some (p + 1, next) else none
      | none => none
    else
      none
  | none => none

/-- What a string literal closed at a position gives: the position after the quote there, and
the byte after it. -/
theorem closedU_some {get : USize → Option UInt8} {p a : USize} {n : UInt8}
    (hc : closedU get p = some (a, n)) :
    a = p + 1 ∧ get p = some (byte! '"') ∧ get (p + 1) = some n := by
  unfold closedU at hc
  split at hc
  · rename_i q hq
    split at hc
    · rename_i hq'
      split at hc
      · rename_i n' hn
        split at hc
        · cases hc
          simp only [beq_iff_eq] at hq'
          exact ⟨rfl, hq ▸ hq' ▸ rfl, hn⟩
        · cases hc
      · cases hc
    · cases hc
  · cases hc

/-- `X1BatchInCore` finds a string literal closed at the index of a position
exactly where the library's lexer finds it closed at the position. -/
theorem closedN_eq {slice : ByteSlice} (h : slice.stop < USize.size) (p : USize)
    (hp : slice.start ≤ p.toNat) :
    closedN (Lexer.Internal.WRustPort.Slice.get? slice) (ix slice.start p) =
      (closedU (inputOf slice h).get? p).map (fun x => (ix slice.start x.1, x.2)) := by
  unfold closedN closedU
  rw [← get?_eq (h := h) p hp]
  cases hq : (inputOf slice h).get? p with
  | none => rfl
  | some q =>
    dsimp only
    have hlt := Lexer.CharClass.Input.lt_stop_of_get? hq
    rw [inputOf_stop] at hlt
    have e := ix_add_one_of_lt_stop h hp hlt
    have hp1 : slice.start ≤ (p + 1).toNat := by simp only [ix] at e; omega
    split
    · rw [← e, ← get?_eq (h := h) (p + 1) hp1]
      cases (inputOf slice h).get? (p + 1) with
      | none => rfl
      | some n =>
        dsimp only
        split
        · simp only [Option.map_some, e]
        · rfl
    · rfl

/-- The Rust port's window of two bytes at a quote and the byte after it finds the string
literal closed as `closedN` does. -/
theorem closedN_window {get : Nat → Option UInt8} {p : Nat} {q n : UInt8}
    (hq : get p = some q) (hn : get (p + 1) = some n) :
    closedN get p =
      if (q == byte! '"' && n != byte! '"') = true then some (p + 1, n) else none := by
  unfold closedN
  rw [hq]
  dsimp only
  rw [hn]
  dsimp only
  cases q == byte! '"' <;> cases n != byte! '"' <;> rfl

/-- Where the Rust port's window of two bytes does not have both bytes, `closedN` does not find
the string literal closed. -/
theorem closedN_none {get : Nat → Option UInt8} {p : Nat}
    (h : ∀ q n, get p = some q → get (p + 1) = some n → False) : closedN get p = none := by
  unfold closedN
  cases hq : get p with
  | none => rfl
  | some q =>
    dsimp only
    split
    · cases hn : get (p + 1) with
      | none => rfl
      | some n => exact (h q n hq hn).elim
    · rfl

/-- Whether a token of the fast path is emitted, as the Rust port computes it and as the
library's lexer does. -/
theorem emit_eq (c e w : Bool) : (if c = true then e || w else e) = (e || (c && w)) := by
  cases c <;> simp

/-- The index of a position chosen by a condition is the index chosen by it. -/
theorem ix_ite {start : Nat} {q : Bool} {a b : USize} {a' b' : Nat} (ea : ix start a = a')
    (eb : ix start b = b') :
    ix start (if q = true then a else b) = if q = true then a' else b' := by
  split <;> assumption

/-- The end of a token on the fast path: after the closing pipe of a quoted symbol, which is
then at the end of its run, or the end of the run. -/
theorem tokenEnd_facts {slice : ByteSlice} (h : slice.stop < USize.size) (index : USize)
    (q : Bool) (r : USize) (r' : Nat) (er : ix slice.start r = r') (hr : slice.start ≤ r.toNat)
    (hlt : index.toNat < r.toNat)
    (hpipe : q = true → (inputOf slice h).get? r = some (byte! '|')) :
    ix slice.start (if q = true then r + 1 else r) = (if q = true then r' + 1 else r') ∧
      index.toNat < (if q = true then r + 1 else r).toNat ∧
      slice.start ≤ (if q = true then r + 1 else r).toNat ∧
      r.toNat ≤ (if q = true then r + 1 else r).toNat ∧
      (inputOf slice h).get? (if q = true then r + 1 else r) =
        Lexer.Internal.WRustPort.Slice.get? slice (if q = true then r' + 1 else r') := by
  have hrq : q = true → r.toNat < slice.stop ∧ (r + 1).toNat = r.toNat + 1 := fun hq => by
    have := Lexer.CharClass.Input.toNat_add_one_of_get? (hpipe hq)
    rw [inputOf_stop] at this
    exact this
  have e : ix slice.start (if q = true then r + 1 else r) = (if q = true then r' + 1 else r') := by
    split
    · rename_i hq
      have := hrq hq
      subst er
      simp only [ix, this.2]
      omega
    · exact er
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · split
    · rename_i hq; have := hrq hq; omega
    · exact hlt
  · split
    · rename_i hq; have := hrq hq; omega
    · exact hr
  · split
    · rename_i hq; have := hrq hq; omega
    · exact Nat.le_refl _
  · rw [← e]
    have hs : slice.start ≤ (if q = true then r + 1 else r).toNat := by
      split
      · rename_i hq; have := hrq hq; omega
      · exact hr
    exact get?_eq _ hs

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]
  {floor : Option Nat} {low : Nat} (b : USize)

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
/-- `fail_bind_sim`, with the token end of the second lexer given by an equation. -/
theorem fail_bind_sim' {α β γ δ : Type} (start : Nat) (ψ : γ → δ) (kind : LexicalErrorKind)
    (te : Lexer.Helpers.TokenEnd) (te' : Lexer.Internal.WRustPort.Slice.TokenEnd)
    (e : endMap start te = te')
    (hb : start ≤ b.toNat) (hp : b.toNat ≤ te.position.toNat)
    (hno : te.position.toNat + 1 < USize.size) (Q : γ → ZS floor low → Prop)
    (k : α → BSmtLib.Lexer.LexM H m R E floor low γ)
    (k' : β → Lexer.Internal.WRustPort.LexM H m R E floor low δ) :
    SimP (BaseIs b) Q (boundMap start) ψ
      (BSmtLib.Lexer.Internal.fail (H := H) (m := m) (R := R) (E := E) kind te >>= k)
      (Lexer.Internal.WRustPort.error kind te' >>= fun e => throw e >>= k') := by
  subst e
  exact fail_bind_sim start ψ b kind te hb hp hno Q k k'

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
/-- `storeUnfinishedSymbolRun`, with the indices of the second lexer given by equations. -/
theorem storeUnfinishedSymbolRun_sim' (slice : ByteSlice) (h : slice.stop < USize.size)
    (entry : UInt8) (offset : Nat) (base index after runEndAt : USize) (batch : Token.TokenBatch)
    (base' index' after' runEndAt' : Nat) (eb : ix slice.start base = base')
    (ei : ix slice.start index = index') (ea : ix slice.start after = after')
    (er : ix slice.start runEndAt = runEndAt')
    (oki : PosOk slice.start base index) (oka : PosOk slice.start base after)
    (okr : PosOk slice.start base runEndAt)
    (hframe hframe' hindex hindex' hrun hrun' hbatch hbatch') :
    SimP (BaseIs b) (fun _ => BaseIs runEndAt)
      (boundMap slice.start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.storeUnfinishedSymbolRun (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) entry offset base index after runEndAt batch hframe hindex hrun hbatch)
      (Lexer.Internal.WRustPort.storeUnfinishedSymbolRun slice entry offset base' index' after'
          runEndAt'
        batch hframe' hindex' hrun' hbatch') := by
  subst eb ei ea er
  exact storeUnfinishedSymbolRun_sim b slice h entry offset base index after runEndAt batch oki oka
    okr _ _ _ _ _ _ _ _

set_option hygiene false in
/-- A comment ended inside the slice: handed over if the consumer takes comments, then the loop
after it. -/
local macro "comment_tac" : tactic => `(tactic| (
  refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimP.bind (pushBorrowed_sim' (H := H) (m := m) (R := R) (E := E) b slice batch offset b
      .comment _ _ ts _ _ _ _ _ rfl ea eE1 eE1 (by omega) (by omega) ⟨hb, by omega⟩
      _ _ _ _ _ _ _ _) fun x => ?_
    obtain ⟨bt, hbt⟩ := x
    exact ih _ (by omega) _ bt rfl _ eE1 (by omega) _ _ _ _ _ _ _ _ _
  · exact ih _ (by omega) _ batch rfl _ eE1 (by omega) _ _ _ _ _ _ _ _ _))

set_option hygiene false in
/-- A comment that reaches the end of the slice: the lexer waits in the comment state. -/
local macro "comment_end_tac" : tactic => `(tactic| (
  refine SimP.bind (leavePending_sim' (H := H) (m := m) (R := R) (E := E) slice.start b .comment
    ts offset b _ batch _ _ rfl hrc2 ⟨hb, by omega⟩ _ _ _ _ _ _ _ _) fun _ =>
      SimP.pure (fun _ h => h) ?_
  apply Subtype.ext
  simp only [pastMap, BSmtLib.Lexer.Internal.Past.«from», Lexer.Internal.WRustPort.Past.«from»]
  exact hrc2))

set_option hygiene false in
/-- A token on the fast path other than a parenthesis, then the loop after it. -/
local macro "fast_push_tac" : tactic => `(tactic| (
  refine SimP.bind (pushFast_sim' (H := H) (m := m) (R := R) (E := E) b slice batch _ offset b
    _ _ _ index _ _ _ _ _ _ _ _ rfl (ix_ite ea rfl) (ix_ite hr2' hte) rfl hte
    (by symm; exact emit_eq _ _ _) _ _
    (by split <;> omega) (by split <;> omega) ⟨hb, hbi⟩ ⟨hb, by omega⟩ _ _ _ _ _ _ _ _)
    fun x => ?_
  obtain ⟨bt, hbt⟩ := x
  exact ih _ (by omega) _ bt rfl _ hte (by omega) _ _ _ _ _ _ _ _ _))

set_option hygiene false in
/-- A parenthesis: the token on the fast path, then the loop after it. -/
local macro "paren_tac" : tactic => `(tactic| (
  refine SimP.bind (pushFast_sim' (H := H) (m := m) (R := R) (E := E) b slice batch _ offset b
    _ index (index + 1) index (index + 1) true true _ _ _ _ _ rfl rfl ea rfl ea rfl _ _ hi
    (by omega) ⟨hb, hbi⟩ ⟨hb, by omega⟩ _ _ _ _ _ _ _ _) fun x => ?_
  obtain ⟨bt, hbt⟩ := x
  exact ih _ (by omega) (index + 1) bt rfl _ ea (by omega) _ _ _ _ _ _ _ _ _))

set_option hygiene false in
/-- A string literal that the fast path does not find closed: the lexer waits in the state of the
string literal. -/
local macro "string_open_tac" : tactic => `(tactic| (
  split
  · rename_i aqZ nZ heqZ
    have hcZ : closedU (inputOf slice h).get? (Lexer.CharClass.runEnd (inputOf slice h)
        (index + 1) Lexer.CharClass.RUN_STRING_PLAIN) = some (aqZ, nZ) := heqZ
    rw [hcl, hcZ] at hcw
    cases hcw
  · try dsimp only
    refine SimP.seq (extendContent_sim' (H := H) (m := m) (R := R) (E := E) b slice h
      _ _ _ _ ea hrd2 (by omega) hrd.1) fun _ => ?_
    refine SimP.bind (leavePending_sim' (H := H) (m := m) (R := R) (E := E)
      slice.start b _ ts offset b _ batch _ _ rfl hrd2 ⟨hb, by omega⟩
      _ _ _ _ _ _ _ _) fun _ => SimP.pure (fun _ h => h) ?_
    apply Subtype.ext
    simp only [pastMap, BSmtLib.Lexer.Internal.Past.«from», Lexer.Internal.WRustPort.Past.«from»]
    exact hrd2))

theorem lexNormalFrom_sim (slice : ByteSlice) (h : slice.stop < USize.size) (offset : Nat)
    (base : USize) (hb : slice.start ≤ base.toNat) (hbase : b = base)
    (origin : USize) (origin' : Nat) (eo : ix slice.start origin = origin')
    (ho : slice.start ≤ origin.toNat) :
    ∀ k (index : USize) (batch : Token.TokenBatch), slice.stop - index.toNat = k →
      ∀ (index' : Nat), ix slice.start index = index' → base.toNat ≤ index.toNat →
      ∀ hframe hframe' hindex hindex' hbatch hbatch' horigin horigin' (u : Unit),
      SimP (BaseIs b) (fun r s => s.val.base = r.val)
        (boundMap slice.start (floor := floor) (low := low))
        (pastMap slice h eo ho)
        (BSmtLib.Lexer.Internal.lexNormalFrom (H := H) (m := m) (R := R) (E := E)
          (inputOf slice h) offset base index batch hframe hindex hbatch origin horigin)
        (Lexer.Internal.WRustPort.lexNormalFrom slice offset
            (ix slice.start base) index' batch u hframe'
          hindex' hbatch' origin' horigin') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro index batch hk index' ei hbi hframe hframe' hindex hindex' hbatch hbatch' horigin horigin'
    u
  subst ei hbase
  have hi : slice.start ≤ index.toNat := by omega
  have hg := get?_eq (h := h) index hi
  have hstopz : (inputOf slice h).stop.toNat = slice.stop := inputOf_stop
  have hsz : slice.size = slice.stop - slice.start := rfl
  rw [Lexer.Internal.WRustPort.lexNormalFrom]
  split
  · rename_i hc'
    rw [BSmtLib.Lexer.Internal.lexNormalFrom]
    split
    · rename_i hc
      simp only [storeLocals_eq, pure_bind]
      have hge := BSmtLib.Lexer.Internal.stop_le_of_get?_none hc
      refine SimP.bind (leave_sim' (H := H) (m := m) (R := R) (E := E) slice.start b offset b
        index batch _ _ rfl rfl ⟨hb, hbi⟩ _ _ _ _) fun _ => SimP.pure (fun _ h => h) ?_
      apply Subtype.ext
      simp only [pastMap, BSmtLib.Lexer.Internal.Past.«from», Lexer.Internal.WRustPort.Past.«from»]
    · rename_i c hc
      exact absurd ((hg ▸ hc).symm.trans hc') (by simp)
  · rename_i c' hc'
    rw [BSmtLib.Lexer.Internal.lexNormalFrom]
    split
    · rename_i hc
      exact absurd ((hg ▸ hc).symm.trans hc') (by simp)
    · rename_i c hc
      obtain rfl : c' = c := Option.some.inj (hc'.symm.trans (hg ▸ hc))
      -- the locals of the loop are empty, and whether the consumer takes whitespace and
      -- comments is known: the reads of either are values
      simp only [storeLocals_eq, loadLocals_eq, consumes_eq_lexer, consumes_eq_x1, pure_bind,
        pushFast_eq, BSmtLib.Lexer.Internal.fastCategory]
      have hlt := Lexer.CharClass.Input.lt_stop_of_get? hc
      rw [hstopz] at hlt
      have e1 := Lexer.CharClass.toNat_add_one_of_lt (bound := (inputOf slice h).stop)
        (Lexer.CharClass.Input.lt_stop_of_get? hc)
      have ea : ix slice.start (index + 1) = ix slice.start index + 1 := by
        simp only [ix, e1]; omega
      refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine getCore_bind _ _ fun core _ => ?_
        refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
        · refine SimP.seq (modifyCore_sim _ _ _ (fun _ _ => by rfl) fun _ hc => hc) fun _ => ?_
          paren_tac
        · paren_tac
      refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine getCore_bind _ _ fun core _ => ?_
        refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
        · refine SimP.seq (modifyCore_sim _ _ _ (fun _ _ => by rfl) fun _ hc => hc) fun _ => ?_
          paren_tac
        · paren_tac
      refine SimP.ite Iff.rfl (fun hfast => ?_) fun hslow => ?_
      · -- the fast path
        have hr := runEnd_eq (h := h) (index + 1) (by omega)
          (Lexer.Helpers.fastFlags c' &&& Lexer.Helpers.FAST_RUN_MASK)
        have hle := Lexer.CharClass.le_runEnd (inputOf slice h) (index + 1)
          (Lexer.Helpers.fastFlags c' &&& Lexer.Helpers.FAST_RUN_MASK)
        have hgr := get?_eq (h := h) _ hr.1
        have hr2 : idx slice (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
            (Lexer.Helpers.fastFlags c' &&& Lexer.Helpers.FAST_RUN_MASK)) =
            Lexer.Internal.WRustPort.Slice.runEnd slice (ix slice.start index + 1)
              (Lexer.Helpers.fastFlags c' &&& Lexer.Helpers.FAST_RUN_MASK) := by
          rw [← ea]; exact hr.2
        rw [hr2] at hgr
        refine SimP.dite (by rw [hgr]; try exact Iff.rfl) (fun hws hws' => ?_) fun hws hws' => ?_
        · refine SimP.bind (startWhitespace_sim (H := H) (m := m) (R := R) (E := E) b slice h
            offset b index _ _ rfl rfl hb rfl hbi batch _ _ _ _ _ _ _ _) fun x => ?_
          cases x with
          | none =>
            exact SimP.pure (fun _ h => h.2 rfl) (by
              apply Subtype.ext
              simp only [pastMap, BSmtLib.Lexer.Internal.Past.«from»,
                  Lexer.Internal.WRustPort.Past.«from», ix,
                hstopz, hsz])
          | some x =>
            obtain ⟨⟨next, bt⟩, hn1, hn2⟩ := x
            dsimp only [Option.map, wsMap] at hn1 ⊢
            refine SimP.mono (fun s hs => hs.1 rfl) (fun _ _ h => h) ?_
            split
            · contradiction
            · rename_i next' bt' hn1' hn2' heq
              simp only [Option.some.injEq, Subtype.mk.injEq, Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl⟩ := heq
              exact ih _ (by omega) next bt rfl _ rfl (by omega) _ _ _ _ _ _ _ _ _
        · have hR := hr.1
          have hr2' : ix slice.start (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
              (Lexer.Helpers.fastFlags c' &&& Lexer.Helpers.FAST_RUN_MASK)) =
              Lexer.Internal.WRustPort.Slice.runEnd slice (ix slice.start index + 1)
                (Lexer.Helpers.fastFlags c' &&& Lexer.Helpers.FAST_RUN_MASK) := hr2
          try dsimp only
          refine SimP.dite (by rw [beq_stop (h := h) hR, hr2', hgr]) (fun hu hu' => ?_)
            fun hu hu' => ?_
          · refine SimP.bind (storeUnfinishedSymbolRun_sim' (H := H) (m := m) (R := R) (E := E) b
              slice h _ offset b index (index + 1) _ batch _ _ _ _ rfl rfl ea hr2' ⟨hb, hbi⟩
              ⟨hb, by omega⟩ ⟨hb, by omega⟩ _ _ _ _ _ _ _ _) fun _ => SimP.pure (fun _ h => h) ?_
            apply Subtype.ext
            simp only [pastMap, BSmtLib.Lexer.Internal.Past.«from»,
                Lexer.Internal.WRustPort.Past.«from»]
            exact hr2'
          · obtain ⟨hte, hTE1, hTE2, hTE3, hgt⟩ := tokenEnd_facts h index
              (Lexer.Helpers.fastFlags c' &&& Lexer.Helpers.FAST_PIPE != 0) _ _ hr2' hR (by omega)
                  (fun hq => by
                simp only [hq, Bool.or_true, ite_true, Bool.true_and, bne_iff_ne, ne_eq,
                  Decidable.not_not] at hu
                exact hu)
            refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
            · rw [hgt]
              cases hx : Lexer.Internal.WRustPort.Slice.get? slice _ with
              | some next =>
                have hTElt := Lexer.Internal.WRustPort.Slice.lt_size_of_get? hx
                rw [← hte] at hTElt
                simp only [ix] at hTElt
                dsimp only
                refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
                · refine SimP.bind (leave_sim' (H := H) (m := m) (R := R) (E := E) slice.start b
                    offset b index batch _ _ rfl rfl ⟨hb, hbi⟩ _ _ _ _) fun _ => ?_
                  refine SimP.bind (startToken_sim' (H := H) (m := m) (R := R) (E := E) index
                    slice.start offset b index _ _ rfl rfl hb hbi _ _) fun _ => ?_
                  exact failAt_bind_sim' (H := H) (m := m) (R := R) (E := E) index
                    slice.start _
                    _ _ _ (by rw [ix_add_one_of_lt_stop h hTE2 (by omega), hte]) hi
                    (by rw [Lexer.CharClass.toNat_add_one_of_lt (bound := (inputOf slice h).stop)
                      (by rw [hstopz]; omega)]; omega) _ _ _
                · fast_push_tac
              | none =>
                dsimp only
                refine SimP.bind (startToken_sim' (H := H) (m := m) (R := R) (E := E) b
                  slice.start offset b index _ _ rfl rfl hb hbi _ _) fun x => ?_
                obtain ⟨st, hst⟩ := x
                dsimp only
                refine SimP.bind (extendContent_sim' (H := H) (m := m) (R := R) (E := E) b slice h
                  _ _ _ _ (ix_ite ea rfl) (ix_ite hr2' hte) (by split <;> omega)
                  (by split <;> omega)) fun _ => ?_
                refine SimP.bind (leavePending_sim' (H := H) (m := m) (R := R) (E := E) slice.start
                  b _ _ offset b _ batch _ _ rfl hte ⟨hb, by omega⟩ _ _ _ _ _ _ _ _) fun _ =>
                    SimP.pure (fun _ h => h) ?_
                apply Subtype.ext
                simp only [pastMap, BSmtLib.Lexer.Internal.Past.«from»,
                    Lexer.Internal.WRustPort.Past.«from»]
                exact hte
            · fast_push_tac
      · -- the slow path: both lexers dispatch on the same class of the byte
        split <;> rename_i hs <;> refine SimF.hide_left fun f' hf' => ?_ <;> split <;>
          rename_i hs' <;> subst hf' <;> (try (have e := hs.symm.trans hs'; cases e; done))
        · -- a line feed
          refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
          · refine SimP.bind (startWhitespace_sim (H := H) (m := m) (R := R) (E := E) b slice h
              offset b index _ _ rfl rfl hb rfl hbi batch _ _ _ _ _ _ _ _) fun x => ?_
            cases x with
            | none =>
              exact SimP.pure (fun _ h => h.2 rfl) (by
                apply Subtype.ext
                simp only [pastMap, BSmtLib.Lexer.Internal.Past.«from»,
                    Lexer.Internal.WRustPort.Past.«from»,
                  ix, hstopz, hsz])
            | some x =>
              obtain ⟨⟨next, bt⟩, hn1, hn2⟩ := x
              dsimp only [Option.map, wsMap] at hn1 ⊢
              refine SimP.mono (fun s hs => hs.1 rfl) (fun _ _ h => h) ?_
              split
              · contradiction
              · rename_i next' bt' hn1' hn2' heq
                simp only [Option.some.injEq, Subtype.mk.injEq, Prod.mk.injEq] at heq
                obtain ⟨rfl, rfl⟩ := heq
                exact ih _ (by omega) next bt rfl _ rfl (by omega) _ _ _ _ _ _ _ _ _
          · refine SimP.seq (markLineFeedAt_sim slice.start b index hb hbi) fun _ => ?_
            exact ih _ (by omega) (index + 1) batch rfl _ ea (by omega) _ _ _ _ _ _ _ _ _
        · -- a comment
          refine SimP.bind (startToken_sim' (H := H) (m := m) (R := R) (E := E) b slice.start
            offset b index _ _ rfl rfl hb hbi _ _) fun x => ?_
          obtain ⟨ts, hts⟩ := x
          dsimp only
          have hrc := runEnd_eq (h := h) (index + 1) (by omega) Lexer.CharClass.RUN_COMMENT_PLAIN
          have hlec := Lexer.CharClass.le_runEnd (inputOf slice h)
              (index + 1) Lexer.CharClass.RUN_COMMENT_PLAIN
          have hrc2 : ix slice.start (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
              Lexer.CharClass.RUN_COMMENT_PLAIN) =
              Lexer.Internal.WRustPort.Slice.runEnd slice
                  (ix slice.start index + 1) Lexer.CharClass.RUN_COMMENT_PLAIN := by
            rw [← ea]; exact hrc.2
          have hgc : (inputOf slice h).get? (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
              Lexer.CharClass.RUN_COMMENT_PLAIN) = Lexer.Internal.WRustPort.Slice.get? slice
                  (Lexer.Internal.WRustPort.Slice.runEnd slice
                (ix slice.start index + 1) Lexer.CharClass.RUN_COMMENT_PLAIN) := by
            rw [← hrc2]; exact get?_eq _ hrc.1
          refine SimF.hide_left fun f' hf' => ?_
          split
          · rename_i cx hx
            subst hf'
            split
            · rename_i cz hz
              rw [← hgc, hz] at hx
              obtain rfl : cx = cz := (Option.some.inj hx).symm
              have hEl := Lexer.CharClass.Input.lt_stop_of_get? hz
              rw [hstopz] at hEl
              have eE1 := ix_add_one_of_lt_stop h hrc.1 hEl
              rw [hrc2] at eE1
              have hE1 := Lexer.CharClass.toNat_add_one_of_lt
                (position := Lexer.CharClass.runEnd (inputOf slice h)
                    (index + 1) Lexer.CharClass.RUN_COMMENT_PLAIN)
                (bound := (inputOf slice h).stop) (by rw [hstopz]; exact hEl)
              refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
              · refine SimP.seq (SimP.congr_g (by rw [hrc2])
                  (markLineFeedAt_sim slice.start b _ hb (by omega))) fun _ => ?_
                comment_tac
              · comment_tac
            · rename_i hz
              rw [← hgc, hz] at hx
              cases hx
          · rename_i hx
            subst hf'
            split
            · rename_i cz hz
              rw [← hgc, hz] at hx
              cases hx
            · rename_i hz
              have hEge := BSmtLib.Lexer.Internal.stop_le_of_get?_none hz
              refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
              · refine SimP.seq (extendContent_sim' (H := H) (m := m) (R := R) (E := E) b slice h
                  _ _ _ _ ea hrc2 (by omega) hrc.1) fun _ => ?_
                comment_end_tac
              · comment_end_tac
        · -- a hash
          refine SimP.bind (startToken_sim' (H := H) (m := m) (R := R) (E := E) b slice.start
            offset b index _ _ rfl rfl hb hbi _ _) fun x => ?_
          obtain ⟨ts, hts⟩ := x
          dsimp only
          have hga : (inputOf slice h).get? (index + 1) =
              Lexer.Internal.WRustPort.Slice.get? slice (ix slice.start index + 1) := by
            rw [← ea]; exact get?_eq _ (by omega)
          refine SimF.hide_left fun f' hf' => ?_
          split
          · rename_i _ run hrunX _
            subst hf'
            split
            · rename_i _ run' hrunZ _
              obtain rfl : run = run' := by
                rw [hga, hrunX] at hrunZ
                exact Option.some.inj hrunZ
              obtain ⟨cc, hcc, -⟩ := Option.bind_eq_some_iff.mp hrunX
              have hA1 := Lexer.Internal.WRustPort.Slice.lt_size_of_get? hcc
              have e2 : (index + 1 + 1).toNat = index.toNat + 1 + 1 := by
                rw [Lexer.CharClass.toNat_add_one_of_lt (bound := (inputOf slice h).stop)
                  (by rw [hstopz]; simp only [ix] at hA1; omega), e1]
              have ea2 : ix slice.start (index + 1 + 1) = ix slice.start index + 1 + 1 := by
                simp only [ix, e2]; omega
              have hrd := runEnd_eq (h := h) (index + 1 + 1) (by omega) run.flag
              have hrd2 : ix slice.start (Lexer.CharClass.runEnd (inputOf slice h) (index + 1 + 1)
                  run.flag) = Lexer.Internal.WRustPort.Slice.runEnd slice
                      (ix slice.start index + 1 + 1) run.flag := by
                rw [← ea2]; exact hrd.2
              have hle2 := Lexer.CharClass.le_runEnd (inputOf slice h) (index + 1 + 1) run.flag
              have hst2 := runEnd_le_stop h (index + 1 + 1) (by omega)
                (by simp only [ix] at hA1; omega) run.flag
              try dsimp only
              refine SimP.dite (by rw [beq_stop (h := h) hrd.1, hrd2])
                  (fun _ _ => ?_) fun hne _ => ?_
              · refine SimP.seq (extendContent_sim' (H := H) (m := m) (R := R) (E := E) b slice h
                  _ _ _ _ ea2 hrd2 (by omega) hrd.1) fun _ => ?_
                refine SimP.bind (leavePending_sim' (H := H) (m := m) (R := R) (E := E)
                  slice.start b _ ts offset b _ batch _ _ rfl hrd2 ⟨hb, by omega⟩
                  _ _ _ _ _ _ _ _) fun _ => SimP.pure (fun _ h => h) ?_
                apply Subtype.ext
                simp only [pastMap, BSmtLib.Lexer.Internal.Past.«from»,
                    Lexer.Internal.WRustPort.Past.«from»]
                exact hrd2
              have hAElt : (Lexer.CharClass.runEnd (inputOf slice h)
                  (index + 1 + 1) run.flag).toNat <
                  slice.stop := by
                rw [beq_stop (h := h) hrd.1] at hne
                simp only [beq_iff_eq, ix] at hne
                have hsz' : slice.size = slice.stop - slice.start := rfl
                omega
              refine getCore_bind _ _ fun core _ => ?_
              refine SimP.ite
                (by rw [borrow_eq (h := h) _ _ (by omega) hrd.1]; simp only [ea2, hrd2]; rfl)
                (fun _ => ?_) fun _ => ?_
              · refine SimP.bind (leave_sim' (H := H) (m := m) (R := R) (E := E) slice.start b
                  offset b index batch _ _ rfl rfl ⟨hb, hbi⟩ _ _ _ _) fun _ => ?_
                exact fail_bind_sim' (H := H) (m := m) (R := R) (E := E) index
                  slice.start _
                  _ _ _ (by rw [← hrd2]; rfl) hi
                  (by dsimp only [Lexer.Helpers.TokenEnd.mkAtByte]; omega)
                  (by dsimp only [Lexer.Helpers.TokenEnd.mkAtByte]; omega) _ _ _
              refine SimP.ite (by rw [get_eq (h := h) _ hrd.1 hrd2]) (fun _ => ?_) fun _ => ?_
              · refine SimP.bind (leave_sim' (H := H) (m := m) (R := R) (E := E) slice.start b
                  offset b index batch _ _ rfl rfl ⟨hb, hbi⟩ _ _ _ _) fun _ => ?_
                exact failAt_bind_sim' (H := H) (m := m) (R := R) (E := E) index
                  slice.start _
                  _ _ _ (by rw [ix_add_one_of_lt_stop h hrd.1 hAElt, hrd2]) hi
                  (by rw [Lexer.CharClass.toNat_add_one_of_lt (bound := (inputOf slice h).stop)
                    (by rw [hstopz]; omega)]; omega) _ _ _
              · refine SimP.bind (pushBorrowed_sim' (H := H) (m := m) (R := R) (E := E) b slice
                  batch offset b _ _ _ ts _ _ _ _ _ rfl ea2 hrd2 hrd2 (by omega) (by omega)
                  ⟨hb, by omega⟩ _ _ _ _ _ _ _ _) fun x => ?_
                obtain ⟨bt, hbt⟩ := x
                exact ih _ (by omega) _ bt rfl _ hrd2 (by omega) _ _ _ _ _ _ _ _ _
            · rename_i hZ
              exact (hZ run (by rw [hga]; exact hrunX) (attach_of_eq _)).elim
          · rename_i hX
            subst hf'
            split
            · rename_i _ run hrunZ _
              exact (hX run (by rw [← hga]; exact hrunZ) (attach_of_eq _)).elim
            · refine SimP.bind (leavePending_sim' (H := H) (m := m) (R := R) (E := E)
                slice.start b _ ts offset b _ batch _ _ rfl ea ⟨hb, by omega⟩
                _ _ _ _ _ _ _ _) fun _ => SimP.pure (fun _ h => h) ?_
              apply Subtype.ext
              simp only [pastMap, BSmtLib.Lexer.Internal.Past.«from»,
                  Lexer.Internal.WRustPort.Past.«from»]
              exact ea
        · -- a quote
          refine SimP.bind (startToken_sim' (H := H) (m := m) (R := R) (E := E) b slice.start
            offset b index _ _ rfl rfl hb hbi _ _) fun x => ?_
          obtain ⟨ts, hts⟩ := x
          dsimp only
          refine getCore_bind _ _ fun core _ => ?_
          refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
          · refine SimP.bind (leavePending_sim' (H := H) (m := m) (R := R) (E := E)
              slice.start b _ ts offset b _ batch _ _ rfl ea ⟨hb, by omega⟩
              _ _ _ _ _ _ _ _) fun _ => SimP.pure (fun _ h => h) ?_
            apply Subtype.ext
            simp only [pastMap, BSmtLib.Lexer.Internal.Past.«from»,
                Lexer.Internal.WRustPort.Past.«from»]
            exact ea
          have hrd := runEnd_eq (h := h) (index + 1) (by omega) Lexer.CharClass.RUN_STRING_PLAIN
          have hrd2 : ix slice.start (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
              Lexer.CharClass.RUN_STRING_PLAIN) =
              Lexer.Internal.WRustPort.Slice.runEnd slice
                  (ix slice.start index + 1) Lexer.CharClass.RUN_STRING_PLAIN := by
            rw [← ea]; exact hrd.2
          have hle2 := Lexer.CharClass.le_runEnd (inputOf slice h)
              (index + 1) Lexer.CharClass.RUN_STRING_PLAIN
          have hst2 := runEnd_le_stop h (index + 1) (by omega)
              (by omega) Lexer.CharClass.RUN_STRING_PLAIN
          have hgq : (inputOf slice h).get? (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
              Lexer.CharClass.RUN_STRING_PLAIN) = Lexer.Internal.WRustPort.Slice.get? slice
                  (Lexer.Internal.WRustPort.Slice.runEnd slice
                (ix slice.start index + 1) Lexer.CharClass.RUN_STRING_PLAIN) := by
            rw [← hrd2]; exact get?_eq _ hrd.1
          have hcl := closedN_eq h (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
            Lexer.CharClass.RUN_STRING_PLAIN) hrd.1
          rw [hrd2] at hcl
          -- the Rust port reads a window of two bytes where the library's lexer reads the byte
          -- after the quote only once it has found the quote (`closedU`); they find the string
          -- closed alike (`closedN_window`, `closedN_none`)
          refine SimF.hide_left fun f' hf' => ?_
          split
          · rename_i quote next hquote hwindow
            subst hf'
            have hcw := closedN_window hquote hwindow
            refine SimF.hide_left fun f' hf' => ?_
            split
            · rename_i hcond
              subst hf'
              simp only [hcond, ↓reduceIte] at hcw
              split
              · rename_i aqZ nZ heqZ
                have hcZ : closedU (inputOf slice h).get? (Lexer.CharClass.runEnd (inputOf slice h)
                    (index + 1) Lexer.CharClass.RUN_STRING_PLAIN) = some (aqZ, nZ) := heqZ
                rw [hcl, hcZ] at hcw
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcw
                obtain ⟨hax, rfl⟩ := hcw
                obtain ⟨rfl, hq1, hq2⟩ := closedU_some hcZ
                have hq1l := Lexer.CharClass.Input.lt_stop_of_get? hq1
                rw [hstopz] at hq1l
                have hq2l := Lexer.CharClass.Input.toNat_add_one_of_get? hq2
                rw [hstopz] at hq2l
                have eq1 := Lexer.CharClass.toNat_add_one_of_lt (bound := (inputOf slice h).stop)
                  (position := Lexer.CharClass.runEnd (inputOf slice h)
                      (index + 1) Lexer.CharClass.RUN_STRING_PLAIN)
                  (by rw [hstopz]; exact hq1l)
                refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
                · refine SimP.bind (leave_sim' (H := H) (m := m) (R := R) (E := E) slice.start b
                    offset b index batch _ _ rfl rfl ⟨hb, hbi⟩ _ _ _ _) fun _ => ?_
                  exact failAt_bind_sim' (H := H) (m := m) (R := R) (E := E) index
                    slice.start _ _ _ _
                    (by rw [ix_add_one_of_lt_stop h (by omega) hq2l.1, hax]) hi (by omega)
                    _ _ _
                · refine SimP.bind (pushBorrowed_sim' (H := H) (m := m) (R := R) (E := E) b slice
                    batch offset b _ _ _ ts _ _ _ _ _ rfl ea hrd2 hax (by omega) (by omega)
                    ⟨hb, by omega⟩ _ _ _ _ _ _ _ _) fun x => ?_
                  obtain ⟨bt, hbt⟩ := x
                  exact ih _ (by omega) _ bt rfl _ hax (by omega) _ _ _ _ _ _ _ _ _
              · rename_i heqZ
                have hcZ : closedU (inputOf slice h).get? (Lexer.CharClass.runEnd (inputOf slice h)
                    (index + 1) Lexer.CharClass.RUN_STRING_PLAIN) = none := heqZ
                rw [hcl, hcZ] at hcw
                cases hcw
            · rename_i hcond
              subst hf'
              simp only [hcond] at hcw
              string_open_tac
          · rename_i hnone
            subst hf'
            have hcw := closedN_none hnone
            string_open_tac
        · -- a colon
          refine SimP.bind (startToken_sim' (H := H) (m := m) (R := R) (E := E) b slice.start
            offset b index _ _ rfl rfl hb hbi _ _) fun x => ?_
          obtain ⟨ts, hts⟩ := x
          dsimp only
          have hrd := runEnd_eq (h := h) (index + 1) (by omega) Lexer.CharClass.RUN_SIMPLE_SYMBOL
          have hrd2 : ix slice.start (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
              Lexer.CharClass.RUN_SIMPLE_SYMBOL) =
              Lexer.Internal.WRustPort.Slice.runEnd slice
                  (ix slice.start index + 1) Lexer.CharClass.RUN_SIMPLE_SYMBOL := by
            rw [← ea]; exact hrd.2
          have hle2 := Lexer.CharClass.le_runEnd (inputOf slice h)
              (index + 1) Lexer.CharClass.RUN_SIMPLE_SYMBOL
          have hst2 := runEnd_le_stop h (index + 1) (by omega)
              (by omega) Lexer.CharClass.RUN_SIMPLE_SYMBOL
          refine SimP.dite (by rw [beq_stop (h := h) hrd.1, hrd2]) (fun _ _ => ?_) fun hne _ => ?_
          · refine SimP.seq (extendContent_sim' (H := H) (m := m) (R := R) (E := E) b slice h
              _ _ _ _ ea hrd2 (by omega) hrd.1) fun _ => ?_
            refine SimP.bind (leavePending_sim' (H := H) (m := m) (R := R) (E := E)
              slice.start b _ ts offset b _ batch _ _ rfl hrd2 ⟨hb, by omega⟩
              _ _ _ _ _ _ _ _) fun _ => SimP.pure (fun _ h => h) ?_
            apply Subtype.ext
            simp only [pastMap, BSmtLib.Lexer.Internal.Past.«from»,
                Lexer.Internal.WRustPort.Past.«from»]
            exact hrd2
          have hAElt : (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
              Lexer.CharClass.RUN_SIMPLE_SYMBOL).toNat < slice.stop := by
            rw [beq_stop (h := h) hrd.1] at hne
            simp only [beq_iff_eq, ix] at hne
            omega
          refine getCore_bind _ _ fun core _ => ?_
          refine SimP.ite
            (by rw [borrow_eq (h := h) _ _ (by omega) hrd.1]; simp only [ea, hrd2]; rfl)
            (fun _ => ?_) fun _ => ?_
          · refine SimP.bind (leave_sim' (H := H) (m := m) (R := R) (E := E) slice.start b
              offset b index batch _ _ rfl rfl ⟨hb, hbi⟩ _ _ _ _) fun _ => ?_
            exact fail_bind_sim' (H := H) (m := m) (R := R) (E := E) index
              slice.start _
              _ _ _ (by rw [← hrd2]; rfl) hi
              (by dsimp only [Lexer.Helpers.TokenEnd.mkAtByte]; omega)
              (by dsimp only [Lexer.Helpers.TokenEnd.mkAtByte]; omega) _ _ _
          refine SimP.ite (by rw [get_eq (h := h) _ hrd.1 hrd2]) (fun _ => ?_) fun _ => ?_
          · refine SimP.bind (leave_sim' (H := H) (m := m) (R := R) (E := E) slice.start b
              offset b index batch _ _ rfl rfl ⟨hb, hbi⟩ _ _ _ _) fun _ => ?_
            exact failAt_bind_sim' (H := H) (m := m) (R := R) (E := E) index
              slice.start _
              _ _ _ (by rw [ix_add_one_of_lt_stop h hrd.1 hAElt, hrd2]) hi
              (by rw [Lexer.CharClass.toNat_add_one_of_lt (bound := (inputOf slice h).stop)
                (by rw [hstopz]; omega)]; omega) _ _ _
          · refine SimP.bind (pushBorrowed_sim' (H := H) (m := m) (R := R) (E := E) b slice
              batch offset b _ _ _ ts _ _ _ _ _ rfl ea hrd2 hrd2 (by omega) (by omega)
              ⟨hb, by omega⟩ _ _ _ _ _ _ _ _) fun x => ?_
            obtain ⟨bt, hbt⟩ := x
            exact ih _ (by omega) _ bt rfl _ hrd2 (by omega) _ _ _ _ _ _ _ _ _
        · -- a digit
          refine SimP.bind (startToken_sim' (H := H) (m := m) (R := R) (E := E) b slice.start
            offset b index _ _ rfl rfl hb hbi _ _) fun x => ?_
          obtain ⟨ts, hts⟩ := x
          dsimp only
          have hrd := runEnd_eq (h := h) (index + 1) (by omega) Lexer.CharClass.RUN_DIGIT
          have hrd2 : ix slice.start (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
              Lexer.CharClass.RUN_DIGIT) =
              Lexer.Internal.WRustPort.Slice.runEnd slice
                  (ix slice.start index + 1) Lexer.CharClass.RUN_DIGIT := by
            rw [← ea]; exact hrd.2
          have hle2 := Lexer.CharClass.le_runEnd (inputOf slice h)
              (index + 1) Lexer.CharClass.RUN_DIGIT
          have hst2 := runEnd_le_stop h (index + 1) (by omega) (by omega) Lexer.CharClass.RUN_DIGIT
          have hgd : (inputOf slice h).get? (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
              Lexer.CharClass.RUN_DIGIT) = Lexer.Internal.WRustPort.Slice.get? slice
                  (Lexer.Internal.WRustPort.Slice.runEnd slice
                (ix slice.start index + 1) Lexer.CharClass.RUN_DIGIT) := by
            rw [← hrd2]; exact get?_eq _ hrd.1
          refine SimP.ite (by rw [decide_gt (slice := slice) hrd.1 (by omega), hrd2, ea])
            (fun hz => ?_) fun _ => ?_
          · have hz' : index.toNat + 1 < (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
                Lexer.CharClass.RUN_DIGIT).toNat := by
              simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt,
                USize.lt_iff_toNat_lt, e1] at hz
              exact hz.2
            refine SimP.bind (leave_sim' (H := H) (m := m) (R := R) (E := E) slice.start b
              offset b index batch _ _ rfl rfl ⟨hb, hbi⟩ _ _ _ _) fun _ => ?_
            exact failAt_bind_sim' (H := H) (m := m) (R := R) (E := E) index
              slice.start _
              _ _ _ (by rw [ix_add_one_of_lt_stop h (by omega) (by omega), ea]) hi
              (by rw [Lexer.CharClass.toNat_add_one_of_lt (bound := (inputOf slice h).stop)
                (by rw [hstopz]; omega)]; omega) _ _ _
          refine SimF.hide_left fun f' hf' => ?_
          split
          · rename_i nX hnX
            subst hf'
            split
            · rename_i nZ hnZ
              obtain rfl : nZ = nX := by
                rw [hgd, hnX] at hnZ
                exact (Option.some.inj hnZ).symm
              have hAEl := Lexer.CharClass.Input.toNat_add_one_of_get? hnZ
              rw [hstopz] at hAEl
              have eAE := ix_add_one_of_lt_stop h hrd.1 hAEl.1
              rw [hrd2] at eAE
              refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
              · -- a fraction
                have hrf := runEnd_eq (h := h) (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
                  Lexer.CharClass.RUN_DIGIT + 1) (by omega) Lexer.CharClass.RUN_DIGIT
                have hrf2 : ix slice.start (Lexer.CharClass.runEnd (inputOf slice h)
                    (Lexer.CharClass.runEnd (inputOf slice h)
                        (index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                    Lexer.CharClass.RUN_DIGIT) = Lexer.Internal.WRustPort.Slice.runEnd slice
                        (Lexer.Internal.WRustPort.Slice.runEnd slice
                      (ix slice.start index + 1) Lexer.CharClass.RUN_DIGIT + 1)
                          Lexer.CharClass.RUN_DIGIT := by
                  rw [← eAE]; exact hrf.2
                have hlf := Lexer.CharClass.le_runEnd (inputOf slice h)
                  (Lexer.CharClass.runEnd (inputOf slice h)
                      (index + 1) Lexer.CharClass.RUN_DIGIT + 1) Lexer.CharClass.RUN_DIGIT
                have hsf := runEnd_le_stop h (Lexer.CharClass.runEnd (inputOf slice h) (index + 1)
                  Lexer.CharClass.RUN_DIGIT + 1) (by omega) (by omega) Lexer.CharClass.RUN_DIGIT
                refine SimP.dite (by rw [beq_stop (h := h) hrf.1, hrf2]) (fun _ _ => ?_)
                  fun hne _ => ?_
                · refine SimP.seq (extendContent_sim' (H := H) (m := m) (R := R) (E := E) b
                    slice h _ _ _ _ rfl hrf2 hi hrf.1) fun _ => ?_
                  refine SimP.bind (leavePending_sim' (H := H) (m := m) (R := R) (E := E)
                    slice.start b _ ts offset b _ batch _ _ rfl hrf2 ⟨hb, by omega⟩
                    _ _ _ _ _ _ _ _) fun _ => SimP.pure (fun _ h => h) ?_
                  apply Subtype.ext
                  simp only [pastMap, BSmtLib.Lexer.Internal.Past.«from»,
                    Lexer.Internal.WRustPort.Past.«from»]
                  exact hrf2
                have hAFl : (Lexer.CharClass.runEnd (inputOf slice h)
                    (Lexer.CharClass.runEnd (inputOf slice h)
                    (index + 1) Lexer.CharClass.RUN_DIGIT + 1) Lexer.CharClass.RUN_DIGIT).toNat <
                        slice.stop := by
                  rw [beq_stop (h := h) hrf.1] at hne
                  simp only [beq_iff_eq, ix] at hne
                  omega
                refine getCore_bind _ _ fun core _ => ?_
                refine SimP.ite (by rw [borrow_eq (h := h) _ _ hi hrf.1]; simp only [hrf2]; rfl)
                  (fun _ => ?_) fun _ => ?_
                · refine SimP.bind (leave_sim' (H := H) (m := m) (R := R) (E := E) slice.start b
                    offset b index batch _ _ rfl rfl ⟨hb, hbi⟩ _ _ _ _) fun _ => ?_
                  exact fail_bind_sim' (H := H) (m := m) (R := R) (E := E) index
                    slice.start _
                    _ _ _ (by rw [← hrf2]; rfl) hi
                    (by dsimp only [Lexer.Helpers.TokenEnd.mkAtByte]; omega)
                    (by dsimp only [Lexer.Helpers.TokenEnd.mkAtByte]; omega) _ _ _
                refine SimP.ite (by rw [get_eq (h := h) _ hrf.1 hrf2]) (fun _ => ?_) fun _ => ?_
                · refine SimP.bind (leave_sim' (H := H) (m := m) (R := R) (E := E) slice.start b
                    offset b index batch _ _ rfl rfl ⟨hb, hbi⟩ _ _ _ _) fun _ => ?_
                  exact failAt_bind_sim' (H := H) (m := m) (R := R) (E := E) index
                    slice.start _
                    _ _ _ (by rw [ix_add_one_of_lt_stop h hrf.1 hAFl, hrf2]) hi
                    (by rw [Lexer.CharClass.toNat_add_one_of_lt (bound := (inputOf slice h).stop)
                      (by rw [hstopz]; omega)]; omega) _ _ _
                · refine SimP.bind (pushBorrowed_sim' (H := H) (m := m) (R := R) (E := E) b slice
                    batch offset b _ _ _ ts _ _ _ _ _ rfl rfl hrf2 hrf2 hi (by omega)
                    ⟨hb, by omega⟩ _ _ _ _ _ _ _ _) fun x => ?_
                  obtain ⟨bt, hbt⟩ := x
                  exact ih _ (by omega) _ bt rfl _ hrf2 (by omega) _ _ _ _ _ _ _ _ _
              · -- a numeral
                refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
                · refine SimP.bind (leave_sim' (H := H) (m := m) (R := R) (E := E) slice.start b
                    offset b index batch _ _ rfl rfl ⟨hb, hbi⟩ _ _ _ _) fun _ => ?_
                  exact failAt_bind_sim' (H := H) (m := m) (R := R) (E := E) index
                    slice.start _
                    _ _ _ eAE hi (by omega) _ _ _
                · refine SimP.bind (pushBorrowed_sim' (H := H) (m := m) (R := R) (E := E) b slice
                    batch offset b _ _ _ ts _ _ _ _ _ rfl rfl hrd2 hrd2 hi (by omega)
                    ⟨hb, by omega⟩ _ _ _ _ _ _ _ _) fun x => ?_
                  obtain ⟨bt, hbt⟩ := x
                  exact ih _ (by omega) _ bt rfl _ hrd2 (by omega) _ _ _ _ _ _ _ _ _
            · rename_i hnZ
              rw [hgd, hnX] at hnZ
              cases hnZ
          · rename_i hnX
            subst hf'
            split
            · rename_i nZ hnZ
              rw [hgd, hnX] at hnZ
              cases hnZ
            · refine SimP.seq (extendContent_sim' (H := H) (m := m) (R := R) (E := E) b slice h
                _ _ _ _ rfl hrd2 hi hrd.1) fun _ => ?_
              refine SimP.bind (leavePending_sim' (H := H) (m := m) (R := R) (E := E)
                slice.start b _ ts offset b _ batch _ _ rfl hrd2 ⟨hb, by omega⟩
                _ _ _ _ _ _ _ _) fun _ => SimP.pure (fun _ h => h) ?_
              apply Subtype.ext
              simp only [pastMap, BSmtLib.Lexer.Internal.Past.«from»,
                  Lexer.Internal.WRustPort.Past.«from»]
              exact hrd2
        all_goals
          -- a byte that starts no token
          refine SimP.bind (startToken_sim' (H := H) (m := m) (R := R) (E := E) b slice.start
            offset b index _ _ rfl rfl hb hbi _ _) fun _ => ?_
          refine SimP.bind (leave_sim' (H := H) (m := m) (R := R) (E := E) slice.start b offset b
            index batch _ _ rfl rfl ⟨hb, hbi⟩ _ _ _ _) fun _ => ?_
          exact failAt_sim' (H := H) (m := m) (R := R) (E := E) index slice.start _ _ _ _ ea hi
            (by omega) _

/-- `lexNormalFrom`, with the offset and the indices of the second lexer given by equations. -/
theorem lexNormalFrom_sim' (slice : ByteSlice) (h : slice.stop < USize.size) (offset offset' : Nat)
    (eoff : offset = offset') (base : USize) (base' : Nat) (eb : ix slice.start base = base')
    (hb : slice.start ≤ base.toNat) (hbase : b = base) (origin : USize) (origin' : Nat)
    (eo : ix slice.start origin = origin') (ho : slice.start ≤ origin.toNat)
    (index : USize) (batch : Token.TokenBatch) (index' : Nat) (ei : ix slice.start index = index')
    (hbi : base.toNat ≤ index.toNat) (hframe hframe' hindex hindex' hbatch hbatch' horigin
      horigin') (u : Unit) :
    SimP (BaseIs b) (fun r s => s.val.base = r.val)
      (boundMap slice.start (floor := floor) (low := low))
      (pastMap slice h eo ho)
      (BSmtLib.Lexer.Internal.lexNormalFrom (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) offset base index batch hframe hindex hbatch origin horigin)
      (Lexer.Internal.WRustPort.lexNormalFrom slice offset' base' index' batch u hframe' hindex'
          hbatch'
        origin' horigin') := by
  subst eoff eb
  exact lexNormalFrom_sim b slice h offset base hb hbase origin origin' eo ho _ index batch rfl
    index' ei hbi _ _ _ _ _ _ _ _ u

/-- The position after a start, for the index after the start's index. -/
def nextMapLt (s0 : Nat) {lo : USize} {lo' : Nat} (e : ix s0 lo = lo') (hlo : s0 ≤ lo.toNat)
    (r : {next : USize // lo.toNat < next.toNat}) : {next : Nat // lo' < next} :=
  ⟨ix s0 r.val, by subst e; have := r.property; simp only [ix]; omega⟩

theorem lexNormal_sim (slice : ByteSlice) (h : slice.stop < USize.size) (start : USize)
    (start' : Nat) (es : ix slice.start start = start') (hb : slice.start ≤ b.toNat)
    (hbs : b = start) (hstart hstart') :
    SimP (BaseIs b) (fun r s => s.val.base = r.val)
      (boundMap slice.start (floor := floor) (low := low)) (nextMapLt slice.start es (hbs ▸ hb))
      (BSmtLib.Lexer.Internal.lexNormal (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) start hstart)
      (Lexer.Internal.WRustPort.lexNormal slice start' hstart') := by
  subst hbs es
  unfold BSmtLib.Lexer.Internal.lexNormal Lexer.Internal.WRustPort.lexNormal
  simp only [loadLocals_eq, pure_bind]
  refine SimP.bind (Q := fun a s => BaseIs b s ∧ a.val.2.1 = b)
    (ψ := fun a => ⟨(a.val.1, ix slice.start a.val.2.1, a.val.2.2), a.property⟩)
    (SimP.modifyGet (fun s _ => rfl) fun s hs => ⟨hs, hs⟩) fun a => ?_
  obtain ⟨⟨o, bs, bt⟩, hf, hbt, hfl⟩ := a
  refine SimP.of_fact fun hbs => ?_
  dsimp only at hbs ⊢
  subst hbs
  split
  rename_i o2 b2 bt2 hp2 heq2
  simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq2
  obtain ⟨rfl, rfl, rfl⟩ := heq2
  refine SimP.bind (lexNormalFrom_sim' (H := H) (m := m) (R := R) (E := E) bs slice h _ _
    (by simp) bs _ rfl hb rfl bs _ rfl hb
    bs bt _ rfl (Nat.le_refl _) _ _ _ _ _ _ _ _ _) fun r => SimP.pure (fun _ h => h) ?_
  apply Subtype.ext
  rfl

end

end BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Normal
