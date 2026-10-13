import BSmtLib.Proofs.X1BatchInCoreLexer.Finish

/-!
# The batch held by the loop of the normal state, in both lexers

The loop of the normal state of both lexers holds the batch and appends the tokens of the fast
path (`pushFast`) and of the slow path (`pushBorrowed`) to it, and puts it back into the lexer
state where the loop ends (`leave`, `leavePending`).
-/

namespace BSmtLib.Proofs.X1BatchInCoreLexer

open BSmtLib.Proofs.Simulation

/-- What the loop knows of positions: the slice starts at `start`, `base` is in it, and the
position is at or after `base` and in the array. -/
structure PosOk (start : Nat) (base p : USize) : Prop where
  hb : start ≤ base.toNat
  hp : base.toNat ≤ p.toNat

theorem PosOk.sub {start : Nat} {base p : USize} (h : PosOk start base p) :
    (p - base).toNat = ix start p - ix start base :=
  sub_toNat_ix h.hb h.hp

theorem PosOk.ix_le {start : Nat} {base p : USize} (h : PosOk start base p) :
    ix start base ≤ ix start p := by
  have := h.hb; have := h.hp; simp only [ix]; omega

theorem start_add_ix {start : Nat} {p : USize} (h : start ≤ p.toNat) :
    start + ix start p = p.toNat := by
  simp only [ix]; omega

/-- Equal arguments push equal tokens. -/
theorem pushOnLine_congr {batch : TokenBatch} {ty : TokenCategory} {a a' b b' l ls s s' e e' : Nat}
    (ea : a = a') (eb : b = b') (es : s = s') (ee : e = e') {after nonempty after' nonempty'} :
    batch.pushOnLine ty a b l ls s e after nonempty =
      batch.pushOnLine ty a' b' l ls s' e' after' nonempty' := by
  subst ea eb es ee
  rfl

theorem pushLocated_congr {batch : TokenBatch} {ty : TokenCategory} {a a' b b' : Nat}
    {s e e' : Location} (ea : a = a') (eb : b = b') (ee : e = e')
    {after nonempty after' nonempty'} :
    batch.pushLocated ty a b s e after nonempty =
      batch.pushLocated ty a' b' s e' after' nonempty' := by
  subst ea eb ee
  rfl

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H R E]
  [∀ batch, ConsumeFrom H (BatchCursor batch) m]
  {floor : Option Nat} {low : Nat} (start : Nat) (b : USize)

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem leave_sim (offset : Nat) (base position : USize) (batch : TokenBatch)
    (ok : PosOk start base position) (hframe hframe' hbatch hbatch') :
    SimP (BaseIs b) (fun _ => BaseIs position) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.leave (H := H) (m := m) (R := R) (E := E) offset base position
        batch hframe hbatch)
      (Lexer.WRustPort.leave offset (ix start base) (ix start position) batch hframe'
        hbatch') := by
  unfold BSmtLib.Lexer.Internal.leave Lexer.WRustPort.leave
  refine modifyBound_sim start _ _ (fun c _ => ?_) fun _ _ => rfl
  simp only [coreMap, ok.sub]

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem leavePending_sim (state : Lexer.LexerState) (s : Location) (offset : Nat)
    (base position : USize) (batch : TokenBatch) (ok : PosOk start base position)
    (hframe hframe' hbatch hbatch' hstart hstart' hfloor hfloor') :
    SimP (BaseIs b) (fun _ => BaseIs position) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.leavePending (H := H) (m := m) (R := R) (E := E) state s offset base
        position batch hframe hbatch hstart hfloor)
      (Lexer.WRustPort.leavePending state s offset (ix start base) (ix start position) batch
        hframe' hbatch' hstart' hfloor') := by
  unfold BSmtLib.Lexer.Internal.leavePending Lexer.WRustPort.leavePending
  refine modifyBound_sim start _ _ (fun c _ => ?_) fun _ _ => rfl
  simp only [coreMap, ok.sub]

theorem flushHeld_sim (batch : TokenBatch) (origin : Nat) (hbatch hbatch') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low))
      (fun r => ⟨r.val, r.property⟩)
      (BSmtLib.Lexer.Internal.flushHeld (H := H) (m := m) (R := R) (E := E) batch origin hbatch)
      (Lexer.X1BatchInCore.flushHeld batch origin hbatch') := by
  unfold BSmtLib.Lexer.Internal.flushHeld Lexer.X1BatchInCore.flushHeld
  exact SimP.seq (handOver_sim start b _ _ _ _) fun _ => SimP.pure (fun _ h => h) rfl

/-- `flushHeld` of equal batches up to equal origins. -/
theorem flushHeld_sim' (batch batch' : TokenBatch) (origin origin' : Nat) (eb : batch = batch')
    (eo : origin = origin') (hbatch hbatch') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap start (floor := floor) (low := low))
      (fun r => ⟨r.val, eo ▸ r.property.1, r.property.2⟩)
      (BSmtLib.Lexer.Internal.flushHeld (H := H) (m := m) (R := R) (E := E) batch origin hbatch)
      (Lexer.X1BatchInCore.flushHeld batch' origin' hbatch') := by
  subst eb eo
  exact flushHeld_sim start b _ _ _ _

/-- The batch held at a position, for that held at its index. -/
def heldMap {offset : Nat} {base p : USize} (ok : PosOk start base p)
    (r : {batch : TokenBatch // BSmtLib.Lexer.Internal.Held floor offset base p batch}) :
    {batch : TokenBatch // Lexer.WRustPort.Held floor offset (ix start base) (ix start p) batch} :=
  ⟨r.val, by rw [← ok.sub]; exact r.property.1, r.property.2⟩

theorem pushFast_sim (slice : ByteSlice) (batch : TokenBatch) (u : Unit) (offset : Nat)
    (base : USize)
    (ty : TokenCategory) (cs ce s e : USize) (emit : Bool) (hty hty')
    (hcs : slice.start ≤ cs.toNat) (hce : slice.start ≤ ce.toNat)
    (oks : PosOk slice.start base s) (oke : PosOk slice.start base e)
    (hstart hstart' hend hend' hframe hframe' hbatch hbatch') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
      (heldMap slice.start oke)
      (BSmtLib.Lexer.Internal.pushFast (H := H) (m := m) (R := R) (E := E) batch offset base ty cs
        ce s e emit hty hstart hend hframe hbatch)
      (Lexer.X1BatchInCore.pushFast slice batch u offset (ix slice.start base) ty
        (ix slice.start cs) (ix slice.start ce) (ix slice.start s) (ix slice.start e) emit hty'
        hstart' hend' hframe' hbatch') := by
  unfold BSmtLib.Lexer.Internal.pushFast Lexer.X1BatchInCore.pushFast
  refine SimP.ite Iff.rfl (fun _ => SimP.pure (fun _ h => h) rfl) fun _ => ?_
  refine getCore_bind _ _ fun c _ => ?_
  dsimp only
  have es : offset + (s - base).toNat = offset + (ix slice.start s - ix slice.start base) := by
    rw [oks.sub]
  have ee : offset + (e - base).toNat = offset + (ix slice.start e - ix slice.start base) := by
    rw [oke.sub]
  refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => SimP.pure (fun _ h => h) ?_
  · refine SimP.seq (flushHeld_sim' _ b _ _ _ _
      (pushOnLine_congr (start_add_ix hcs).symm (start_add_ix hce).symm es ee) ee _ _) fun x => ?_
    obtain ⟨bt, hl, hf⟩ := x
    dsimp only
    exact SimP.pure (fun _ h => h) rfl
  · apply Subtype.ext
    dsimp only [heldMap]
    exact pushOnLine_congr (start_add_ix hcs).symm (start_add_ix hce).symm es ee

theorem pushBorrowed_sim (slice : ByteSlice) (batch : TokenBatch) (offset : Nat) (base : USize)
    (ty : TokenCategory) (cs ce : USize) (s : Location) (te : USize)
    (hcs : slice.start ≤ cs.toNat) (hce : slice.start ≤ ce.toNat)
    (oke : PosOk slice.start base te) (hty hty' hafter hafter' hend hend' hfloor hfloor') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
      (heldMap slice.start oke)
      (BSmtLib.Lexer.Internal.pushBorrowed (H := H) (m := m) (R := R) (E := E) batch offset base ty
        cs ce s te hty hafter hend hfloor)
      (Lexer.WRustPort.pushBorrowed slice batch offset (ix slice.start base) ty
        (ix slice.start cs) (ix slice.start ce) s (ix slice.start te) hty' hafter' hend'
        hfloor') := by
  unfold BSmtLib.Lexer.Internal.pushBorrowed Lexer.WRustPort.pushBorrowed
  refine getCore_bind _ _ fun c _ => ?_
  dsimp only
  have ee : offset + (te - base).toNat = offset + (ix slice.start te - ix slice.start base) := by
    rw [oke.sub]
  have el : Location.mk (offset + (te - base).toNat) c.line
      (offset + (te - base).toNat - c.lineStart) =
      Location.mk (offset + (ix slice.start te - ix slice.start base)) c.line
        (offset + (ix slice.start te - ix slice.start base) - c.lineStart) := by
    rw [ee]
  refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => SimP.pure (fun _ h => h) ?_
  · refine SimP.seq (flushHeld_sim' _ b _ _ _ _
      (pushLocated_congr (start_add_ix hcs).symm (start_add_ix hce).symm el) ee _ _) fun x => ?_
    obtain ⟨bt, hl, hf⟩ := x
    dsimp only
    exact SimP.pure (fun _ h => h) rfl
  · apply Subtype.ext
    dsimp only [heldMap]
    exact pushLocated_congr (start_add_ix hcs).symm (start_add_ix hce).symm el

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
/-- `leave`, with the indices of the second lexer given by equations. -/
theorem leave_sim' (offset : Nat) (base position : USize) (batch : TokenBatch)
    (base' position' : Nat) (eb : ix start base = base') (ep : ix start position = position')
    (ok : PosOk start base position) (hframe hframe' hbatch hbatch') :
    SimP (BaseIs b) (fun _ => BaseIs position) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.leave (H := H) (m := m) (R := R) (E := E) offset base position
        batch hframe hbatch)
      (Lexer.WRustPort.leave offset base' position' batch hframe' hbatch') := by
  subst eb ep
  exact leave_sim start b offset base position batch ok _ _ _ _

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
/-- `leavePending`, with the indices of the second lexer given by equations. -/
theorem leavePending_sim' (state : Lexer.LexerState) (s : Location) (offset : Nat)
    (base position : USize) (batch : TokenBatch) (base' position' : Nat)
    (eb : ix start base = base') (ep : ix start position = position')
    (ok : PosOk start base position)
    (hframe hframe' hbatch hbatch' hstart hstart' hfloor hfloor') :
    SimP (BaseIs b) (fun _ => BaseIs position) (boundMap start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.leavePending (H := H) (m := m) (R := R) (E := E) state s offset base
        position batch hframe hbatch hstart hfloor)
      (Lexer.WRustPort.leavePending state s offset base' position' batch hframe' hbatch' hstart'
        hfloor') := by
  subst eb ep
  exact leavePending_sim start b state s offset base position batch ok _ _ _ _ _ _ _ _

/-- `pushBorrowed`, with the indices of the second lexer given by equations. -/
theorem pushBorrowed_sim' (slice : ByteSlice) (batch : TokenBatch) (offset : Nat) (base : USize)
    (ty : TokenCategory) (cs ce : USize) (s : Location) (te : USize) (base' cs' ce' te' : Nat)
    (eb : ix slice.start base = base') (ecs : ix slice.start cs = cs')
    (ece : ix slice.start ce = ce') (ete : ix slice.start te = te')
    (hcs : slice.start ≤ cs.toNat) (hce : slice.start ≤ ce.toNat)
    (oke : PosOk slice.start base te) (hty hty' hafter hafter' hend hend' hfloor hfloor') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
      (fun r => ⟨r.val, by rw [← eb, ← ete, ← oke.sub]; exact r.property.1, r.property.2⟩)
      (BSmtLib.Lexer.Internal.pushBorrowed (H := H) (m := m) (R := R) (E := E) batch offset base ty
        cs ce s te hty hafter hend hfloor)
      (Lexer.WRustPort.pushBorrowed slice batch offset base' ty cs' ce' s te' hty' hafter' hend'
        hfloor') := by
  subst eb ecs ece ete
  exact pushBorrowed_sim b slice batch offset base ty cs ce s te hcs hce oke _ _ _ _ _ _ _ _

/-- `pushFast`, with the indices of the second lexer given by equations. -/
theorem pushFast_sim' (slice : ByteSlice) (batch : TokenBatch) (u : Unit) (offset : Nat)
    (base : USize) (ty : TokenCategory) (cs ce s e : USize) (emit emit' : Bool)
    (base' cs' ce' s' e' : Nat)
    (eb : ix slice.start base = base') (ecs : ix slice.start cs = cs')
    (ece : ix slice.start ce = ce') (es : ix slice.start s = s') (ee : ix slice.start e = e')
    (eemit : emit = emit')
    (hty hty') (hcs : slice.start ≤ cs.toNat) (hce : slice.start ≤ ce.toNat)
    (oks : PosOk slice.start base s) (oke : PosOk slice.start base e)
    (hstart hstart' hend hend' hframe hframe' hbatch hbatch') :
    SimP (BaseIs b) (fun _ => BaseIs b) (boundMap slice.start (floor := floor) (low := low))
      (fun r => ⟨r.val, by rw [← eb, ← ee, ← oke.sub]; exact r.property.1, r.property.2⟩)
      (BSmtLib.Lexer.Internal.pushFast (H := H) (m := m) (R := R) (E := E) batch offset base ty cs
        ce s e emit hty hstart hend hframe hbatch)
      (Lexer.X1BatchInCore.pushFast slice batch u offset base' ty cs' ce' s' e' emit' hty' hstart'
        hend' hframe' hbatch') := by
  subst eb ecs ece es ee eemit
  exact pushFast_sim b slice batch u offset base ty cs ce s e emit _ _ hcs hce oks oke
    _ _ _ _ _ _ _ _

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem storeUnfinishedSymbolRun_sim (slice : ByteSlice) (h : slice.stop < USize.size)
    (entry : UInt8) (offset : Nat) (base index after runEndAt : USize) (batch : TokenBatch)
    (oki : PosOk slice.start base index) (oka : PosOk slice.start base after)
    (okr : PosOk slice.start base runEndAt)
    (hframe hframe' hindex hindex' hrun hrun' hbatch hbatch') :
    SimP (BaseIs b) (fun _ => BaseIs runEndAt)
      (boundMap slice.start (floor := floor) (low := low)) id
      (BSmtLib.Lexer.Internal.storeUnfinishedSymbolRun (H := H) (m := m) (R := R) (E := E)
        (inputOf slice h) entry offset base index after runEndAt batch hframe hindex hrun hbatch)
      (Lexer.WRustPort.storeUnfinishedSymbolRun slice entry offset (ix slice.start base)
        (ix slice.start index) (ix slice.start after) (ix slice.start runEndAt) batch hframe'
        hindex' hrun' hbatch') := by
  unfold BSmtLib.Lexer.Internal.storeUnfinishedSymbolRun
    Lexer.WRustPort.storeUnfinishedSymbolRun
  have := oki.hb; have := oki.hp; have := oka.hp; have := okr.hp
  refine SimP.seq (startToken_sim _ b offset base index oki.hb oki.hp _ _) fun x => ?_
  obtain ⟨s, hs⟩ := x
  dsimp only
  refine SimP.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimP.seq (extendContent_sim b slice h after runEndAt (by omega) (by omega)) fun _ => ?_
    exact leavePending_sim _ b _ _ _ _ _ _ okr _ _ _ _ _ _ _ _
  · refine SimP.seq (extendContent_sim b slice h index runEndAt (by omega) (by omega)) fun _ => ?_
    exact leavePending_sim _ b _ _ _ _ _ _ okr _ _ _ _ _ _ _ _

end

end BSmtLib.Proofs.X1BatchInCoreLexer
