import BSmtLib.Proofs.X1BatchInCoreX2Contents.Finish

/-!
# The batch held by the loop of the normal state, in both lexers

The loop of the normal state of both lexers holds the batch and appends the tokens it lexes from
the slice to it: the lexer with the content buffer with their contents as positions in the
slice's array, the lexer with the batch kept in the lexer's state with their contents as views
of the slice, from which it takes the same positions (`slice_start`, `slice_stop`) as long as
the content lies within the slice. The runs of the slice end within it (`runEnd_le`), which is
where the contents end.
-/

namespace BSmtLib.Proofs.X1BatchInCoreX2Contents

open BSmtLib.Proofs.Simulation

/-! ## Where runs end -/

theorem runEndBy_le_or (stops : UInt8 → Bool) (slice : ByteSlice) (index : Nat) :
    Lexer.Slice.runEndBy stops slice index ≤ slice.size ∨
      Lexer.Slice.runEndBy stops slice index = index := by
  fun_induction Lexer.Slice.runEndBy stops slice index with
  | case1 i hi _ => exact .inl (Nat.le_of_lt hi)
  | case2 i hi _ ih => exact .inl (ih.elim id fun h => by omega)
  | case3 i _ => exact .inr rfl

theorem runEnd_le_or (slice : ByteSlice) (index : Nat) (mask : UInt8) :
    Lexer.Slice.runEnd slice index mask ≤ slice.size ∨
      Lexer.Slice.runEnd slice index mask = index :=
  runEndBy_le_or _ _ _

theorem runEndAll_le_or (slice : ByteSlice) (index : Nat) (mask : UInt8) :
    Lexer.Slice.runEndAll slice index mask ≤ slice.size ∨
      Lexer.Slice.runEndAll slice index mask = index :=
  runEndBy_le_or _ _ _

/-- A run from an index within the slice ends within it. -/
theorem runEnd_le {slice : ByteSlice} {index : Nat} (h : index ≤ slice.size) (mask : UInt8) :
    Lexer.Slice.runEnd slice index mask ≤ slice.size :=
  (runEnd_le_or slice index mask).elim id fun e => by omega

/-- The range of a run is one the content can be extended from. -/
theorem runEnd_range (slice : ByteSlice) (index : Nat) (mask : UInt8) :
    Lexer.Slice.runEnd slice index mask ≤ slice.size ∨
      Lexer.Slice.runEnd slice index mask ≤ index :=
  (runEnd_le_or slice index mask).imp_right Nat.le_of_eq

theorem runEndAll_range (slice : ByteSlice) (index : Nat) (mask : UInt8) :
    Lexer.Slice.runEndAll slice index mask ≤ slice.size ∨
      Lexer.Slice.runEndAll slice index mask ≤ index :=
  (runEndAll_le_or slice index mask).imp_right Nat.le_of_eq

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat}

omit [Consume H m R E] in
theorem leave_sim (offset : Nat) (base position : Nat) (batch : TokenBatch)
    (hframe hframe' hbatch hbatch') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.leave (H := H) (m := m) (R := R) (E := E) offset base position batch
        hframe hbatch)
      (Lexer.X1BatchInCore.leave offset base position batch hframe' hbatch') :=
  modifyBound_sim _ _ (fun _ _ => rfl) fun _ hc => hc

omit [Consume H m R E] in
theorem leavePending_sim (state : Lexer.LexerState) (s : Location) (offset : Nat)
    (base position : Nat) (batch : TokenBatch)
    (hframe hframe' hbatch hbatch' hstart hstart' hfloor hfloor') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.leavePending (H := H) (m := m) (R := R) (E := E) state s offset base
        position batch hframe hbatch hstart hfloor)
      (Lexer.X1BatchInCore.leavePending state s offset base position batch hframe' hbatch'
        hstart' hfloor') :=
  modifyBound_sim _ _ (fun _ _ => rfl) fun _ hc => hc

variable (hblind : ContentBlind H m R E)
include hblind

theorem flushHeld_sim (batch : TokenBatch) (origin : Nat) (hbatch hbatch') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low))
      id
      (Lexer.X2Contents.flushHeld (H := H) (m := m) (R := R) (E := E) batch origin hbatch)
      (Lexer.X1BatchInCore.flushHeld batch origin hbatch') := by
  unfold Lexer.X2Contents.flushHeld Lexer.X1BatchInCore.flushHeld
  refine SimF.bind (handOver_sim hblind _ _ (sameTokens_refl _ _) _ _ _) fun _ => ?_
  exact SimF.pure (fun _ h => h) rfl

theorem pushFast_sim (input : ByteSlice) (batch : TokenBatch) (offset base : Nat)
    (ty : TokenCategory) (cs ce start «end» : Nat) (emit : Bool) (hcs : cs ≤ ce)
    (hce : ce ≤ input.size) (hty hty' hstart hstart' hend hend' hframe hframe' hbatch
      hbatch') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low))
      id
      (Lexer.X2Contents.pushFast (H := H) (m := m) (R := R) (E := E) input batch offset base ty
        cs ce start «end» emit hty hstart hend hframe hbatch)
      (Lexer.X1BatchInCore.pushFast batch offset base ty (input.slice cs ce) start «end» emit
        hty' hstart' hend' hframe' hbatch') := by
  unfold Lexer.X2Contents.pushFast Lexer.X1BatchInCore.pushFast
  rw [slice_start input hcs hce, slice_stop input hce]
  refine SimF.ite Iff.rfl (fun _ => SimF.pure (fun _ h => h) rfl) fun _ => ?_
  refine getCore_bind fun c _ => ?_
  refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => SimF.pure (fun _ h => h) rfl
  refine SimF.bind (flushHeld_sim (m := m) hblind _ _ _ _) fun x => ?_
  obtain ⟨b, hl, hf⟩ := x
  dsimp only
  exact SimF.pure (fun _ h => h) rfl

theorem pushBorrowed_sim (input : ByteSlice) (batch : TokenBatch) (offset base : Nat)
    (ty : TokenCategory) (cs ce : Nat) (start : Location) (tokenEnd : Nat) (hcs : cs ≤ ce)
    (hce : ce ≤ input.size) (hty hty' hafter hafter' hend hend' hfloor hfloor') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low))
      id
      (Lexer.X2Contents.pushBorrowed (H := H) (m := m) (R := R) (E := E) input batch offset base
        ty cs ce start tokenEnd hty hafter hend hfloor)
      (Lexer.X1BatchInCore.pushBorrowed batch offset base ty (input.slice cs ce) start tokenEnd
        hty' hafter' hend' hfloor') := by
  unfold Lexer.X2Contents.pushBorrowed Lexer.X1BatchInCore.pushBorrowed
  rw [slice_start input hcs hce, slice_stop input hce]
  refine getCore_bind fun c _ => ?_
  refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => SimF.pure (fun _ h => h) rfl
  refine SimF.bind (flushHeld_sim (m := m) hblind _ _ _ _) fun x => ?_
  obtain ⟨b, hl, hf⟩ := x
  dsimp only
  exact SimF.pure (fun _ h => h) rfl

/-- `pushFast_sim`, with the type and the view of the second lexer given by equations. -/
theorem pushFast_sim' (input : ByteSlice) (batch : TokenBatch) (offset base : Nat)
    (ty ty' : TokenCategory) (ety : ty' = ty) (cs ce : Nat) (content : ByteSlice)
    (econtent : content = input.slice cs ce) (start «end» : Nat) (emit : Bool) (hcs : cs ≤ ce)
    (hce : ce ≤ input.size) (hty hty' hstart hstart' hend hend' hframe hframe' hbatch
      hbatch') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low))
      id
      (Lexer.X2Contents.pushFast (H := H) (m := m) (R := R) (E := E) input batch offset base ty
        cs ce start «end» emit hty hstart hend hframe hbatch)
      (Lexer.X1BatchInCore.pushFast batch offset base ty' content start «end» emit
        hty' hstart' hend' hframe' hbatch') := by
  subst ety econtent
  exact pushFast_sim hblind input batch offset base ty' cs ce start «end» emit hcs hce _ _ _ _ _ _
    _ _ _ _

/-- `pushBorrowed_sim`, with the view of the second lexer given by an equation. -/
theorem pushBorrowed_sim' (input : ByteSlice) (batch : TokenBatch) (offset base : Nat)
    (ty : TokenCategory) (cs ce : Nat) (content : ByteSlice)
    (econtent : content = input.slice cs ce) (start : Location) (tokenEnd : Nat) (hcs : cs ≤ ce)
    (hce : ce ≤ input.size) (hty hty' hafter hafter' hend hend' hfloor hfloor') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low))
      id
      (Lexer.X2Contents.pushBorrowed (H := H) (m := m) (R := R) (E := E) input batch offset base
        ty cs ce start tokenEnd hty hafter hend hfloor)
      (Lexer.X1BatchInCore.pushBorrowed batch offset base ty content start tokenEnd
        hty' hafter' hend' hfloor') := by
  subst econtent
  exact pushBorrowed_sim hblind input batch offset base ty cs ce start tokenEnd hcs hce _ _ _ _ _ _
    _ _

omit hblind [Consume H m R E] in
/-- Extending the content by a view of the slice, given by an equation. -/
theorem extendContentFrom_sim (input : ByteSlice) (a b : Nat) (content : ByteSlice)
    (econtent : content = input.slice a b) (hr : b ≤ input.size ∨ b ≤ a) :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.extendContent (H := H) (m := m) (R := R) (E := E) input a b)
      (Lexer.X1BatchInCore.extendContentFrom content) := by
  subst econtent
  exact extendContent_sim input a b hr

omit hblind [Consume H m R E] [LawfulMonad m] in
theorem fastCategory_eq (q w : Bool) :
    Lexer.X1BatchInCore.fastCategory q w = Lexer.X2Contents.fastCategory q w := rfl

omit hblind in
theorem consumes_sim :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.consumesWhitespaceAndComments (H := H) (m := m) (R := R) (E := E))
      (Lexer.X1BatchInCore.consumesWhitespaceAndComments) := by
  unfold Lexer.X2Contents.consumesWhitespaceAndComments
    Lexer.X1BatchInCore.consumesWhitespaceAndComments
  exact SimF.pure (fun _ h => h) rfl

omit hblind [Consume H m R E] in
theorem storeUnfinishedSymbolRun_sim (input : ByteSlice) (entry : UInt8) (offset : Nat)
    (base index after runEndAt : Nat) (batch : TokenBatch) (hrun : runEndAt ≤ input.size)
    (hframe hframe' hindex hindex' hrun' hrun'' hbatch hbatch') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.storeUnfinishedSymbolRun (H := H) (m := m) (R := R) (E := E) input entry
        offset base index after runEndAt batch hframe hindex hrun' hbatch)
      (Lexer.X1BatchInCore.storeUnfinishedSymbolRun input entry offset base index after runEndAt
        batch hframe' hindex' hrun'' hbatch') := by
  unfold Lexer.X2Contents.storeUnfinishedSymbolRun Lexer.X1BatchInCore.storeUnfinishedSymbolRun
  refine SimF.bind (startToken_sim _ _ _ _ _) fun x => ?_
  obtain ⟨s, hs⟩ := x
  dsimp only
  refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_ <;>
    exact SimF.seq (extendContent_sim input _ _ (.inl hrun)) fun _ =>
      leavePending_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem startWhitespaceFrom_sim (input : ByteSlice) (offset : Nat) (base index : Nat)
    (s : Location) :
    ∀ k (batch : TokenBatch) (e : Nat), input.size - e = k → ∀ hframe hframe' hstart hstart'
      hend hend' hrun hrun' hbatch hbatch',
      SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low))
        id
        (Lexer.X2Contents.startWhitespaceFrom (H := H) (m := m) (R := R) (E := E) input offset
          base index e s batch hframe hstart hend hrun hbatch)
        (Lexer.X1BatchInCore.startWhitespaceFrom input offset base index e s batch hframe'
          hstart' hend' hrun' hbatch') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro batch e hk hframe hframe' hstart hstart' hend hend' hrun hrun' hbatch hbatch'
  rw [Lexer.X2Contents.startWhitespaceFrom, Lexer.X1BatchInCore.startWhitespaceFrom]
  dsimp only
  have hle := runEnd_le hend.2.2 Lexer.RUN_NON_LF_WHITESPACE
  have hge := Lexer.Slice.le_runEnd input e Lexer.RUN_NON_LF_WHITESPACE
  split
  · rename_i c hc
    have hlt := Lexer.Slice.lt_size_of_get? hc
    split
    · rename_i hlf
      split
      · rename_i c' hc'
        obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
        split
        · refine SimF.seq (markLineFeedAt_sim _) fun _ => ?_
          exact ih _ (by omega) _ _ rfl _ _ _ _ _ _ _ _ _ _
        · contradiction
      · rename_i hc'
        exact absurd (hc'.symm.trans hc) (by simp)
    · rename_i hlf
      split
      · rename_i c' hc'
        obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
        split
        · contradiction
        · have hrun2 := Lexer.X2Contents.lt_whitespaceRunEnd hend.2.1 hrun hc hlf
          refine SimF.bind (pushBorrowed_sim (m := m) hblind input batch offset base _ index _ s _
            (by omega) hle _ _ _ _ _ _ _ _) fun x => ?_
          exact SimF.pure (fun _ h => h) rfl
      · rename_i hc'
        exact absurd (hc'.symm.trans hc) (by simp)
  · rename_i hc
    split
    · rename_i c' hc'
      exact absurd (hc'.symm.trans hc) (by simp)
    · refine SimF.seq (extendContent_sim input _ _ (.inl (Nat.le_refl _))) fun _ => ?_
      refine SimF.seq (leavePending_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _) fun _ => ?_
      exact SimF.pure (fun _ h => h) rfl

theorem startWhitespace_sim (input : ByteSlice) (offset : Nat) (base index : Nat)
    (batch : TokenBatch) (hrun hrun' hframe hframe' hindex hindex' hbatch hbatch') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.startWhitespace (H := H) (m := m) (R := R) (E := E) input offset base
        index batch hrun hframe hindex hbatch)
      (Lexer.X1BatchInCore.startWhitespace input offset base index batch hrun' hframe' hindex'
        hbatch') := by
  unfold Lexer.X2Contents.startWhitespace Lexer.X1BatchInCore.startWhitespace
  refine SimF.bind (startToken_sim _ _ _ _ _) fun x => ?_
  obtain ⟨s, hs⟩ := x
  exact startWhitespaceFrom_sim hblind input offset base index s _ batch index rfl _ _ _ _ _ _ _ _
    _ _

end

end BSmtLib.Proofs.X1BatchInCoreX2Contents
