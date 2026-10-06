import BSmtLib.Proofs.X1BatchInCoreX2Contents.Cursor
import BSmtLib.Proofs.X1BatchInCoreX2Contents.Framework

/-!
# The helpers of the two lexers that read and change the state

Each helper of the lexer with the content buffer is simulated by the same helper of the lexer
with the batch kept in the lexer's state, under the map of states `coreMap`, from the states
whose content buffer fits its array (`BFits`), which every helper keeps. The helpers that change
the content are where the two differ.
-/

namespace BSmtLib.Proofs.X1BatchInCoreX2Contents

open BSmtLib.Proofs.Simulation

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m]
  {floor : Option Nat} {low : Nat}

theorem getCore_sim (P : S2 floor low → Prop) :
    SimF BFits P (fun c s => P s ∧ c = s.val) boundMap coreMap
      (Lexer.X2Contents.getCore (H := H) (m := m) (R := R) (E := E))
      (Lexer.X1BatchInCore.getCore) := by
  unfold Lexer.X2Contents.getCore Lexer.X1BatchInCore.getCore
  exact SimF.bind (SimF.get (Q := fun a s => P s ∧ a = s) fun s hs => ⟨hs, rfl⟩)
    fun a => SimF.pure (fun s hs => ⟨hs.1, by rw [hs.2]⟩) rfl

/-- A step after reading the state, from a state whose buffer fits. -/
theorem getCore_bind {α β : Type} {ψ : α → β}
    {k : Core2 → Lexer.X2Contents.LexM H m R E floor low α}
    {k' : Core1 → Lexer.X1BatchInCore.LexM H m R E floor low β} {Q : α → S2 floor low → Prop}
    (hk : ∀ c, Fits c.tokenContent → SimF BFits BFits Q boundMap ψ (k c) (k' (coreMap c))) :
    SimF BFits BFits Q boundMap ψ (Lexer.X2Contents.getCore >>= k)
      (Lexer.X1BatchInCore.getCore >>= k') := by
  refine SimF.bind (getCore_sim _) fun c => ?_
  intro s hs h
  exact hk c (by rw [hs.2]; exact hs.1) s hs.1 h

theorem modifyCore_sim {f : Core2 → Core2} {g : Core1 → Core1}
    {hf : ∀ c, c.Bound floor low → (f c).Bound floor low}
    {hg : ∀ c, c.Bound floor low → (g c).Bound floor low}
    (P : S2 floor low → Prop) (Q : Unit → S2 floor low → Prop)
    (e : ∀ c, P c → g (coreMap c.val) = coreMap (f c.val))
    (hq : ∀ c, P c → Q () ⟨f c.val, hf c.val c.property⟩) :
    SimF BFits P Q boundMap id
      (Lexer.X2Contents.modifyCore (H := H) (m := m) (R := R) (E := E) f hf)
      (Lexer.X1BatchInCore.modifyCore g hg) := by
  unfold Lexer.X2Contents.modifyCore Lexer.X1BatchInCore.modifyCore
  exact SimF.modify (fun c hc => Subtype.ext (e c hc)) hq

theorem modifyBound_sim
    {f : (c : Core2) → c.Bound floor low → {c' : Core2 // c'.Bound floor low}}
    {g : (c : Core1) → c.Bound floor low → {c' : Core1 // c'.Bound floor low}}
    (P : S2 floor low → Prop) (Q : Unit → S2 floor low → Prop)
    (e : ∀ c, P c → (g (coreMap c.val) c.property).val = coreMap (f c.val c.property))
    (hq : ∀ c, P c → Q () (f c.val c.property)) :
    SimF BFits P Q boundMap id
      (Lexer.X2Contents.modifyBound (H := H) (m := m) (R := R) (E := E) f)
      (Lexer.X1BatchInCore.modifyBound g) := by
  unfold Lexer.X2Contents.modifyBound Lexer.X1BatchInCore.modifyBound
  exact SimF.modify (fun c hc => Subtype.ext (e c hc)) hq

/-- A change of the state that keeps the content buffer and is the same in both lexers. -/
theorem modifyCore_same {f : Core2 → Core2} {g : Core1 → Core1}
    {hf : ∀ c, c.Bound floor low → (f c).Bound floor low}
    {hg : ∀ c, c.Bound floor low → (g c).Bound floor low}
    (e : ∀ c, g (coreMap c) = coreMap (f c))
    (ht : ∀ c, (f c).tokenContent = c.tokenContent) :
    SimF BFits BFits (fun _ => BFits) boundMap id
      (Lexer.X2Contents.modifyCore (H := H) (m := m) (R := R) (E := E) f hf)
      (Lexer.X1BatchInCore.modifyCore g hg) :=
  modifyCore_sim _ _ (fun c _ => e c.val) fun c hc => by
    show Fits (f c.val).tokenContent
    rw [ht]
    exact hc

theorem setNormal_sim :
    SimF BFits BFits (fun _ => BFits) boundMap id
      (Lexer.X2Contents.setNormal (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low))
      Lexer.X1BatchInCore.setNormal :=
  modifyCore_same (fun _ => rfl) fun _ => rfl

theorem setTokenState_sim (state : Lexer.LexerState) (s : Location)
    (h : Lexer.X2Contents.Started floor low s) (h' : Lexer.X1BatchInCore.Started floor low s) :
    SimF BFits BFits (fun _ => BFits) boundMap id
      (Lexer.X2Contents.setTokenState (H := H) (m := m) (R := R) (E := E) state s h)
      (Lexer.X1BatchInCore.setTokenState state s h') :=
  modifyBound_sim _ _ (fun _ _ => rfl) fun _ hc => hc

theorem modifyContent_sim (f : Lexer.ContentBuffer → Lexer.ContentBuffer)
    (g : ByteArray → ByteArray) (e : ∀ buf, Fits buf → g (contentBytes buf) = contentBytes (f buf))
    (hf : ∀ buf, Fits buf → Fits (f buf)) :
    SimF BFits BFits (fun _ => BFits) boundMap id
      (Lexer.X2Contents.modifyContent (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) f)
      (Lexer.X1BatchInCore.modifyContent g) := by
  unfold Lexer.X2Contents.modifyContent Lexer.X1BatchInCore.modifyContent
  refine modifyCore_sim _ _ (fun c hc => ?_) fun c hc => hf _ hc
  simp only [coreMap, e _ hc]

theorem extendContent_sim (input : ByteSlice) (a b : Nat) (hr : b ≤ input.size ∨ b ≤ a) :
    SimF BFits BFits (fun _ => BFits) boundMap id
      (Lexer.X2Contents.extendContent (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) input a b)
      (Lexer.X1BatchInCore.extendContent input a b) := by
  unfold Lexer.X2Contents.extendContent Lexer.X1BatchInCore.extendContent
    Lexer.X1BatchInCore.extendContentFrom
  exact modifyContent_sim _ _ (fun buf h => (contentBytes_extendSlice input h hr).symm)
    fun buf h => fits_extendSlice input h hr

theorem pushContent_sim (x : UInt8) :
    SimF BFits BFits (fun _ => BFits) boundMap id
      (Lexer.X2Contents.pushContent (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) x)
      (Lexer.X1BatchInCore.pushContent x) := by
  unfold Lexer.X2Contents.pushContent Lexer.X1BatchInCore.pushContent
  exact modifyContent_sim _ _ (fun buf h => (contentBytes_push h x).symm) fun buf h => fits_push h x

theorem startToken_sim (offset : Nat) (base position : Nat)
    (hframe : Lexer.X2Contents.Frame floor low offset)
    (hframe' : Lexer.X1BatchInCore.Frame floor low offset) :
    SimF BFits BFits (fun _ => BFits) boundMap id
      (Lexer.X2Contents.startToken (H := H) (m := m) (R := R) (E := E) offset base position
        hframe)
      (Lexer.X1BatchInCore.startToken offset base position hframe') := by
  unfold Lexer.X2Contents.startToken Lexer.X1BatchInCore.startToken
  refine getCore_bind fun c _ => ?_
  refine SimF.seq (modifyCore_same (fun _ => rfl) fun _ => rfl) fun _ => ?_
  refine SimF.seq (modifyContent_sim _ _ (fun buf _ => (contentBytes_clear buf).symm)
    fun buf _ => fits_clear buf) fun _ => ?_
  exact SimF.pure (fun _ h => h) rfl

theorem markLineFeedAt_sim (position : Nat) :
    SimF BFits BFits (fun _ => BFits) boundMap id
      (Lexer.X2Contents.markLineFeedAt (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) position)
      (Lexer.X1BatchInCore.markLineFeedAt position) :=
  modifyCore_same (fun _ => rfl) fun _ => rfl

theorem failWith_sim {α β : Type} (ψ : α → β) (kind : LexicalErrorKind) (position failure : Nat)
    (Q : α → S2 floor low → Prop) :
    SimF BFits BFits Q boundMap ψ
      (Lexer.X2Contents.failWith (H := H) (m := m) (R := R) (E := E) kind position failure)
      (Lexer.X1BatchInCore.failWith kind position failure) := by
  unfold Lexer.X2Contents.failWith Lexer.X1BatchInCore.failWith
  refine getCore_bind fun c _ => ?_
  exact SimF.throw (fun _ h => h) _

theorem failAt_sim {α β : Type} (ψ : α → β) (kind : LexicalErrorKind) (position : Nat)
    (Q : α → S2 floor low → Prop) :
    SimF BFits BFits Q boundMap ψ
      (Lexer.X2Contents.failAt (H := H) (m := m) (R := R) (E := E) kind position)
      (Lexer.X1BatchInCore.failAt kind position) :=
  failWith_sim ψ kind _ _ Q

theorem fail_sim {α β : Type} (ψ : α → β) (kind : LexicalErrorKind) (te : Lexer.Slice.TokenEnd)
    (Q : α → S2 floor low → Prop) :
    SimF BFits BFits Q boundMap ψ
      (Lexer.X2Contents.fail (H := H) (m := m) (R := R) (E := E) kind te)
      (Lexer.X1BatchInCore.fail kind te) :=
  failWith_sim ψ kind _ _ Q

theorem expectDelimiter_sim (next : UInt8) (position : Nat) :
    SimF BFits BFits (fun _ => BFits) boundMap id
      (Lexer.X2Contents.expectDelimiter (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) next position)
      (Lexer.X1BatchInCore.expectDelimiter next position) := by
  unfold Lexer.X2Contents.expectDelimiter Lexer.X1BatchInCore.expectDelimiter
  exact SimF.ite Iff.rfl (fun _ => SimF.pure (fun _ h => h) rfl)
    fun _ => failAt_sim id _ _ _

theorem locationFrom_sim (base position : Nat) :
    SimF BFits BFits (fun _ => BFits) boundMap id
      (Lexer.X2Contents.locationFrom (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) base position)
      (Lexer.X1BatchInCore.locationFrom base position) := by
  unfold Lexer.X2Contents.locationFrom Lexer.X1BatchInCore.locationFrom
  exact getCore_bind fun c _ => SimF.pure (fun _ h => h) rfl

end

end BSmtLib.Proofs.X1BatchInCoreX2Contents
