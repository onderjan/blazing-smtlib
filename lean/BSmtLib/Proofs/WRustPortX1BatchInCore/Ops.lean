import BSmtLib.Proofs.WRustPortX1BatchInCore.Core

/-!
# Operations that simulate each other

The Rust port's code is written over a structure of operations (`WRustPort.Ops`): the batch
layer and the line counters of the fast path. Two structures of operations simulate each other
(`OpsSim`) when each operation of the one, run from states that correspond, is simulated by the
same operation of the other, with what the code that calls it needs before and after. The locals
of the loop of the normal state, which the two may keep apart, are related by `LRel` at the line
and the line start of the states, which do not change while the loop holds the locals.

`OpsSim` is all that the code over the operations needs: the code run over two structures of
operations that simulate each other runs alike (`WRustPortX1BatchInCore.Calls`).
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation
open BSmtLib.Proofs.Lexer.WRustPort (Ops)

/-- The two structures of operations simulate each other, with their locals related by `LRel` at
the line and the line start. -/
structure OpsSim {H : Type} {m : Type → Type} {R E : Type} [Monad m] (o₁ o₂ : Ops H m R E)
    (LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop) :
    Prop where
  /-- The locals are loaded related at the line and the line start of the states. -/
  loadLocals {floor : Option Nat} {low : Nat} {Er : St floor low → St floor low → Prop}
    (l ls : Nat) (Bx : TokenBatch → TokenBatch → Prop) :
    SimR Er (SRLx l ls Bx) (fun a b s t => LRel a b l ls ∧ SRLx l ls Bx s t)
      (Ops.loadLocals (self := o₁)) (Ops.loadLocals (self := o₂))
  /-- Locals related at the line and the line start of the states are stored alike. -/
  storeLocals {floor : Option Nat} {low : Nat} {Er : St floor low → St floor low → Prop}
    (l ls : Nat) (Bx : TokenBatch → TokenBatch → Prop) (a : Ops.Locals H m R E (self := o₁))
    (b : Ops.Locals H m R E (self := o₂)) (hab : LRel a b l ls) :
    SimR Er (SRLx l ls Bx) (fun _ _ => SRLx l ls Bx)
      (Ops.storeLocals (self := o₁) a) (Ops.storeLocals (self := o₂) b)
  /-- A token of the fast path goes into the batches held alike. -/
  pushFast {floor : Option Nat} {low : Nat} {strict : Bool} (l ls : Nat) (b b' : TokenBatch)
    (hb : HR b b') (a : Ops.Locals H m R E (self := o₁)) (a' : Ops.Locals H m R E (self := o₂))
    (ha : LRel a a' l ls) (input : ByteSlice) (offset base : Nat) (ty : TokenCategory)
    (contentStart contentStop start «end» : Nat) (emit : Bool) (hty hstart hend hframe hbatch
      hbatch') :
    LSim strict (SRE (floor := floor) (low := low) l ls) (PushQ l ls (·.val) (·.val))
      (Ops.pushFast (self := o₁) input b a offset base ty contentStart contentStop start «end»
        emit hty hstart hend hframe hbatch)
      (Ops.pushFast (self := o₂) input b' a' offset base ty contentStart contentStop start «end»
        emit hty hstart hend hframe hbatch')
  /-- The full batches held are handed over alike, and given back emptied. -/
  flushHeld {floor : Option Nat} {low : Nat} {strict : Bool} (l ls : Nat)
    (batch batch' : TokenBatch) (hb : Agree batch batch') (hbytes : batch.bytes = batch'.bytes)
    (origin : Nat) (hbatch hbatch') :
    LSim strict (SRE (floor := floor) (low := low) l ls)
      (fun a b s t => Agree a.val b.val ∧ a.val.bytes = b.val.bytes ∧ a.val.len = 0 ∧
        SRE l ls s t)
      (Ops.flushHeld (self := o₁) batch origin hbatch)
      (Ops.flushHeld (self := o₂) batch' origin hbatch')
  /-- The batches in the states are handed over alike, and left without tokens; a stop of the
  consumer is thrown from states whose batches have none. -/
  flushBatch {floor : Option Nat} {low : Nat} {strict : Bool} (l ls : Nat) :
    SimR (ErZ strict) (SRLb (floor := floor) (low := low) strict l ls)
      (fun _ _ => SREb strict l ls) (Ops.flushBatch (self := o₁)) (Ops.flushBatch (self := o₂))
  /-- A token whose content is in the content buffer is handed over alike, after the batches. -/
  sinkStoredAt {floor : Option Nat} {low : Nat} {strict : Bool} (l ls : Nat) (ty : TokenCategory)
    (start «end» : Location) (hend : start.offset < «end».offset) (hfloor) :
    SimR (ErZ strict) (SRLb (floor := floor) (low := low) strict l ls)
      (fun _ _ => SREb strict l ls) (Ops.sinkStoredAt (self := o₁) ty start «end» hend hfloor)
      (Ops.sinkStoredAt (self := o₂) ty start «end» hend hfloor)
  /-- The end-of-file token is handed over alike, from states whose batches have no tokens and
  whose content buffer is empty. -/
  sinkEof {low : Nat} (l ls : Nat) (location : Location) :
    SimR (ErZ false)
      (fun s t => SRE (floor := none) (low := low) l ls s t ∧ s.val.tokenContent.len = 0)
      (fun _ _ => SRE l ls) (Ops.sinkEof (self := o₁) location)
      (Ops.sinkEof (self := o₂) location)
  /-- The batches the end of the input starts with have no tokens, from states that correspond
  whose batches have none. -/
  eofBatch (c c' : Core) (hc : CoreRel c c') (hlen : c.batch.len = 0) :
    (Ops.eofBatch H m R E (self := o₁) c).val.len = 0 ∧
      (Ops.eofBatch H m R E (self := o₂) c').val.len = 0

end BSmtLib.Proofs.WRustPortX1BatchInCore
