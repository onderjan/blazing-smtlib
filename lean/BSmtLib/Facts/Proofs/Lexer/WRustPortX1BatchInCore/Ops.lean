import BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Core

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

namespace BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Ops

open BSmtLib.Lexer.Internal.WRustPort (Ops)
open BSmtLib.Facts.Proofs.Lexer.Simulation.Batch BSmtLib.Facts.Proofs.Lexer.Simulation.Relation

/-- The two structures of operations simulate each other, with their locals related by `LRel` at
the line and the line start. -/
structure OpsSim {H : Type} {m : Type → Type} {R E : Type} [Monad m] (o₁ o₂ : Ops H m R E)
    (LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop) :
    Prop where
  /-- The locals are loaded related at the line and the line start of the states. -/
  loadLocals {floor : Option Nat} {low : Nat} {Er : Core.St floor low → Core.St floor low → Prop}
    (l ls : Nat) (Bx : Token.TokenBatch → Token.TokenBatch → Prop) :
    SimR Er (Core.SRLx l ls Bx) (fun a b s t => LRel a b l ls ∧ Core.SRLx l ls Bx s t)
      (Ops.loadLocals (self := o₁)) (Ops.loadLocals (self := o₂))
  /-- Locals related at the line and the line start of the states are stored alike. -/
  storeLocals {floor : Option Nat} {low : Nat} {Er : Core.St floor low → Core.St floor low → Prop}
    (l ls : Nat) (Bx : Token.TokenBatch → Token.TokenBatch → Prop)
    (a : Ops.Locals H m R E (self := o₁))
    (b : Ops.Locals H m R E (self := o₂)) (hab : LRel a b l ls) :
    SimR Er (Core.SRLx l ls Bx) (fun _ _ => Core.SRLx l ls Bx)
      (Ops.storeLocals (self := o₁) a) (Ops.storeLocals (self := o₂) b)
  /-- A token of the fast path goes into the batches held alike. -/
  pushFast {floor : Option Nat} {low : Nat} {strict : Bool} (l ls : Nat) (b b' : Token.TokenBatch)
    (hb : Core.HR b b') (a : Ops.Locals H m R E (self := o₁)) (a' : Ops.Locals H m R E (self := o₂))
    (ha : LRel a a' l ls) (input : ByteSlice) (offset base : Nat) (ty : Token.TokenCategory)
    (contentStart contentStop start «end» : Nat) (emit : Bool) (hty hstart hend hframe hbatch
      hbatch') :
    Core.LSim strict (Core.SRE (floor := floor) (low := low) l ls) (Core.PushQ l ls (·.val) (·.val))
      (Ops.pushFast (self := o₁) input b a offset base ty contentStart contentStop start «end»
        emit hty hstart hend hframe hbatch)
      (Ops.pushFast (self := o₂) input b' a' offset base ty contentStart contentStop start «end»
        emit hty hstart hend hframe hbatch')
  /-- The full batches held are handed over alike, and given back emptied. -/
  flushHeld {floor : Option Nat} {low : Nat} {strict : Bool} (l ls : Nat)
    (batch batch' : Token.TokenBatch) (hb : Agree batch batch')
    (hbytes : batch.bytes = batch'.bytes)
    (origin : Nat) (hbatch hbatch') :
    Core.LSim strict (Core.SRE (floor := floor) (low := low) l ls)
      (fun a b s t => Agree a.val b.val ∧ a.val.bytes = b.val.bytes ∧ a.val.len = 0 ∧
        Core.SRE l ls s t)
      (Ops.flushHeld (self := o₁) batch origin hbatch)
      (Ops.flushHeld (self := o₂) batch' origin hbatch')
  /-- The batches in the states are handed over alike, and left without tokens; a stop of the
  consumer is thrown from states whose batches have none. -/
  flushBatch {floor : Option Nat} {low : Nat} {strict : Bool} (l ls : Nat) :
    SimR (Core.ErZ strict) (Core.SRLb (floor := floor) (low := low) strict l ls)
      (fun _ _ => Core.SREb strict l ls) (Ops.flushBatch (self := o₁)) (Ops.flushBatch (self := o₂))
  /-- A token whose content is in the content buffer is handed over alike, after the batches. -/
  sinkStoredAt {floor : Option Nat} {low : Nat} {strict : Bool} (l ls : Nat)
      (ty : Token.TokenCategory)
    (start «end» : Span.Location) (hend : start.offset < «end».offset) (hfloor) :
    SimR (Core.ErZ strict) (Core.SRLb (floor := floor) (low := low) strict l ls)
      (fun _ _ => Core.SREb strict l ls) (Ops.sinkStoredAt (self := o₁) ty start «end» hend hfloor)
      (Ops.sinkStoredAt (self := o₂) ty start «end» hend hfloor)
  /-- The end-of-file token is handed over alike, from states whose batches have no tokens and
  whose content buffer is empty. -/
  sinkEof {low : Nat} (l ls : Nat) (location : Span.Location) :
    SimR (Core.ErZ false)
      (fun s t => Core.SRE (floor := none) (low := low) l ls s t ∧ s.val.tokenContent.len = 0)
      (fun _ _ => Core.SRE l ls) (Ops.sinkEof (self := o₁) location)
      (Ops.sinkEof (self := o₂) location)
  /-- The batches the end of the input starts with have no tokens, from states that correspond
  whose batches have none. -/
  eofBatch (c c' : Core) (hc : Core.CoreRel c c') (hlen : c.batch.len = 0) :
    (Ops.eofBatch H m R E (self := o₁) c).val.len = 0 ∧
      (Ops.eofBatch H m R E (self := o₂) c').val.len = 0

end BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Ops
