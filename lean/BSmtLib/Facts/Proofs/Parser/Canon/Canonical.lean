module

public import BSmtLib.Facts.Proofs.Parser.Canon.Adapter
public import BSmtLib.Facts.Proofs.Parser.Canon.Idem
import all BSmtLib.Parser.Adapter

@[expose] public section

/-!
# The canonical adapter

`CanonAdapter` is the parse adapter that keeps its state canonical: each call runs the parse
adapter, then canonicalises the state it leaves. Its calls on cursors that agree leave the same
state, so it reads the cursors only below the length of their batches
(`canonAdapter_consumesAlike`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Canon.Canonical

open BSmtLib.Parser BSmtLib.Parser.Adapter
open BSmtLibSpec.Parser.Properties (Event)
open BSmtLib.Facts.Reader.Adapters (RecAdapter)
open BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
open BSmtLib.Facts.Proofs.Reader.Param.Adapter (id_bind_eq)
open Basic States Loop Adapter Idem

/-- The parse adapter over the recording handler, kept canonical. -/
structure CanonAdapter where
  adapter : RecAdapter

instance : Token.Consume CanonAdapter Unit (ParseErrorCause Unit) where
  isConcrete := false

/-- A call of the canonical adapter: the parse adapter's call, its state then canonicalised. -/
def canonConsume {b : Token.BatchTag} (c : Token.BatchCursor b) (h : c.HasNext) :
    StateT CanonAdapter Id
      (Except (ParseErrorCause Unit) (ControlFlow Unit) ×
        {c' // Token.BatchCursor.Consumed c' c}) :=
  fun s =>
    let q := (Token.ConsumeFrom.consume (m := Id) c h : StateT RecAdapter Id _).run s.adapter
    (q.1, ⟨canonA q.2⟩)

instance {b : Token.BatchTag} : Token.ConsumeFrom CanonAdapter (Token.BatchCursor b) Id where
  consume c h := canonConsume c h

theorem canonA_canonA (a : RecAdapter) : canonA (canonA a) = canonA a := by
  show ParseAdapter.mk _ (canon (canon a.parser)) _ _ = ParseAdapter.mk _ (canon a.parser) _ _
  rw [CanonIdem.idem]
  rfl

/-- The canonical adapter reads the cursors only below the length of their batches. -/
theorem canonAdapter_consumesAlike : ConsumesAlike CanonAdapter Id Unit (ParseErrorCause Unit) := by
  intro g g' c d hc hd hcd s
  obtain ⟨e1, e2, e3⟩ := consume_agree hc hd cursorRel_agree hcd (a₁ := s.adapter)
    (a₂ := s.adapter) rfl
  refine ⟨⟨(((Token.ConsumeFrom.consume (m := Id) c hc : StateT RecAdapter Id _).run
      s.adapter).1, ((Token.ConsumeFrom.consume (m := Id) d hd : StateT RecAdapter Id _).run
      s.adapter).1, ⟨canonA ((Token.ConsumeFrom.consume (m := Id) c hc :
        StateT RecAdapter Id _).run s.adapter).2⟩), e1, e2⟩, rfl, ?_⟩
  show (_, (⟨canonA _⟩ : CanonAdapter)) = (_, ⟨canonA _⟩)
  rw [e3]

end BSmtLib.Facts.Proofs.Parser.Canon.Canonical
