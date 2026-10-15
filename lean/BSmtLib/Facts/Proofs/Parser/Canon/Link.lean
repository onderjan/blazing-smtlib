module

public import BSmtLib.Facts.Proofs.Parser.Canon.Canonical
public import BSmtLib.Facts.Proofs.Reader.Param.Calls
import all BSmtLib.Parser.Adapter

@[expose] public section

/-!
# The parse adapter and the canonical adapter

The library's lexer with the parse adapter and with the canonical adapter, from states whose
canonicalisations agree, hand over alike: the same answers and cursors, and states whose
canonicalisations agree again (`consumers`). So the steps of its calls relate as
`Reader.Param.Calls` says.
-/

namespace BSmtLib.Facts.Proofs.Parser.Canon.Link

open BSmtLib.Parser BSmtLib.Parser.Adapter
open BSmtLibSpec.Parser.Properties (Event)
open BSmtLib.Facts.Reader.Adapters (RecAdapter)
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.HandOver
open Basic Loop Adapter Canonical

/-- The relator of the parse adapter and the canonical adapter: from states whose
canonicalisations agree, related values and states whose canonicalisations agree. -/
def relator : Relator RecAdapter Id CanonAdapter Id where
  rel Q x y := ∀ a b, canonA a = b.adapter →
    Q (x.run a).1 (y.run b).1 ∧ canonA (x.run a).2 = (y.run b).2.adapter
  pure := by
    intro _ _ _ _ _ h s t hst
    exact ⟨h, hst⟩
  bind := by
    intro _ _ _ _ _ _ _ _ _ _ hx hk s t hst
    obtain ⟨hq, hs⟩ := hx s t hst
    exact hk _ _ hq _ _ hs
  mono := by
    intro _ _ _ _ _ _ hQ h s t hst
    exact ⟨hQ _ _ (h s t hst).1, (h s t hst).2⟩

/-- The link of the parse adapter and the canonical adapter. -/
def link : Link RecAdapter Id Unit (ParseError Unit) CanonAdapter Id Unit
    (ParseError Unit) where
  rc := relator
  rr := (· = ·)
  re := (· = ·)

theorem eRel_refl (x : Except (ParseError Unit) (ControlFlow Unit)) :
    ERel link.re (FlowRel link.rr) x x := by
  rcases x with e | f
  · exact (rfl : e = e)
  · cases f <;> first | trivial | exact (rfl : () = ())

/-- The two adapters answer each call alike. -/
theorem calls : Calls link where
  concrete := rfl
  consume c h a b hab := by
    have ha : canonA a = canonA b.adapter := by rw [← hab, canonA_canonA]
    obtain ⟨e1, e2, e3⟩ := consume_agree h h cursorRel_eq rfl ha
    refine ⟨?_, ?_⟩
    · show ERel _ _ _ ((Token.ConsumeFrom.consume (m := Id) c h :
          StateT RecAdapter Id _).run b.adapter).1.1 ∧ _
      rw [← e1]
      exact ⟨eRel_refl _, Subtype.ext e2⟩
    · show canonA _ = canonA _
      exact e3

theorem consumers : Consumers link := Consumers.ofCalls calls

end BSmtLib.Facts.Proofs.Parser.Canon.Link
