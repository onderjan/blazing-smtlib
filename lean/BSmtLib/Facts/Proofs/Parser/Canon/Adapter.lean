module

public import BSmtLib.Facts.Proofs.Parser.Canon.Loop
public import BSmtLib.Facts.Parser
import all BSmtLib.Parser
import all BSmtLib.Parser.Adapter
import all BSmtLib.Token
import all BSmtLib.Token.Cursor

@[expose] public section

/-!
# The parse adapter on cursors that agree

The parse adapter over the recording handler and the script parser, called on two cursors that
agree from states that are the same up to the views in the parser (`canonA`), gives the same
answer, cursors that agree, and states that are the same up to the views again
(`consume_agree`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Canon.Adapter

open BSmtLib.Parser BSmtLib.Parser.Adapter BSmtLib.Parser.Script
open BSmtLibSpec.Parser.Properties (Event)
open BSmtLib.Facts.Reader.Adapters (RecAdapter)
open BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
open BSmtLib.Facts.Proofs.Reader.Param.Adapter (id_bind_eq)
open Basic States Loop

/-- The adapter with the views in its parser replaced by their contents. -/
def canonA (a : RecAdapter) : RecAdapter :=
  ParseAdapter.Internal.mk a.handler (canon a.parser) (ParseAdapter.Internal.versionSet a)
    (ParseAdapter.Internal.parseState a)

variable {g g' : Token.BatchTag}

/-- The handler's log when the adapter's parse of a cursor in the version begins. -/
def startLog (a : RecAdapter) (version : Token.Version) : List Event :=
  ((if ParseAdapter.Internal.versionSet a then pure ()
    else Traits.Handler.setVersion (H := List Event) version :
    StateT (List Event) Id Unit).run a.handler).2

/-- A call of the adapter: its parse from its parser and its log, the version told first unless
it was. -/
theorem consume_run (c : Token.BatchCursor g) (h : c.HasNext) (a : RecAdapter) :
    let r := (Parse.parse a.parser (ParseAdapter.Internal.parseState a) c).run
      (startLog a c.version)
    (Token.ConsumeFrom.consume (m := Id) c h : StateT RecAdapter Id _).run a =
      ((r.1.1, ⟨r.1.2.2.2.val, r.1.2.2.2.property h⟩),
        ParseAdapter.Internal.mk r.2 r.1.2.1 (ParseAdapter.Internal.versionSetAfter r.1.1)
          r.1.2.2.1) := by
  intro r
  rfl

theorem consume_agree {c₁ : Token.BatchCursor g} {c₂ : Token.BatchCursor g'}
    (h₁ : c₁.HasNext) (h₂ : c₂.HasNext) {Rel : Token.BatchCursor g → Token.BatchCursor g' → Prop}
    (hR : CursorRel Rel) (hc : Rel c₁ c₂) {a₁ a₂ : RecAdapter}
    (ha : canonA a₁ = canonA a₂) :
    ((Token.ConsumeFrom.consume (m := Id) c₁ h₁ : StateT RecAdapter Id _).run a₁).1.1 =
        ((Token.ConsumeFrom.consume (m := Id) c₂ h₂ : StateT RecAdapter Id _).run a₂).1.1 ∧
      Rel
        ((Token.ConsumeFrom.consume (m := Id) c₁ h₁ : StateT RecAdapter Id _).run a₁).1.2.val
        ((Token.ConsumeFrom.consume (m := Id) c₂ h₂ : StateT RecAdapter Id _).run a₂).1.2.val ∧
      canonA ((Token.ConsumeFrom.consume (m := Id) c₁ h₁ : StateT RecAdapter Id _).run a₁).2 =
        canonA ((Token.ConsumeFrom.consume (m := Id) c₂ h₂ : StateT RecAdapter Id _).run a₂).2 := by
  obtain ⟨hh, hp, hv, hs⟩ := ParseAdapter.Internal.mk_inj.mp ha
  have hl : startLog a₁ c₁.version = startLog a₂ c₂.version := by
    unfold startLog
    rw [hh, hv, hR.version hc]
  rw [consume_run, consume_run]
  dsimp only
  rw [BSmtLib.Facts.Parser.fused_parses_as_port, BSmtLib.Facts.Parser.fused_parses_as_port,
    hl, hs]
  obtain ⟨r1, r2, r3, r4, r5⟩ := parseByToken_agree hp (ParseAdapter.Internal.parseState a₂) hR
    hc (startLog a₂ c₂.version)
  refine ⟨r1, r4, ?_⟩
  simp only [canonA, ParseAdapter.Internal.handler_mk, ParseAdapter.Internal.parser_mk,
    ParseAdapter.Internal.versionSet_mk, ParseAdapter.Internal.parseState_mk]
  rw [r1, r2, r3, r5]

end BSmtLib.Facts.Proofs.Parser.Canon.Adapter
