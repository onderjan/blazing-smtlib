module

public import BSmtLib.Facts.Proofs.Reader.Param.UnaryCalls

@[expose] public section

/-!
# Any consumer with a record of what went wrong

`Watch C` answers exactly as the consumer `C` does, its errors wrapped in `some`, and keeps in its
state, beside the state of `C`, the record that `Flagged` keeps for the adapter's consumer:
whether it has answered an error or been handed a cursor in another version than the one of the
last cursor it gave back (`errored`), that version (`version`), whether it has been called after
something went wrong or handed such a cursor (`spoiled`), and whether the call at which it went
wrong was handed whitespace or a comment (`layout`, which stays `false`, as `C` answers no error
`none`). The record is read by nothing but the proofs.

`C` runs in `Id`; `Watch C` runs in `StateM Unit`, a state monad as the unary walk asks for. It
keeps its record as the walk's consumers do (`Unary.Watched`), so a call of the library's lexer
whose watched consumer answered an error fails (`UnaryCalls.lexSliceStep_flag`,
`UnaryCalls.lexEofStep_flag`).

`Watch C` answers as `C` does, its errors wrapped in `some`, and its record holds the state of
`C`; so the library's lexer with `Watch C` and with `C` are related call by call (`innerLink`, by
`Param.lexSliceStep_sim` and `Param.lexEofStep_sim`): the same results, the errors wrapped, the
same lexer state, and the state of `C` in the record.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Watch

open BSmtLib.Lexer
open BSmtLib.Facts.Proofs.Reader.Param.Basic (Relator Link ERel FlowRel)
open BSmtLib.Facts.Proofs.Reader.Param.HandOver (Consumers)
open BSmtLib.Facts.Proofs.Reader.Param.Flagged (isError isLayoutAnswer)
open BSmtLib.Facts.Proofs.Reader.Param.Unary (Watched)
/-- The monad of `Watch`: a state with nothing in it. -/
abbrev WM := StateM Unit

/-- A consumer with a record of what went wrong. -/
structure _root_.BSmtLib.Facts.Proofs.Reader.Param.Watch (C : Type) : Type where
  /-- The state of the consumer. -/
  inner : C
  /-- Whether the consumer has answered an error, or been handed a cursor in another version than
  the one of the last cursor it gave back. -/
  errored : Bool
  /-- The version of the last cursor it gave back, or the one it started with. -/
  version : Token.Version
  /-- Whether the consumer has been called after something went wrong, or handed a cursor in
  another version than the one of the last cursor it gave back. -/
  spoiled : Bool
  /-- Whether the call at which the consumer went wrong was handed whitespace or a comment and
  answered with the error `none`, which `C` never does. -/
  layout : Bool

section

variable {C R E : Type} [Token.Consume C R E] [∀ b, Token.ConsumeFrom C (Token.BatchCursor b) Id]

instance : Token.Consume (Watch C) R (Option E) where
  isConcrete := Token.Consume.isConcrete (H := C)

/-- What the consumer answers on the cursor from its state: the answer, its error wrapped in
`some`, the cursor it gives back, and its state after. -/
def answer (inner : C) {b : Token.BatchTag} (cursor : Token.BatchCursor b) (h : cursor.HasNext) :
    (Except (Option E) (ControlFlow R) × {c : Token.BatchCursor b // c.Consumed cursor}) × C :=
  let r := ((Token.ConsumeFrom.consume cursor h : StateT C Id _).run inner : Id _)
  ((r.1.1.mapError some, r.1.2), r.2)

/-- The record after a call on the cursor that answered `answer`, gave back `next` and left the
consumer in the state `inner`. -/
def after (w : Watch C) {b : Token.BatchTag} (cursor : Token.BatchCursor b) {α : Type}
    (answer : Except (Option E) α) (next : Token.BatchCursor b) (inner : C) : Watch C where
  inner
  errored := w.errored || cursor.version != w.version || isError answer
  version := next.version
  spoiled := w.spoiled || w.errored || cursor.version != w.version
  layout := if w.errored then w.layout else isLayoutAnswer answer

/-- Takes the tokens as `C` does, and records what went wrong. -/
def consume {b : Token.BatchTag} (cursor : Token.BatchCursor b) (h : cursor.HasNext) :
    StateT (Watch C) WM
      (Except (Option E) (ControlFlow R) × {c : Token.BatchCursor b // c.Consumed cursor}) := do
  let w ← get
  let r := Watch.answer w.inner cursor h
  set (w.after cursor r.1.1 r.1.2.val r.2)
  return r.1

instance {b : Token.BatchTag} : Token.ConsumeFrom (Watch C) (Token.BatchCursor b) WM where
  consume cursor h := Watch.consume cursor h

/-- The record of a consumer before anything went wrong, from the version. -/
def new (inner : C) (version : Token.Version) : Watch C :=
  { inner, errored := false, version, spoiled := false, layout := false }

/-- `Watch C` keeps its record in its fields. -/
instance : Watched (Watch C) Unit R E where
  errored := Watch.errored
  version := Watch.version
  spoiled := Watch.spoiled
  layout := Watch.layout
  call cursor h w u he hv := by
    have he' : w.errored = false := he
    have hv' : cursor.version = w.version := hv
    refine ⟨?_, rfl, ?_, ?_⟩
    · show (w.errored || cursor.version != w.version ||
          isError (Watch.answer w.inner cursor h).1.1) = _
      rw [he', hv', UnarySteps.bne_self_version]
      rfl
    · show (w.spoiled || w.errored || cursor.version != w.version) = w.spoiled
      rw [he', hv', UnarySteps.bne_self_version]
      simp
    · show (if w.errored then w.layout else isLayoutAnswer (Watch.answer w.inner cursor h).1.1) = _
      rw [he']
      rfl

end

section

variable (C : Type)

/-- The relator of `Watch C` and `C`: from the state of `C` in the record, related values, and the
state of `C` after in the record. -/
def innerRelator : Relator (Watch C) WM C Id where
  rel Q x y := ∀ w u, Q ((x.run w).run u).1.1 (y.run w.inner).1 ∧
    ((x.run w).run u).1.2.inner = (y.run w.inner).2
  pure h _ _ := ⟨h, rfl⟩
  bind {_ _ _ _ _ _ x y f g} hx hk w u := by
    obtain ⟨h₁, h₂⟩ := hx w u
    have e₁ : ((x >>= f).run w).run u =
        ((f ((x.run w).run u).1.1).run ((x.run w).run u).1.2).run ((x.run w).run u).2 := rfl
    have e₂ : (y >>= g).run w.inner = (g (y.run w.inner).1).run (y.run w.inner).2 := rfl
    rw [e₁, e₂, ← h₂]
    exact hk _ _ h₁ _ _
  mono hQ h w u := ⟨hQ _ _ (h w u).1, (h w u).2⟩

variable {R E : Type} [Token.Consume C R E]

/-- The link of `Watch C` and `C`: equal results, and the errors of `Watch C` those of `C`
wrapped. -/
def innerLink : Link (Watch C) WM R (Option E) C Id R E where
  rc := innerRelator C
  rr := (· = ·)
  re := fun e₁ e₂ => e₁ = some e₂

end

section

variable {C R E : Type} [Token.Consume C R E] [∀ b, Token.ConsumeFrom C (Token.BatchCursor b) Id]

/-- A call of `Watch C`, run: the answer of `C`, and the record after it. -/
theorem consume_run {b : Token.BatchTag} (cursor : Token.BatchCursor b) (h : cursor.HasNext)
    (w : Watch C)
    (u : Unit) :
    ((Token.ConsumeFrom.consume (m := WM) cursor h : StateT (Watch C) WM _).run w).run u =
      (((Watch.answer w.inner cursor h).1,
        w.after cursor (Watch.answer w.inner cursor h).1.1
          (Watch.answer w.inner cursor h).1.2.val (Watch.answer w.inner cursor h).2), u) :=
  rfl

/-- An answer and the same answer with its error wrapped are related as `innerLink` relates
them. -/
theorem eRel_mapError {α : Type} (r : Except E (ControlFlow α)) :
    ERel (fun e₁ e₂ => e₁ = some e₂) (FlowRel (· = ·)) (r.mapError some) r := by
  rcases r with e | (_ | v)
  · rfl
  · trivial
  · rfl

theorem inner_consumers : Consumers (innerLink C (R := R) (E := E)) where
  concrete := rfl
  consume cursor h w u := by
    rw [consume_run]
    exact ⟨⟨eRel_mapError _, rfl⟩, rfl⟩

end

end BSmtLib.Facts.Proofs.Reader.Param.Watch
