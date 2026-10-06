import BSmtLib.Proofs.X2ContentsLexer.Top
import BSmtLib.Proofs.Adapter

/-!
# What the library's lexer and the lexer with the content buffer hand over

The constructors give related lexers, and the calls keep them related (`Top`), so the adapter,
which feeds the slices and then the end of the input, records the same from both, for slices
that end below `USize.size`.
-/

namespace BSmtLib.Proofs.X2ContentsLexer

open BSmtLib.Lexer.Internal (handler core ofParts)

theorem new_eq {H : Type} (consumer : H) (version : Version) :
    Lexer.X2Contents.Lexer.new consumer version =
      { handler := handler (BSmtLib.Lexer.new consumer version)
        core := coreMap 0 (core (BSmtLib.Lexer.new consumer version)) } :=
  rfl

theorem newRecovering_eq {H : Type} {m : Type → Type} [Recover H m] (consumer : H)
    (version : Version) :
    Lexer.X2Contents.Lexer.newRecovering (m := m) consumer version =
      { handler := handler (BSmtLib.Lexer.newRecovering (m := m) consumer version)
        core := coreMap 0 (core (BSmtLib.Lexer.newRecovering (m := m) consumer version)) } :=
  rfl

open Adapter in
theorem feed_eq :
    ∀ (slices : List Spec.Lexicon.Chars), (∀ s ∈ slices, s.length < USize.size) →
    ∀ (l : BSmtLib.Lexer Collector) (x : Lexer.X2Contents.Lexer Collector),
      x.handler = handler l → Rel (core l) x.core →
      feed X2Contents.ops x slices = feed Lexer.ops l slices := by
  intro slices
  induction slices with
  | nil =>
    intro _ l x hh hx
    have e := lexEof_sim (m := Id) (R := Empty) (E := Unit) l x hh hx
    simp only [feed, X2Contents.ops, Lexer.ops]
    generalize Lexer.X2Contents.Lexer.lexEof x = rx at e ⊢
    generalize BSmtLib.Lexer.lexEof l = rz at e ⊢
    have e' : resultZb afterEofZb rx = resultMap afterEofMap rz := e
    rcases rz with ⟨ez, az⟩ | ⟨fz, lz⟩ <;> rcases rx with ⟨ex, ax⟩ | ⟨fx, lx⟩ <;>
      simp only [resultMap, resultZb, reduceCtorEq, Except.ok.injEq, Prod.mk.injEq] at e'
    · rfl
    · obtain ⟨rfl, e2⟩ := e'
      cases fx with
      | «continue» => exact congrArg (fun y => some (y.handler).handed) e2
      | «break» f => exact f.value.elim
  | cons s rest ih =>
    intro hb l x hh hx
    have hs : (s.toByteArray.toByteSlice).stop < USize.size := by
      have := hb s List.mem_cons_self
      unfold ByteArray.toByteSlice
      simp only [Nat.le_refl, dite_true, Nat.zero_le]
      show s.toByteArray.size < USize.size
      rw [List.size_toByteArray]
      exact this
    have e := lexSlice_sim (m := Id) (R := Empty) (E := Unit) l x hh hx _ hs
    simp only [feed, X2Contents.ops, Lexer.ops]
    generalize Lexer.X2Contents.Lexer.lexSlice x _ = rx at e ⊢
    generalize BSmtLib.Lexer.lexSlice l _ = rz at e ⊢
    have e' : resultZb afterErrorZb rx = resultMap afterErrorMap rz := e
    rcases rz with ⟨ez, az⟩ | ⟨fz, lz⟩ <;> rcases rx with ⟨ex, ax⟩ | ⟨fx, lx⟩ <;>
      simp only [resultMap, resultZb, reduceCtorEq, Except.ok.injEq, Prod.mk.injEq] at e'
    · rfl
    · obtain ⟨rfl, e2⟩ := e'
      cases fx with
      | «continue» =>
        refine ih (fun s hs => hb s (List.mem_cons_of_mem _ hs)) lz lx
          (congrArg (fun y => y.handler) e2) ?_
        exact congrArg (fun y => y.core) e2
      | «break» f => exact f.value.elim

end BSmtLib.Proofs.X2ContentsLexer
