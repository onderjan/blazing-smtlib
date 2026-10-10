import BSmtLib.Proofs.X1BatchInCoreLexer.Top
import BSmtLib.Proofs.X1BatchInCoreLexer.Chunks

/-!
# What the library's lexer and `X1BatchInCore` hand over

The constructors give related lexers (`LexerRel`), and every call keeps them related, also a
call that fails (`Top`). So the two lexers, fed the same slices one call after another with the
adapter's consumer, give the same result and related lexers, where every slice ends below
`USize.size` (`runSlices_rel`); and as the library's lexer gives for a list of slices what it
gives for their cut (`Chunks.run_cutAll`), the library's lexer fed any slices gives what the
lexer with the batch kept in its state gives fed their cut (`runSlices_cutAll`). The adapter,
which feeds the slices and then, if the input has ended, the end of the input, records then the
same from both, and they fail alike (`feedInput_eq_cutAll`).
-/

namespace BSmtLib.Proofs.X1BatchInCoreLexer

open BSmtLib.Proofs.Simulation (MCouple)
open BSmtLib.Proofs.Adapter (Collector feedInput feedEnd)
open BSmtLib.Lexer.Internal (handler core ofParts)

theorem new_eq {H : Type} (consumer : H) (version : Version) :
    Lexer.WRustPort.Lexer.new consumer version =
      { handler := handler (BSmtLib.Lexer.new consumer version)
        core := coreMap 0 (core (BSmtLib.Lexer.new consumer version)) } :=
  rfl

theorem newRecovering_eq {H : Type} {m : Type → Type} [Recover H m] (consumer : H)
    (version : Version) :
    Lexer.WRustPort.Lexer.newRecovering (m := m) consumer version =
      { handler := handler (BSmtLib.Lexer.newRecovering (m := m) consumer version)
        core := coreMap 0 (core (BSmtLib.Lexer.newRecovering (m := m) consumer version)) } :=
  rfl

theorem lexerRel_new {H : Type} (consumer : H) (version : Version) :
    LexerRel (BSmtLib.Lexer.new consumer version) (Lexer.WRustPort.Lexer.new consumer version) :=
  ⟨rfl, rel_coreMap 0 _⟩

theorem lexerRel_newRecovering {H : Type} {m : Type → Type} [Recover H m] (consumer : H)
    (version : Version) :
    LexerRel (BSmtLib.Lexer.newRecovering (m := m) consumer version)
      (Lexer.WRustPort.Lexer.newRecovering (m := m) consumer version) :=
  ⟨rfl, rel_coreMap 0 _⟩

/-- Coupled computations in `Id` are related values. -/
theorem mcouple_id {α β : Type} {Rel : α → β → Prop} {a : Id α} {b : Id β}
    (h : MCouple Rel a b) : Rel a b := by
  obtain ⟨y, h1, h2⟩ := h
  rw [h1, h2]
  exact y.property

/-- A call of the two lexers on a slice that ends below `USize.size`, with the adapter's
consumer. -/
theorem step_rel (l : BSmtLib.Lexer Collector) (x : Lexer.WRustPort.Lexer Collector)
    (hlx : LexerRel l x) (slice : ByteSlice) (hs : slice.stop < USize.size) :
    (lexerStep l slice).1 = (x1Step x slice).1 ∧
      LexerRel (lexerStep l slice).2 (x1Step x slice).2 :=
  mcouple_id (a := lexerStep l slice) (b := x1Step x slice)
    (run_lexSliceStep (m := Id) (R := Empty) (E := Unit) (LexRecovery.abandon .failFast)
      (LexRecovery.recover .failFast) l x hlx slice hs)

/-- The slice of the bytes of a list of characters ends below `USize.size` if the list is that
short. -/
theorem stop_toByteSlice_lt {s : Spec.Lexicon.Chars} (h : s.length < USize.size) :
    (s.toByteArray.toByteSlice).stop < USize.size := by
  unfold ByteArray.toByteSlice
  simp only [Nat.le_refl, dite_true, Nat.zero_le]
  show s.toByteArray.size < USize.size
  rw [List.size_toByteArray]
  exact h

/-- The two lexers, fed the same slices one call after another from related lexers, give the
same result and related lexers, where every slice ends below `USize.size`. -/
theorem runSlices_rel : ∀ (slices : List Spec.Lexicon.Chars),
    (∀ s ∈ slices, s.length < USize.size) →
    ∀ (l : BSmtLib.Lexer Collector) (x : Lexer.WRustPort.Lexer Collector), LexerRel l x →
      (runSlices lexerStep l slices).1 = (runSlices x1Step x slices).1 ∧
        LexerRel (runSlices lexerStep l slices).2 (runSlices x1Step x slices).2
  | [], _, _, _, hlx => ⟨rfl, hlx⟩
  | s :: rest, hb, l, x, hlx => by
    obtain ⟨e1, e2⟩ := step_rel l x hlx _ (stop_toByteSlice_lt (hb s List.mem_cons_self))
    simp only [runSlices]
    generalize lexerStep l s.toByteArray.toByteSlice = cl at e1 e2 ⊢
    generalize x1Step x s.toByteArray.toByteSlice = cx at e1 e2 ⊢
    obtain ⟨r, l'⟩ := cl
    obtain ⟨r', x'⟩ := cx
    dsimp only at e1 e2
    subst e1
    rcases r with e | (_ | f)
    · exact ⟨rfl, e2⟩
    · exact runSlices_rel rest (fun s h => hb s (List.mem_cons_of_mem _ h)) l' x' e2
    · exact ⟨rfl, e2⟩

/-- The library's lexer, fed the slices one call after another, gives the result that the lexer
with the batch kept in its state gives fed their cut, and a lexer related to it, from related
lexers that neither discard nor recover. -/
theorem runSlices_cutAll (slices : List Spec.Lexicon.Chars) (l : BSmtLib.Lexer Collector)
    (x : Lexer.WRustPort.Lexer Collector) (hlx : LexerRel l x) (hl : Chunks.Inv (core l)) :
    (runSlices lexerStep l slices).1 = (runSlices x1Step x (Chunks.cutAll slices)).1 ∧
      LexerRel (runSlices lexerStep l slices).2 (runSlices x1Step x (Chunks.cutAll slices)).2 := by
  rw [Chunks.run_cutAll slices l hl]
  exact runSlices_rel _ (fun _ h => Chunks.mem_cutAll h) l x hlx

/-- The end of the input, fed by the adapter from related lexers. -/
theorem feedEnd_eq (l : BSmtLib.Lexer Collector) (x : Lexer.WRustPort.Lexer Collector)
    (hlx : LexerRel l x) :
    feedEnd Adapter.Lexer.ops l = feedEnd Adapter.X1BatchInCore.ops x := by
  have hr := mcouple_id (run_lexEofStep (m := Id) (R := Empty) (E := Unit)
    (LexRecovery.abandon .failFast) (LexRecovery.recover .failFast) l x hlx)
  have e1 : Adapter.Lexer.ops.lexEofStep l = BSmtLib.Lexer.Internal.run l
      (BSmtLib.Lexer.Internal.lexEofStep (LexRecovery.abandon .failFast)
        (LexRecovery.recover .failFast)) := rfl
  have e2 : Adapter.X1BatchInCore.ops.lexEofStep x =
      x.run (Lexer.WRustPort.lexEofStep (ops := Lexer.X1BatchInCore.ops)
        (LexRecovery.abandon .failFast) (LexRecovery.recover .failFast)) := rfl
  simp only [feedEnd, e1, e2]
  revert hr
  generalize BSmtLib.Lexer.Internal.run l (BSmtLib.Lexer.Internal.lexEofStep (R := Empty)
    (E := Unit) (LexRecovery.abandon .failFast) (LexRecovery.recover .failFast)) = rl
  generalize x.run (Lexer.WRustPort.lexEofStep (ops := Lexer.X1BatchInCore.ops) (R := Empty)
    (E := Unit) (LexRecovery.abandon .failFast) (LexRecovery.recover .failFast)) = rx
  intro hr
  obtain ⟨res, l'⟩ := rl
  obtain ⟨res', x'⟩ := rx
  obtain ⟨e, hl⟩ := hr
  simp only at e hl
  subst e
  rcases res with err | flow
  · show (handler l', true) = (x'.handler, true)
    rw [hl.1]
  · cases flow with
    | «continue» =>
      show (handler l', false) = (x'.handler, false)
      rw [hl.1]
    | «break» f => exact f.value.elim

/-- What the adapter records after the calls, from the same result and related lexers. -/
theorem afterRun_eq (ended : Bool) (cl : Called (BSmtLib.Lexer Collector))
    (cx : Called (Lexer.WRustPort.Lexer Collector)) (e : cl.1 = cx.1) (hr : LexerRel cl.2 cx.2) :
    afterRun Adapter.Lexer.ops ended cl = afterRun Adapter.X1BatchInCore.ops ended cx := by
  obtain ⟨r, l⟩ := cl
  obtain ⟨r', x⟩ := cx
  dsimp only at e hr
  subst e
  rcases r with _ | (_ | f)
  · show (handler l, true) = (x.handler, true)
    rw [hr.1]
  · cases ended with
    | false =>
      show (handler l, false) = (x.handler, false)
      rw [hr.1]
    | true => exact feedEnd_eq l x hr
  · exact f.value.elim

/-- The library's lexer, fed by the adapter, records for the slices what the lexer with the
batch kept in its state records for their cut, and fails alike. -/
theorem feedInput_eq_cutAll (version : Spec.Lexicon.Version) (ended : Bool)
    (slices : List Spec.Lexicon.Chars) :
    feedInput Adapter.Lexer.ops
        (Adapter.Lexer.ops.new { handed := [] } (Adapter.toVersion version)) ended slices =
      feedInput Adapter.X1BatchInCore.ops
        (Adapter.X1BatchInCore.ops.new { handed := [] } (Adapter.toVersion version)) ended
        (Chunks.cutAll slices) := by
  rw [feedInput_eq_afterRun Adapter.Lexer.ops ended lexerStep (fun _ _ => rfl),
    feedInput_eq_afterRun Adapter.X1BatchInCore.ops ended x1Step (fun _ _ => rfl)]
  obtain ⟨e, hr⟩ := runSlices_cutAll slices _ _ (lexerRel_new _ _) ⟨rfl, rfl⟩
  exact afterRun_eq ended _ _ e hr

end BSmtLib.Proofs.X1BatchInCoreLexer
