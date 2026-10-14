module

public import BSmtLib.Facts.Lexer.Adapters
public import BSmtLib.Facts.Proofs.Lexer.Simulation.Couple

@[expose] public section

/-!
# Lexers that do alike with every consumer of the spec

`lexing_alike`: two lexers that are constructed related, and whose steps on a slice and at the
end of the input give the same results and take the same tokens with lexers related again, do
the same with every consumer of the spec (`Adapters.lexing` of the two is equal).
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.Alike

open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Lexer.Adapters

theorem idBind {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

section
variable (ops₁ ops₂ : LexOps) {consumer : BSmtLibSpec.Lexer.Consumer}
  (Rel : ops₁.Lexer consumer → ops₂.Lexer consumer → Prop)

/-- Steps that give the same result, the same tokens taken and lexers related again. -/
def StepsAlike {α : Type} (step₁ : ops₁.Lexer consumer → AnswerM (α × ops₁.Lexer consumer))
    (step₂ : ops₂.Lexer consumer → AnswerM (α × ops₂.Lexer consumer)) : Prop :=
  ∀ a b (taken : List Handed), Rel a b →
    ((step₁ a).run taken).1.1 = ((step₂ b).run taken).1.1 ∧
      Rel ((step₁ a).run taken).1.2 ((step₂ b).run taken).1.2 ∧
      ((step₁ a).run taken).2 = ((step₂ b).run taken).2

/-- Two lexers whose steps on every slice and at the end of the input give the same results with
lexers related again, and whose related lexers hold the same result, stand alike after the
same input, take the same tokens and are related again. -/
theorem runInput_alike
    (hslice : ∀ slice, StepsAlike ops₁ ops₂ Rel (fun a => ops₁.lexSliceStep a slice)
      (fun b => ops₂.lexSliceStep b slice))
    (heof : StepsAlike ops₁ ops₂ Rel ops₁.lexEofStep ops₂.lexEofStep)
    (hheld : ∀ a b, Rel a b → ops₁.held a = ops₂.held b)
    (hwith : ∀ a b held, Rel a b → Rel (ops₁.withHeld a held) (ops₂.withHeld b held))
    (ended : Bool) (slices : List BSmtLibSpec.Regex.Chars) :
    StepsAlike ops₁ ops₂ Rel (fun a => ops₁.runInput a ended slices)
      (fun b => ops₂.runInput b ended slices) := by
  induction slices with
  | nil =>
    intro a b taken h
    cases ended with
    | false =>
      simp only [LexOps.runInput, Bool.false_eq_true, ite_false]
      refine ⟨?_, h, rfl⟩
      show ops₁.standing a = ops₂.standing b
      unfold LexOps.standing
      rw [hheld a b h]
    | true =>
      obtain ⟨e1, e2, e3⟩ := heof a b taken h
      simp only [LexOps.runInput, ite_true, StateT.run_bind]
      generalize (ops₁.lexEofStep a).run taken = ra at e1 e2 e3 ⊢
      generalize (ops₂.lexEofStep b).run taken = rb at e1 e2 e3 ⊢
      obtain ⟨⟨r, a'⟩, t⟩ := ra
      obtain ⟨⟨r', b'⟩, t'⟩ := rb
      simp only at e1 e2 e3
      subst e1 e3
      cases r with
      | error e => exact ⟨rfl, e2, rfl⟩
      | ok flow =>
        simp only [idBind]
        rw [hheld a' b' e2]
        cases eofResult (ops₂.held b') flow with
        | none => exact ⟨rfl, hwith _ _ _ e2, rfl⟩
        | some res => exact ⟨rfl, hwith _ _ _ e2, rfl⟩
  | cons slice slices ih =>
    intro a b taken h
    obtain ⟨e1, e2, e3⟩ := hslice slice.toByteArray.toByteSlice a b taken h
    simp only [LexOps.runInput, StateT.run_bind]
    generalize (ops₁.lexSliceStep a slice.toByteArray.toByteSlice).run taken = ra at e1 e2 e3 ⊢
    generalize (ops₂.lexSliceStep b slice.toByteArray.toByteSlice).run taken = rb at e1 e2 e3 ⊢
    obtain ⟨⟨r, a'⟩, t⟩ := ra
    obtain ⟨⟨r', b'⟩, t'⟩ := rb
    simp only at e1 e2 e3
    subst e1 e3
    cases r with
    | error e => exact ⟨rfl, e2, rfl⟩
    | ok held =>
      simp only [idBind]
      rw [hheld a' b' e2]
      exact ih _ _ t (hwith _ _ _ e2)

end
/-- What the adapter makes of a lexer, by the projections of the last input's run. -/
theorem lexing_def (ops : LexOps) (consumer : BSmtLibSpec.Lexer.Consumer)
    (version : BSmtLibSpec.Lexicon.Version) (earlier : List (List BSmtLibSpec.Regex.Chars))
    (slices : List BSmtLibSpec.Regex.Chars) (ended : Bool) :
    lexing ops consumer version earlier slices ended =
      let lexer := earlier.foldl (ops.next consumer (toVersion version))
        (ops.new consumer {} (toVersion version))
      let r := (ops.runInput lexer ended slices).run []
      { taken := r.2, outcome := r.1.1, version := fromVersion (ops.version r.1.2)
        discardedFrom := (ops.discardedFrom r.1.2).map toLocation } := rfl

/-- Lexers related after earlier inputs, the second fed each input as `cut` cuts it: they stay
related where lexers related give the same outcome on an input and its cut, and related lexers
when they do not fail, and the constructed lexers are related. -/
theorem foldl_next_rel (ops₁ ops₂ : LexOps) {consumer : BSmtLibSpec.Lexer.Consumer}
    (Rel : ops₁.Lexer consumer → ops₂.Lexer consumer → Prop) (version : Token.Version)
    (cut : List BSmtLibSpec.Regex.Chars → List BSmtLibSpec.Regex.Chars)
    (hnew : Rel (ops₁.new consumer {} version) (ops₂.new consumer {} version))
    (hrun : ∀ input a b, Rel a b →
      ((ops₁.runInput a true input).run []).1.1 =
          ((ops₂.runInput b true (cut input)).run []).1.1 ∧
        (((ops₁.runInput a true input).run []).1.1.isFailed = false →
          Rel ((ops₁.runInput a true input).run []).1.2
            ((ops₂.runInput b true (cut input)).run []).1.2)) :
    ∀ (inputs : List (List BSmtLibSpec.Regex.Chars)) a b, Rel a b →
      Rel (inputs.foldl (ops₁.next consumer version) a)
        ((inputs.map cut).foldl (ops₂.next consumer version) b) := by
  intro inputs
  induction inputs with
  | nil => intro a b h; exact h
  | cons input inputs ih =>
    intro a b h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    apply ih
    obtain ⟨e1, e2⟩ := hrun input a b h
    unfold LexOps.next
    generalize ((ops₁.runInput a true input).run []).1 = r1 at e1 e2
    generalize ((ops₂.runInput b true (cut input)).run []).1 = r2 at e1 e2
    obtain ⟨o, a'⟩ := r1
    obtain ⟨o', b'⟩ := r2
    simp only at e1 e2
    subst e1
    cases o with
    | failed f => exact hnew
    | _ => exact e2 rfl

/-- Two lexers that are constructed related, and whose steps give the same results with lexers
related again, do the same with every consumer of the spec: what the adapter makes of them is
equal. -/
theorem lexing_alike (ops₁ ops₂ : LexOps)
    (Rel : ∀ consumer : BSmtLibSpec.Lexer.Consumer, ops₁.Lexer consumer → ops₂.Lexer consumer →
    Prop)
    (hnew : ∀ consumer version,
      Rel consumer (ops₁.new consumer {} version) (ops₂.new consumer {} version))
    (hslice : ∀ consumer slice, StepsAlike ops₁ ops₂ (Rel consumer)
      (fun a => ops₁.lexSliceStep a slice) (fun b => ops₂.lexSliceStep b slice))
    (heof : ∀ consumer,
      StepsAlike ops₁ ops₂ (Rel consumer) ops₁.lexEofStep ops₂.lexEofStep)
    (hheld : ∀ consumer a b, Rel consumer a b → ops₁.held a = ops₂.held b)
    (hwith : ∀ consumer a b held, Rel consumer a b →
      Rel consumer (ops₁.withHeld a held) (ops₂.withHeld b held))
    (hversion : ∀ consumer a b, Rel consumer a b → ops₁.version a = ops₂.version b)
    (hdisc : ∀ consumer a b, Rel consumer a b → ops₁.discardedFrom a = ops₂.discardedFrom b) :
    lexing ops₁ = lexing ops₂ := by
  funext consumer version earlier slices ended
  have hrun := runInput_alike ops₁ ops₂ (Rel consumer) (hslice consumer) (heof consumer)
    (hheld consumer) (hwith consumer)
  rw [lexing_def, lexing_def]
  have hL := foldl_next_rel ops₁ ops₂ (Rel consumer) (toVersion version) id
    (hnew consumer (toVersion version))
    (fun input a b h => ⟨(hrun true input a b [] h).1, fun _ => (hrun true input a b [] h).2.1⟩)
    earlier _ _ (hnew consumer (toVersion version))
  rw [List.map_id] at hL
  obtain ⟨e1, e2, e3⟩ := hrun ended slices _ _ [] hL
  simp only
  rw [e1, e3, hversion consumer _ _ e2, hdisc consumer _ _ e2]


/-- Coupled computations in the consumer's monad, run from the same tokens taken, give related
values and the same tokens taken. -/
theorem mcouple_answerM {α β : Type} {Rel : α → β → Prop} {a : AnswerM α} {b : AnswerM β}
    (h : Simulation.Couple.MCouple Rel a b) (taken : List BSmtLibSpec.Lexer.Handed) :
    Rel (a.run taken).1 (b.run taken).1 ∧ (a.run taken).2 = (b.run taken).2 := by
  obtain ⟨y, h1, h2⟩ := h
  subst h1 h2
  exact ⟨(y.run taken).1.property, rfl⟩

end BSmtLib.Facts.Proofs.Lexer.Consumers.Alike
