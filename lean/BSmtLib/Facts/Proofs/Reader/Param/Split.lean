module

public import BSmtLib.Facts.Proofs.Reader.Param.HandOver
public import BSmtLib.Facts.Proofs.Reader.Param.Stop
public import BSmtLib.Facts.Reader.Adapters
public import BSmtLib.Facts.Proofs.Parser.Fused.Step
import all BSmtLib.Lexer
import all BSmtLib.Parser
import all BSmtLib.Parser.Adapter
import all BSmtLib.Token
import all BSmtLib.Token.SyntaxToken

@[expose] public section

/-!
# The lexer's handovers to the parse adapter and to the one that stops

The parse adapter goes on with its cursor after its parser had the cursor switch the version or
discard the rest of the input; the adapter of the reader proofs (`Param.Stop`) stops there, and
the lexer hands it the tokens left over anew. The lexer's handover of a batch is the same with
the two (`handOver_eq`), for every parser whose `parse` on a batch cursor is its loop over single
tokens, as the script parser's is.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Split

open BSmtLib.Lexer
open BSmtLib.Traits
open BSmtLib.Parser (Parse ParseErrorCause ParseState)
open BSmtLib.Parser.Adapter (ParseAdapter)

/-! ## The loop over single tokens against the one that stops -/

section Loops

open BSmtLib.Parser.Internal (After ParseByToken takeOne rest parseByToken)

variable {H P R E : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [ParseByToken P H m E R]
variable {Z : Type} [Token.Produce Z]

/-- What the parser did with a token, read as the loop that goes on with its cursor reads it: a
parser that stopped going on goes on. -/
def fixAfter : After P R E → After P R E
  | .stop (.ok .continue) parser => .goOn parser
  | after => after

/-- The loop's token is that of the loop that stops, a stop going on read as going on. -/
theorem takeOne_eq (parser : P) (cursor : Z) (token : Token.Produce.Token Z) (next : Z)
    (consumed : Token.Produce.Consumed next cursor) :
    takeOne (m := m) parser cursor token next consumed =
      (fun x => (fixAfter x.1, x.2)) <$> Stop.takeOne parser cursor token next consumed := by
  unfold takeOne Stop.takeOne
  simp only [map_bind]
  congr 1
  funext r
  rcases r with e | flow
  · simp [fixAfter]
  · cases flow with
    | more p => simp [fixAfter]
    | done res => simp [fixAfter]
    | switchVersion declared resume =>
      dsimp only
      split
      · split
        · simp [fixAfter]
        · rename_i a e1 s e2
          exact absurd (e1.symm.trans e2) (by simp)
      · split
        · rename_i s e1 a e2
          exact absurd (e1.symm.trans e2) (by simp)
        · rename_i s e1 s' e2
          have := Except.ok.inj (e1.symm.trans e2)
          subst this
          simp only [map_bind]
          congr 1
          funext r'
          rcases r' with e | st
          · simp [fixAfter]
          · cases st <;> simp [fixAfter, Parser.Internal.resumed, Stop.resumed]
    | discardRest resume =>
      dsimp only
      simp only [map_bind]
      congr 1
      funext r'
      rcases r' with e | st
      · simp [fixAfter]
      · cases st <;> simp [fixAfter, Parser.Internal.resumed, Stop.resumed]

/-- How the loop goes on after the loop that stops has stopped: on with the cursor if the parser
went on, else with the answer. -/
def resume (origin : Z) :
    Except (ParseErrorCause E) (ControlFlow R) × P × { z : Z // Token.Produce.Consumed z origin } →
      StateT H m (Except (ParseErrorCause E) (ControlFlow R) × P ×
        { z : Z // Token.Produce.Consumed z origin })
  | (.ok .continue, parser, ⟨cursor, consumed⟩) => rest origin parser cursor consumed
  | x => pure x

/-- The loop over single tokens is the loop that stops, then itself from where that stopped. -/
theorem rest_eq (origin : Z) :
    ∀ (parser : P) (cursor : Z) (consumed : Token.Produce.Consumed cursor origin),
      rest (m := m) origin parser cursor consumed =
        Stop.rest origin parser cursor consumed >>= resume origin := by
  intro parser cursor consumed
  induction cursor using (Token.Produce.consumed_wf (Z := Z)).induction generalizing parser with
  | _ cursor ih =>
  rw [rest, Stop.rest]
  rcases hn : Token.Produce.next? cursor with _ | ⟨token, ⟨next, step⟩⟩
  · simp only [pure_bind, resume]
    rw [rest, hn]
  · dsimp only
    rw [takeOne_eq]
    simp only [bind_assoc, bind_map_left]
    congr 1
    funext x
    obtain ⟨after, ⟨later, taken⟩⟩ := x
    cases after with
    | goOn p =>
      simp only [fixAfter]
      exact ih later taken p _
    | stop answer p =>
      rcases answer with e | (_ | r)
      · simp [fixAfter, resume]
      · simp [fixAfter, resume]
      · simp [fixAfter, resume]

/-- The loop's values do not depend on where its cursor came from. -/
theorem rest_origin (o o' : Z) :
    ∀ (parser : P) (cursor : Z) (hc : Token.Produce.Consumed cursor o)
      (hc' : Token.Produce.Consumed cursor o'),
      (fun x => (x.1, x.2.1, x.2.2.val)) <$> rest (m := m) o parser cursor hc =
        (fun x => (x.1, x.2.1, x.2.2.val)) <$> rest (m := m) o' parser cursor hc' := by
  intro parser cursor hc hc'
  induction cursor using (Token.Produce.consumed_wf (Z := Z)).induction generalizing parser with
  | _ cursor ih =>
  rw [rest, rest]
  rcases hn : Token.Produce.next? cursor with _ | ⟨token, ⟨next, step⟩⟩
  · simp
  · dsimp only
    simp only [map_bind]
    congr 1
    funext x
    obtain ⟨after, ⟨later, taken⟩⟩ := x
    cases after with
    | goOn p => exact ih later taken p _ _
    | stop answer p => simp

end Loops

/-! ## The loops on cursors alike but for the start of their handover -/

section Alike

open BSmtLib.Parser.Internal (After ParseByToken takeOne rest parseByToken)
open BSmtLib.Token (BatchTag BatchCursor)
open BSmtLib.Token.BatchCursor.Internal (Alike)

variable {H P R E : Type} [ParseByToken P H Id E R] {b : BatchTag}

theorem id_bind {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

theorem id_map {α β : Type} (x : α) (f : α → β) : (f <$> (x : Id α) : Id β) = f x := rfl

theorem id_pure {α : Type} (x : α) : (pure x : Id α) = x := rfl

theorem syntax_alike {x y : BatchCursor b} (h : Alike x y) (t : BSmtLib.Token b) :
    Token.Produce.«syntax» x t = Token.Produce.«syntax» y t := by
  show BatchCursor.«syntax» x t = BatchCursor.«syntax» y t
  simp only [BatchCursor.«syntax», Token.SyntaxToken.fromToken, h.category, h.content, h.version]

/-- The loop's token on cursors alike: the same parser and answer, the same handler, and cursors
alike. -/
theorem takeOne_alike (parser : P) {c c' n n' : BatchCursor b} (t : BSmtLib.Token b)
    (k : n.Consumed c) (k' : n'.Consumed c') (hn : Alike n n') (h : H) :
    ((takeOne parser c t n k).run h).1.1 = ((takeOne parser c' t n' k').run h).1.1 ∧
      Alike ((takeOne parser c t n k).run h).1.2.val ((takeOne parser c' t n' k').run h).1.2.val ∧
      ((takeOne parser c t n k).run h).2 = ((takeOne parser c' t n' k').run h).2 := by
  have hs := syntax_alike hn t
  have hv : Token.Produce.version n = Token.Produce.version n' := hn.version
  unfold takeOne
  simp only [StateT.run_bind]
  rw [hs, hv]
  generalize (ExceptT.run (do
      ParseByToken.arrive parser (Parser.Internal.Input.ofSyntax (Token.Produce.«syntax» n' t))
      ParseByToken.step (Token.Produce.version n') parser
        (Parser.Internal.Input.ofSyntax (Token.Produce.«syntax» n' t)))).run h = r
  obtain ⟨r, h₁⟩ := r
  rcases r with e | flow
  · exact ⟨rfl, hn, rfl⟩
  · cases flow with
    | more p => exact ⟨rfl, hn, rfl⟩
    | done res => exact ⟨rfl, hn, rfl⟩
    | switchVersion declared resume =>
      simp only [id_bind]
      split
      · rename_i a e1
        exact absurd e1 (by simp [Token.Produce.setVersion, BatchCursor.setVersion])
      · rename_i s1 e1
        split
        · rename_i a e2
          exact absurd e2 (by simp [Token.Produce.setVersion, BatchCursor.setVersion])
        · rename_i s2 e2
          have hal : Alike s1 s2 := hn.setVersion declared e1 e2
          simp only [StateT.run_bind]
          generalize (ExceptT.run resume).run h₁ = r'
          obtain ⟨r', h₂⟩ := r'
          rcases r' with e' | st
          · exact ⟨rfl, hal, rfl⟩
          · exact ⟨rfl, hal, rfl⟩
    | discardRest resume =>
      simp only [id_bind, StateT.run_bind]
      generalize (ExceptT.run resume).run h₁ = r'
      obtain ⟨r', h₂⟩ := r'
      rcases r' with e' | st
      · exact ⟨rfl, hn.discardRest, rfl⟩
      · exact ⟨rfl, hn.discardRest, rfl⟩

theorem next?_some {x : BatchCursor b} (hx : x.HasNext) :
    Token.Produce.next? x = some (x.next hx) := by
  show BatchCursor.next? x = _
  simp [BatchCursor.next?, hx]

theorem next?_none {x : BatchCursor b} (hx : ¬ x.HasNext) : Token.Produce.next? x = none := by
  show BatchCursor.next? x = _
  simp [BatchCursor.next?, hx]

/-- The loop on cursors alike, from wherever they come: the same answer and parser, the same
handler, and cursors alike. -/
theorem rest_alike {o o' : BatchCursor b} :
    ∀ (n : Nat) (parser : P) (c c' : BatchCursor b) (hc : c.Consumed o) (hc' : c'.Consumed o'),
      Alike c c' → c.remaining < n → ∀ h : H,
      ((rest o parser c hc).run h).1.1 = ((rest o' parser c' hc').run h).1.1 ∧
        ((rest o parser c hc).run h).1.2.1 = ((rest o' parser c' hc').run h).1.2.1 ∧
        Alike ((rest o parser c hc).run h).1.2.2.val ((rest o' parser c' hc').run h).1.2.2.val ∧
        ((rest o parser c hc).run h).2 = ((rest o' parser c' hc').run h).2
  | 0, _, _, _, _, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, parser, c, c', hc, hc', hal, hn, h => by
    rw [rest, rest]
    by_cases hx : c.HasNext
    · have hy : c'.HasNext := hal.hasNext_iff.mp hx
      rw [next?_some hx, next?_some hy]
      obtain ⟨ht, hnal⟩ := hal.next hx hy
      generalize c.next hx = cn at ht hnal ⊢
      generalize c'.next hy = cn' at ht hnal ⊢
      obtain ⟨t, ⟨d, k⟩⟩ := cn
      obtain ⟨t', ⟨d', k'⟩⟩ := cn'
      dsimp only at ht hnal
      subst ht
      simp only [StateT.run_bind]
      obtain ⟨ha, hal', hs⟩ := takeOne_alike parser t k k' hnal h
      generalize (takeOne parser c t d k).run h = x at ha hal' hs
      generalize (takeOne parser c' t d' k').run h = y at ha hal' hs
      obtain ⟨⟨a, ⟨z, hz⟩⟩, h₁⟩ := x
      obtain ⟨⟨a', ⟨z', hz'⟩⟩, h₂⟩ := y
      simp only at ha hal' hs
      subst ha hs
      cases a with
      | goOn p =>
        exact rest_alike n p z z' _ _ hal'
          (Nat.lt_of_lt_of_le hz.remaining_lt (Nat.le_of_lt_succ hn)) h₁
      | stop answer p => exact ⟨rfl, rfl, hal', rfl⟩
    · have hy : ¬ c'.HasNext := fun hy => hx (hal.hasNext_iff.mpr hy)
      rw [next?_none hx, next?_none hy]
      exact ⟨rfl, rfl, hal, rfl⟩

theorem parseByToken_none (parser : P) (state : ParseState H) {d : BatchCursor b}
    (hd : ¬ d.HasNext) :
    parseByToken parser state d =
      pure (.ok .continue, parser, state, ⟨d, fun hn => absurd hn hd⟩) := by
  unfold parseByToken
  split
  · rfl
  · rename_i heq
    rw [next?_none hd] at heq
    cases heq

theorem parseByToken_some (parser : P) (state : ParseState H) {d : BatchCursor b}
    (hd : d.HasNext) :
    parseByToken parser state d = (do
      match ← takeOne parser d (d.next hd).1 (d.next hd).2.val (d.next hd).2.property with
      | (.goOn parser, ⟨later, taken⟩) =>
        let (answer, parser, ⟨done, h⟩) ← rest d parser later taken
        return (answer, parser, state, ⟨done, fun _ => h⟩)
      | (.stop answer parser, ⟨later, taken⟩) =>
        return (answer, parser, state, ⟨later, fun _ => taken⟩)) := by
  unfold parseByToken
  split
  · rename_i heq
    rw [next?_some hd] at heq
    cases heq
  · rename_i t n k heq
    rw [next?_some hd] at heq
    have := Option.some.inj heq
    generalize d.next hd = dn at this ⊢
    subst this
    congr 1
    funext x
    obtain ⟨a, ⟨z, hz⟩⟩ := x
    cases a with
    | goOn p => congr 1
    | stop answer p => rfl

/-- The loop over the tokens of a cursor from wherever it comes is the parse of the cursor. -/
theorem rest_parseByToken {o d : BatchCursor b} (parser : P) (state : ParseState H)
    (hd : d.Consumed o) (h : H) :
    ((rest o parser d hd).run h).1.1 = ((parseByToken parser state d).run h).1.1 ∧
      ((rest o parser d hd).run h).1.2.1 = ((parseByToken parser state d).run h).1.2.1 ∧
      Alike ((rest o parser d hd).run h).1.2.2.val
        ((parseByToken parser state d).run h).1.2.2.2.val ∧
      ((rest o parser d hd).run h).2 = ((parseByToken parser state d).run h).2 := by
  by_cases hn : d.HasNext
  · rw [parseByToken_some parser state hn, rest, next?_some hn]
    generalize d.next hn = dn
    obtain ⟨t, ⟨n, k⟩⟩ := dn
    simp only [StateT.run_bind]
    generalize (takeOne parser d t n k).run h = x
    obtain ⟨⟨a, ⟨z, hz⟩⟩, h₁⟩ := x
    cases a with
    | goOn p =>
      obtain ⟨e1, e2, e3, e4⟩ := rest_alike (z.remaining + 1) p z z (hz.trans hd) hz
        (Alike.refl z) (Nat.lt_succ_self _) h₁
      exact ⟨e1, e2, e3, e4⟩
    | stop answer p => exact ⟨rfl, rfl, Alike.refl _, rfl⟩
  · rw [parseByToken_none parser state hn, rest, next?_none hn]
    exact ⟨rfl, rfl, Alike.refl _, rfl⟩

theorem rest_run_origin {o o' : BatchCursor b} (parser : P) (c : BatchCursor b)
    (hc : c.Consumed o) (hc' : c.Consumed o') (h : H) :
    ((rest o parser c hc).run h).1.1 = ((rest o' parser c hc').run h).1.1 ∧
      ((rest o parser c hc).run h).1.2.1 = ((rest o' parser c hc').run h).1.2.1 ∧
      ((rest o parser c hc).run h).1.2.2.val = ((rest o' parser c hc').run h).1.2.2.val ∧
      ((rest o parser c hc).run h).2 = ((rest o' parser c hc').run h).2 := by
  have e := congrArg (fun x => StateT.run x h) (rest_origin (m := Id) o o' parser c hc hc')
  simp only [StateT.run_map, id_map] at e
  have e' : ((((rest o parser c hc).run h).1.1, ((rest o parser c hc).run h).1.2.1,
      ((rest o parser c hc).run h).1.2.2.val), ((rest o parser c hc).run h).2) =
      ((((rest o' parser c hc').run h).1.1, ((rest o' parser c hc').run h).1.2.1,
      ((rest o' parser c hc').run h).1.2.2.val), ((rest o' parser c hc').run h).2) := e
  simp only [Prod.mk.injEq] at e'
  exact ⟨e'.1.1, e'.1.2.1, e'.1.2.2, e'.2⟩

/-- The loop over the tokens of a cursor from wherever it comes is the parse of the cursor, with
the same values. -/
theorem rest_parseByToken_eq {o d : BatchCursor b} (parser : P) (state : ParseState H)
    (hd : d.Consumed o) (h : H) :
    ((rest o parser d hd).run h).1.1 = ((parseByToken parser state d).run h).1.1 ∧
      ((rest o parser d hd).run h).1.2.1 = ((parseByToken parser state d).run h).1.2.1 ∧
      ((rest o parser d hd).run h).1.2.2.val =
        ((parseByToken parser state d).run h).1.2.2.2.val ∧
      ((rest o parser d hd).run h).2 = ((parseByToken parser state d).run h).2 := by
  by_cases hn : d.HasNext
  · rw [parseByToken_some parser state hn, rest, next?_some hn]
    generalize d.next hn = dn
    obtain ⟨t, ⟨n, k⟩⟩ := dn
    simp only [StateT.run_bind]
    generalize (takeOne parser d t n k).run h = x
    obtain ⟨⟨a, ⟨z, hz⟩⟩, h₁⟩ := x
    cases a with
    | goOn p => exact rest_run_origin p z (hz.trans hd) hz h₁
    | stop answer p => exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [parseByToken_none parser state hn, rest, next?_none hn]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The parse of cursors alike: the same answer and parser, the same handler, and cursors
alike. -/
theorem parseByToken_alike (parser : P) (state : ParseState H) {d d' : BatchCursor b}
    (hal : Alike d d') (h : H) :
    ((parseByToken parser state d).run h).1.1 = ((parseByToken parser state d').run h).1.1 ∧
      ((parseByToken parser state d).run h).1.2.1 =
        ((parseByToken parser state d').run h).1.2.1 ∧
      Alike ((parseByToken parser state d).run h).1.2.2.2.val
        ((parseByToken parser state d').run h).1.2.2.2.val ∧
      ((parseByToken parser state d).run h).2 = ((parseByToken parser state d').run h).2 := by
  by_cases hn : d.HasNext
  · have hn' : d'.HasNext := hal.hasNext_iff.mp hn
    rw [parseByToken_some parser state hn, parseByToken_some parser state hn']
    obtain ⟨ht, hnal⟩ := hal.next hn hn'
    generalize d.next hn = dn at ht hnal ⊢
    generalize d'.next hn' = dn' at ht hnal ⊢
    obtain ⟨t, ⟨n, k⟩⟩ := dn
    obtain ⟨t', ⟨n', k'⟩⟩ := dn'
    dsimp only at ht hnal
    subst ht
    simp only [StateT.run_bind]
    obtain ⟨ha, hal', hs⟩ := takeOne_alike parser t k k' hnal h
    generalize (takeOne parser d t n k).run h = x at ha hal' hs
    generalize (takeOne parser d' t n' k').run h = y at ha hal' hs
    obtain ⟨⟨a, ⟨z, hz⟩⟩, h₁⟩ := x
    obtain ⟨⟨a', ⟨z', hz'⟩⟩, h₂⟩ := y
    dsimp only at ha hal' hs
    subst ha hs
    cases a with
    | goOn p =>
      obtain ⟨e1, e2, e3, e4⟩ := rest_alike (z.remaining + 1) p z z' hz hz' hal'
        (Nat.lt_succ_self _) h₁
      exact ⟨e1, e2, e3, e4⟩
    | stop answer p => exact ⟨rfl, rfl, hal', rfl⟩
  · have hn' : ¬ d'.HasNext := fun hn' => hn (hal.hasNext_iff.mpr hn')
    rw [parseByToken_none parser state hn, parseByToken_none parser state hn']
    exact ⟨rfl, rfl, hal, rfl⟩

/-- A cursor through which no request was made. -/
def Fresh (x : BatchCursor b) : Prop := x.relexRequested = false ∧ x.discardRequested = false

/-- After a token of the loop that stops, a cursor with a token left has no request made, if the
cursor had none before. -/
theorem takeOneS_fresh (parser : P) {c n : BatchCursor b} (t : BSmtLib.Token b)
    (k : n.Consumed c) (hn : Fresh n) (h : H) :
    ((Stop.takeOne parser c t n k).run h).1.2.val.HasNext →
      Fresh ((Stop.takeOne parser c t n k).run h).1.2.val := by
  unfold Stop.takeOne
  simp only [StateT.run_bind]
  generalize (ExceptT.run (do
      ParseByToken.arrive parser (Parser.Internal.Input.ofSyntax (Token.Produce.«syntax» n t))
      ParseByToken.step (Token.Produce.version n) parser
        (Parser.Internal.Input.ofSyntax (Token.Produce.«syntax» n t)))).run h = r
  obtain ⟨r, h₁⟩ := r
  rcases r with e | flow
  · exact fun _ => hn
  · cases flow with
    | more p => exact fun _ => hn
    | done res => exact fun _ => hn
    | switchVersion declared resume =>
      simp only [id_bind]
      split
      · exact fun _ => hn
      · rename_i s1 e1
        simp only [StateT.run_bind]
        generalize (ExceptT.run resume).run h₁ = r'
        obtain ⟨r', h₂⟩ := r'
        intro hs
        rcases r' with e' | st
        · exact Alike.flags_hasNext hn.1 hn.2 declared e1 hs
        · exact Alike.flags_hasNext hn.1 hn.2 declared e1 hs
    | discardRest resume =>
      simp only [id_bind, StateT.run_bind]
      generalize (ExceptT.run resume).run h₁ = r'
      obtain ⟨r', h₂⟩ := r'
      intro hs
      rcases r' with e' | st
      · exact absurd hs (BatchCursor.discardRest_hasNext n)
      · exact absurd hs (BatchCursor.discardRest_hasNext n)

/-- After the loop that stops, a cursor with a token left has no request made, if the cursor had
none before where it had a token left. -/
theorem restS_fresh {o : BatchCursor b} :
    ∀ (m : Nat) (parser : P) (c : BatchCursor b) (hc : c.Consumed o), c.remaining < m →
      (c.HasNext → Fresh c) → ∀ h : H, ((Stop.rest o parser c hc).run h).1.2.2.val.HasNext →
        Fresh ((Stop.rest o parser c hc).run h).1.2.2.val
  | 0, _, _, _, hm, _, _ => absurd hm (Nat.not_lt_zero _)
  | m + 1, parser, c, hc, hm, hf, h => by
    rw [Stop.rest]
    by_cases hx : c.HasNext
    · rw [next?_some hx]
      have hfn : Fresh (c.next hx).2.val := by
        obtain ⟨e1, e2⟩ := BatchCursor.relexRequested_next hx
        exact ⟨e1.trans (hf hx).1, e2.trans (hf hx).2⟩
      have hk := takeOneS_fresh parser (c.next hx).1 (c.next hx).2.property hfn h
      generalize c.next hx = cn at hk ⊢
      obtain ⟨t, ⟨n, k⟩⟩ := cn
      simp only [StateT.run_bind]
      generalize (Stop.takeOne parser c t n k).run h = x at hk
      obtain ⟨⟨a, ⟨z, hz⟩⟩, h₁⟩ := x
      cases a with
      | goOn p =>
        exact restS_fresh m p z _ (Nat.lt_of_lt_of_le hz.remaining_lt (Nat.le_of_lt_succ hm))
          hk h₁
      | stop answer p => exact hk
    · rw [next?_none hx]
      exact fun hs => absurd hs hx

end Alike

/-! ## The calls of the two consumers -/

section Calls

open BSmtLib.Parser.Internal (After ParseByToken takeOne rest parseByToken)
open BSmtLib.Token (BatchTag BatchCursor)
open BSmtLib.Token.BatchCursor.Internal (Alike)

variable {H P R E : Type} [Handler H Id] [ParseByToken P H Id E R] [Parse P H Id E R]
  {b : BatchTag}

/-- What a call gives, without the proof of the consumption: the answer, the cursor, and the
adapter. -/
abbrev Out (H P R E : Type) (b : BatchTag) :=
  (Except (ParseErrorCause E) (ControlFlow R) × BatchCursor b) × ParseAdapter H P

/-- The same answer and adapter, and cursors alike. -/
def AlikeOut (x y : Out H P R E b) : Prop :=
  x.1.1 = y.1.1 ∧ Alike x.1.2 y.1.2 ∧ x.2 = y.2

omit [Handler H Id] [ParseByToken P H Id E R] [Parse P H Id E R] in
theorem AlikeOut.trans {x y z : Out H P R E b} (h : AlikeOut x y) (h' : AlikeOut y z) :
    AlikeOut x z :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

/-- A call of the parse adapter, without the proof of the consumption. -/
def outN (c : BatchCursor b) (h : c.HasNext) (A : ParseAdapter H P) : Out H P R E b :=
  let x := (Token.ConsumeFrom.consume (H := ParseAdapter H P) (m := Id) c h).run A
  ((x.1.1, x.1.2.val), x.2)

/-- A call of the adapter that stops, without the proof of the consumption. -/
def outS (c : BatchCursor b) (h : c.HasNext) (A : ParseAdapter H P) : Out H P R E b :=
  let x := (Stop.consume (H := H) (P := P) c h).run A
  ((x.1.1, x.1.2.val), x.2)

omit [Parse P H Id E R] in
theorem outS_eq (c : BatchCursor b) (h : c.HasNext) (A : ParseAdapter H P) :
    outS c h A =
      let x := Stop.finish c A.parseState ((Stop.takeOne A.parser c (c.next h).1
        (c.next h).2.val (c.next h).2.property).run (Stop.told A c))
      ((x.1.1, x.1.2.val), x.2) := rfl

variable (hp : ∀ {b : BatchTag} (parser : P) (state : ParseState H) (cursor : BatchCursor b),
  Parse.parse parser state cursor = Parser.Internal.parseByToken parser state cursor)
include hp

theorem outN_eq (c : BatchCursor b) (h : c.HasNext) (A : ParseAdapter H P) :
    outN c h A =
      let r := (parseByToken A.parser A.parseState c).run (Stop.told A c)
      ((r.1.1, r.1.2.2.2.val),
        ParseAdapter.mk r.2 r.1.2.1 (ParseAdapter.versionSetAfter r.1.1) r.1.2.2.1) := by
  simp only [outN, Token.ConsumeFrom.consume, hp, Stop.told]
  rfl


/-- A call of the parse adapter on cursors alike: the same answer and adapter, and cursors
alike. -/
theorem outN_alike {c c' : BatchCursor b} (hal : Alike c c') (h : c.HasNext) (h' : c'.HasNext)
    (A : ParseAdapter H P) : AlikeOut (outN c h A) (outN c' h' A) := by
  rw [outN_eq hp, outN_eq hp]
  have ht : Stop.told A c = Stop.told A c' := by
    unfold Stop.told; rw [show Token.Produce.version c = Token.Produce.version c' from hal.version]
  rw [ht]
  obtain ⟨e1, e2, e3, e4⟩ := parseByToken_alike A.parser A.parseState hal (Stop.told A c')
  refine ⟨e1, e3, ?_⟩
  dsimp only
  rw [e1, e2, e4]

/-- How the parse adapter's call goes on after the call of the adapter that stops: from where
that stopped, with the adapter it left, if the parser went on with a token left. -/
def resumeOut : Out H P R E b → Out H P R E b
  | ((.ok .continue, d), A') =>
    if hd : d.HasNext then outN d hd A' else ((.ok .continue, d), A')
  | y => y

/-- A call of the parse adapter is the call of the adapter that stops, then the parse adapter's
call from where that stopped. -/
theorem outN_split_eq (c : BatchCursor b) (h : c.HasNext) (A : ParseAdapter H P) :
    outN c h A = resumeOut (outS c h A) := by
  rw [outN_eq hp, outS_eq, parseByToken_some _ _ h, takeOne_eq]
  generalize c.next h = cn
  obtain ⟨t, ⟨n, k⟩⟩ := cn
  dsimp only
  simp only [StateT.run_bind, StateT.run_map]
  generalize (Stop.takeOne A.parser c t n k).run (Stop.told A c) = x
  obtain ⟨⟨after, ⟨l, tk⟩⟩, h₂⟩ := x
  simp only [id_map, id_bind]
  -- the parse adapter's call from where the adapter that stops stopped
  have hcont : ∀ (p : P) (d : BatchCursor b) (hd : d.Consumed c) (h₃ : H),
      ((((rest c p d hd).run h₃).1.1, ((rest c p d hd).run h₃).1.2.2.val),
          ParseAdapter.mk ((rest c p d hd).run h₃).2 ((rest c p d hd).run h₃).1.2.1
            (ParseAdapter.versionSetAfter ((rest c p d hd).run h₃).1.1) A.parseState) =
        (resumeOut ((.ok .continue, d), ParseAdapter.mk h₃ p true A.parseState) :
          Out H P R E b) := by
    intro p d hd h₃
    by_cases hn : d.HasNext
    · simp only [resumeOut, hn, ↓reduceDIte]
      rw [outN_eq hp]
      have ht : Stop.told (ParseAdapter.mk h₃ p true A.parseState) d = h₃ := rfl
      rw [ht]
      obtain ⟨e1, e2, e3, e4⟩ := rest_parseByToken_eq p A.parseState hd h₃
      dsimp only
      rw [e1, e2, e3, e4]
    · simp only [resumeOut, hn, ↓reduceDIte]
      rw [rest, next?_none hn]
      rfl
  cases after with
  | goOn p =>
    simp only [fixAfter, Stop.finish]
    rw [rest_eq]
    simp only [StateT.run_bind]
    generalize (Stop.rest c p l tk).run h₂ = y
    obtain ⟨⟨a, p', ⟨d, hd⟩⟩, h₃⟩ := y
    rcases a with e | (_ | r)
    · rfl
    · exact hcont p' d hd h₃
    · rfl
  | stop answer p =>
    rcases answer with e | (_ | r)
    · rfl
    · simp only [fixAfter, Stop.finish]
      exact hcont p l tk h₂
    · rfl

theorem outN_split (c : BatchCursor b) (h : c.HasNext) (A : ParseAdapter H P) :
    AlikeOut (outN c h A) (resumeOut (outS c h A)) := by
  rw [outN_split_eq hp]
  exact ⟨rfl, Alike.refl _, rfl⟩

omit [Parse P H Id E R] hp in
/-- After a call of the adapter that stops on a cursor through which no request was made, a
cursor with a token left has no request made. -/
theorem outS_fresh (c : BatchCursor b) (h : c.HasNext) (A : ParseAdapter H P) (hc : Fresh c) :
    (outS c h A).1.2.HasNext → Fresh (outS c h A).1.2 := by
  rw [outS_eq]
  have hfn : Fresh (c.next h).2.val := by
    obtain ⟨e1, e2⟩ := BatchCursor.relexRequested_next h
    exact ⟨e1.trans hc.1, e2.trans hc.2⟩
  have hk := takeOneS_fresh A.parser (c.next h).1 (c.next h).2.property hfn (Stop.told A c)
  generalize c.next h = cn at hk ⊢
  obtain ⟨t, ⟨n, k⟩⟩ := cn
  dsimp only at hk ⊢
  generalize (Stop.takeOne A.parser c t n k).run (Stop.told A c) = x at hk
  obtain ⟨⟨a, ⟨z, hz⟩⟩, h₁⟩ := x
  cases a with
  | goOn p =>
    exact restS_fresh (z.remaining + 1) p z hz (Nat.lt_succ_self _) hk h₁
  | stop answer p => exact hk

end Calls

/-! ## The lexer's handover of a cursor -/

section Kont

open BSmtLib.Lexer.Internal

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] {floor : Option Nat} {low : Nat}

/-- What the lexer does after the consumer's call in its handover of a cursor
(`Lexer.Internal.flushCursor`). -/
def kont {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → cursor.EndsAfter p) :
    Except E (ControlFlow R) × { c : Token.BatchCursor b // c.Consumed cursor } →
      LexM H m R E floor low (Option (Interrupted R E floor) × Token.BatchCursor b)
  | (result, ⟨next, consumed⟩) => do
    let location := next.consumedEndOf consumed
    have after : ∀ p, floor = some p → p < location.offset := fun p hp =>
      consumed.lt_consumedEndOf (hfloor p hp)
    match result with
    | .ok flow =>
      if next.discardRequested then
        let held := match flow with
          | .continue => none
          | .break result => some result
        return (some {
          result := .ok (.discarded held)
          span := next.consumedSpanOf consumed
          location
          stopAfter := fun p hp _ _ => after p hp }, next)
      else
        match flow with
        | .continue =>
          if next.relexRequested then
            return (some {
              result := .ok .relex
              span := next.consumedSpanOf consumed
              location
              stopAfter := fun p hp _ _ => after p hp }, next)
          else
            flushCursor next.resetConsumed fun p hp =>
              Token.BatchCursor.endsAfter_resetConsumed (consumed.follows.endsAfter (hfloor p hp))
        | .break result =>
          if h : next.HasNext then
            return (some (trailingAt (next.span (next.peek h))), next)
          else
            return (some {
              result := .ok (.finished result)
              span := next.consumedSpanOf consumed
              location
              stopAfter := fun p hp _ _ => after p hp }, next)
    | .error err =>
      if next.discardRequested then
        modifyCore fun c => { c with discardedFrom := c.discardedFrom.or (some location) }
      return (some {
        result := .error (.consumer err)
        span := next.consumedSpanOf consumed
        location
        stopAfter := fun _ _ _ h => nomatch h }, next)

theorem flushCursor_eq {b : Token.BatchTag} (cursor : Token.BatchCursor b)
    (hfloor : ∀ p, floor = some p → cursor.EndsAfter p) :
    flushCursor (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) cursor hfloor =
      if h : cursor.HasNext then do
        if (← getCore (H := H) (m := m) (R := R) (E := E) (floor := floor)
            (low := low)).holding then
          return (some (trailingAt (cursor.span (cursor.peek h))), cursor)
        else
          callConsumer cursor h >>= kont cursor hfloor
      else return (none, cursor) := by
  rw [flushCursor]
  rfl

end Kont

section KontRel

open BSmtLib.Lexer.Internal
open BSmtLib.Token.BatchCursor.Internal (Alike)

variable {H : Type} {R E : Type} [Token.Consume H R E] {floor : Option Nat} {low : Nat}
  {b : Token.BatchTag}

/-- What the handover of a cursor gives, with the states after it. -/
abbrev FlushOut (H R E : Type) (floor : Option Nat) (low : Nat) (b : Token.BatchTag) :=
  (Except (Interrupted R E floor) (Option (Interrupted R E floor) × Token.BatchCursor b) ×
    {c : LexerCore // c.Bound floor low}) × H

/-- The same states and stop, and cursors alike, or the same failure. -/
def FRel (x y : FlushOut H R E floor low b) : Prop :=
  x.2 = y.2 ∧ x.1.2 = y.1.2 ∧
    match x.1.1, y.1.1 with
    | .ok v, .ok w => v.1 = w.1 ∧ Alike v.2 w.2
    | .error e, .error e' => e = e'
    | _, _ => False

theorem run_modifyThe {S I : Type} (f : S → S) (s : S) (a : H) :
    ((ExceptT.run (modifyThe S f : ExceptT I (StateT S (StateT H Id)) Unit)).run s).run a =
      ((.ok (), f s), a) := rfl

/-- Run a step of the lexer from the states. -/
abbrev runL {α : Type} (x : LexM H Id R E floor low α) (s : {c : LexerCore // c.Bound floor low})
    (a : H) := ((x.run).run s).run a

theorem kont_rel (i₁ i₂ : ∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) Id)
    {c c' n n' : Token.BatchCursor b} (hf : ∀ p, floor = some p → c.EndsAfter p)
    (hf' : ∀ p, floor = some p → c'.EndsAfter p) (r : Except E (ControlFlow R))
    (k : n.Consumed c) (k' : n'.Consumed c') (hal : Alike n n')
    (s : {c : LexerCore // c.Bound floor low}) (a : H)
    (hr : n.discardRequested = false → n.relexRequested = false → r = .ok .continue →
      ∀ hn hn', FRel (runL (@flushCursor H Id R E _ _ i₁ floor low b n.resetConsumed hn) s a)
        (runL (@flushCursor H Id R E _ _ i₂ floor low b n'.resetConsumed hn') s a)) :
    FRel (runL (@kont H Id R E _ _ i₁ floor low b c hf (r, ⟨n, k⟩)) s a)
      (runL (@kont H Id R E _ _ i₂ floor low b c' hf' (r, ⟨n', k'⟩)) s a) := by
  have hloc := hal.consumedEndOf k k'
  have hspan := hal.consumedSpanOf k k'
  have hd := hal.discardRequested
  have hx := hal.relexRequested
  unfold kont
  rcases r with err | flow
  · dsimp only
    rw [← hd]
    cases hdisc : n.discardRequested
    · simp [runL, FRel, hloc, hspan, hal, id_pure]
    · simp [runL, FRel, hloc, hspan, hal, modifyCore, id_map, run_modifyThe,
        Except.map]
  · dsimp only
    rw [← hd]
    cases hdisc : n.discardRequested
    · cases flow with
      | «continue» =>
        dsimp only
        rw [← hx]
        cases hrel : n.relexRequested
        · simp only [Bool.false_eq_true, ite_false]
          exact hr hdisc hrel rfl _ _
        · simp [runL, FRel, hloc, hspan, hal, id_pure]
      | «break» res =>
        dsimp only
        by_cases hn : n.HasNext
        · have hn' : n'.HasNext := hal.hasNext_iff.mp hn
          simp [runL, FRel, hn, hn', hal, id_pure, hal.span_peek hn hn']
        · have hn' : ¬ n'.HasNext := fun h' => hn (hal.hasNext_iff.mpr h')
          simp [runL, FRel, hn, hn', hal, hloc, hspan, id_pure]
    · simp [runL, FRel, hloc, hspan, hal, id_pure]

omit [Token.Consume H R E] in
theorem FRel.refl (x : FlushOut H R E floor low b) : FRel x x := by
  obtain ⟨⟨r, s'⟩, a⟩ := x
  refine ⟨rfl, rfl, ?_⟩
  rcases r with e | v
  · rfl
  · exact ⟨rfl, Alike.refl _⟩

omit [Token.Consume H R E] in
theorem FRel.symm {x y : FlushOut H R E floor low b} (h : FRel x y) : FRel y x := by
  obtain ⟨⟨r, s'⟩, a⟩ := x
  obtain ⟨⟨r', s''⟩, a'⟩ := y
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.symm, h2.symm, ?_⟩
  rcases r with e | v <;> rcases r' with e' | v'
  · exact h3.symm
  · exact h3.elim
  · exact h3.elim
  · exact ⟨h3.1.symm, h3.2.symm⟩

omit [Token.Consume H R E] in
theorem FRel.trans {x y z : FlushOut H R E floor low b} (h : FRel x y) (h' : FRel y z) :
    FRel x z := by
  obtain ⟨⟨r, s₁⟩, a₁⟩ := x
  obtain ⟨⟨r', s₂⟩, a₂⟩ := y
  obtain ⟨⟨r'', s₃⟩, a₃⟩ := z
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨h1.trans h1', h2.trans h2', ?_⟩
  rcases r with e | v <;> rcases r' with e' | v' <;> rcases r'' with e'' | v''
  all_goals first
    | exact h3.trans h3'
    | exact ⟨h3.1.trans h3'.1, h3.2.trans h3'.2⟩
    | exact h3.elim
    | exact h3'.elim

theorem run_getCore_bind {α : Type} [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) Id]
    (f : LexerCore → LexM H Id R E floor low α) (s : {c : LexerCore // c.Bound floor low})
    (a : H) : runL (getCore >>= f) s a = runL (f s.val) s a := (rfl)

theorem run_callConsumer_bind {α : Type} (i : ∀ batch,
    Token.ConsumeFrom H (Token.BatchCursor batch) Id)
    {c : Token.BatchCursor b} (h : c.HasNext)
    (f : Except E (ControlFlow R) × { n : Token.BatchCursor b // n.Consumed c } →
      LexM H Id R E floor low α)
    (s : {c : LexerCore // c.Bound floor low}) (a : H) :
    runL (@callConsumer H Id R E _ _ i floor low b c h >>= f) s a =
      runL (f (((i b).consume c h).run a).1) s (((i b).consume c h).run a).2 := (rfl)

end KontRel

/-! ## The handovers of a cursor to the two consumers -/

section Flush

open BSmtLib.Lexer.Internal
open BSmtLib.Parser.Internal (ParseByToken)
open BSmtLib.Token (BatchTag BatchCursor)
open BSmtLib.Token.BatchCursor.Internal (Alike)

variable {H P R E : Type} [Handler H Id] [ParseByToken P H Id E R] [Parse P H Id E R]
  {b : BatchTag} {floor : Option Nat} {low : Nat}

/-- The parse adapter's consumer. -/
abbrev instN : ∀ batch, Token.ConsumeFrom (ParseAdapter H P) (BatchCursor batch) Id :=
  fun _ => inferInstance

/-- The consumer of the adapter that stops. -/
abbrev instS : ∀ batch, Token.ConsumeFrom (ParseAdapter H P) (BatchCursor batch) Id :=
  fun _ => Stop.consumeFrom

omit [ParseByToken P H Id E R] in
theorem resumeOut_of_not {r : Except (ParseErrorCause E) (ControlFlow R)} {d : BatchCursor b}
    {A : ParseAdapter H P} (h : ¬ (r = .ok .continue ∧ d.HasNext)) :
    resumeOut ((r, d), A) = ((r, d), A) := by
  rcases r with e | (_ | res)
  · rfl
  · have hd : ¬ d.HasNext := fun hd => h ⟨rfl, hd⟩
    simp only [resumeOut, hd, ↓reduceDIte]
  · rfl

omit [Handler H Id] [ParseByToken P H Id E R] in
/-- After a continue on a cursor through which no request was made, the lexer hands the rest of
the cursor over anew. -/
theorem kont_continue (i : ∀ batch, Token.ConsumeFrom (ParseAdapter H P) (BatchCursor batch) Id)
    {c n : BatchCursor b} (hf : ∀ p, floor = some p → c.EndsAfter p) (k : n.Consumed c)
    (hn : Fresh n) (s : {c : LexerCore // c.Bound floor low}) (a : ParseAdapter H P) :
    runL (@kont _ Id R (ParseErrorCause E) _ _ i floor low b c hf (.ok .continue, ⟨n, k⟩)) s a =
      runL (@flushCursor _ Id R (ParseErrorCause E) _ _ i floor low b n.resetConsumed
        fun p hp => Token.BatchCursor.endsAfter_resetConsumed (k.follows.endsAfter (hf p hp))) s
        a := by
  unfold kont
  simp only [hn.1, hn.2, Bool.false_eq_true, ite_false]

variable (hp : ∀ {b : BatchTag} (parser : P) (state : ParseState H) (cursor : BatchCursor b),
  Parse.parse parser state cursor = Parser.Internal.parseByToken parser state cursor)
include hp

/-- The lexer's handover of a cursor through which no request was made, to the parse adapter and
to the adapter that stops: the same stop and states, and cursors alike. -/
theorem flush_eq : ∀ (m : Nat) (c : BatchCursor b) (hfloor : ∀ p, floor = some p → c.EndsAfter p),
    c.remaining < m → Fresh c → ∀ (s : {c : LexerCore // c.Bound floor low}) (a : ParseAdapter H P),
    FRel (runL (@flushCursor (ParseAdapter H P) Id R (ParseErrorCause E) _ _ instN floor low b c
        hfloor) s a)
      (runL (@flushCursor (ParseAdapter H P) Id R (ParseErrorCause E) _ _ instS floor low b c
        hfloor) s a)
  | 0, _, _, hm, _, _, _ => absurd hm (Nat.not_lt_zero _)
  | m + 1, c, hfloor, hm, hc, s, a => by
    rw [flushCursor_eq,
      @flushCursor_eq (ParseAdapter H P) Id R (ParseErrorCause E) _ _ instS floor low b c hfloor]
    by_cases hx : c.HasNext
    · simp only [hx, ↓reduceDIte]
      rw [run_getCore_bind, run_getCore_bind]
      cases hh : s.val.holding
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [run_callConsumer_bind, run_callConsumer_bind]
        have hsplit := outN_split hp c hx a
        have hfresh := outS_fresh c hx a hc
        have eN : outN c hx a =
            let x := ((instN (P := P) b).consume c hx).run a
            ((x.1.1, x.1.2.val), x.2) := rfl
        have eS : outS c hx a =
            let x := ((instS (P := P) b).consume c hx).run a
            ((x.1.1, x.1.2.val), x.2) := rfl
        rw [eN, eS] at hsplit
        rw [eS] at hfresh
        generalize ((instN (P := P) b).consume c hx).run a = yN at hsplit ⊢
        generalize ((instS (P := P) b).consume c hx).run a = yS at hsplit hfresh ⊢
        obtain ⟨⟨rN, ⟨nN, kN⟩⟩, aN⟩ := yN
        obtain ⟨⟨rS, ⟨nS, kS⟩⟩, aS⟩ := yS
        dsimp only at hsplit hfresh ⊢
        by_cases hcont : rS = .ok .continue ∧ nS.HasNext
        · obtain ⟨rfl, hnS⟩ := hcont
          have hfS : Fresh nS := hfresh hnS
          simp only [resumeOut, hnS, ↓reduceDIte] at hsplit
          rw [kont_continue instS hfloor kS hfS]
          have hih := flush_eq m nS.resetConsumed
            (fun p hp' => Token.BatchCursor.endsAfter_resetConsumed (kS.follows.endsAfter
              (hfloor p hp')))
            (by rw [Token.BatchCursor.remaining_resetConsumed]; have := kS.remaining_lt; omega)
            ⟨(Alike.resetConsumed nS).relexRequested.trans hfS.1,
              (Alike.resetConsumed nS).discardRequested.trans hfS.2⟩ s aS
          refine FRel.trans ?_ hih
          -- the parse adapter's handover of the rest, anew
          have hnR : nS.resetConsumed.HasNext := Token.BatchCursor.hasNext_resetConsumed.mpr hnS
          rw [flushCursor_eq]
          simp only [hnR, ↓reduceDIte]
          rw [run_getCore_bind, hh]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [run_callConsumer_bind]
          have hal := outN_alike hp (Alike.resetConsumed nS).symm hnS hnR aS
          have hsplit' := hsplit.trans hal
          have eN' : outN nS.resetConsumed hnR aS =
              let x := ((instN (P := P) b).consume nS.resetConsumed hnR).run aS
              ((x.1.1, x.1.2.val), x.2) := rfl
          rw [eN'] at hsplit'
          generalize ((instN (P := P) b).consume nS.resetConsumed hnR).run aS = yR at hsplit' ⊢
          obtain ⟨⟨rR, ⟨nR, kR⟩⟩, aR⟩ := yR
          obtain ⟨e1, e2, e3⟩ := hsplit'
          dsimp only at e1 e2 e3
          subst e1 e3
          refine kont_rel instN instN hfloor _ rN kN kR e2 s aN ?_
          intro _ _ _ h₁ h₂
          have hr := e2.resetConsumed_eq
          revert h₁ h₂
          rw [hr]
          intro h₁ h₂
          exact FRel.refl _
        · rw [resumeOut_of_not hcont] at hsplit
          obtain ⟨e1, e2, e3⟩ := hsplit
          dsimp only at e1 e2 e3
          subst e1 e3
          refine kont_rel instN instS hfloor hfloor rN kN kS e2 s aN ?_
          intro hd hr' _ h₁ h₂
          have hrs := e2.resetConsumed_eq
          revert h₁
          rw [hrs]
          intro h₁
          exact flush_eq m nS.resetConsumed h₁
            (by rw [Token.BatchCursor.remaining_resetConsumed]; have := kS.remaining_lt; omega)
            ⟨(Alike.resetConsumed nS).relexRequested.trans (e2.relexRequested.symm.trans hr'),
              (Alike.resetConsumed nS).discardRequested.trans (e2.discardRequested.symm.trans hd)⟩
            s aN
      · simp only [↓reduceIte]
        exact FRel.refl _
    · simp only [hx, ↓reduceDIte]
      exact FRel.refl _

omit [Handler H Id] [ParseByToken P H Id E R] [Parse P H Id E R] hp in
theorem runL_bind {α β : Type} (x : LexM (ParseAdapter H P) Id R (ParseErrorCause E) floor low α)
    (f : α → LexM (ParseAdapter H P) Id R (ParseErrorCause E) floor low β)
    (s : {c : LexerCore // c.Bound floor low}) (a : ParseAdapter H P) :
    runL (x >>= f) s a =
      match (runL x s a).1.1 with
      | .ok v => runL (f v) (runL x s a).1.2 (runL x s a).2
      | .error e => ((.error e, (runL x s a).1.2), (runL x s a).2) := by
  simp only [runL, ExceptT.run_bind, StateT.run_bind]
  generalize ((ExceptT.run x).run s).run a = r
  obtain ⟨⟨r, s'⟩, a'⟩ := r
  cases r <;> rfl

omit hp in
theorem fresh_new (v : Token.Version) (batch : Token.TokenBatch) :
    Fresh (BatchCursor.new v batch) := ⟨rfl, rfl⟩

/-- The lexer's handover of a batch is the same to the parse adapter and to the adapter that
stops. -/
theorem handOver_run (batch : Token.TokenBatch) (bytesAfter : ByteArray)
    (hfloor : ∀ p, floor = some p → batch.EndsAfter p) (s : {c : LexerCore // c.Bound floor low})
    (a : ParseAdapter H P) :
    runL (@handOver (ParseAdapter H P) Id R (ParseErrorCause E) _ _ instN floor low batch
        bytesAfter hfloor) s a =
      runL (@handOver (ParseAdapter H P) Id R (ParseErrorCause E) _ _ instS floor low batch
        bytesAfter hfloor) s a := by
  unfold handOver
  rw [run_getCore_bind, run_getCore_bind, runL_bind, runL_bind]
  have hfl := flush_eq hp ((BatchCursor.new s.val.version batch).remaining + 1)
    (BatchCursor.new s.val.version batch)
    (fun p hp' => Token.BatchCursor.endsAfter_new (hfloor p hp') _) (Nat.lt_succ_self _)
    (fresh_new _ _) s a
  generalize runL (@flushCursor (ParseAdapter H P) Id R (ParseErrorCause E) _ _ instN floor low
    _ (BatchCursor.new s.val.version batch) _) s a = xN at hfl ⊢
  generalize runL (@flushCursor (ParseAdapter H P) Id R (ParseErrorCause E) _ _ instS floor low
    _ (BatchCursor.new s.val.version batch) _) s a = xS at hfl ⊢
  obtain ⟨⟨rN, sN⟩, aN⟩ := xN
  obtain ⟨⟨rS, sS⟩, aS⟩ := xS
  obtain ⟨e1, e2, e3⟩ := hfl
  dsimp only at e1 e2 e3 ⊢
  subst e1 e2
  rcases rN with eN | ⟨stopN, cN⟩ <;> rcases rS with eS | ⟨stopS, cS⟩
  · subst e3; rfl
  · exact e3.elim
  · exact e3.elim
  · obtain ⟨rfl, hal⟩ := e3
    dsimp only at hal
    have hfold : (@BatchCursor.foldConsumedCategories _ Nat cN) =
        (@BatchCursor.foldConsumedCategories _ Nat cS) := by
      funext init f
      exact hal.foldConsumedCategories init f
    have hb : Internal.intoBatch cN = Internal.intoBatch cS := hal.batch_eq
    dsimp only
    rw [hfold, hal.version, hb]

end Flush

section

variable {H P R E : Type} [Handler H Id] [Parser.Internal.ParseByToken P H Id E R]
  [Parse P H Id E R]

/-- The handover of a batch to the parse adapter is that to the adapter that stops after an action
on its cursor, where the parser's `parse` on a batch cursor is its loop over single tokens. -/
theorem handOver_eq
    (hp : ∀ {b : Token.BatchTag} (parser : P) (state : ParseState H)
      (cursor : Token.BatchCursor b),
      Parse.parse parser state cursor = Parser.Internal.parseByToken parser state cursor)
    (floor : Option Nat) (low : Nat) (batch : Token.TokenBatch) (bytesAfter : ByteArray)
    (hfloor : ∀ p, floor = some p → batch.EndsAfter p) :
    @Internal.handOver (ParseAdapter H P) Id R (ParseErrorCause E) _ _ (fun _ => inferInstance)
        floor low batch bytesAfter hfloor =
      @Internal.handOver (ParseAdapter H P) Id R (ParseErrorCause E) _ _
        (fun _ => Stop.consumeFrom) floor low batch bytesAfter hfloor := by
  apply ExceptT.ext
  funext s a
  exact handOver_run hp batch bytesAfter hfloor s a

end

open BSmtLib.Facts.Reader.Adapters (RecAdapter)

/-- The script parser's `parse` on a batch cursor, with the recording handler, is its loop over
single tokens. -/
theorem script_parse_eq {b : Token.BatchTag} (parser : BSmtLib.Parser.Script.ScriptParser
    (List BSmtLibSpec.Parser.Properties.Event)) (state : ParseState
        (List BSmtLibSpec.Parser.Properties.Event))
    (cursor : Token.BatchCursor b) :
    Parse.parse (m := Id) parser state cursor = Parser.Internal.parseByToken parser state cursor :=
  Proofs.Parser.Fused.Step.parse_eq parser state cursor

/-- The handover of a batch to the parse adapter of the script parser with the recording handler
is that to the adapter that stops. -/
theorem script_handOver_eq (floor : Option Nat) (low : Nat) (batch : Token.TokenBatch)
    (bytesAfter : ByteArray) (hfloor : ∀ p, floor = some p → batch.EndsAfter p) :
    @Internal.handOver RecAdapter Id Unit (ParseErrorCause Unit) _ _ (fun _ => inferInstance)
        floor low batch bytesAfter hfloor =
      @Internal.handOver RecAdapter Id Unit (ParseErrorCause Unit) _ _
        (fun _ => Stop.consumeFrom) floor low batch bytesAfter hfloor :=
  handOver_eq script_parse_eq floor low batch bytesAfter hfloor

end BSmtLib.Facts.Proofs.Reader.Param.Split
