module

public import BSmtLib.Facts.Proofs.Reader.Param.Watch
public import BSmtLib.Facts.Proofs.Reader.Param.Posture
public import BSmtLib.Facts.Proofs.Reader.Param.Split
public import BSmtLib.Facts.Proofs.Reader.Param.Run
public import BSmtLib.Facts.Proofs.Reader.Reader
public import BSmtLib.Facts.PublicApi.Adapters
import all BSmtLib.Lexer
import all BSmtLib.Parser.Adapter
import all BSmtLib.Parser.Script
import all BSmtLib.Reader
import all BSmtLib.Span

@[expose] public section

/-!
# A reader under a posture and under a looser one

Two script readers with the recording handler that differ only in their posture, `loose` looser
than `strict`, are related call by call while the reader under `strict` does not fail. The
relation goes through `Watch RecAdapter`, the parse adapter under `strict` with a record of what
went wrong:
- the library's lexer with `Watch RecAdapter` does what it does with the adapter under `strict`
  (`Watch.innerLink`);
- a call whose watched adapter answered an error fails (`UnaryCalls.lexSliceStep_flag`,
  `UnaryCalls.lexEofStep_flag`), so where the call under `strict` does not fail, nothing went wrong;
- where nothing went wrong, the lexer with `Watch RecAdapter` does what the lexer with the
  adapter under `loose` does (`looserLink`, one-sided as `Param.linkRelatorG` is: its relator
  says nothing of a run in which the watched adapter answers an error), as the adapter takes each
  token alike under the two postures unless it fails under `strict`
  (`Posture.consume_looser`).

So a reader under `strict` that reads an input to the end reads it as the reader under `loose`
does (`readThrough_looser`). The relation carries an invariant `I` of the record besides the
posture, which each call keeps where nothing went wrong.
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Reader.Looser

open BSmtLib.Lexer
open BSmtLib.Lexer.Cursor.LexerCursor.Internal (remaining)
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Parser
open BSmtLibSpec.Parser.Properties (Event)
open BSmtLib.Facts.Proofs.Reader.Param.Basic (Relator Link ERel FlowRel ORel LocRel SSim)
open BSmtLib.Facts.Proofs.Reader.Param.HandOver (Consumers)
open BSmtLib.Facts.Proofs.Reader.Param.Calls (SliceRel EofRel)
open BSmtLib.Facts.Proofs.Reader.Param.Flagged (isError)
open BSmtLib.Facts.Reader.Adapters (RecAdapter)
open BSmtLib.Facts.Proofs.Reader.Param.Run (run_id)
open BSmtLib.Parser.Adapter BSmtLib.Parser.Script

open BSmtLib.Facts.Proofs.Reader.Param (Watch)
open BSmtLib.Facts.Proofs.Reader.Param.Watch (WM innerLink inner_consumers consume_run
    eRel_mapError)
open BSmtLib.Facts.Proofs.Reader.Param.Posture (Looser adapterWith consume_looser)
open BSmtLib.Facts.PublicApi.Adapters (ByteList feed readThrough)

/-! ## The link -/

section

variable (strict loose : Version.VersionPosture) (I : Watch RecAdapter → Prop)

/-- The watched adapter is under `strict`, and its record satisfies `I`. -/
def Good (w : Watch RecAdapter) : Prop :=
  ScriptParser.Internal.posture w.inner.parser = strict ∧ I w

/-- The relator of the watched adapter and the adapter under `loose`:
- every value of the first has a partner;
- once something went wrong, it stays so;
- from a record where nothing went wrong, if nothing goes wrong, the record stays good, the
  values are related, and the adapter under `loose`, run from the watched adapter under `loose`,
  ends as the watched adapter does, under `loose`. -/
def looserRelator : Relator (Watch RecAdapter) WM RecAdapter Id where
  rel Q x y :=
    (∀ w u, ∃ b, Q ((x.run w).run u).1.1 b) ∧
    (∀ w u, w.errored = true → ((x.run w).run u).1.2.errored = true) ∧
    (∀ w u, w.errored = false → Good strict I w → ((x.run w).run u).1.2.errored = false →
      Good strict I ((x.run w).run u).1.2 ∧
      Q ((x.run w).run u).1.1 (y.run (adapterWith loose w.inner)).1 ∧
      (y.run (adapterWith loose w.inner)).2 = adapterWith loose ((x.run w).run u).1.2.inner)
  pure {_ _ _ _ b} h :=
    ⟨fun _ _ => ⟨b, h⟩, fun _ _ he => he, fun _ _ _ hg _ => ⟨hg, h, rfl⟩⟩
  bind {_ _ _ _ _ _ x y f g} hx hk := by
    have e₁ : ∀ w u, ((x >>= f).run w).run u =
        ((f ((x.run w).run u).1.1).run ((x.run w).run u).1.2).run ((x.run w).run u).2 :=
      fun _ _ => rfl
    have e₂ : ∀ a, (y >>= g).run a = (g (y.run a).1).run (y.run a).2 := fun _ => rfl
    refine ⟨fun w u => ?_, fun w u he => ?_, fun w u he hg hfin => ?_⟩
    · obtain ⟨b, hb⟩ := hx.1 w u
      rw [e₁]
      exact (hk _ _ hb).1 _ _
    · obtain ⟨b, hb⟩ := hx.1 w u
      rw [e₁]
      exact (hk _ _ hb).2.1 _ _ (hx.2.1 w u he)
    · obtain ⟨b', hb'⟩ := hx.1 w u
      rw [e₁ w u] at hfin ⊢
      rw [e₂]
      have he₁ : ((x.run w).run u).1.2.errored = false := by
        cases h : ((x.run w).run u).1.2.errored
        · rfl
        · have := (hk _ _ hb').2.1 _ ((x.run w).run u).2 h
          rw [this] at hfin
          cases hfin
      obtain ⟨hg₁, hq, hs⟩ := hx.2.2 w u he hg he₁
      rw [hs]
      exact (hk _ _ hq).2.2 _ _ he₁ hg₁ hfin
  mono hQ h :=
    ⟨fun w u => let ⟨b, hb⟩ := h.1 w u; ⟨b, hQ _ _ hb⟩, h.2.1,
      fun w u he hg hf => let ⟨h₁, h₂, h₃⟩ := h.2.2 w u he hg hf; ⟨h₁, hQ _ _ h₂, h₃⟩⟩

/-- The link of the watched adapter and the adapter under `loose`: equal results, and the errors
of the first those of the second wrapped. -/
def looserLink : Link (Watch RecAdapter) WM Unit (Option (ParseError Unit)) RecAdapter Id
    Unit (ParseError Unit) where
  rc := looserRelator strict loose I
  rr := (· = ·)
  re := fun e₁ e₂ => e₁ = some e₂

/-- Where nothing went wrong, a call keeps `I`. -/
def KeepsI : Prop :=
  ∀ {b : Token.BatchTag} (cursor : LexerCursor b) (h : cursor.HasNext) (w : Watch RecAdapter),
    w.errored = false → Good strict I w →
    (((Token.ConsumeFrom.consume (m := WM) cursor h : StateT (Watch RecAdapter) WM _).run w).run
      ()).1.2.errored = false →
    I (((Token.ConsumeFrom.consume (m := WM) cursor h : StateT (Watch RecAdapter) WM _).run w).run
        ()).1.2

end

section Continue

open BSmtLib.Facts.Proofs.Reader.Param.Split (outN outS resumeOut outN_split_eq script_parse_eq
  resumeOut_of_not)
open BSmtLib.Facts.Proofs.Parser.HandOver (recording_noHandOver)

/-- A call of the parse adapter goes alike under `loose` as under `strict`, unless it fails under
`strict`; the parser keeps its posture: from the call of the adapter that stops, which does so
(`Posture.consume_looser`), and the call from where that stopped. -/
theorem outN_looser {strict loose : Version.VersionPosture} (hl : Looser strict loose)
    {b : Token.BatchTag} :
    ∀ (n : Nat) (cursor : LexerCursor b) (h : cursor.HasNext) (adapter : RecAdapter),
      (remaining cursor) < n → ScriptParser.Internal.posture adapter.parser = strict →
      (∃ e, (outN cursor h adapter).1.1 = .error e) ∨
        (outN cursor h (adapterWith loose adapter) =
            ((outN cursor h adapter).1, adapterWith loose (outN cursor h adapter).2) ∧
          ScriptParser.Internal.posture (outN cursor h adapter).2.parser = strict)
  | 0, _, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, cursor, h, adapter, hn, hp => by
    rw [outN_split_eq script_parse_eq recording_noHandOver,
      outN_split_eq script_parse_eq recording_noHandOver]
    have hs := Param.Posture.consume_looser hl cursor h adapter hp
    have eS : ∀ A, outS cursor h A =
        let x := (Param.Stop.consume (H := List Event) (P := ScriptParser
            (List Event)) cursor h).run A
        ((x.1.1, x.1.2.val), x.2) := fun _ => rfl
    rw [eS, eS]
    change (∃ e, ((Param.Stop.consume (H := List Event) (P := ScriptParser (List Event)) cursor
        h).run adapter).1.1 = .error e) ∨
      ((Param.Stop.consume (H := List Event) (P := ScriptParser (List Event)) cursor h).run
          (adapterWith loose adapter) =
        (((Param.Stop.consume (H := List Event) (P := ScriptParser (List Event)) cursor h).run
          adapter).1, adapterWith loose
            ((Param.Stop.consume (H := List Event) (P := ScriptParser (List Event)) cursor
              h).run adapter).2) ∧
        ScriptParser.Internal.posture
          ((Param.Stop.consume (H := List Event) (P := ScriptParser (List Event)) cursor h).run
            adapter).2.parser = strict) at hs
    generalize (Param.Stop.consume (H := List Event) (P := ScriptParser (List Event)) cursor
      h).run adapter = x at hs ⊢
    generalize (Param.Stop.consume (H := List Event) (P := ScriptParser (List Event)) cursor
      h).run (adapterWith loose adapter) = y at hs ⊢
    obtain ⟨⟨a, ⟨d, hd⟩⟩, A'⟩ := x
    rcases hs with ⟨e, he⟩ | ⟨rfl, hp'⟩
    · dsimp only at he ⊢
      subst he
      left
      exact ⟨e, by rw [resumeOut_of_not (fun hc => by cases hc.1)]⟩
    · dsimp only at hp' ⊢
      by_cases hc : a = .ok .continue ∧ d.HasNext
      · obtain ⟨rfl, hdn⟩ := hc
        simp only [resumeOut, hdn, ↓reduceDIte]
        exact outN_looser hl n d hdn A'
          (Nat.lt_of_lt_of_le hd.remaining_lt (Nat.le_of_lt_succ hn)) hp'
      · rw [resumeOut_of_not hc, resumeOut_of_not hc]
        exact .inr ⟨rfl, hp'⟩

/-- `outN_looser` for the call itself. -/
theorem consume_looserN {strict loose : Version.VersionPosture} (hl : Looser strict loose)
    {b : Token.BatchTag}
    (cursor : LexerCursor b) (h : cursor.HasNext) (adapter : RecAdapter)
    (hp : ScriptParser.Internal.posture adapter.parser = strict) :
    (∃ e, ((Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run
        adapter).1.1 = .error e) ∨
      ((Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run
          (adapterWith loose adapter) =
        (((Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run adapter).1,
          adapterWith loose
            ((Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run
                adapter).2) ∧
        ScriptParser.Internal.posture
          ((Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run
            adapter).2.parser = strict) := by
  have hl' := outN_looser hl (remaining cursor + 1) cursor h adapter (Nat.lt_succ_self _) hp
  have eN : ∀ A, outN cursor h A =
      let x := (Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run A
      ((x.1.1, x.1.2.val), x.2) := fun _ => rfl
  rw [eN, eN] at hl'
  generalize (Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run
    adapter = x at hl' ⊢
  generalize (Token.ConsumeFrom.consume (m := Id) cursor h : StateT RecAdapter Id _).run
    (adapterWith loose adapter) = y at hl' ⊢
  obtain ⟨⟨a, ⟨d, hd⟩⟩, A'⟩ := x
  obtain ⟨⟨a', ⟨d', hd'⟩⟩, A''⟩ := y
  dsimp only at hl' ⊢
  rcases hl' with ⟨e, he⟩ | ⟨he, hp'⟩
  · exact .inl ⟨e, he⟩
  · simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    exact .inr ⟨rfl, hp'⟩

end Continue

theorem isError_mapError {ε ε' α : Type} (f : ε → ε') (r : Except ε α) :
    isError (r.mapError f) = isError r := by
  cases r <;> rfl

theorem looser_calls {strict loose : Version.VersionPosture} {I : Watch RecAdapter → Prop}
    (hl : Looser strict loose) (hI : KeepsI strict I) :
    Param.HandOver.Calls (looserLink strict loose I) where
  concrete := rfl
  consume cursor h := by
    refine ⟨fun w u => ?_, fun w u he => ?_, fun w u he hg hfin => ?_⟩
    · rw [consume_run]
      exact ⟨_, eRel_mapError _, rfl⟩
    · rw [consume_run]
      simp only [Watch.after, he, Bool.true_or]
    · have hI' := hI cursor h w he hg (by cases u; exact hfin)
      rw [consume_run] at hfin hI' ⊢
      simp only [Watch.after, he, Bool.false_or, Bool.or_eq_false_iff] at hfin
      obtain ⟨-, hok⟩ := hfin
      simp only [Watch.answer, isError_mapError] at hok hI' ⊢
      rcases consume_looserN hl cursor h w.inner hg.1 with ⟨e, he'⟩ | ⟨hq, hp⟩
      · rw [he'] at hok
        cases hok
      · rw [hq]
        exact ⟨⟨hp, hI'⟩, ⟨eRel_mapError _, rfl⟩, rfl⟩

theorem looser_consumers {strict loose : Version.VersionPosture} {I : Watch RecAdapter → Prop}
    (hl : Looser strict loose) (hI : KeepsI strict I) : Consumers (looserLink strict loose I) :=
  .ofCalls (looser_calls hl hI)

/-! ## The steps of the calls -/

section

variable {strict loose : Version.VersionPosture} {I : Watch RecAdapter → Prop}

theorem oRel_eq {α : Type} {a b : Option (Span.Located α)} (h : ORel (LocRel (· = ·)) a b) :
    a = b := by
  match a, b, h with
  | none, none, _ => rfl
  | some ⟨v, l⟩, some ⟨v', l'⟩, ⟨hv, hl⟩ =>
    simp only at hv hl
    rw [hv, hl]

theorem flowRel_eq {α : Type} {a b : ControlFlow (Span.Located α)}
    (h : FlowRel (LocRel (· = ·)) a b) :
    a = b := by
  match a, b, h with
  | .continue, .continue, _ => rfl
  | .break ⟨v, l⟩, .break ⟨v', l'⟩, ⟨hv, hl⟩ =>
    simp only at hv hl
    rw [hv, hl]

/-- The step of a call on a slice with the adapter under `strict` that does not fail: nothing
went wrong with the watched adapter, and the step with the adapter under `loose` ends alike. -/
theorem slice_looser (hl : Looser strict loose) (hI : KeepsI strict I) (slice : ByteSlice)
    (c : LexerCore) (w : Watch RecAdapter) (he : w.errored = false) (hv : c.version = w.version)
    (hg : Good strict I w)
    (hok : isError (((Internal.lexSliceStep (H := RecAdapter) (m := Id)
      (Recovery.LexerRecovery.abandon Recovery.FailFast)
          (Recovery.LexerRecovery.recover Recovery.FailFast)
      slice).run c).run w.inner).1.1 = false) :
    ∃ w' : Watch RecAdapter, w'.errored = false ∧
      (((Internal.lexSliceStep (H := RecAdapter) (m := Id)
          (Recovery.LexerRecovery.abandon Recovery.FailFast)
        (Recovery.LexerRecovery.recover Recovery.FailFast) slice).run c).run w.inner).1.2.version =
        w'.version ∧ Good strict I w' ∧
      w'.inner = (((Internal.lexSliceStep (H := RecAdapter) (m := Id)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
            (Recovery.LexerRecovery.recover Recovery.FailFast)
        slice).run c).run w.inner).2 ∧
      ((Internal.lexSliceStep (H := RecAdapter) (m := Id)
          (Recovery.LexerRecovery.abandon Recovery.FailFast)
        (Recovery.LexerRecovery.recover Recovery.FailFast) slice).run c).run
            (adapterWith loose w.inner) =
        ((((Internal.lexSliceStep (H := RecAdapter) (m := Id)
            (Recovery.LexerRecovery.abandon Recovery.FailFast)
          (Recovery.LexerRecovery.recover Recovery.FailFast) slice).run c).run w.inner).1,
          adapterWith loose w'.inner) := by
  have hA := Param.Calls.lexSliceStep_sim (inner_consumers (C := RecAdapter))
    (Recovery.LexerRecovery.abandon (H := Watch RecAdapter) (m := WM) Recovery.FailFast)
    (Recovery.LexerRecovery.recover (H := Watch RecAdapter) (m := WM) Recovery.FailFast)
    (Recovery.LexerRecovery.abandon (H := RecAdapter) (m := Id) Recovery.FailFast)
    (Recovery.LexerRecovery.recover (H := RecAdapter) (m := Id) Recovery.FailFast)
    (fun _ => (innerLink RecAdapter).rc.pure rfl) (fun _ => (innerLink RecAdapter).rc.pure rfl)
    slice c w ()
  have hB := (Param.Calls.lexSliceStep_sim (looser_consumers hl hI)
    (Recovery.LexerRecovery.abandon (H := Watch RecAdapter) (m := WM) Recovery.FailFast)
    (Recovery.LexerRecovery.recover (H := Watch RecAdapter) (m := WM) Recovery.FailFast)
    (Recovery.LexerRecovery.abandon (H := RecAdapter) (m := Id) Recovery.FailFast)
    (Recovery.LexerRecovery.recover (H := RecAdapter) (m := Id) Recovery.FailFast)
    (fun _ => (looserLink strict loose I).rc.pure rfl)
    (fun _ => (looserLink strict loose I).rc.pure rfl) slice c).2.2 w ()
  have hU := Param.UnaryCalls.lexSliceStep_flag slice c w () he hv
  unfold Param.UnaryCalls.irun at hU
  generalize ((StateT.run (Internal.lexSliceStep (H := Watch RecAdapter) (m := WM)
    (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast) slice) c).run
      w).run () = rW at hA hB hU
  generalize (StateT.run (Internal.lexSliceStep (H := RecAdapter) (m := Id)
    (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast) slice) c).run
      w.inner = rP at hA hok ⊢
  generalize (StateT.run (Internal.lexSliceStep (H := RecAdapter) (m := Id)
    (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast) slice) c).run
      (adapterWith loose w.inner) = rL at hB ⊢
  obtain ⟨⟨⟨resW, cW⟩, w'⟩, u'⟩ := rW
  obtain ⟨⟨resP, cP⟩, p'⟩ := rP
  obtain ⟨⟨resL, cL⟩, l'⟩ := rL
  obtain ⟨⟨hrA, rfl⟩, hinner⟩ := hA
  obtain ⟨hU₁, hU₂, -⟩ := hU
  dsimp only at hok hU₁ hU₂ hinner hB ⊢
  rcases resP with eP | heldP
  · cases hok
  rcases resW with eW | heldW
  · exact absurd hrA id
  have he' : w'.errored = false := by
    cases h : w'.errored
    · rfl
    · exact absurd (hU₂ h) id
  obtain ⟨hg', ⟨hrB, rfl⟩, rfl⟩ := hB he hg he'
  rcases resL with eL | heldL
  · exact absurd hrB id
  have e₁ : heldW = heldP := oRel_eq hrA
  have e₂ : heldW = heldL := oRel_eq hrB
  subst e₁ e₂
  exact ⟨w', he', hU₁ he', hg', hinner, rfl⟩

/-- The step of a call at the end of the input with the adapter under `strict` that does not
fail: nothing went wrong with the watched adapter, and the step with the adapter under `loose`
ends alike. -/
theorem eof_looser (hl : Looser strict loose) (hI : KeepsI strict I)
    (c : LexerCore) (w : Watch RecAdapter) (he : w.errored = false) (hv : c.version = w.version)
    (hg : Good strict I w)
    (hok : isError (((Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
      (E := ParseError Unit) (Recovery.LexerRecovery.abandon Recovery.FailFast)
      (Recovery.LexerRecovery.recover Recovery.FailFast)).run c).run w.inner).1.1 = false) :
    ∃ w' : Watch RecAdapter, w'.errored = false ∧ Good strict I w' ∧
      w'.inner = (((Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
        (E := ParseError Unit) (Recovery.LexerRecovery.abandon Recovery.FailFast)
        (Recovery.LexerRecovery.recover Recovery.FailFast)).run c).run w.inner).2 ∧
      ((Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit) (E := ParseError Unit)
        (Recovery.LexerRecovery.abandon Recovery.FailFast)
            (Recovery.LexerRecovery.recover Recovery.FailFast)).run
          c).run (adapterWith loose w.inner) =
        ((((Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit) (E := ParseError Unit)
          (Recovery.LexerRecovery.abandon Recovery.FailFast)
              (Recovery.LexerRecovery.recover Recovery.FailFast)).run
            c).run w.inner).1, adapterWith loose w'.inner) := by
  have hA := Param.Calls.lexEofStep_sim (inner_consumers (C := RecAdapter))
    (Recovery.LexerRecovery.abandon (H := Watch RecAdapter) (m := WM) Recovery.FailFast)
    (Recovery.LexerRecovery.recover (H := Watch RecAdapter) (m := WM) Recovery.FailFast)
    (Recovery.LexerRecovery.abandon (H := RecAdapter) (m := Id) Recovery.FailFast)
    (Recovery.LexerRecovery.recover (H := RecAdapter) (m := Id) Recovery.FailFast)
    (fun _ => (innerLink RecAdapter).rc.pure rfl) (fun _ => (innerLink RecAdapter).rc.pure rfl)
    c w ()
  have hB := (Param.Calls.lexEofStep_sim (looser_consumers hl hI)
    (Recovery.LexerRecovery.abandon (H := Watch RecAdapter) (m := WM) Recovery.FailFast)
    (Recovery.LexerRecovery.recover (H := Watch RecAdapter) (m := WM) Recovery.FailFast)
    (Recovery.LexerRecovery.abandon (H := RecAdapter) (m := Id) Recovery.FailFast)
    (Recovery.LexerRecovery.recover (H := RecAdapter) (m := Id) Recovery.FailFast)
    (fun _ => (looserLink strict loose I).rc.pure rfl)
    (fun _ => (looserLink strict loose I).rc.pure rfl) c).2.2 w ()
  have hU := Param.UnaryCalls.lexEofStep_flag c w () he hv
  unfold Param.UnaryCalls.irun at hU
  generalize ((StateT.run (Internal.lexEofStep (H := Watch RecAdapter) (m := WM) (R := Unit)
    (E := Option (ParseError Unit)) (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast)) c).run w).run () = rW at hA hB hU
  generalize (StateT.run (Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
    (E := ParseError Unit) (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast)) c).run w.inner = rP at hA hok ⊢
  generalize (StateT.run (Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
    (E := ParseError Unit) (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast)) c).run
    (adapterWith loose w.inner) = rL at hB ⊢
  obtain ⟨⟨⟨resW, cW⟩, w'⟩, u'⟩ := rW
  obtain ⟨⟨resP, cP⟩, p'⟩ := rP
  obtain ⟨⟨resL, cL⟩, l'⟩ := rL
  obtain ⟨⟨hrA, rfl⟩, hinner⟩ := hA
  obtain ⟨hU₁, -⟩ := hU
  dsimp only at hok hU₁ hinner hB ⊢
  rcases resP with eP | flowP
  · cases hok
  rcases resW with eW | flowW
  · exact absurd hrA id
  have he' : w'.errored = false := by
    cases h : w'.errored
    · rfl
    · exact absurd (hU₁ h) id
  obtain ⟨hg', ⟨hrB, rfl⟩, rfl⟩ := hB he hg he'
  rcases resL with eL | flowL
  · exact absurd hrB id
  have e₁ : flowW = flowP := flowRel_eq hrA
  have e₂ : flowW = flowL := flowRel_eq hrB
  subst e₁ e₂
  exact ⟨w', he', hg', hinner, rfl⟩

end

/-! ## The calls -/

section

variable {strict loose : Version.VersionPosture} {I : Watch RecAdapter → Prop}

theorem handler_ofParts {H R E : Type} [Token.Consume H R E] (h : H) (c : LexerCore)
    (d : Option (Span.Located R)) : Internal.handler
    (Internal.ofParts h c d : BSmtLib.Lexer H) = h := (rfl)

/-- The lexer with the adapter under `loose` for the lexer with the adapter under `strict`: the same
but for the posture. -/
def loosened (loose : Version.VersionPosture) (p : BSmtLib.Lexer RecAdapter) :
    BSmtLib.Lexer RecAdapter :=
  Internal.ofParts (adapterWith loose (Internal.handler p)) (Internal.core p) (Internal.held p)

variable (strict I) in
/-- What holds of the lexer with the adapter under `strict` and the record of the watched adapter
between the calls. -/
def Between (p : BSmtLib.Lexer RecAdapter) (w : Watch RecAdapter) : Prop :=
  Internal.handler p = w.inner ∧ w.errored = false ∧
      (Internal.core p).version = w.version ∧ Good strict I w

theorem lexSlice_looser (hl : Looser strict loose) (hI : KeepsI strict I) (slice : ByteSlice)
    {p : BSmtLib.Lexer RecAdapter} {w : Watch RecAdapter} (hR : Between strict I p w)
    {p' : BSmtLib.Lexer RecAdapter} (h : (Lexer.lexSlice p slice : Id _) = .ok p') :
    (Lexer.lexSlice (loosened loose p) slice : Id _) = .ok (loosened loose p') ∧
      ∃ w', Between strict I p' w' := by
  obtain ⟨hpw, he, hv, hg⟩ := hR
  simp only [Lexer.lexSlice] at h ⊢
  rw [run_id] at h ⊢
  simp only [loosened, Param.Flagged.core_ofParts,
    Param.Flagged.held_ofParts, handler_ofParts] at h ⊢
  rw [hpw] at h ⊢
  have hok : isError (((Internal.lexSliceStep (H := RecAdapter) (m := Id)
      (Recovery.LexerRecovery.abandon Recovery.FailFast)
          (Recovery.LexerRecovery.recover Recovery.FailFast)
      slice).run (Internal.core p)).run w.inner).1.1 = false := by
    revert h
    generalize (((Internal.lexSliceStep (H := RecAdapter) (m := Id)
      (Recovery.LexerRecovery.abandon Recovery.FailFast)
          (Recovery.LexerRecovery.recover Recovery.FailFast)
      slice).run (Internal.core p)).run w.inner).1.1 = r
    rcases r with e | held
    · intro h; cases h
    · intro _; rfl
  obtain ⟨w', he', hv', hg', hinner, hloose⟩ := slice_looser hl hI slice
      (Internal.core p) w he hv hg hok
  rw [hloose]
  revert h hv' hinner
  generalize ((Internal.lexSliceStep (H := RecAdapter) (m := Id)
    (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast)
    slice).run (Internal.core p)).run w.inner = r
  obtain ⟨⟨res, c'⟩, a'⟩ := r
  intro h hv' hinner
  dsimp only at h hv' hinner ⊢
  subst hinner
  rcases res with e | held'
  · cases h
  · cases h
    exact ⟨rfl, w', rfl, he', hv', hg'⟩

theorem lexEof_looser (hl : Looser strict loose) (hI : KeepsI strict I)
    {p : BSmtLib.Lexer RecAdapter} {w : Watch RecAdapter} (hR : Between strict I p w)
    {result : Option (Span.Located Unit)} {p' : BSmtLib.Lexer RecAdapter}
    (h : (Lexer.lexEof p : Id _) = .ok (result, p')) :
    (Lexer.lexEof (loosened loose p) : Id _) = .ok (result, loosened loose p') ∧
      ∃ w', Good strict I w' ∧ w'.inner = Internal.handler p' := by
  obtain ⟨hpw, he, hv, hg⟩ := hR
  simp only [Lexer.lexEof] at h ⊢
  rw [run_id] at h ⊢
  simp only [loosened, Param.Flagged.core_ofParts,
    Param.Flagged.held_ofParts, handler_ofParts] at h ⊢
  rw [hpw] at h ⊢
  have hok : isError (((Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
      (E := ParseError Unit) (Recovery.LexerRecovery.abandon Recovery.FailFast)
      (Recovery.LexerRecovery.recover Recovery.FailFast)).run
          (Internal.core p)).run w.inner).1.1 = false := by
    revert h
    generalize (((Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
      (E := ParseError Unit) (Recovery.LexerRecovery.abandon Recovery.FailFast)
      (Recovery.LexerRecovery.recover Recovery.FailFast)).run (Internal.core p)).run w.inner).1.1 = r
    rcases r with e | flow
    · intro h; cases h
    · intro _; rfl
  obtain ⟨w', he', hg', hinner, hloose⟩ := eof_looser hl hI (Internal.core p) w he hv hg hok
  rw [hloose]
  revert h hinner
  generalize ((Internal.lexEofStep (H := RecAdapter) (m := Id) (R := Unit)
    (E := ParseError Unit) (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast)).run (Internal.core p)).run w.inner = r
  obtain ⟨⟨res, c'⟩, a'⟩ := r
  intro h hinner
  dsimp only at h hinner ⊢
  subst hinner
  rcases res with e | flow
  · cases h
  · cases h
    exact ⟨rfl, w', hg', rfl⟩

/-- The parse adapter with the recording handler, nothing recorded yet, and the script parser
under the posture. -/
abbrev adapterOf (posture : Version.VersionPosture) : RecAdapter :=
  ParseAdapter.new ([] : List Event) (ScriptParser.new (H := List Event) posture)

/-- The script reader with the recording handler, under the posture, with the initial version. -/
abbrev readerWith (posture : Version.VersionPosture) (version : Version) :
    Reader (List Event) (ScriptParser (List Event)) :=
  Reader.script ([] : List Event) posture version

theorem feed_looser (hl : Looser strict loose) (hI : KeepsI strict I) :
    ∀ (slices : List ByteList) (p : BSmtLib.Lexer RecAdapter) (w : Watch RecAdapter)
      {before : Reader (List Event) (ScriptParser (List Event))}, Between strict I p w →
      feed (Reader.Internal.ofLexer p) slices = .ok before →
      feed (Reader.Internal.ofLexer (loosened loose p)) slices =
          .ok (Reader.Internal.ofLexer (loosened loose (Reader.Internal.lexer before))) ∧
        ∃ w', Between strict I (Reader.Internal.lexer before) w'
  | [], p, w, before, hR, h => by
    simp only [feed, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, w, hR⟩
  | slice :: slices, p, w, before, hR, h => by
    simp only [feed] at h ⊢
    rw [Reader.readSlice_ofLexer] at h ⊢
    revert h
    cases hs : (Lexer.lexSlice p slice.toByteArray.toByteSlice : Id _) with
    | error e => intro h; cases h
    | ok p' =>
      intro h
      obtain ⟨hq, w', hR'⟩ := lexSlice_looser hl hI _ hR hs
      rw [hq]
      exact feed_looser hl hI slices p' w' hR' h

/-- A reader under `strict` that reads an input to the end reads it as the reader under `loose`:
with the same result, the same handler at the end, and the same discarding before the end of the
input; and a watched adapter under `strict` in which nothing went wrong ends with the handler. -/
theorem readThrough_looser (hl : Looser strict loose) (hI : KeepsI strict I)
    (version : Version)
    (hI₀ : I (Watch.new (adapterOf strict) version))
    {slices : List ByteList} {result : Option (Span.Located Unit)}
    {before after : Reader (List Event) (ScriptParser (List Event))}
    (h : readThrough (readerWith strict version) slices = .ok (result, before, after)) :
    ∃ before' after', readThrough (readerWith loose version) slices =
        .ok (result, before', after') ∧
      after'.handler = after.handler ∧ before'.discardedFrom = before.discardedFrom ∧
      ∃ w : Watch RecAdapter, Good strict I w ∧
        w.inner = Internal.handler (Reader.Internal.lexer after) := by
  have hR : Between strict I (Lexer.new (adapterOf strict) version)
      (Watch.new (adapterOf strict) version) :=
    ⟨rfl, rfl, rfl, rfl, hI₀⟩
  have hloose : loosened loose (Lexer.new (adapterOf strict) version) =
      Lexer.new (adapterOf loose) version := rfl
  unfold readThrough at h ⊢
  have hf₁ : feed (readerWith strict version) slices =
      feed (Reader.Internal.ofLexer
        (Lexer.new (adapterOf strict) version)) slices := rfl
  have hf₂ : feed (readerWith loose version) slices =
      feed (Reader.Internal.ofLexer (loosened loose
        (Lexer.new (adapterOf strict) version))) slices := by
    rw [hloose]
    rfl
  rw [hf₁] at h
  rw [hf₂]
  revert h
  cases hfeed : feed (Reader.Internal.ofLexer
      (Lexer.new (adapterOf strict) version)) slices with
  | error e => intro h; cases h
  | ok before₁ =>
    intro h
    obtain ⟨hq, w, hR'⟩ := feed_looser hl hI slices _ _ hR hfeed
    rw [hq]
    dsimp only at h ⊢
    have hb : before₁ = Reader.Internal.ofLexer (Reader.Internal.lexer before₁) := rfl
    rw [hb, Reader.readEof_ofLexer] at h
    rw [Reader.readEof_ofLexer]
    revert h
    cases he : (Lexer.lexEof (Reader.Internal.lexer before₁) : Id _) with
    | error e => intro h; cases h
    | ok r =>
      obtain ⟨result₁, p'⟩ := r
      intro h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hq', w', hg', hw'⟩ := lexEof_looser hl hI hR' he
      rw [hq']
      exact ⟨_, _, rfl, rfl, rfl, w', hg', hw'⟩

end

end BSmtLib.Facts.Proofs.Reader.Looser
