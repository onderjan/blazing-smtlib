module

public import BSmtLib.Facts.Proofs.PublicApi.ReaderResets
public import BSmtLib.Facts.Proofs.PublicApi.SlicingC
public import BSmtLib.Facts.Proofs.Reader.Lexes.ThroughPhi
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Error
import all BSmtLib.Reader
import all BSmtLib.Parser.Adapter

@[expose] public section

/-!
# The script reader does not tell how its input is cut

The script reader over the recording handler, allowing every version, ends the same way however
its input is cut into slices (`slicing_recording`). Its lexer ends as the library's lexer with the
adapter's consumer for the replaying consumer does (`Reader.Lexes.ThroughPhi.through_replay`):
alike results, and an error on which the recording run over items standing for the tokens taken
fails where that lexer's consumer fails. That lexer does not tell how its input is cut
(`SlicingC.slicing`), as it never ends on trailing input: it ends as the lexer with the adapter's
consumer for the script consumer does (`Reader.Lexes.ThroughPhi.replay_script`), which ends as
`Reader.Session.Classified` says. Where the reader does not fail, its handler is the log of the
recording run over items standing for the tokens taken (`Reader.Lexes.Through.through_flagged`),
the same tokens however the input is cut, and it began to discard where the lexer with the
script consumer, the input not ended, did (`Discard.reader_discardedFrom`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.ReaderSlicing

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Parser BSmtLib.Parser.Adapter BSmtLib.Parser.Script
open BSmtLib.Facts.PublicApi.Adapters
open BSmtLib.Facts.Reader.Adapters
open BSmtLib.Facts.Lexer.Adapters (toVersion toLocation lexing LexOps)
open BSmtLib.Facts.Proofs.Lexer.Consumers.RunE
open BSmtLib.Facts.Proofs.Parser.Canon.Through (lexThrough)
open BSmtLib.Facts.Proofs.PublicApi.ReaderResets (ReadLex readThrough_lex SameRead)
open BSmtLib.Facts.Proofs.Reader.Param.Basic (ERel ORel LocRel LexErrRel CauseRel)
open BSmtLib.Facts.Proofs.Reader.Param.Run (HeldRel' FLexer)
open BSmtLib.Facts.Proofs.Reader.Param.General (AdapterAtG)
open BSmtLib.Facts.Proofs.Reader.Param.Phi (causeOfT)
open BSmtLib.Facts.Proofs.Reader.Param.PhiR (replay)
open BSmtLib.Facts.Proofs.Reader.Lexes.ThroughPhi (CM ZOps through_replay replay_script linkS)
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection (rcv)
open BSmtLib.Facts.Parser.Adapters.Run.Rejection (LibItem)
open BSmtLib.Facts.Proofs.Parser.Canon.Basic (Canon)
open BSmtLibSpec.Lexer (Handed)

/-! ## Small facts -/

/-- Where a run without the end of the input fails, the run with it fails alike. -/
theorem runInputE_false_error (ops : LexOps) {C : BSmtLibSpec.Lexer.Consumer} :
    ∀ (slices : List BSmtLibSpec.Regex.Chars) (lexer : ops.Lexer C) (t : List Handed)
      (e : LexerError (Option C.Error)),
      ((runInputE ops lexer false slices).run t).1.1 = .error e →
        ((runInputE ops lexer true slices).run t).1.1 = .error e
  | [], lexer, t, e, h => by
    rw [runInputE_nil_false] at h
    cases h
  | slice :: slices, lexer, t, e, h => by
    rw [runInputE_cons] at h ⊢
    generalize (ops.lexSliceStep lexer slice.toByteArray.toByteSlice).run t = r at h ⊢
    obtain ⟨⟨_ | held, l⟩, t'⟩ := r
    · exact h
    · exact runInputE_false_error ops slices _ t' e h

theorem toLocation_injective {a b : Span.Location} (h : toLocation a = toLocation b) : a = b := by
  obtain ⟨o₁, l₁, c₁⟩ := a
  obtain ⟨o₂, l₂, c₂⟩ := b
  simp only [toLocation, BSmtLibSpec.Lexer.Location.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem map_toLocation_injective {a b : Option Span.Location}
    (h : a.map toLocation = b.map toLocation) : a = b := by
  rcases a with _ | a <;> rcases b with _ | b <;> simp only [Option.map] at h
  · rfl
  · cases h
  · cases h
  · injection h with h
    rw [toLocation_injective h]

/-- Two held results of no value related to the same one are the same. -/
theorem heldRel_unique {α : Type} {x₁ x₂ : Option (Span.Located Unit)} {y : Option (Span.Located α)}
    (h₁ : HeldRel' x₁ y) (h₂ : HeldRel' x₂ y) : x₁ = x₂ := by
  rcases x₁ with _ | ⟨⟨⟩, l₁⟩ <;> rcases x₂ with _ | ⟨⟨⟩, l₂⟩ <;> rcases y with _ | ly <;>
    simp only [HeldRel', ORel, LocRel] at h₁ h₂
  · rfl
  · rw [h₁.2.trans h₂.2.symm]

/-- The parse adapters where the recording runs over items standing for the same tokens leave
the parser have the same handler. -/
theorem handler_of_adapterAt {version : BSmtLibSpec.Lexicon.Version} {items₁ items₂ : List LibItem}
    {v₁ v₂ : Version} {a₁ a₂ : RecAdapter}
    (h : items₁.map (rcv ∘ Subtype.val) = items₂.map (rcv ∘ Subtype.val))
    (h₁ : AdapterAtG version items₁ v₁ a₁) (h₂ : AdapterAtG version items₂ v₂ a₂) :
    a₁.handler = a₂.handler := by
  obtain ⟨hr, hl⟩ := Reader.Param.RecCanon.recRun_congr version h
  have hlen : items₁.isEmpty = items₂.isEmpty := by
    have := congrArg List.length h
    simp only [List.length_map] at this
    cases items₁ <;> cases items₂ <;> simp_all
  unfold AdapterAtG at h₁ h₂
  revert h₁ h₂ hr hl
  generalize Reader.Param.Link.recRun version items₁ = R₁
  generalize Reader.Param.Link.recRun version items₂ = R₂
  obtain ⟨r₁, log₁⟩ := R₁
  obtain ⟨r₂, log₂⟩ := R₂
  intro h₁ h₂ hr hl
  dsimp only at hr hl
  subst hl
  rcases r₁ with e₁ | (⟨w₁, q₁⟩ | f₁) <;> rcases r₂ with e₂ | (⟨w₂, q₂⟩ | f₂) <;>
    simp only [Except.map, Canon.canon, reduceCtorEq, Except.ok.injEq, Sum.map, Sum.elim_inl,
      Sum.elim_inr, Function.comp_apply, Sum.inl.injEq, Prod.mk.injEq] at hr h₁ h₂ ⊢
  all_goals first
    | exact h₁.trans h₂.symm
    | exact h₁.1.trans h₂.1.symm
    | skip
  obtain ⟨rfl, -, hs₁, hv₁⟩ := h₁
  obtain ⟨rfl, -, hs₂, hv₂⟩ := h₂
  have hw : w₁ = w₂ := hr.1
  subst hw
  have hs := hs₁.trans hs₂.symm
  unfold Reader.Param.Adapter.startLog at hs
  rw [hv₁, hv₂, hlen] at hs
  split at hs
  · exact hs
  · exact (List.cons.inj hs).2

/-! ## One input -/

section

open BSmtLib.Facts.Proofs.Reader.Consumer BSmtLib.Facts.Proofs.Reader.Lexes.Good
open BSmtLib.Facts.Proofs.Reader.Lexes.NoLayout BSmtLib.Facts.Proofs.Reader.Lexes.Told
open BSmtLib.Facts.Proofs.Reader.Param.Failing BSmtLib.Facts.Proofs.Reader.Param.Finish
open BSmtLib.Facts.Proofs.Reader.Param.Final BSmtLib.Facts.Proofs.Reader.Param.Flagged
open BSmtLib.Facts.Proofs.Reader.Reader BSmtLib.Facts.Proofs.Reader.Lexes.Through
open BSmtLib.Facts.Proofs.Reader.Classify BSmtLib.Facts.Proofs.Reader.Session
open BSmtLib.Facts.Proofs.Lexer.Consumers.AlikeF
open BSmtLib.Facts.Proofs.Reader.Param.Link (toVersion_eq_libVersion)
open BSmtLib.Facts.Proofs.Reader.Param.Final (recRun_nil)

/-- The library's lexer with the adapter's consumer for a consumer of the formalism, constructed
with the version, fed the slices and, if the input has ended, the end of the input. -/
abbrev zRun (C : BSmtLibSpec.Lexer.Consumer) (version : BSmtLibSpec.Lexicon.Version)
    (ended : Bool) (slices : List BSmtLibSpec.Regex.Chars) :=
  (runInputE ZOps (ZOps.new C {} (toVersion version)) ended slices).run []

/-- The parse adapter's lexer of a new script reader over the recording handler. -/
abbrev pNew (version : BSmtLibSpec.Lexicon.Version) : PLexer :=
  Lexer.new recordingAdapter (toVersion version)

/-- With the script consumer, the library's lexer never ends on trailing input. -/
theorem script_noTrailing (version : BSmtLibSpec.Lexicon.Version)
    (slices : List BSmtLibSpec.Regex.Chars) (e : LexerError (Option ScriptError))
    (he : (zRun (scriptConsumer version) version true slices).1.1 = .error e) :
    e.cause ≠ .lexical .unexpectedTrailingToken := by
  intro hc
  have hcl := lexing_classified _ Facts.Lexer.correctWithConsumers version slices
  have hout : (lexing Lexer.Adapters.Lexer.lexOps (scriptConsumer version) version [] slices
      true).outcome =
      outcomeOf (consumer := scriptConsumer version) true (.error e) := by
    rw [← he]
    exact congrArg (fun x => x.1.1)
      (runInput_eq ZOps true slices (ZOps.new (scriptConsumer version) {} (toVersion version)) [])

  have hf : outcomeOf (consumer := scriptConsumer version) true (.error e : Except
      (LexerError (Option ScriptError))
      (Option (Span.Located Unit))) = .failed (.trailing (toLocation e.span.start)) := by
    simp only [outcomeOf, BSmtLib.Facts.Lexer.Adapters.failureOf, hc]
    simp only [show (LexicalErrorKind.unexpectedTrailingToken ==
      LexicalErrorKind.unexpectedTrailingToken) = true from rfl, ite_true]
  unfold Classified at hcl
  rw [hout.trans hf] at hcl
  rcases hcl with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

/-- The script reader over the recording handler fed an input to its end ends as the library's
lexer with the adapter's consumer for the replaying consumer does, which ends as the one for the
script consumer does, never on trailing input. -/
theorem input_facts (version : BSmtLibSpec.Lexicon.Version) (slices : List ByteList) :
    ERel (LexErrRel (CM version)) HeldRel'
        ((lexThrough (R := Unit) (E := ParseError Unit) (pNew version) slices).map (·.1))
        (zRun (replay version) version true slices).1.1 ∧
      ERel (LexErrRel (linkS version).re) HeldRel' (zRun (replay version) version true slices).1.1
        (zRun (scriptConsumer version) version true slices).1.1 ∧
      (zRun (replay version) version true slices).2 =
        (zRun (scriptConsumer version) version true slices).2 ∧
      ∀ e, (zRun (replay version) version true slices).1.1 = .error e →
        e.cause ≠ .lexical .unexpectedTrailingToken := by
  have hgood := lexing_good _ Facts.Lexer.correctWithConsumers version slices true
  rw [lexing_flagged] at hgood
  let a₀ : FLexer version :=
    Lexer.new { errored := false, version := toVersion version, spoiled := false, layout := false }
      (toVersion version)
  have htaken : (lexing flaggedOps (scriptConsumer version) version [] slices true).taken =
      ((flaggedOps.runInput a₀ true slices).run []).2 := rfl
  rw [htaken] at hgood
  have hI : InvF version a₀ (pNew version) [] := by
    refine ⟨rfl, trivial, rfl, rfl, rfl, [], rfl, ?_⟩
    unfold AdapterAtG
    rw [recRun_nil]
    refine ⟨toVersion_eq_libVersion version, rfl, ?_, rfl⟩
    rw [show (Internal.handler a₀).version = toVersion version from rfl,
      toVersion_eq_libVersion]
    rfl
  have hR : Reach (scriptConsumer version) (toVersion version) (Internal.core a₀) := Reach.new
  have hnl := noLayout (scriptConsumer version) (scriptConsumer_concrete version)
      (toVersion version)
  have h₁ := through_replay hnl slices a₀ (pNew version)
    (ZOps.new (replay version) {} (toVersion version)) [] hI hR rfl trivial hgood
  obtain ⟨h₂, h₃⟩ := replay_script slices (ZOps.new (replay version) {} (toVersion version))
    (ZOps.new (scriptConsumer version) {} (toVersion version)) [] rfl trivial
  refine ⟨h₁, h₂, h₃, fun e he hc => ?_⟩
  revert h₂
  rw [he]
  generalize hz : (zRun (scriptConsumer version) version true slices).1.1 = z
  rcases z with e' | o <;> intro h₂
  · refine script_noTrailing version slices e' hz ?_
    have h₀ := h₂.1
    rw [hc] at h₀
    rcases hcz : e'.cause with k | x <;> rw [hcz] at h₀ <;> simp only [CauseRel] at h₀
    subst h₀
    rfl
  · exact h₂

/-- The script reader over the recording handler that read an input to its end: its handler is
the one the recording run over items standing for the tokens that the library's lexer with the
adapter's consumer for the script consumer takes leaves, and it began to discard where that lexer,
the input not ended, did. -/
theorem after_facts (version : BSmtLibSpec.Lexicon.Version) (slices : List ByteList)
    {result : Option (Span.Located Unit)} {before after : RecReader}
    (h : readThrough (readerOf version) slices = .ok (result, before, after)) :
    (∃ (items : List LibItem) (v : Version), items.map (rcv ∘ Subtype.val) =
        (zRun (scriptConsumer version) version true slices).2.map (rcv ∘ itemOf) ∧
        AdapterAtG version items v (Internal.handler (Reader.Internal.lexer after))) ∧
      before.discardedFrom.map toLocation =
        (Internal.core (zRun (scriptConsumer version) version false slices).1.2).discardedFrom.map
          toLocation := by
  have hgood := lexing_good _ Facts.Lexer.correctWithConsumers version slices true
  rw [lexing_flagged] at hgood
  let a₀ : FLexer version :=
    Lexer.new { errored := false, version := toVersion version, spoiled := false, layout := false }
      (toVersion version)
  have htaken : (lexing flaggedOps (scriptConsumer version) version [] slices true).taken =
      ((flaggedOps.runInput a₀ true slices).run []).2 := rfl
  rw [htaken] at hgood
  have hI : InvF version a₀ (pNew version) [] := by
    refine ⟨rfl, trivial, rfl, rfl, rfl, [], rfl, ?_⟩
    unfold AdapterAtG
    rw [recRun_nil]
    refine ⟨toVersion_eq_libVersion version, rfl, ?_, rfl⟩
    rw [show (Internal.handler a₀).version = toVersion version from rfl,
      toVersion_eq_libVersion]
    rfl
  have hR : Reach (scriptConsumer version) (toVersion version) (Internal.core a₀) := Reach.new
  have hnl := noLayout (scriptConsumer version) (scriptConsumer_concrete version)
      (toVersion version)
  obtain ⟨-, -, fl, items, hst, hat⟩ :=
    through_flagged hnl slices a₀ (pNew version) [] hI hR hgood (by rw [← readerOf_eq]; exact h)
  obtain ⟨-, e2, -, -⟩ := runInput_alikeF ZOps flaggedOps (AlikeLexers (scriptConsumer version))
    (fun a b => Internal.core a = Internal.core b) (slice_alikeF _) (eof_alikeF _)
    (fun _ _ h => h.2) (fun _ _ _ h => ⟨h.1, rfl⟩) (fun _ _ h => h.1) true slices
    (ZOps.new (scriptConsumer version) {} (toVersion version)) a₀ [] ⟨rfl, rfl⟩
  have e3 := congrArg Prod.snd
    (runInput_eq ZOps true slices (ZOps.new (scriptConsumer version) {} (toVersion version)) [])
  refine ⟨⟨items, fl.version, ?_, hat⟩, ?_⟩
  · rw [hst, ← e2, e3]
  · rw [Discard.reader_discardedFrom version slices (Discard.feed_of_readThrough h)]
    have e4 := congrArg (fun x => x.1.2)
      (runInput_eq ZOps false slices (ZOps.new (scriptConsumer version) {} (toVersion version)) [])
    show (ZOps.discardedFrom ((ZOps.runInput (ZOps.new (scriptConsumer version) {}
      (toVersion version)) false slices).run []).1.2).map toLocation = _
    rw [e4]
    rfl

end

/-! ## However the input is cut -/

/-- Two errors of the parse adapter's lexer related to the same error of the lexer with the
adapter's consumer for the replaying consumer, which is not the adapter's error `none`, are the
same. -/
theorem error_eq_of_cm {version : BSmtLibSpec.Lexicon.Version}
    {e₁ e₂ : LexerError (ParseError Unit)} {y : LexerError (Option (List Handed))}
    (h₁ : LexErrRel (CM version) e₁ y) (h₂ : LexErrRel (CM version) e₂ y)
    (hn : y.cause ≠ .consumer none) : e₁ = e₂ := by
  obtain ⟨c₁, s₁, f₁⟩ := e₁
  obtain ⟨c₂, s₂, f₂⟩ := e₂
  obtain ⟨cy, sy, fy⟩ := y
  obtain ⟨hc₁, rfl, rfl⟩ := h₁
  obtain ⟨hc₂, hs, hf⟩ := h₂
  dsimp only at hc₁ hc₂ hs hf hn ⊢
  subst hs hf
  congr 1
  rcases cy with k | (_ | t)
  · rcases c₁ with k₁ | a₁ <;> rcases c₂ with k₂ | a₂ <;> simp only [CauseRel] at hc₁ hc₂
    rw [hc₁, hc₂]
  · exact absurd rfl hn
  · rcases c₁ with k₁ | a₁ <;> rcases c₂ with k₂ | a₂ <;> simp only [CauseRel] at hc₁ hc₂
    rcases hc₁ with h | ⟨t₁, h₁, rfl⟩ <;> rcases hc₂ with h' | ⟨t₂, h₂, rfl⟩
    · cases h
    · cases h
    · cases h'
    · cases h₁
      cases h₂
      rfl

/-- The script reader over the recording handler, allowing every version, reads an input alike
however it is cut into slices. -/
theorem slicing_recording (version : Version) (slices : List ByteList) :
    SameRead (readThrough (Reader.script ([] : List BSmtLibSpec.Parser.Properties.Event)
        allVersions version) slices)
      (readThrough (Reader.script ([] : List BSmtLibSpec.Parser.Properties.Event) allVersions
        version) [slices.flatten]) := by
  rw [Reprinting.reader_eq]
  generalize BSmtLib.Facts.Lexer.Adapters.fromVersion version = v
  obtain ⟨A₁, B₁, T₁, N₁⟩ := input_facts v slices
  obtain ⟨A₂, B₂, T₂, N₂⟩ := input_facts v [slices.flatten]
  obtain ⟨S₁, S₂, -⟩ := SlicingC.slicing (replay v) rfl (toVersion v) true slices
  have hres := S₂ N₁
  have hW := (SlicingC.z_naive (replay v) (toVersion v) true slices).2.2.1
  obtain ⟨-, -, D₃⟩ := SlicingC.slicing (scriptConsumer v)
    (BSmtLib.Facts.Proofs.Reader.Consumer.scriptConsumer_concrete v) (toVersion v) false slices
  have hres' : (zRun (replay v) v true slices).1.1 =
      (zRun (replay v) v true [slices.flatten]).1.1 := hres
  have hS₁ : (zRun (replay v) v true slices).2 = (zRun (replay v) v true [slices.flatten]).2 := S₁
  have hW' : ∀ e, (zRun (replay v) v true slices).1.1 = .error e → e.cause ≠ .consumer none :=
    fun e he => (hW e he).2.2 rfl
  have hD : (zRun (scriptConsumer v) v false slices).1.1.isOk = true →
      (zRun (scriptConsumer v) v false [slices.flatten]).1.1.isOk = true →
      (Internal.core (zRun (scriptConsumer v) v false slices).1.2).discardedFrom =
        (Internal.core (zRun (scriptConsumer v) v false [slices.flatten]).1.2).discardedFrom := D₃
  have R₁ := readThrough_lex slices (pNew v)
  have R₂ := readThrough_lex [slices.flatten] (pNew v)
  rw [← BSmtLib.Facts.Proofs.Reader.Reader.readerOf_eq] at R₁ R₂
  -- a run without the end of the input does not fail where the run with it does not
  have hOk : ∀ S : List ByteList, (zRun (scriptConsumer v) v true S).1.1.isOk = true →
      (zRun (scriptConsumer v) v false S).1.1.isOk = true := by
    intro S h
    generalize hx : (zRun (scriptConsumer v) v false S).1.1 = x
    rcases x with e | o
    · rw [runInputE_false_error ZOps S _ [] e hx] at h
      cases h
    · rfl
  generalize hX₁ : readThrough (readerOf v) slices = X₁ at R₁
  generalize hX₂ : readThrough (readerOf v) [slices.flatten] = X₂ at R₂
  generalize lexThrough (R := Unit) (E := ParseError Unit) (pNew v) slices = Y₁ at R₁ A₁
  generalize lexThrough (R := Unit) (E := ParseError Unit) (pNew v) [slices.flatten] = Y₂
    at R₂ A₂
  rcases X₁ with f₁ | ⟨r₁, b₁, a₁⟩ <;> rcases Y₁ with e₁ | ⟨s₁, c₁, d₁⟩ <;>
    simp only [ReadLex] at R₁ <;>
    rcases X₂ with f₂ | ⟨r₂, b₂, a₂⟩ <;> rcases Y₂ with e₂ | ⟨s₂, c₂, d₂⟩ <;>
    simp only [ReadLex] at R₂ <;> simp only [SameRead]
  · -- both fail: with the same error
    rw [R₁, R₂]
    congr 1
    revert A₁ A₂ hW'
    rw [← hres']
    generalize (zRun (replay v) v true slices).1.1 = q
    intro hW' A₁ A₂
    rcases q with y | o
    · exact error_eq_of_cm A₁ A₂ (hW' y rfl)
    · exact (A₁ : False).elim
  · -- one fails, the other does not: impossible
    revert A₁ A₂
    rw [← hres']
    generalize (zRun (replay v) v true slices).1.1 = q
    intro A₁ A₂
    rcases q with y | o
    · exact (A₂ : False).elim
    · exact (A₁ : False).elim
  · revert A₁ A₂
    rw [← hres']
    generalize (zRun (replay v) v true slices).1.1 = q
    intro A₁ A₂
    rcases q with y | o
    · exact (A₁ : False).elim
    · exact (A₂ : False).elim
  · -- both do not fail
    obtain ⟨rfl, rfl, rfl⟩ := R₁
    obtain ⟨rfl, rfl, rfl⟩ := R₂
    obtain ⟨⟨items₁, v₁, hi₁, hat₁⟩, hd₁⟩ := after_facts v slices hX₁
    obtain ⟨⟨items₂, v₂, hi₂, hat₂⟩, hd₂⟩ := after_facts v [slices.flatten] hX₂
    -- the lexers with the adapter's consumers did not fail
    have hz₁ : (zRun (replay v) v true slices).1.1.isOk = true := by
      revert A₁
      generalize (zRun (replay v) v true slices).1.1 = q
      intro A₁
      rcases q with y | o
      · exact (A₁ : False).elim
      · rfl
    have hz₂ : (zRun (replay v) v true [slices.flatten]).1.1.isOk = true := hres' ▸ hz₁
    have hs : ∀ S : List ByteList, (zRun (replay v) v true S).1.1.isOk = true →
        ERel (LexErrRel (linkS v).re) HeldRel' (zRun (replay v) v true S).1.1
          (zRun (scriptConsumer v) v true S).1.1 →
        (zRun (scriptConsumer v) v true S).1.1.isOk = true := by
      intro S h hb
      revert h hb
      generalize (zRun (replay v) v true S).1.1 = q
      generalize (zRun (scriptConsumer v) v true S).1.1 = q'
      intro h hb
      rcases q with y | o <;> rcases q' with y' | o'
      · cases h
      · rfl
      · exact (hb : False).elim
      · rfl
    refine ⟨?_, ?_, ?_⟩
    · -- the same result
      revert A₁ A₂
      rw [← hres']
      generalize (zRun (replay v) v true slices).1.1 = q
      intro A₁ A₂
      rcases q with y | o
      · exact (A₁ : False).elim
      · exact heldRel_unique A₁ A₂
    · -- the same handler
      have ht : (zRun (scriptConsumer v) v true slices).2 =
          (zRun (scriptConsumer v) v true [slices.flatten]).2 := T₁.symm.trans (hS₁.trans T₂)
      exact handler_of_adapterAt (hi₁.trans (ht ▸ hi₂.symm)) hat₁ hat₂
    · -- discarding from the same location
      apply map_toLocation_injective
      rw [hd₁, hd₂, hD (hOk _ (hs _ hz₁ B₁)) (hOk _ (hs _ hz₂ B₂))]


section

-- the handlers are the one given, not the recording handler's instances
attribute [-instance] BSmtLib.Facts.Parser.Adapters.Handler.recordingLibraryTerms
  BSmtLib.Facts.Parser.Adapters.Handler.recordingLibrary

/-- `reading_slicing` of a library handler with the recording handler's state, outside the
printer. -/
def SlicingWith (I : Handler.CommandHandler (List BSmtLibSpec.Parser.Properties.Event) Id) :
    Prop :=
  letI := I
  ∀ (version : Version) (slices : List ByteList),
    SameRead (readThrough (Reader.script ([] : List BSmtLibSpec.Parser.Properties.Event)
        allVersions version) slices)
      (readThrough (Reader.script ([] : List BSmtLibSpec.Parser.Properties.Event) allVersions
        version) [slices.flatten])

end

theorem recording_SlicingWith :
    SlicingWith BSmtLib.Facts.Parser.Adapters.Handler.recordingLibrary :=
  slicing_recording

open Reprinting BSmtLib.Facts.PublicApi.Adapters.Content in
/-- The recorder reads an input alike however it is cut into slices. -/
theorem recorder_slicing :
    ∀ version slices, recorder.observe (readThrough (recorder.reader version) slices) =
      recorder.observe (readThrough (recorder.reader version) [slices.flatten]) := by
  have hw : SlicingWith (@ContentHandler.instCommandHandler
      (List BSmtLibSpec.Parser.Properties.Event)
      Recorder.recorderContent) := Recorder.instCommandHandler_eq ▸ recording_SlicingWith
  intro version slices
  have hs : SameRead (readThrough (recorder.reader version) slices)
      (readThrough (recorder.reader version) [slices.flatten]) := hw version slices
  unfold BSmtLib.Facts.PublicApi.Adapters.Reprinter.observe
  revert hs
  generalize readThrough (recorder.reader version) slices = X
  generalize readThrough (recorder.reader version) [slices.flatten] = Y
  intro hs
  rcases X with f | ⟨r, b, a⟩ <;> rcases Y with g | ⟨r', b', a'⟩ <;> simp only [SameRead] at hs
  · dsimp only
    rw [hs]
  · obtain ⟨rfl, ha, hb⟩ := hs
    dsimp only
    rw [ha, hb]

end BSmtLib.Facts.Proofs.PublicApi.ReaderSlicing
