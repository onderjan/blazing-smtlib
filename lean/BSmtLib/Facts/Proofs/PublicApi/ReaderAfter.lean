module

public import BSmtLib.Facts.Proofs.PublicApi.Resets
public import BSmtLib.Facts.Proofs.PublicApi.Discard
public import BSmtLib.Facts.Proofs.Reader.Lexes.Through
public import BSmtLib.Facts.Proofs.Reader.Session
public import BSmtLib.Facts.Parser
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Reader
import all BSmtLib.Parser.Adapter

@[expose] public section

/-!
# The script reader after an input it read to the end

`after_state` describes the script reader over the recording handler, allowing every version,
after an input it read to the end:
- its lexer's fields are those a lexer constructed with the version has after the end of the
  input (`Resets.resetOf`);
- its adapter is reset and not told the version.

The fields come from the lexer with the stand-in consumer, which ends with the fields of the
reader's lexer (`Reader.Lexes.Through.through_flagged`) and those of the lexer with the adapter's
consumer (`Reader.Param.Flagged.slice_alikeF`), whose fields the chain of lexers gives
(`fields_afterC`). The adapter stands where the recording run over the tokens taken leaves the
parser, which has finished, as the stand-in consumer has.
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.PublicApi.ReaderAfter

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Facts.PublicApi.Adapters
open BSmtLib.Facts.Proofs.Lexer BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
open BSmtLib.Facts.Proofs.PublicApi.Resets
open BSmtLib.Facts.Lexer.Adapters (Answering AnswerM)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Alike BSmtLib.Facts.Proofs.Lexer.Consumers.AlikeF

/-- The library's lexer with the adapter's consumer for a consumer of the formalism, fed an input to
the end without failing, has the version it was constructed with as its initial one, and does not
recover. -/
theorem fields_afterC (C : BSmtLibSpec.Lexer.Consumer) (version : Version)
    (slices : List BSmtLibSpec.Regex.Chars)
    (hok : ((ZOps.runInput (ZOps.new C {} version) true slices).run
      []).1.1.isFailed = false) :
    (Internal.core ((ZOps.runInput (ZOps.new C {} version) true slices).run
        []).1.2).recovers = false ∧
      (Internal.core ((ZOps.runInput (ZOps.new C {} version) true slices).run
        []).1.2).initialVersion = version := by
  -- the library's lexer and the lexer with the batch in its state, fed the input cut
  obtain ⟨z1, -, -, z4⟩ := BSmtLib.Facts.Proofs.Lexer.Consumers.ChainZ.runInput_cut true slices
    (ZOps.new C {} version) (XOps.new C {} version) []
    (X1BatchInCoreLexer.Handed.lexerRel_new _ _)
  have hz := z4 hok
  -- the Rust port and the lexer with the batch in its state
  obtain ⟨x1, x2, -⟩ := runInput_alike WOps XOps
    WRustPortX1BatchInCore.Calls.LexRel
    (BSmtLib.Facts.Proofs.Lexer.Consumers.ChainX1.slice_alike C)
    (BSmtLib.Facts.Proofs.Lexer.Consumers.ChainX1.eof_alike C)
    (fun _ _ h => h.2.2) (fun _ _ _ h => ⟨h.1, h.2.1, rfl⟩) true
    (X1BatchInCoreLexer.Chunks.cutAll slices)
    (WOps.new C {} version) (XOps.new C {} version) []
    (WRustPortX1BatchInCore.Handed.new_rel _ _)
  -- the Rust port and the naive lexer
  obtain ⟨v1, -, v3, -⟩ := runInput_alikeF WOps VOps
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.WVRel C)
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.WVWeak C)
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wv_slice C)
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wv_eof C)
    (fun _ _ h => h.1) (fun _ _ _ h => ⟨rfl, h.2⟩)
    (fun _ _ h => ⟨h.2.version, BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.cr_weak h.2⟩)
    true (X1BatchInCoreLexer.Chunks.cutAll slices)
    (WOps.new C {} version) (VOps.new C {} version) []
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wvRel_new _ _)
  have hw := v3 (by rw [x1, ← z1]; exact hok)
  have hv := BSmtLib.Facts.Proofs.Lexer.Consumers.VReset.runInput_reset C
    (X1BatchInCoreLexer.Chunks.cutAll slices)
    (Lexer.Internal.VNaive.Core.initial version) none [] trivial
  have hrel := hz.2.1
  have hr1 := congrArg (·.recovers) hrel
  have hr2 := congrArg (·.initialVersion) hrel
  simp only [X1BatchInCoreLexer.Outer.zb,
    X1BatchInCoreLexer.Outer.zm,
    X1BatchInCoreLexer.Core.coreMap] at hr1 hr2
  refine ⟨hr1.symm.trans ((x2.2.1.1.recovers).symm.trans hw.2.recovers), ?_⟩
  exact hr2.symm.trans ((x2.2.1.1.initialVersion).symm.trans (hw.2.initial.trans hv.2.1))

/-! ## A successful end of the input resets the fields -/

section

variable {H : Type} {R E : Type} [Token.Consume H R E]

/-- The run of an inner step in `Id`. -/
abbrev irunI {α : Type} (x : InnerM H Id α) (c : LexerCore) (h : H) :=
  (x.run c).run h

theorem irunI_bind {α β : Type} (x : InnerM H Id α) (k : α → InnerM H Id β) (c h) :
    irunI (x >>= k) c h =
      irunI (k (irunI x c h).1.1) (irunI x c h).1.2 (irunI x c h).2 := (rfl)

theorem irunI_reset (c h) :
    irunI (Internal.reset (H := H) (m := Id)) c h = (((), resetOf c), h) := (rfl)
omit [Token.Consume H R E] in

/-- What the end of the input does after its inner step, ending successfully only where it
resets the state. -/
theorem tail_okI (x : InnerM H Id (Except (Failure E) (ControlFlow (Span.Located R))))
    (K : Except (Failure E) (ControlFlow (Span.Located R)) →
      InnerM H Id (Except (LexerError E) (ControlFlow (Span.Located R))))
    (hok : ∀ flow, K (.ok flow) = (Internal.reset >>= fun _ => Pure.pure (.ok flow)))
    (herr : ∀ f c h, ∃ e, (irunI (K (.error f)) c h).1.1 = .error e)
    {c : LexerCore} {h : H} {flow : ControlFlow (Span.Located R)} {c' : LexerCore} {h' : H}
    (hrun : irunI (x >>= K) c h = ((.ok flow, c'), h')) :
    ∃ c₀, c' = resetOf c₀ := by
  rw [irunI_bind] at hrun
  generalize irunI x c h = Q at hrun
  obtain ⟨⟨r, c₁⟩, h₁⟩ := Q
  cases r with
  | ok f =>
    simp only at hrun
    rw [hok, irunI_bind, irunI_reset] at hrun
    exact ⟨c₁, (congrArg (·.1.2) hrun).symm⟩
  | error failure =>
    simp only at hrun
    obtain ⟨e, he⟩ := herr failure c₁ h₁
    rw [hrun] at he
    cases he

/-- A successful end of the input leaves the lexer's state reset. -/
theorem eofStep_okI [∀ b, Token.ConsumeFrom H (LexerCursor b) Id] {c : LexerCore} {h : H}
    {flow : ControlFlow (Span.Located R)} {c' : LexerCore} {h' : H}
    (hrun : irunI (Internal.lexEofStep (R := R) (E := E)
      (Recovery.LexerRecovery.abandon Recovery.FailFast)
      (Recovery.LexerRecovery.recover Recovery.FailFast)) c h = ((.ok flow, c'), h')) :
    ∃ c₀, c' = resetOf c₀ := by
  unfold Internal.lexEofStep at hrun
  rw [irunI_bind] at hrun
  simp only at hrun
  split at hrun
  · rw [irunI_bind, irunI_bind, irunI_bind] at hrun
    exact tail_okI _ _ (fun _ => rfl) (fun _ _ _ => ⟨_, rfl⟩) hrun
  · exact tail_okI _ _ (fun _ => rfl) (fun _ _ _ => ⟨_, rfl⟩) hrun

end

open BSmtLib.Facts.Reader.Adapters (RecReader)

theorem run_eqI {H R E α : Type} [Token.Consume H R E] (l : BSmtLib.Lexer H)
    (x : InnerM H Id α) :
    Internal.run l x =
      (((x.run (Internal.core l)).run (Internal.handler l)).1.1,
        Internal.ofParts ((x.run (Internal.core l)).run (Internal.handler l)).2
          ((x.run (Internal.core l)).run (Internal.handler l)).1.2 (Internal.held l)) := (rfl)

/-- A successful end of the input leaves the reader's lexer reset and holding nothing. -/
theorem readEof_reset {reader : RecReader} {result : Option (Span.Located Unit)}
    {after : RecReader} (h : (reader.readEof : Id _) = .ok (result, after)) :
    (∃ c₀, Internal.core (Reader.Internal.lexer after) = resetOf c₀) ∧
      Internal.held (Reader.Internal.lexer after) = none := by
  simp only [Reader.readEof, BSmtLib.Lexer.lexEof] at h
  rw [run_eqI] at h
  generalize hR : ((Internal.lexEofStep (R := Unit) (E := Parser.ParseError Unit)
    (Recovery.LexerRecovery.abandon Recovery.FailFast)
    (Recovery.LexerRecovery.recover Recovery.FailFast)).run (Internal.core reader.lexer)).run
      (Internal.handler reader.lexer) = Q at h
  obtain ⟨⟨r, c'⟩, h'⟩ := Q
  cases r with
  | ok flow =>
    simp only at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨eofStep_okI hR, rfl⟩
  | error e => cases h

/-- A read through to the end ends with a successful end of the input. -/
theorem readEof_of_readThrough {reader : RecReader} {slices : List ByteList}
    {result : Option (Span.Located Unit)} {before after : RecReader}
    (h : readThrough reader slices = .ok (result, before, after)) :
    (before.readEof : Id _) = .ok (result, after) := by
  unfold readThrough at h
  split at h
  · cases h
  · split at h
    · rename_i r a heof
      cases h
      exact heof
    · cases h

/-! ## The reader after an input it read to the end -/

section

open BSmtLib.Facts.Proofs.Reader.Consumer BSmtLib.Facts.Proofs.Reader.Lexes.Good
open BSmtLib.Facts.Proofs.Reader.Lexes.NoLayout BSmtLib.Facts.Proofs.Reader.Lexes.Told
open BSmtLib.Facts.Proofs.Reader.Param.Failing BSmtLib.Facts.Proofs.Reader.Param.Finish
open BSmtLib.Facts.Proofs.Reader.Param.General BSmtLib.Facts.Proofs.Reader.Param.Link
open BSmtLib.Facts.Proofs.Reader.Param.Final BSmtLib.Facts.Proofs.Reader.Param.Flagged
open BSmtLib.Facts.Proofs.Reader.Reader BSmtLib.Facts.Proofs.Reader.Lexes.Through
open BSmtLib.Facts.Proofs.Reader.Classify BSmtLib.Facts.Proofs.Reader.Session
open BSmtLib.Facts.Reader.Adapters
open BSmtLib.Facts.Lexer.Adapters (toVersion lexing)
open BSmtLib.Facts.Parser.Adapters.Run (unrestrictedPosture)
open BSmtLib.Facts.Proofs.Reader.Param.Run (FLexer)
open BSmtLib.Facts.Parser.Adapters.Run.Rejection (libraryParser libEnding)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection (rcv)

/-- The script reader over the recording handler, allowing every version, after an input it read
to the end: its adapter is reset and not told the version, and its lexer holds nothing and has
the fields that a lexer constructed with the version, which does not recover, has after the end
of the input. -/
theorem after_state (version : BSmtLibSpec.Lexicon.Version) (slices : List ByteList)
    {result : Option (Span.Located Unit)} {before after : RecReader}
    (h : readThrough (readerOf version) slices = .ok (result, before, after)) :
    (Internal.handler (Reader.Internal.lexer after)).parser =
        ScriptParser.new unrestrictedPosture ∧
      Parser.Adapter.ParseAdapter.Internal.versionSet
          (Internal.handler (Reader.Internal.lexer after)) = false ∧
      (∃ c₀, Internal.core (Reader.Internal.lexer after) = resetOf c₀ ∧
        c₀.initialVersion = toVersion version ∧ c₀.recovers = false) ∧
      Internal.held (Reader.Internal.lexer after) = none := by
  have hgood := lexing_good _ Facts.Lexer.correctWithConsumers version slices true
  have hcl := lexing_classified _ Facts.Lexer.correctWithConsumers version slices
  rw [lexing_flagged] at hgood hcl
  let a₀ : FLexer version :=
    Lexer.new { errored := false, version := toVersion version, spoiled := false, layout := false }
      (toVersion version)
  have htaken : (lexing flaggedOps (scriptConsumer version) version [] slices true).taken =
      ((flaggedOps.runInput a₀ true slices).run []).2 := rfl
  have hout : (lexing flaggedOps (scriptConsumer version) version [] slices true).outcome =
      ((flaggedOps.runInput a₀ true slices).run []).1.1 := rfl
  rw [htaken] at hgood
  have hI : InvF version a₀ (Lexer.new recordingAdapter (toVersion version)) [] := by
    refine ⟨rfl, trivial, rfl, rfl, rfl, [], rfl, ?_⟩
    unfold AdapterAtG
    rw [recRun_nil]
    exact ⟨toVersion_eq_libVersion version, rfl, by rw [toVersion_eq_libVersion]; rfl, rfl⟩
  have hR : Reach (scriptConsumer version) (toVersion version) (Internal.core a₀) := Reach.new
  have hnl := noLayout (scriptConsumer version) (scriptConsumer_concrete version)
      (toVersion version)
  obtain ⟨hnf, hcore, fl, items, hst, hat⟩ :=
    through_flagged hnl slices a₀ _ [] hI hR hgood (by rw [← readerOf_eq]; exact h)
  -- the run with the stand-in consumer did not fail, so it finished on tokens that stand for
  -- what a parser takes for a script
  obtain ⟨commands, htakes⟩ : ∃ commands, BSmtLibSpec.Parser.Properties.Takes version commands
      (((flaggedOps.runInput a₀ true slices).run []).2.map (rcv ∘ itemOf)) .finished := by
    unfold Classified at hcl
    rw [htaken, hout] at hcl
    rcases hcl with ⟨-, commands, htakes, -⟩ | ⟨hf, -⟩ | ⟨hf, -⟩ | ⟨hf, -⟩
    · exact ⟨commands, htakes⟩
    all_goals rw [hf] at hnf; cases hnf
  -- so the recording run over items standing for them finished
  have hlen : items.length =
      (((flaggedOps.runInput a₀ true slices).run []).2.map (rcv ∘ itemOf)).length := by
    simpa only [List.length_map] using congrArg List.length hst
  have hpar := BSmtLib.Facts.Parser.follows_the_traversal version commands _ .finished items
    htakes hst items.length (Nat.le_of_eq hlen)
  erw [List.take_of_length_le (Nat.le_refl _)] at hpar
  rw [ite_eq_right (by omega), parse_recRun] at hpar
  have hend := congrArg Prod.snd hpar
  unfold AdapterAtG at hat
  generalize recRun version items = R at hat hend
  obtain ⟨r, log⟩ := R
  rcases r with e | (_ | _)
  · dsimp only at hend
    revert hend
    unfold libEnding
    split <;> intro hend <;> (try (rename_i heq; cases heq)) <;> cases hend
  · cases hend
  · obtain ⟨-, hparser, hset⟩ := hat
    refine ⟨hparser, hset, ?_, (readEof_reset (readEof_of_readThrough h)).2⟩
    obtain ⟨⟨c₀, hc₀⟩, -⟩ := readEof_reset (readEof_of_readThrough h)
    obtain ⟨e1, -, e3, -⟩ := runInput_alikeF ZOps flaggedOps (AlikeLexers (scriptConsumer version))
      (fun a b => Internal.core a = Internal.core b) (slice_alikeF _) (eof_alikeF _)
      (fun _ _ h => h.2) (fun _ _ _ h => ⟨h.1, rfl⟩) (fun _ _ h => h.1) true slices
      (ZOps.new (scriptConsumer version) {} (toVersion version)) a₀ [] ⟨rfl, rfl⟩
    have hnz : ((ZOps.runInput (ZOps.new (scriptConsumer version) {} (toVersion version)) true
        slices).run []).1.1.isFailed = false := by rw [e1]; exact hnf
    obtain ⟨hrec, hiv⟩ := fields_afterC (scriptConsumer version) (toVersion version) slices hnz
    have hcz : resetOf c₀ = Internal.core ((ZOps.runInput (ZOps.new (scriptConsumer version) {}
        (toVersion version)) true slices).run []).1.2 :=
      hc₀.symm.trans (hcore.trans (e3 hnz).1.symm)
    exact ⟨c₀, hc₀, (congrArg LexerCore.initialVersion hcz).trans hiv,
      (congrArg LexerCore.recovers hcz).trans hrec⟩

end

end BSmtLib.Facts.Proofs.PublicApi.ReaderAfter
