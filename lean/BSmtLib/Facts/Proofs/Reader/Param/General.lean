import BSmtLib.Facts.Proofs.Reader.Param.Dom
import BSmtLib.Facts.Proofs.Reader.Param.Layout
import BSmtLib.Facts.Proofs.Reader.Param.Relate

/-!
# The parse adapter against the stand-in consumer, on any tokens

`Loop`, `Relate` and `Run` relate the parse adapter to `Flagged (scriptConsumer version)` while
the tokens taken stand for a start of a script. Here they are related on every run whose tokens
are `Good`: the stand-in consumer went on at every token but the last, and at every start of them
the parser's run depends only on what its items stand for (`Dom`). This covers runs that fail:
where the stand-in consumer fails at a token, the parse adapter fails at it too, at whitespace or
a comment because no parser takes it (`paLoop_layout`); unless the stand-in consumer was handed
whitespace or a comment, the adapter stands where the recording run over items standing for the
tokens taken leaves the parser (`AdapterAtG`), also where both fail.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.General

open BSmtLibSpec
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Parser (Input Parse)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM toHanded)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Bridge.Rejection
open BSmtLib.Facts.Parser.Adapters.Run.Rejection BSmtLib.Facts.Proofs.Parser.Cut
open BSmtLib.Facts.Proofs.Reader.Outcome BSmtLib.Facts.Proofs.Reader.Param.Adapter
open BSmtLib.Facts.Proofs.Reader.Param.Erase BSmtLib.Facts.Proofs.Reader.Param.Layout
open BSmtLib.Facts.Proofs.Reader.Param.Link BSmtLib.Facts.Proofs.Reader.Param.Loop
open BSmtLib.Facts.Reader.Adapters

/-- Where the adapter stands after the items, in the version, as `AdapterAt` says, the handler
told the version exactly where it took an item, and also after the recording run failed: its
handler holds the run's log with the events that are not calls left out. -/
def AdapterAtG (version : Lexicon.Version) (items : List LibItem) (v : Token.Version)
    (adapter : RecAdapter) : Prop :=
  match recRun version items with
  | (.ok (.inl (v', parser)), log) =>
    v' = v ∧ adapter.parser = parser ∧ startLog adapter v = calls log ∧
      adapter.versionSet = !items.isEmpty
  | (.ok (.inr _), log) => adapter.handler = calls log
  | (.error _, log) => adapter.handler = calls log

theorem map_libItem (taken : List Handed) :
    (taken.map libItem).map (rcv ∘ Subtype.val) = taken.map (rcv ∘ itemOf) := by
  simp [libItem, Function.comp_def]

/-- The recording run over one more item, read as the parser's run over the items. -/
theorem parse_snoc (version : Lexicon.Version) (items : List LibItem) (item : LibItem)
    {v : Token.Version} {parser : ScriptParser (List Event)} {log : List Event}
    (hrun : recRun version items = (.ok (.inl (v, parser)), log)) :
    libraryParser.parse version (items ++ [item]) =
      (((recAfter v parser item.val).run.run log).2.reverse,
        libEnding (match ((recAfter v parser item.val).run.run log).1 with
          | .ok (.inl _) => .ok none
          | .ok (.inr ()) => .ok (some ((), []))
          | .error e => .error e)) := by
  rw [parse_recRun, recRun_snoc version items item hrun]
  rcases (recAfter v parser item.val).run.run log with ⟨_ | (_ | _), log'⟩ <;> rfl

/-- One token among tokens whose run depends only on what they stand for: the stand-in
consumer's requests and the parser's ending at it are those of the recording run over the
adapter's items, and so are the calls. -/
theorem token_obs {version : Lexicon.Version} {taken : List Handed} {handed : Handed}
    (hdom : Dom version ((taken ++ [handed]).map (rcv ∘ itemOf))) {items : List LibItem}
    {item : LibItem} (hst : items.map (rcv ∘ Subtype.val) = taken.map (rcv ∘ itemOf))
    (hitem : rcv item.val = rcv (itemOf handed)) :
    Dom.Obs (libraryParser.parse version (items ++ [item])) =
      Dom.Obs (libraryParser.parse version ((taken ++ [handed]).map libItem)) := by
  refine Dom.obs_congr hdom ?_ (map_libItem _)
  simp [hst, hitem]

/-- The stand-in consumer's answer, as its parser's run ends. -/
theorem answer_eq (version : Lexicon.Version) (taken : List Handed) :
    (scriptConsumer version).answer taken =
      answerOf (taken.getLast?.map (·.type) = some .endOfFile)
        (libraryParser.parse version (taken.map libItem)).2 := rfl

/-- The stand-in consumer's answer where the parser's run failed: it fails. -/
theorem answerOf_error (atEnd : Bool) (e : Parser.ParseErrorCause Unit) :
    ∃ err, answerOf atEnd (libEnding (.error e)) = .fail err := by
  rcases e with k | h
  · cases k <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- The adapter's loop over a cursor whose next token is whitespace or a comment, from any parser:
it fails at that token, the cursor after it. -/
theorem paLoop_layout {b : Token.BatchTag} {cursor : Token.BatchCursor b} (h : cursor.HasNext)
    (parser : ScriptParser (List Event)) (handler : List Event)
    (hl : Input.ofSyntax (cursor.syntax (cursor.next h).1) = .layout) :
    ∃ e, ((paLoop parser cursor).run handler).1.1 = .error e ∧
      ((paLoop parser cursor).run handler).1.2.2 = (cursor.next h).2.val := by
  rw [paLoop_step h]
  obtain ⟨e, handler', ht⟩ := takeOne_layout parser cursor (cursor.next h).2.val (cursor.next h).1
    (cursor.next h).2.property handler hl
  rw [ht]
  exact ⟨e, rfl, rfl⟩

/-- Token by token, the adapter's loop and the adapter's consumer agree on tokens that are
`Good`, the consumer failing included: the same answer and the same cursor, and where the
consumer was not handed whitespace or a comment, the adapter where the recording run leaves the
parser. -/
theorem loop_agreeG {version : Lexicon.Version} {b : Token.BatchTag} :
    ∀ (n : Nat) (cursor : Token.BatchCursor b) (taken : List Handed) (items : List LibItem)
      (parser : ScriptParser (List Event)) (log : List Event), cursor.remaining < n →
      items.map (rcv ∘ Subtype.val) = taken.map (rcv ∘ itemOf) →
      recRun version items = (.ok (.inl (cursor.version, parser)), log) →
      (items ≠ [] ∨ cursor.HasNext) →
      Dom.Good version (ansRest version cursor taken).2 →
      Shape (ansRest version cursor taken).1.1 ((paLoop parser cursor).run (calls log)).1.1 ∧
      (ansRest version cursor taken).1.2 = ((paLoop parser cursor).run (calls log)).1.2.2 ∧
      (Flagged.isLayoutAnswer (ansRest version cursor taken).1.1 = false →
        ∃ items' : List LibItem,
          items'.map (rcv ∘ Subtype.val) = (ansRest version cursor taken).2.map (rcv ∘ itemOf) ∧
          AdapterAtG version items' (ansRest version cursor taken).1.2.version
            { handler := ((paLoop parser cursor).run (calls log)).2,
              parser := ((paLoop parser cursor).run (calls log)).1.2.1,
              versionSet :=
                ParseAdapter.versionSetAfter ((paLoop parser cursor).run (calls log)).1.1 })
  | 0, _, _, _, _, _, hn, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, cursor, taken, items, parser, log, hn, hst, hrun, hne, hgood => by
    by_cases h : cursor.HasNext
    · obtain ⟨more, hmore⟩ := ansRest_extends version (n + 1) cursor taken hn
      have hgood₀ := hgood
      rw [ansRest_step version h] at hgood ⊢
      cases hh : toHanded cursor (cursor.next h).1 with
      | none =>
        -- whitespace or a comment: both fail at it
        obtain ⟨e, he, hc⟩ := paLoop_layout h parser (calls log) (ofSyntax_layout cursor _ hh)
        rw [he, hc]
        exact ⟨trivial, rfl, fun herr => by simp [Flagged.isLayoutAnswer] at herr⟩
      | some handed =>
        rw [paLoop_step h]
        simp only [hh] at hgood ⊢
        have hrecv :
            Bridge.received (Input.ofSyntax ((cursor.next h).2.val.syntax (cursor.next h).1)) =
              some (rcv (itemOf handed)) := received_ofSyntax cursor (cursor.next h).1 hh
        obtain ⟨item, hitemdef⟩ : ∃ item : LibItem,
            item.val = Input.ofSyntax ((cursor.next h).2.val.syntax (cursor.next h).1) :=
          ⟨⟨Input.ofSyntax ((cursor.next h).2.val.syntax (cursor.next h).1),
            fun h' => by cases hrecv.symm.trans h'⟩, rfl⟩
        have hitem : rcv item.val = rcv (itemOf handed) := by
          rw [hitemdef]; simp only [rcv, hrecv, Option.getD_some]
        have htake := takeOne_rec parser cursor (cursor.next h).2.val (cursor.next h).1
          (cursor.next h).2.property log hrecv
        rw [← hitemdef] at htake
        change _ = paOf parser (cursor.next h).2.val
          ((recAfter cursor.version parser item.val).run.run log) at htake
        have hver : ∀ {v' : Token.Version} {p' : ScriptParser (List Event)} {log' : List Event},
            (recAfter cursor.version parser item.val).run.run log = (.ok (.inl (v', p')), log') →
            v' = match Parser.Adapters.Run.switchOf log'.reverse with
              | some switched => toVersion switched
              | none => cursor.version := fun hR =>
          recAfter_version _ _ (received := rcv (itemOf handed))
            (by rw [hitemdef]; exact hrecv) _ hR
        have hst' : (items ++ [item]).map (rcv ∘ Subtype.val) =
            (taken ++ [handed]).map (rcv ∘ itemOf) := by
          simp [hst, hitem]
        -- the tokens up to this one are good: the run depends only on what they stand for
        have hgood' : Dom.Good version (taken ++ [handed]) := by
          have hext : ∃ more, (ansRest version cursor taken).2 = taken ++ [handed] ++ more := by
            rw [ansRest_step version h]
            simp only [hh]
            cases (scriptConsumer version).answer (taken ++ [handed]) with
            | fail e => exact ⟨[], by simp⟩
            | «break» r => exact ⟨[], by simp⟩
            | «continue» =>
              dsimp only
              split
              · exact ⟨[], by simp⟩
              · exact ansRest_extends version (cursor.next h).2.val.remaining.succ
                  (cursor.next h).2.val (taken ++ [handed]) (Nat.lt_succ_self _)
          obtain ⟨more', hm⟩ := hext
          rw [hm] at hgood₀
          exact hgood₀.of_append
        have hdom : Dom version ((taken ++ [handed]).map (rcv ∘ itemOf)) := by
          have := hgood'.1 (taken ++ [handed]).length (Nat.le_refl _)
          rwa [List.take_length] at this
        have hobs := token_obs hdom hst hitem
        rw [parse_snoc version items item hrun] at hobs
        have hans := answer_eq version (taken ++ [handed])
        generalize hR : (recAfter cursor.version parser item.val).run.run log = R
          at htake hver hobs
        generalize (ParseAdapter.takeOne (H := List Event) (m := Id) parser cursor (cursor.next h).1
          (cursor.next h).2.val (cursor.next h).2.property).run (calls log) = T at htake ⊢
        obtain ⟨⟨after, ⟨later, hlater⟩⟩, H'⟩ := T
        obtain ⟨res, log'⟩ := R
        simp only [Dom.Obs, Prod.mk.injEq] at hobs
        obtain ⟨-, hending, hsw, hdi⟩ := hobs
        have hsw' : Parser.Adapters.Run.switchOf log'.reverse =
            (scriptConsumer version).switchTo (taken ++ [handed]) := hsw
        have hdi' : Parser.Adapters.Run.discardOf log'.reverse =
            (scriptConsumer version).discards (taken ++ [handed]) := hdi
        have hatEnd : (decide ((taken ++ [handed]).getLast?.map (·.type) = some .endOfFile)) =
            true → ((taken ++ [handed]).map (rcv ∘ itemOf)).getLast? = some .endOfInput := by
          intro hatend
          simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
            Option.map_some, Option.some.injEq, decide_eq_true_eq] at hatend
          simp only [List.map_append, List.map_cons, List.map_nil, List.getLast?_append,
            List.getLast?_singleton, Option.some_or, Function.comp_apply, Option.some.injEq]
          exact (rcv_itemOf_endOfInput_iff handed).mpr hatend
        cases hcase : (scriptConsumer version).answer (taken ++ [handed]) with
        | fail e =>
          simp only [hcase] at hgood ⊢
          -- the parser's run did not go on: it failed, as the end of the input is never
          -- waited at
          have hres : ∃ err, res = .error err := by
            rcases res with err | (⟨v', p'⟩ | u)
            · exact ⟨err, rfl⟩
            · exfalso
              have hw : (libraryParser.parse version ((taken ++ [handed]).map libItem)).2 =
                  .waiting := by rw [← hending]; rfl
              rw [hans, hw] at hcase
              simp only [answerOf] at hcase
              split at hcase
              · rename_i hatend
                exact Dom.parse_endOfInput hdom (hatEnd hatend) (map_libItem _) hw
              · cases hcase
            · exfalso
              have hf : (libraryParser.parse version ((taken ++ [handed]).map libItem)).2 =
                  .finished := by rw [← hending]; rfl
              rw [hans, hf] at hcase
              cases hcase
          obtain ⟨err, rfl⟩ := hres
          simp only [paOf] at htake
          simp only [Prod.mk.injEq] at htake
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := htake
          refine ⟨trivial, by rw [← hsw', ← hdi'], fun _ => ⟨items ++ [item], hst', ?_⟩⟩
          unfold AdapterAtG
          rw [recRun_snoc version items item hrun, hR]
        | «break» r =>
          simp only [hcase] at hgood ⊢
          have hres : ∃ u, res = .ok (.inr u) := by
            rcases res with err | (⟨v', p'⟩ | u)
            · exfalso
              have he : (libraryParser.parse version ((taken ++ [handed]).map libItem)).2 =
                  libEnding (.error err) := by rw [← hending]
              obtain ⟨err', herr'⟩ := answerOf_error
                (decide ((taken ++ [handed]).getLast?.map (·.type) = some .endOfFile)) err
              rw [hans, he, herr'] at hcase
              cases hcase
            · exfalso
              have hw : (libraryParser.parse version ((taken ++ [handed]).map libItem)).2 =
                  .waiting := by rw [← hending]; rfl
              rw [hans, hw] at hcase
              simp only [answerOf] at hcase
              split at hcase <;> cases hcase
            · exact ⟨u, rfl⟩
          obtain ⟨u, rfl⟩ := hres
          simp only [paOf] at htake
          simp only [Prod.mk.injEq] at htake
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := htake
          refine ⟨trivial, by rw [← hsw', ← hdi'], fun _ => ⟨items ++ [item], hst', ?_⟩⟩
          unfold AdapterAtG
          rw [recRun_snoc version items item hrun, hR]
        | «continue» =>
          simp only [hcase] at hgood ⊢
          have hres : ∃ v' p', res = .ok (.inl (v', p')) := by
            rcases res with err | (⟨v', p'⟩ | u)
            · exfalso
              have he : (libraryParser.parse version ((taken ++ [handed]).map libItem)).2 =
                  libEnding (.error err) := by rw [← hending]
              obtain ⟨err', herr'⟩ := answerOf_error
                (decide ((taken ++ [handed]).getLast?.map (·.type) = some .endOfFile)) err
              rw [hans, he, herr'] at hcase
              cases hcase
            · exact ⟨v', p', rfl⟩
            · exfalso
              have hf : (libraryParser.parse version ((taken ++ [handed]).map libItem)).2 =
                  .finished := by rw [← hending]; rfl
              rw [hans, hf] at hcase
              cases hcase
          obtain ⟨v', p', rfl⟩ := hres
          have hv' := hver rfl
          simp only [paOf] at htake
          rw [hsw', hdi'] at htake
          split
          · rename_i hreq
            simp only [hreq, ite_true, Prod.mk.injEq] at htake
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := htake
            refine ⟨trivial, rfl, fun _ => ⟨items ++ [item], hst', ?_⟩⟩
            unfold AdapterAtG
            rw [recRun_snoc version items item hrun, hR]
            refine ⟨?_, rfl, rfl, by simp [ParseAdapter.versionSetAfter]⟩
            rw [hv', applyRequests_version, ← hsw']
            rfl
          · rename_i hreq
            simp only [hreq, Bool.false_eq_true, ite_false, Prod.mk.injEq] at htake
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := htake
            have hsw'' : Parser.Adapters.Run.switchOf log'.reverse = none := by
              rw [hsw']
              cases hc : (scriptConsumer version).switchTo (taken ++ [handed]) with
              | none => rfl
              | some _ => simp [hc] at hreq
            rw [ite_eq_right hreq] at hgood
            rw [hsw''] at hv'
            exact loop_agreeG n (cursor.next h).2.val (taken ++ [handed]) (items ++ [item])
              p' log' (Nat.lt_of_lt_of_le ((cursor.next h).2.property.remaining_lt)
                (Nat.le_of_lt_succ hn))
              hst' (by rw [recRun_snoc version items item hrun, hR, hv']; rfl)
              (.inl (by simp)) hgood
    · unfold ansRest
      rw [dite_eq_right_of_eq_false (eq_false h), paLoop, dite_eq_right_of_eq_false (eq_false h)]
      refine ⟨trivial, rfl, fun _ => ⟨items, hst, ?_⟩⟩
      unfold AdapterAtG
      rw [hrun]
      have hne' : items ≠ [] := hne.resolve_right h
      refine ⟨rfl, rfl, rfl, ?_⟩
      cases items with
      | nil => exact absurd rfl hne'
      | cons _ _ => rfl

end BSmtLib.Facts.Proofs.Reader.Param.General
