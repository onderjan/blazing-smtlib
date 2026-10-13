import BSmtLib.EndToEnd.Param.Link

/-!
# A call of the parse adapter against a call of the stand-in consumer

Token by token, the parse adapter's loop over a cursor (`paLoop`) and the adapter's consumer
`Answering (scriptConsumer version)` take the same tokens and stop at the same one with the same
answer and the same cursor, while the tokens taken stand for a start of the script
(`loop_agree`).
-/

namespace BSmtLib.EndToEnd.Param

open BSmtLib.Spec BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal
open BSmtLib.Spec.Lexer (Handed)
open BSmtLib.ParserProofs BSmtLib.ParserProofs.Rejection
open BSmtLib.Parser (Input ScriptParser Parse ParseAdapter)
open BSmtLib.Proofs.Adapter (toVersion Answering AnswerM toHanded)

/-- The adapter's consumer's loop from a cursor, which may have no token left. -/
def ansRest (version : Lexicon.Version) {b : BatchTag} (cursor : BatchCursor b)
    (taken : List Handed) :
    (Except (Option ScriptError) (ControlFlow Unit) × BatchCursor b) × List Handed :=
  if h : cursor.HasNext then
    ((((Answering.consume (scriptConsumer version) cursor h).run taken).1.1,
      ((Answering.consume (scriptConsumer version) cursor h).run taken).1.2.val),
      ((Answering.consume (scriptConsumer version) cursor h).run taken).2)
  else ((.ok .continue, cursor), taken)

/-- Where the adapter stands after the items, in the version: the recording run's parser, and its
log with the events that are not calls left out as the log the adapter's handler holds when its
next loop begins; after the end of the script, its log. -/
def AdapterAt (version : Lexicon.Version) (items : List LibItem) (v : Version)
    (adapter : RecAdapter) : Prop :=
  match recRun version items with
  | (.ok (.inl (v', parser)), log) =>
    v' = v ∧ adapter.parser = parser ∧ startLog adapter v = calls log
  | (.ok (.inr _), log) => adapter.handler = calls log
  | (.error _, _) => False

/-- The same answer: going on, finished or failed. -/
abbrev Shape {ε ε' α α' : Type} : Except ε (ControlFlow α) → Except ε' (ControlFlow α') → Prop :=
  ERel (fun _ _ => True) (FlowRel (fun _ _ => True))

theorem requests_eq (consumer : Spec.Lexer.Consumer) (taken : List Handed) {b : BatchTag}
    (cursor : BatchCursor b) :
    (Answering.requests consumer taken cursor).val =
      applyRequests cursor (consumer.switchTo taken) (consumer.discards taken) := by
  unfold Answering.requests Answering.switched applyRequests
  dsimp only
  cases hd : consumer.discards taken <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    split <;> rename_i hsw <;> simp only [hsw] <;>
    (try (split <;> rename_i hset <;> simp only [hset]))

theorem ansRest_step (version : Lexicon.Version) {b : BatchTag} {cursor : BatchCursor b}
    (h : cursor.HasNext) (taken : List Handed) :
    ansRest version cursor taken =
      match toHanded cursor (cursor.next h).1 with
      | none => ((.error none, (cursor.next h).2.val), taken)
      | some handed =>
        match (scriptConsumer version).answer (taken ++ [handed]) with
        | .fail e =>
          ((.error (some e), applyRequests (cursor.next h).2.val
            ((scriptConsumer version).switchTo (taken ++ [handed]))
            ((scriptConsumer version).discards (taken ++ [handed]))), taken ++ [handed])
        | .break r =>
          ((.ok (.break r), applyRequests (cursor.next h).2.val
            ((scriptConsumer version).switchTo (taken ++ [handed]))
            ((scriptConsumer version).discards (taken ++ [handed]))), taken ++ [handed])
        | .continue =>
          if ((scriptConsumer version).switchTo (taken ++ [handed])).isSome ||
              (scriptConsumer version).discards (taken ++ [handed]) then
            ((.ok .continue, applyRequests (cursor.next h).2.val
              ((scriptConsumer version).switchTo (taken ++ [handed]))
              ((scriptConsumer version).discards (taken ++ [handed]))), taken ++ [handed])
          else ansRest version (cursor.next h).2.val (taken ++ [handed]) := by
  conv => lhs; unfold ansRest
  rw [dite_eq_left_of_eq_true (eq_true h), Answering.consume]
  split
  rename_i token next consumed heq
  have hn : ∀ p, cursor.next p = (token, ⟨next, consumed⟩) := fun _ => heq
  simp only [hn]
  unfold Answering.entry
  cases hh : toHanded cursor token with
  | none => rfl
  | some handed =>
    simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind]
    cases hans : (scriptConsumer version).answer (taken ++ [handed]) with
    | fail e =>
      simp only [requests_eq, StateT.run_pure]
      rfl
    | «break» r =>
      simp only [requests_eq, StateT.run_pure]
      rfl
    | «continue» =>
      dsimp only
      split
      · simp only [requests_eq, StateT.run_pure]
        rfl
      · unfold ansRest
        split <;> rfl

theorem paLoop_step {b : BatchTag} {cursor : BatchCursor b} (h : cursor.HasNext)
    (parser : ScriptParser (List Event)) (handler : List Event) :
    (paLoop parser cursor).run handler =
      match (ParseAdapter.takeOne (H := List Event) (m := Id) parser cursor (cursor.next h).1
          (cursor.next h).2.val (cursor.next h).2.property).run handler with
      | ((.goOn parser', ⟨later, _⟩), handler') => (paLoop parser' later).run handler'
      | ((.stop answer parser', ⟨later, _⟩), handler') => ((answer, parser', later), handler') := by
  conv => lhs; rw [paLoop]
  rw [dite_eq_left_of_eq_true (eq_true h)]
  generalize cursor.next _ = pr
  obtain ⟨token, next, consumed⟩ := pr
  simp only [StateT.run_bind]
  generalize (ParseAdapter.takeOne (H := List Event) (m := Id) parser cursor token next
    consumed).run handler = t
  obtain ⟨⟨after, ⟨later, taken⟩⟩, handler'⟩ := t
  cases after <;> rfl

/-- The adapter's consumer only adds to the tokens taken. -/
theorem ansRest_extends (version : Lexicon.Version) {b : BatchTag} :
    ∀ (n : Nat) (cursor : BatchCursor b) (taken : List Handed), cursor.remaining < n →
      ∃ more, (ansRest version cursor taken).2 = taken ++ more
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, cursor, taken, hn => by
    by_cases h : cursor.HasNext
    · rw [ansRest_step version h]
      cases toHanded cursor (cursor.next h).1 with
      | none => exact ⟨[], by simp⟩
      | some handed =>
        dsimp only
        cases (scriptConsumer version).answer (taken ++ [handed]) with
        | fail e => exact ⟨[handed], rfl⟩
        | «break» r => exact ⟨[handed], rfl⟩
        | «continue» =>
          dsimp only
          split
          · exact ⟨[handed], rfl⟩
          · obtain ⟨more, hmore⟩ := ansRest_extends version n (cursor.next h).2.val
              (taken ++ [handed])
              (Nat.lt_of_lt_of_le ((cursor.next h).2.property.remaining_lt) (Nat.le_of_lt_succ hn))
            exact ⟨handed :: more, by rw [hmore]; simp⟩
    · unfold ansRest
      rw [dite_eq_right_of_eq_false (eq_false h)]
      exact ⟨[], by simp⟩

theorem applyRequests_version {b : BatchTag} (cursor : BatchCursor b)
    (switch : Option Lexicon.Version) (discard : Bool) :
    (applyRequests cursor switch discard).version =
      match switch with
      | some switched => toVersion switched
      | none => cursor.version := by
  unfold applyRequests
  cases switch with
  | none => cases discard <;> rfl
  | some v => cases discard <;> rfl

/-- Token by token, the adapter's loop and the adapter's consumer agree while what is taken stands
for a start of the script. -/
theorem loop_agree {version : Lexicon.Version} {commands : List Tree.Command}
    (hscript : Script version commands) {b : BatchTag} :
    ∀ (n : Nat) (cursor : BatchCursor b) (taken : List Handed) (items : List LibItem)
      (parser : ScriptParser (List Event)) (log : List Event), cursor.remaining < n →
      items.map (rcv ∘ Subtype.val) = taken.map (rcv ∘ itemOf) →
      recRun version items = (.ok (.inl (cursor.version, parser)), log) →
      isError (ansRest version cursor taken).1.1 = false →
      Viable commands (ansRest version cursor taken).2 →
      Shape (ansRest version cursor taken).1.1 ((paLoop parser cursor).run (calls log)).1.1 ∧
      (ansRest version cursor taken).1.2 = ((paLoop parser cursor).run (calls log)).1.2.2 ∧
      ∃ items' : List LibItem,
        items'.map (rcv ∘ Subtype.val) = (ansRest version cursor taken).2.map (rcv ∘ itemOf) ∧
        AdapterAt version items' (ansRest version cursor taken).1.2.version
          { handler := ((paLoop parser cursor).run (calls log)).2,
            parser := ((paLoop parser cursor).run (calls log)).1.2.1,
            versionSet :=
              ParseAdapter.versionSetAfter ((paLoop parser cursor).run (calls log)).1.1 }
  | 0, _, _, _, _, _, hn, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, cursor, taken, items, parser, log, hn, hst, hrun, herr, hvia => by
    by_cases h : cursor.HasNext
    · obtain ⟨more, hmore⟩ := ansRest_extends version (n + 1) cursor taken hn
      rw [ansRest_step version h] at herr hvia ⊢
      rw [paLoop_step h]
      cases hh : toHanded cursor (cursor.next h).1 with
      | none => simp only [hh, isError] at herr; cases herr
      | some handed =>
        simp only [hh] at herr hvia ⊢
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
        have hver : ∀ {v' : Version} {p' : ScriptParser (List Event)} {log' : List Event},
            (recAfter cursor.version parser item.val).run.run log = (.ok (.inl (v', p')), log') →
            v' = match ParserProofs.switchOf log'.reverse with
              | some switched => toVersion switched
              | none => cursor.version := fun hR =>
          recAfter_version _ _ (received := rcv (itemOf handed))
            (by rw [hitemdef]; exact hrecv) _ hR
        have hst' : (items ++ [item]).map (rcv ∘ Subtype.val) =
            (taken ++ [handed]).map (rcv ∘ itemOf) := by
          simp [hst, hitem]
        generalize hR : (recAfter cursor.version parser item.val).run.run log = R
          at htake hver
        generalize (ParseAdapter.takeOne (H := List Event) (m := Id) parser cursor (cursor.next h).1
          (cursor.next h).2.val (cursor.next h).2.property).run (calls log) = T at htake ⊢
        obtain ⟨⟨after, ⟨later, hlater⟩⟩, H'⟩ := T
        obtain ⟨res, log'⟩ := R
        cases hans : (scriptConsumer version).answer (taken ++ [handed]) with
        | fail e => simp only [hans, isError] at herr; cases herr
        | «break» r =>
          simp only [hans] at hvia ⊢
          obtain ⟨hsw, hdi, hlt, hge⟩ := script_token hscript hvia hst hitem hrun
          rw [hR] at hsw hdi hlt hge
          have hk : ¬ (taken ++ [handed]).length < (received commands).length := fun hk => by
            have := (hlt hk).1
            rw [hans] at this
            cases this
          obtain ⟨-, hres⟩ := hge hk
          simp only at hres
          subst hres
          simp only [paOf] at htake
          simp only [Prod.mk.injEq] at htake
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := htake
          refine ⟨trivial, by rw [← hsw, ← hdi], items ++ [item], hst', ?_⟩
          unfold AdapterAt
          rw [recRun_snoc version items item hrun, hR]
        | «continue» =>
          simp only [hans] at hvia herr ⊢
          have hvia' : Viable commands (taken ++ [handed]) := by
            split at hvia
            · exact hvia
            · obtain ⟨more', hmore'⟩ := ansRest_extends version (cursor.next h).2.val.remaining.succ
                (cursor.next h).2.val (taken ++ [handed]) (Nat.lt_succ_self _)
              rw [hmore'] at hvia
              exact hvia.of_append
          obtain ⟨hsw, hdi, hlt, hge⟩ := script_token hscript hvia' hst hitem hrun
          rw [hR] at hsw hdi hlt hge
          have hk : (taken ++ [handed]).length < (received commands).length := by
            refine Decidable.byContradiction fun hk => ?_
            have := (hge hk).1
            rw [hans] at this
            cases this
          obtain ⟨-, v', p', hres⟩ := hlt hk
          simp only at hres
          subst hres
          have hv' := hver rfl
          simp only [paOf] at htake
          rw [hsw, hdi] at htake
          split
          · rename_i hreq
            simp only [hreq, ite_true, Prod.mk.injEq] at htake
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := htake
            refine ⟨trivial, rfl, items ++ [item], hst', ?_⟩
            unfold AdapterAt
            rw [recRun_snoc version items item hrun, hR]
            refine ⟨?_, rfl, rfl⟩
            rw [hv', applyRequests_version, ← hsw]
            rfl
          · rename_i hreq
            simp only [hreq, Bool.false_eq_true, ite_false, Prod.mk.injEq] at htake
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := htake
            have hsw' : ParserProofs.switchOf log'.reverse = none := by
              rw [hsw]
              cases hc : (scriptConsumer version).switchTo (taken ++ [handed]) with
              | none => rfl
              | some _ => simp [hc] at hreq
            rw [ite_eq_right hreq] at herr hvia
            rw [hsw'] at hv'
            exact loop_agree hscript n (cursor.next h).2.val (taken ++ [handed]) (items ++ [item])
              p' log' (Nat.lt_of_lt_of_le ((cursor.next h).2.property.remaining_lt)
                (Nat.le_of_lt_succ hn))
              hst' (by rw [recRun_snoc version items item hrun, hR, hv']; rfl) herr hvia
    · unfold ansRest
      rw [dite_eq_right_of_eq_false (eq_false h), paLoop, dite_eq_right_of_eq_false (eq_false h)]
      refine ⟨trivial, rfl, items, hst, ?_⟩
      unfold AdapterAt
      rw [hrun]
      exact ⟨rfl, rfl, rfl⟩


/-- A call that does not fail takes a token. -/
theorem ansRest_grows (version : Lexicon.Version) {b : BatchTag} {cursor : BatchCursor b}
    (h : cursor.HasNext) (taken : List Handed)
    (herr : isError (ansRest version cursor taken).1.1 = false) :
    taken.length < (ansRest version cursor taken).2.length := by
  rw [ansRest_step version h] at herr ⊢
  cases hh : toHanded cursor (cursor.next h).1 with
  | none => simp only [hh, isError] at herr; cases herr
  | some handed =>
    simp only [hh] at herr ⊢
    cases (scriptConsumer version).answer (taken ++ [handed]) with
    | fail e => simp
    | «break» r => simp
    | «continue» =>
      dsimp only at herr ⊢
      split
      · simp
      · obtain ⟨more, hmore⟩ := ansRest_extends version (cursor.next h).2.val.remaining.succ
          (cursor.next h).2.val (taken ++ [handed]) (Nat.lt_succ_self _)
        rw [hmore]
        simp

end BSmtLib.EndToEnd.Param
