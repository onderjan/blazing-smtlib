module

public import BSmtLib.Facts.Proofs.Reader.Handler.Drive
public import BSmtLib.Facts.Proofs.Reader.Param.Loop
public import BSmtLib.Facts.Proofs.Parser.Blank.Loop
public import BSmtLib.Facts.Proofs.Parser.Blank.Recording
import all BSmtLib.Parser.Adapter
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor
import all BSmtLib.Facts.Proofs.Reader.Param.Stop

@[expose] public section

/-!
# A call of the parse adapter with any handler that never fails

The parse adapter of the reader proofs (`Param.Stop`) over a handler whose calls never fail, and
the adapter's consumer `Answering (scriptConsumer version)`, take the same tokens of a cursor and
stop at the same one with the same answer and the same cursor, while the tokens taken stand for a
start of the script (`loop_agree`). The handler then holds what the script parser's driver over
the items taken leaves it with (`Drive.drive`, `At`). The recording run over the same items
(`Link.recRun`) goes along as a witness: its parser is the handler's with the values blanked
(`Blank`), and the facts about it (`Link.script_token`) say where the adapter stops.
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Reader.Handler.Loop

open BSmtLib.Facts.Proofs.Reader (Param.Flagged.isError Param.Link.Viable)

open BSmtLibSpec BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Handler
open BSmtLib.Parser (Parse ParseError ParseErrorCause)
open BSmtLib.Lexer.Cursor.LexerCursor.Internal (remaining)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Parser.Adapter (ParseAdapter)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM toHanded)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Bridge.Rejection
open BSmtLib.Facts.Parser.Adapters.Run BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Facts.Proofs.Parser.Cut
open BSmtLib.Facts.Proofs.Reader.Param.Adapter BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Facts.Proofs.Reader.Param.Erase BSmtLib.Facts.Proofs.Reader.Param.Link
open BSmtLib.Facts.Proofs.Reader.Param.Loop
open BSmtLib.Facts.Proofs.Reader.Param (Stop.takeOne)
open BSmtLib.Facts.Proofs.Reader.Handler.Drive
open BSmtLib.Facts.Proofs.Parser.Blank.Basic BSmtLib.Facts.Proofs.Parser.Blank.States
open BSmtLib.Facts.Proofs.Parser.Blank.Loop (AfterB takeOne_blank)
open BSmtLib.Facts.Reader.Adapters
open BSmtLib.Parser.Internal (After)

variable {H : Type} [CommandHandler H Id]

/-! ## The adapter's loop over a cursor -/

/-- The loop of the reader proofs' adapter over the tokens of a cursor, from the parser: each
token taken in turn, until the cursor has none or the handover stops. -/
def loop {b : Token.BatchTag} (parser : ScriptParser H) (cursor : LexerCursor b) :
    StateT H Id
      (Except (ParseError (Handler.Error H)) (ControlFlow Unit) × ScriptParser H ×
        LexerCursor b) :=
  if h : cursor.HasNext then
    match cursor.next h with
    | (token, ⟨next, consumed⟩) => do
      match ← Stop.takeOne (m := Id) parser cursor token next consumed with
      | (.goOn parser', ⟨later, _taken⟩) => loop parser' later
      | (.stop answer parser', ⟨later, _⟩) => return (answer, parser', later)
  else return (.ok .continue, parser, cursor)
termination_by remaining cursor
decreasing_by exact Lexer.Cursor.LexerCursor.Consumed.remaining_lt _taken

theorem loop_step {b : Token.BatchTag} {cursor : LexerCursor b} (h : cursor.HasNext)
    (parser : ScriptParser H) (handler : H) :
    (loop parser cursor).run handler =
      match (Stop.takeOne (m := Id) parser cursor (cursor.next h).1
          (cursor.next h).2.val (cursor.next h).2.property).run handler with
      | ((.goOn parser', ⟨later, _⟩), handler') => (loop parser' later).run handler'
      | ((.stop answer parser', ⟨later, _⟩), handler') => ((answer, parser', later), handler') := by
  conv => lhs; rw [loop]
  rw [dite_eq_left_of_eq_true (eq_true h)]
  generalize cursor.next _ = pr
  obtain ⟨token, next, consumed⟩ := pr
  simp only [StateT.run_bind]
  generalize (Stop.takeOne (m := Id) parser cursor token next consumed).run handler = t
  obtain ⟨⟨after, ⟨later, taken⟩⟩, handler'⟩ := t
  cases after <;> rfl

/-! ## Where the adapter stands -/

/-- The handler told the version, unless it was told the version of the input already. -/
def toldAt (adapter : ParseAdapter H (ScriptParser H)) (version : Version) : H :=
  if ParseAdapter.Internal.versionSet adapter then adapter.handler
  else ((Handler.setVersion (H := H) version).run adapter.handler).2

/-- The driver's run over the items of a script with the initial version, from the handler told
the version first. -/
def hRun (version : Lexicon.Version) (init : H) (items : List LibItem) :=
  (drive (Bridge.libVersion version) (ScriptParser.new unrestrictedPosture)
    (items.map Subtype.val)).run.run
    ((Handler.setVersion (H := H) (Bridge.libVersion version)).run init).2

/-- Where the adapter stands after the items, in the version: the driver's parser, and the
handler the driver leaves, as the handler the adapter's next loop begins with; after the end of
the script, the handler the driver leaves. The recording run over the items goes on in the same
version, its parser the driver's with the values blanked, or ends as the driver does. -/
def At (version : Lexicon.Version) (init : H) (items : List LibItem) (v : Version)
    (adapter : ParseAdapter H (ScriptParser H)) : Prop :=
  match hRun version init items, recRun version items with
  | (.ok (.inl (v', parser)), handler), (.ok (.inl (vr, pr)), _) =>
    v' = v ∧ vr = v ∧ adapter.parser = parser ∧ toldAt adapter v = handler ∧
      blank parser = blank pr
  | (.ok (.inr _), handler), (.ok (.inr _), _) => adapter.handler = handler
  | _, _ => False

/-! ## A token, on the two handlers -/

/-- What the parser did with a token with the handler and with the recording handler, both related
to what it did with the blank handler: the same, up to the values. -/
def AfterB2 : After (ScriptParser H) Unit (Handler.Error H) →
    After (ScriptParser (List Event)) Unit Unit → Prop
  | .goOn p, .goOn q => blank p = blank q
  | .stop a p, .stop a' q => blankAnswer a = blankAnswer a' ∧ blank p = blank q
  | _, _ => False

theorem afterB2 [NoFails H] {x : After (ScriptParser H) Unit (Handler.Error H)}
    {y : After (ScriptParser (List Event)) Unit Unit}
    {z : After (ScriptParser Shell) Unit Unit} (hx : AfterB x z) (hy : AfterB y z) :
    AfterB2 x y := by
  cases x <;> cases y <;> cases z <;> simp only [AfterB] at hx hy
  · exact hx.symm.trans hy
  · exact ⟨hx.1.symm.trans hy.1, hx.2.symm.trans hy.2⟩

theorem blankAnswer_flow {ε ε' : Type} {a : Except (ParseError ε) (ControlFlow Unit)}
    {f : ControlFlow Unit}
    (h : blankAnswer a = (blankAnswer (.ok f : Except (ParseError ε') (ControlFlow Unit)))) :
    a = .ok f := by
  cases a with
  | error e => cases h
  | ok g => cases h; rfl

/-- The driver's run over one more item. -/
theorem hRun_snoc (version : Lexicon.Version) (init : H) (items : List LibItem) (item : LibItem)
    {v : Version} {parser : ScriptParser H} {s : H}
    (h : hRun version init items = (.ok (.inl (v, parser)), s)) :
    hRun version init (items ++ [item]) =
      match (tokenStep v parser item.val).run.run s with
      | (.ok (.inl x), s') => (.ok (.inl x), s')
      | (.ok (.inr ()), s') => (.ok (.inr ((), [])), s')
      | (.error e, s') => (.error e, s') := by
  unfold hRun at h ⊢
  rw [List.map_append, drive_append]
  simp only [ExceptT.run_bind, StateT.run_bind, Drive.id_bind]
  rw [h]
  simp only [List.map_cons, List.map_nil, Drive.drive, ExceptT.run_bind, StateT.run_bind,
    Drive.id_bind]
  rcases (tokenStep v parser item.val).run.run s with ⟨_ | (_ | _), s'⟩ <;> rfl

/-! ## The loop -/

/-- Token by token, the adapter's loop over a handler that never fails and the adapter's consumer
agree while what is taken stands for a start of the script, and the handler is where the driver
over the items leaves it. -/
theorem loop_agree [NoFails H] {version : Lexicon.Version} {commands : List Tree.Command}
    (hscript : Script version commands) (init : H) {b : Token.BatchTag} :
    ∀ (n : Nat) (cursor : LexerCursor b) (taken : List Handed) (items : List LibItem)
      (pr : ScriptParser (List Event)) (log : List Event) (parser : ScriptParser H) (s : H),
      remaining cursor < n →
      items.map (rcv ∘ Subtype.val) = taken.map (rcv ∘ itemOf) →
      recRun version items = (.ok (.inl (cursor.version, pr)), log) →
      hRun version init items = (.ok (.inl (cursor.version, parser)), s) →
      blank parser = blank pr →
      Param.Flagged.isError (ansRest version cursor taken).1.1 = false →
      Param.Link.Viable commands (ansRest version cursor taken).2 →
      Shape (ansRest version cursor taken).1.1 ((loop parser cursor).run s).1.1 ∧
      (ansRest version cursor taken).1.2 = ((loop parser cursor).run s).1.2.2 ∧
      ∃ items' : List LibItem,
        items'.map (rcv ∘ Subtype.val) = (ansRest version cursor taken).2.map (rcv ∘ itemOf) ∧
        At version init items' (ansRest version cursor taken).1.2.version
          (ParseAdapter.Internal.mk ((loop parser cursor).run s).2
            ((loop parser cursor).run s).1.2.1
            (ParseAdapter.Internal.versionSetAfter ((loop parser cursor).run s).1.1) .new)
  | 0, _, _, _, _, _, _, _, hn, _, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, cursor, taken, items, pr, log, parser, s, hn, hst, hrun, hdrive, hb, herr, hvia => by
    by_cases h : cursor.HasNext
    · obtain ⟨more, hmore⟩ := ansRest_extends version (n + 1) cursor taken hn
      rw [ansRest_step version h] at herr hvia ⊢
      rw [loop_step h]
      cases hh : toHanded cursor (cursor.next h).1 with
      | none => simp only [hh, Param.Flagged.isError] at herr; cases herr
      | some handed =>
        simp only [hh] at herr hvia ⊢
        have hrecv :
            Bridge.received (Parser.Internal.Input.ofSyntax ((cursor.next h).2.val.syntax
                (cursor.next h).1)) =
              some (rcv (itemOf handed)) := received_ofSyntax cursor (cursor.next h).1 hh
        obtain ⟨item, hitemdef⟩ : ∃ item : LibItem,
            item.val = Parser.Internal.Input.ofSyntax ((cursor.next h).2.val.syntax
                (cursor.next h).1) :=
          ⟨⟨Parser.Internal.Input.ofSyntax ((cursor.next h).2.val.syntax (cursor.next h).1),
            fun h' => by cases hrecv.symm.trans h'⟩, rfl⟩
        have hitem : rcv item.val = rcv (itemOf handed) := by
          rw [hitemdef]; simp only [rcv, hrecv, Option.getD_some]
        have htake := takeOne_rec pr cursor (cursor.next h).2.val (cursor.next h).1
          (cursor.next h).2.property log hrecv
        rw [← hitemdef] at htake
        change _ = paOf pr (cursor.next h).2.val
          ((recAfter cursor.version pr item.val).run.run log) at htake
        have hver : ∀ {v' : Version} {p' : ScriptParser (List Event)} {log' : List Event},
            (recAfter cursor.version pr item.val).run.run log = (.ok (.inl (v', p')), log') →
            v' = match Parser.Adapters.Run.switchOf log'.reverse with
              | some switched => toVersion switched
              | none => cursor.version := fun hR =>
          recAfter_version _ _ (received := rcv (itemOf handed))
            (by rw [hitemdef]; exact hrecv) _ hR
        have hst' : (items ++ [item]).map (rcv ∘ Subtype.val) =
            (taken ++ [handed]).map (rcv ∘ itemOf) := by
          simp [hst, hitem]
        have hbt := takeOne_blank parser cursor (cursor.next h).1 (cursor.next h).2.val
          (cursor.next h).2.property s
        have hrt := takeOne_blank pr cursor (cursor.next h).1 (cursor.next h).2.val
          (cursor.next h).2.property (calls log)
        rw [← hb] at hrt
        have hdr := takeOne_drive parser cursor (cursor.next h).2.val (cursor.next h).1
          (cursor.next h).2.property s
        rw [← hitemdef] at hdr
        change (tokenStep cursor.version parser item.val).run.run s = _ at hdr
        have hsnoc := hRun_snoc version init items item hdrive
        rw [hdr] at hsnoc
        generalize hR : (recAfter cursor.version pr item.val).run.run log = R at htake hver
        generalize (Stop.takeOne (m := Id) pr cursor (cursor.next h).1
          (cursor.next h).2.val (cursor.next h).2.property).run (calls log) = T at htake hrt
        generalize (Stop.takeOne (m := Id) parser cursor (cursor.next h).1
          (cursor.next h).2.val (cursor.next h).2.property).run s = TB at hbt hsnoc ⊢
        generalize (Stop.takeOne (m := Id) (blank parser) cursor (cursor.next h).1
          (cursor.next h).2.val (cursor.next h).2.property).run {} = TS at hbt hrt
        obtain ⟨⟨after, ⟨later, hlater⟩⟩, H'⟩ := T
        obtain ⟨⟨afterB, ⟨laterB, hlaterB⟩⟩, HB⟩ := TB
        obtain ⟨⟨afterS, ⟨laterS, hlaterS⟩⟩, HS⟩ := TS
        obtain ⟨hab, hlb⟩ := hbt
        obtain ⟨har, hlr⟩ := hrt
        dsimp only at hab hlb har hlr hsnoc ⊢
        have h2 := afterB2 hab har
        subst hlb
        subst hlr
        obtain ⟨res, log'⟩ := R
        cases hans : (scriptConsumer version).answer (taken ++ [handed]) with
        | fail e => simp only [hans, Param.Flagged.isError] at herr; cases herr
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
          cases afterB with
          | goOn _ => exact absurd h2 id
          | stop a p =>
            obtain ⟨ha, -⟩ := h2
            have := blankAnswer_flow ha
            subst this
            refine ⟨trivial, by rw [← hsw, ← hdi], items ++ [item], hst', ?_⟩
            unfold At
            rw [hsnoc, recRun_snoc version items item hrun, hR]
            rfl
        | «continue» =>
          simp only [hans] at hvia herr ⊢
          have hvia' : Param.Link.Viable commands (taken ++ [handed]) := by
            split at hvia
            · exact hvia
            · obtain ⟨more', hmore'⟩ := ansRest_extends version
                (remaining (cursor.next h).2.val).succ
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
            cases afterB with
            | goOn _ => exact absurd h2 id
            | stop a pb =>
              obtain ⟨ha, hpb⟩ := h2
              have := blankAnswer_flow ha
              subst this
              refine ⟨trivial, rfl, items ++ [item], hst', ?_⟩
              unfold At
              rw [hsnoc, recRun_snoc version items item hrun, hR]
              refine ⟨rfl, ?_, rfl, rfl, hpb⟩
              rw [hv', applyRequests_version, ← hsw]
              rfl
          · rename_i hreq
            simp only [hreq, Bool.false_eq_true, ite_false, Prod.mk.injEq] at htake
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := htake
            cases afterB with
            | stop _ _ => exact absurd h2 id
            | goOn pb =>
              have hsw' : Parser.Adapters.Run.switchOf log'.reverse = none := by
                rw [hsw]
                cases hc : (scriptConsumer version).switchTo (taken ++ [handed]) with
                | none => rfl
                | some _ => simp [hc] at hreq
              rw [ite_eq_right hreq] at herr hvia
              rw [hsw'] at hv'
              exact loop_agree hscript init n (cursor.next h).2.val (taken ++ [handed])
                (items ++ [item]) p' log' pb HB
                (Nat.lt_of_lt_of_le ((cursor.next h).2.property.remaining_lt)
                  (Nat.le_of_lt_succ hn))
                hst' (by rw [recRun_snoc version items item hrun, hR, hv']; rfl)
                (by rw [hsnoc]; rfl) h2 herr hvia
    · unfold ansRest
      rw [dite_eq_right_of_eq_false (eq_false h), loop, dite_eq_right_of_eq_false (eq_false h)]
      refine ⟨trivial, rfl, items, hst, ?_⟩
      unfold At
      rw [hdrive, hrun]
      exact ⟨rfl, rfl, rfl, rfl, hb⟩

end BSmtLib.Facts.Proofs.Reader.Handler.Loop
