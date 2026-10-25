module

public import BSmtLib.Facts.Proofs.Reader.Param.Adapter
public import BSmtLib.Facts.Proofs.Reader.Param.UnaryCalls
public import BSmtLib.Facts.Proofs.Lexer.VNaive.Reserved
import all BSmtLib.Parser
import all BSmtLib.Lexicon.Value
import all BSmtLib.Token.Reserved
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor

@[expose] public section

/-!
# The parse adapter answers as the stand-in consumer on a script

Along the tokens of a valid script, the parse adapter with the recording handler and the script
parser answers every call as `Flagged (scriptConsumer version)` does, and gives back the same
cursor: both read the same recording run of the parser, the stand-in consumer on the tokens'
items as the spec reads them, the adapter on its cursor's items, and the parser's properties
(`Facts.Parser.follows_the_traversal`) say that the two runs make the same events and end alike.
-/

open BSmtLib.Lexer.Cursor (LexerCursor LexerToken)

namespace BSmtLib.Facts.Proofs.Reader.Param.Link

open BSmtLibSpec BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Parser (Parse)
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Facts.Lexer.Adapters (toVersion Answering AnswerM toHanded)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Bridge.Rejection
open BSmtLib.Facts.Parser.Adapters.Run BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Facts.Proofs.Parser.Cut BSmtLib.Facts.Proofs.Parser.Rejection.Lexical
open BSmtLib.Facts.Proofs.Parser.Rejection.Library BSmtLib.Facts.Proofs.Parser.Rejection.Script
open BSmtLib.Facts.Proofs.Parser.Reserved BSmtLib.Facts.Proofs.Parser.Trace
open BSmtLib.Facts.Proofs.Reader.Consumer BSmtLib.Facts.Reader.Adapters BSmtLib.Lexicon.Value

/-- The recording run on items that stand for a start of what a parser takes: the traversal's
events before the next item, and waiting, or at the end, ending as what it takes does. -/
theorem parse_items {version : Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes version commands taken ending)
    {items : List LibItem} (hst : items.map (rcv ∘ Subtype.val) = taken.take items.length)
    (hlen : items.length ≤ taken.length) :
    libraryParser.parse version items =
      (eventsBefore items.length (record version commands),
        if items.length < taken.length then .waiting else ending) := by
  have hof := takes_ofVersion htakes
  obtain ⟨rest, hrest⟩ := items_for (taken.drop items.length) fun i r hr => by
    rw [List.getElem?_drop] at hr
    exact inputOf_isSome (hof _ r hr)
  have hall : (items ++ rest : List LibItem).map (rcv ∘ Subtype.val) = taken := by
    rw [List.map_append, hrest, hst, List.take_append_drop]
  have := library_follows version commands taken ending (items ++ rest) htakes hall
    items.length hlen
  have heq : (items ++ rest : List LibItem).take items.length = items := by
    rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  erw [heq] at this
  exact this

/-! ## The adapter's item for a token, and the spec's -/

theorem toByteSlice_beq_slice (a : ByteArray) (s : ByteSlice) (h : (a.toByteSlice == s) = true) :
    a.data.toList = s.toByteArray.toList := by
  change ByteSlice.beq _ _ = true at h
  unfold ByteSlice.beq at h
  rw [Lexer.Simulation.Bytes.toByteArray_toByteSlice] at h
  change (a.data == s.toByteArray.data) = true at h
  rw [beq_iff_eq] at h
  rw [Lexer.Simulation.Bytes.byteArray_toList, h]

/-- The table of reserved words holds each word with its bytes. -/
theorem reservedTable_bytes : ∀ e ∈ Token.Reserved.Internal.reservedTable.toList,
    e.1.size = 0 ∨ e.1.data.toList = Bridge.reserved e.2.1 := by
  decide +kernel

/-- A reserved word the library's lookup finds is the one the spec's bytes decode to. -/
theorem fromBytes_decode {s : ByteSlice} {v : Version} {w : Token.Reserved}
    (h : Token.Reserved.fromBytes? s v = some w) :
    decodeReserved (Lexer.Adapters.toContent s) = some w := by
  by_cases h0 : s.size = 0
  · simp [Token.Reserved.fromBytes?, h0] at h
  · rw [Lexer.VNaive.Reserved.fromBytes_eq _ _ h0] at h
    have hmem := Lexer.VNaive.Reserved.getElem!_mem Token.Reserved.Internal.reservedTable
      (Lexer.VNaive.Reserved.slotOf s)
    generalize Token.Reserved.Internal.reservedTable[Lexer.VNaive.Reserved.slotOf s]! = e
      at h hmem
    obtain ⟨word, r, since⟩ := e
    simp only at h
    split at h
    · rename_i hc
      cases h
      have hbeq : (word.toByteSlice == s) = true := by
        simp only [Bool.and_eq_true] at hc
        exact hc.1
      have hbytes := toByteSlice_beq_slice word s hbeq
      have hne : word.size ≠ 0 := by
        intro hz
        apply h0
        rw [← Lexer.Simulation.Bytes.size_toByteArray,
          show s.toByteArray.size = s.toByteArray.toList.length by
            rw [Lexer.Simulation.Bytes.byteArray_toList, Array.length_toList]; rfl,
          ← hbytes, Array.length_toList]
        exact hz
      rcases hmem with hmem | hmem
      · rcases reservedTable_bytes _ hmem with hz | hw
        · exact absurd hz hne
        · show decodeReserved s.toByteArray.toList = some w
          rw [← hbytes, hw]
          exact decodeReserved_reserved w
      · have hw : word = default := congrArg Prod.fst hmem
        exact absurd (by rw [hw]; rfl) hne
    · cases h

/-- The parse adapter's item for a token stands for what the spec's form of the token stands
for. -/
theorem received_ofSyntax {b : Token.BatchTag} (cursor : LexerCursor b) (token : LexerToken b)
    {handed : Handed} (h : toHanded cursor token = some handed) :
    Bridge.received (Parser.Internal.Input.ofSyntax (cursor.syntax token)) = some (rcv
        (itemOf handed)) := by
  unfold toHanded at h
  simp only [Lexer.Cursor.LexerCursor.«syntax», Token.fromLexerToken] at h ⊢
  generalize cursor.category token = category at h ⊢
  generalize cursor.content token = content at h ⊢
  have hc : Bridge.chars (bytesOf (Lexer.Adapters.toContent content)) =
      Bridge.chars content := chars_bytesOf _
  cases category <;> simp only [Lexer.Adapters.toTokenType, Option.map_none,
    Option.map_some, reduceCtorEq, Option.some.injEq] at h <;> subst h
  case unquotedSymbol =>
    cases hw : Token.Reserved.fromBytes? content cursor.version with
    | none =>
      simp only [Token.Internal.fromParts, hw, Parser.Internal.Input.ofSyntax, itemOf,
        Lexer.Adapters.toReservedKind, Bridge.received, rcv, Option.getD_some,
        Bridge.symbol, Symbol.asSlice, Symbol.isQuoted, Symbol.Internal.newUnchecked,
        hc]
    | some word =>
      simp only [Token.Internal.fromParts, hw, Parser.Internal.Input.ofSyntax, itemOf,
        Lexer.Adapters.toReservedKind, fromBytes_decode hw, Bridge.received, rcv,
        Option.getD_some]
  all_goals simp only [Token.Internal.fromParts, Parser.Internal.Input.ofSyntax, itemOf,
      Bridge.received, rcv,
    Option.getD_some, Bridge.constant, Bridge.keyword, Bridge.symbol, Numeral.asSlice,
    Numeral.Internal.newUnchecked, Decimal.asSlice, Decimal.Internal.newUnchecked,
        HexDigits.asSlice,
    HexDigits.Internal.newUnchecked, BinDigits.asSlice, BinDigits.Internal.newUnchecked,
    StringContent.asSlice, StringContent.Internal.newUnchecked, Keyword.asSlice,
    Keyword.Internal.newUnchecked, Symbol.asSlice, Symbol.isQuoted,
    Symbol.Internal.newUnchecked, hc]

/-! ## The recording run over the adapter's items -/

theorem toVersion_eq_libVersion (version : Lexicon.Version) :
    toVersion version = Bridge.libVersion version := by
  cases version <;> rfl

/-- The recording run of the script parser over items, from the start of a script. -/
def recRun (version : Lexicon.Version) (items : List LibItem) :=
  (driveScript (Bridge.libVersion version) (ScriptParser.new unrestrictedPosture)
    (items.map Subtype.val)).run.run
    (startEvents (Bridge.libVersion version))

/-- The recording parser's run, by the recording run with its state. -/
theorem parse_recRun (version : Lexicon.Version) (items : List LibItem) :
    libraryParser.parse version items =
      ((recRun version items).2.reverse,
        libEnding (match (recRun version items).1 with
          | .ok (.inl _) => .ok none
          | .ok (.inr result) => .ok (some result)
          | .error e => .error e)) := by
  simp only [libraryParser, recRun, driveInput_run]
  rw [driveParse_run]
  rcases (driveScript (Bridge.libVersion version) (ScriptParser.new unrestrictedPosture)
    (items.map Subtype.val)).run.run (startEvents (Bridge.libVersion version)) with
    ⟨_ | _ | _, e⟩ <;> rfl

/-- The recording run over one more item, from where the run over the items goes on. -/
theorem recRun_snoc (version : Lexicon.Version) (items : List LibItem) (item : LibItem)
    {v : Version} {parser : ScriptParser (List Event)} {log : List Event}
    (h : recRun version items = (.ok (.inl (v, parser)), log)) :
    recRun version (items ++ [item]) =
      match (recAfter v parser item.val).run.run log with
      | (.ok (.inl x), log') => (.ok (.inl x), log')
      | (.ok (.inr ()), log') => (.ok (.inr ((), [])), log')
      | (.error e, log') => (.error e, log') := by
  unfold recRun at h ⊢
  rw [List.map_append, driveScript_append, run_bind_split, h]
  simp only [List.map_cons, List.map_nil, driveScript]
  rw [run_bind_split]
  rcases (recAfter v parser item.val).run.run log with ⟨_ | (_ | _), log'⟩ <;> rfl

/-! ## A token of the script, on both sides -/

/-- The tokens taken stand for a start of what a parser receives for the commands. -/
def Viable (commands : List Tree.Command) (taken : List Handed) : Prop :=
  taken.length ≤ (received commands).length ∧
    taken.map (rcv ∘ itemOf) = (received commands).take taken.length

theorem Viable.of_append {commands : List Tree.Command} {taken more : List Handed}
    (h : Viable commands (taken ++ more)) : Viable commands taken := by
  obtain ⟨hlen, hst⟩ := h
  simp only [List.length_append, List.map_append] at hlen hst
  refine ⟨by omega, ?_⟩
  have := congrArg (List.take taken.length) hst
  rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
    List.take_take, Nat.min_eq_left (by omega)] at this
  exact this

/-- One token of a script: the stand-in consumer's answer and requests at it, and how the
recording run over the adapter's items goes on from it. -/
theorem script_token {version : Lexicon.Version} {commands : List Tree.Command}
    (hscript : Script version commands) {taken : List Handed} {handed : Handed}
    (hviable : Viable commands (taken ++ [handed])) {items : List LibItem} {item : LibItem}
    (hst : items.map (rcv ∘ Subtype.val) = taken.map (rcv ∘ itemOf))
    (hitem : rcv item.val = rcv (itemOf handed))
    {v : Version} {parser : ScriptParser (List Event)} {log : List Event}
    (hrun : recRun version items = (.ok (.inl (v, parser)), log)) :
    Parser.Adapters.Run.switchOf ((recAfter v parser item.val).run.run log).2.reverse =
        (scriptConsumer version).switchTo (taken ++ [handed]) ∧
      Parser.Adapters.Run.discardOf ((recAfter v parser item.val).run.run log).2.reverse =
        (scriptConsumer version).discards (taken ++ [handed]) ∧
      ((taken ++ [handed]).length < (received commands).length →
        (scriptConsumer version).answer (taken ++ [handed]) = .continue ∧
        ∃ v' parser', ((recAfter v parser item.val).run.run log).1 = .ok (.inl (v', parser'))) ∧
      (¬ (taken ++ [handed]).length < (received commands).length →
        (scriptConsumer version).answer (taken ++ [handed]) = .break () ∧
        ((recAfter v parser item.val).run.run log).1 = .ok (.inr ())) := by
  have htakes := takes_of_script hscript
  obtain ⟨hlen, hst'⟩ := hviable
  have hst'' : (items ++ [item]).map (rcv ∘ Subtype.val) =
      (received commands).take (items ++ [item]).length := by
    have hl : (items ++ [item]).length = (taken ++ [handed]).length := by
      have := congrArg List.length hst
      simp only [List.length_map] at this
      simp [this]
    rw [hl, ← hst', List.map_append, List.map_append, hst]
    simp [hitem]
  have hlen' : (items ++ [item]).length = (taken ++ [handed]).length := by
    have := congrArg List.length hst
    simp only [List.length_map] at this
    simp [this]
  have hparse := parse_items htakes hst'' (by rw [hlen']; exact hlen)
  rw [parse_recRun, recRun_snoc version items item hrun, hlen'] at hparse
  obtain ⟨hsw, hdi⟩ := requests_takes hscript hst' (by simp) hlen
  have hrec := requests_record hscript ((taken ++ [handed]).length - 1)
    (by simp only [List.length_append, List.length_singleton] at hlen ⊢; omega)
  rw [show (taken ++ [handed]).length - 1 + 1 = (taken ++ [handed]).length by simp] at hrec
  have hans := answer_takes htakes hst' hlen
  generalize (recAfter v parser item.val).run.run log = R at hparse ⊢
  obtain ⟨res, log'⟩ := R
  have hevents : log'.reverse =
      eventsBefore (taken ++ [handed]).length (record version commands) := by
    rcases res with _ | (_ | _) <;> exact congrArg Prod.fst hparse
  refine ⟨by rw [hevents, hsw, hrec.1], by rw [hevents, hdi, hrec.2], fun hlt => ?_, fun hlt => ?_⟩
  · refine ⟨by rw [hans, ite_eq_left hlt]; rfl, ?_⟩
    have hend := congrArg Prod.snd hparse
    simp only [hlt, ite_true] at hend
    rcases res with e | (⟨v', p'⟩ | u)
    · rcases e with _ | (_ | _) | _ <;> simp [libEnding] at hend
    · exact ⟨v', p', rfl⟩
    · simp [libEnding] at hend
  · have hend := congrArg Prod.snd hparse
    simp only [hlt, ite_false] at hend
    refine ⟨by rw [hans, ite_eq_right hlt]; rfl, ?_⟩
    rcases res with e | (⟨v', p'⟩ | u)
    · rcases e with _ | (_ | _) | _ <;> simp [libEnding] at hend
    · simp [libEnding] at hend
    · rfl

end BSmtLib.Facts.Proofs.Reader.Param.Link
