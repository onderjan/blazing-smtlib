module

public import BSmtLib.Facts.Proofs.Parser.Canon.Loop
public import BSmtLib.Facts.Proofs.Reader.Param.Link
import all BSmtLib.Parser
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# The recording run does not tell where an item's characters are stored

The driver's run of the script parser over one item, `Cut.recAfter`, from canonically equal
parsers on canonically equal items, makes the same log and gives canonically equal results
(`recAfter_canon`); so the recording run over items that stand for the same tokens gives the same
error, the same log and the same ending (`recRun_congr`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.RecCanon

open BSmtLib.Parser BSmtLib.Parser.Script
open BSmtLibSpec.Parser.Properties (Event recordingPoints recordingProducer)
open BSmtLib.Facts.Proofs.Parser.Quiet (RPM)
open BSmtLib.Facts.Proofs.Parser.Cut
open BSmtLib.Facts.Proofs.Parser.Canon.Basic BSmtLib.Facts.Proofs.Parser.Canon.States
open BSmtLib.Facts.Proofs.Parser.Canon.Simp BSmtLib.Facts.Proofs.Parser.Canon.Commands
open BSmtLib.Facts.Parser.Adapters BSmtLib.Facts.Parser.Adapters.Bridge
open BSmtLib.Facts.Parser.Adapters.Run

instance {α β : Type} [Canon α] [Canon β] : Canon (α ⊕ β) := ⟨Sum.map canon canon⟩

instance {ε α : Type} [Canon α] : Canon (Except ε α) := ⟨Except.map canon⟩

instance {ε α : Type} [Canon α] [CanonId α] : CanonId (Except ε α) :=
  ⟨fun x => by cases x <;> simp [Canon.canon, Except.map, CanonId.canon_id]⟩

theorem received_canon (i : Internal.Input) :
    Bridge.received (canonInput i) = Bridge.received i := by
  cases i <;> simp only [Bridge.received, canonInput, Canon.canon, canon_simps]

theorem CSim.map_canon {α : Type} [Canon α] (x : RPM α) : CSim x (canon <$> x) :=
  ⟨fun log => BSmtLib.Facts.Proofs.Parser.Canon.Loop.run_map canon x log⟩

/-- What the driver does after an item's processing, from a parser and an item, and from their
canonicalisations. -/
theorem afterProcessing_canon (version : Token.Version) (parser : ScriptParser (List Event))
    (token : Internal.Input) :
    CSim (afterProcessing recordingProducer version parser token)
      (afterProcessing recordingProducer version (canon parser) (canon token)) := by
  unfold afterProcessing
  refine CSim.bind (ScriptParser_step_canon (version := version) rfl rfl) fun f => ?_
  cases f with
  | more q => exact CSim.pure rfl
  | done r => exact CSim.pure rfl
  | switchVersion d resume =>
    dsimp only [Canon.canon, canonFlow]
    refine CSim.bind (CSim.same rfl) fun r => ?_
    rcases r with e | ⟨⟩
    · exact CSim.throw _
    · refine CSim.bind (CSim.map_canon resume) fun s => ?_
      cases s with
      | more q => exact CSim.pure rfl
      | done r => exact CSim.pure rfl
  | discardRest resume =>
    dsimp only [Canon.canon, canonFlow]
    refine CSim.bind (CSim.same rfl) fun _ => ?_
    refine CSim.bind (CSim.map_canon resume) fun s => ?_
    cases s with
    | more q => exact CSim.pure rfl
    | done r => exact CSim.pure rfl

/-- The driver's run over one item, from a parser and an item, and from their
canonicalisations. -/
theorem recAfter_canon (version : Token.Version) (parser : ScriptParser (List Event))
    (token : Internal.Input) :
    CSim (recAfter version parser token) (recAfter version (canon parser) (canon token)) := by
  unfold recAfter afterToken
  have ha : arriveAt (m := Id) recordingPoints (canon token) = arriveAt recordingPoints token := by
    unfold arriveAt; rw [show (canon token) = canonInput token from rfl, received_canon]
  have hp : processAt (m := Id) recordingPoints (canon token) =
      processAt recordingPoints token := by
    unfold processAt; rw [show (canon token) = canonInput token from rfl, received_canon]
  rw [ha, hp]
  refine CSim.bind (CSim.same rfl) fun _ => ?_
  refine CSim.bind (ScriptParser_arrive_canon rfl rfl) fun _ => ?_
  refine CSim.bind (CSim.same rfl) fun _ => ?_
  exact afterProcessing_canon version parser token

/-! ## Items that stand for the same token -/

theorem canonSlice_of_chars {s t : ByteSlice} (h : Bridge.chars s = Bridge.chars t) :
    canonSlice s = canonSlice t := by
  unfold Bridge.chars at h
  rw [BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes.byteArray_toList,
    BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes.byteArray_toList] at h
  have hd : s.toByteArray.data = t.toByteArray.data := Array.toList_inj.mp h
  unfold canonSlice
  have : s.toByteArray = t.toByteArray := by
    cases hs : s.toByteArray; cases ht : t.toByteArray
    rw [hs, ht] at hd
    simp only at hd
    rw [hd]
  rw [this]

theorem canonSymbol_of_symbol {s t : Plain.Symbol} (h : Bridge.symbol s = Bridge.symbol t) :
    canonSymbol s = canonSymbol t := by
  simp only [Bridge.symbol, BSmtLibSpec.Grammar.Tree.Symbol.mk.injEq] at h
  obtain ⟨hc, hq⟩ := h
  simp only [canonSymbol, canonSlice_of_chars hc, hq]

/-- Items that stand for the same token, other than whitespace and comments, are canonically
equal. -/
theorem canonInput_of_received {a b : Internal.Input}
    (h : Bridge.received a = Bridge.received b) (hn : Bridge.received a ≠ none) :
    canonInput a = canonInput b := by
  rcases a with _ | _ | c | s | k | w | _ | _ <;> rcases b with _ | _ | d | t | l | x | _ | _
  all_goals first
    | rfl
    | (simp only [Bridge.received, ne_eq, not_true_eq_false] at hn)
    | skip
  all_goals (try cases c) <;> (try cases d) <;>
    simp only [Bridge.received, Bridge.constant, BSmtLibSpec.Grammar.Tree.SpecConstant.token,
      Option.some.injEq, reduceCtorEq, BSmtLibSpec.Parser.Traversal.Received.token.injEq,
      BSmtLibSpec.Grammar.SyntaxToken.numeral.injEq, BSmtLibSpec.Grammar.SyntaxToken.decimal.injEq,
      BSmtLibSpec.Grammar.SyntaxToken.hexadecimal.injEq,
      BSmtLibSpec.Grammar.SyntaxToken.binary.injEq, BSmtLibSpec.Grammar.SyntaxToken.string.injEq,
      BSmtLibSpec.Grammar.SyntaxToken.symbol.injEq, BSmtLibSpec.Grammar.SyntaxToken.keyword.injEq,
      BSmtLibSpec.Grammar.SyntaxToken.reserved.injEq] at h ⊢
  all_goals first
    | simp only [canonInput, Canon.canon, canonConstant, canonSlice_of_chars h]
    | simp only [canonInput, Canon.canon, canonSymbol_of_symbol h]
    | exact congrArg
        (fun s => Internal.Input.keyword (BSmtLib.Plain.Keyword.Internal.newUnchecked s))
        (canonSlice_of_chars h)
    | rw [BSmtLib.Facts.Proofs.Parser.Reserved.Bridge.reserved_injective h]

/-! ## The recording run -/

open BSmtLib.Facts.Proofs.Parser.Rejection.Script (driveScript)

/-- The script parser's recording run over items, from a parser, and over their
canonicalisations from its canonicalisation. -/
theorem driveScript_canon : ∀ (items : List Internal.Input) (version : Token.Version)
    (parser : ScriptParser (List Event)),
    CSim (driveScript version parser items) (driveScript version (canon parser) (canon items))
  | [], version, parser => CSim.pure rfl
  | token :: tokens, version, parser => by
    show CSim (recAfter version parser token >>= _)
      (recAfter version (canon parser) (canon token) >>= _)
    refine CSim.bind (recAfter_canon version parser token) fun r => ?_
    rcases r with ⟨v', p'⟩ | ⟨⟩
    · exact driveScript_canon tokens v' p'
    · exact CSim.pure rfl

open BSmtLib.Facts.Parser.Adapters.Run.Rejection (LibItem) in
open BSmtLib.Facts.Parser.Adapters.Bridge.Rejection (rcv) in
/-- The recording run over items that stand for the same tokens: the same log and canonically
equal results, so the same error. -/
theorem recRun_congr (version : BSmtLibSpec.Lexicon.Version) {items₁ items₂ : List LibItem}
    (h : items₁.map (rcv ∘ Subtype.val) = items₂.map (rcv ∘ Subtype.val)) :
    (Link.recRun version items₁).1.map canon = (Link.recRun version items₂).1.map canon ∧
      (Link.recRun version items₁).2 = (Link.recRun version items₂).2 := by
  have hc : canon (items₁.map Subtype.val) = canon (items₂.map Subtype.val) := by
    show (items₁.map Subtype.val).map canonInput = (items₂.map Subtype.val).map canonInput
    have hl : items₁.length = items₂.length := by
      simpa only [List.length_map] using congrArg List.length h
    apply List.ext_getElem (by simp [hl])
    intro i hi₁ hi₂
    simp only [List.getElem_map]
    have hi : i < items₁.length := by simpa using hi₁
    have hrcv := congrArg (fun l => l[i]?) h
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (hl ▸ hi), Option.map_some, Function.comp_apply,
      Option.some.injEq] at hrcv
    have hn := items₁[i].property
    unfold rcv at hrcv
    cases ha : Bridge.received items₁[i].val with
    | none => exact absurd ha hn
    | some r₁ =>
      cases hb : Bridge.received items₂[i].val with
      | none => exact absurd hb items₂[i].property
      | some r₂ =>
        rw [ha, hb] at hrcv
        simp only [Option.getD_some] at hrcv
        exact canonInput_of_received (by rw [ha, hb, hrcv]) (by rw [ha]; nofun)
  have h₁ := driveScript_canon (items₁.map Subtype.val) (Bridge.libVersion version)
    (ScriptParser.new unrestrictedPosture)
  have h₂ := driveScript_canon (items₂.map Subtype.val) (Bridge.libVersion version)
    (ScriptParser.new unrestrictedPosture)
  rw [hc] at h₁
  exact BSmtLib.Facts.Proofs.Parser.Canon.Loop.CSim.agree h₁ h₂ _

end BSmtLib.Facts.Proofs.Reader.Param.RecCanon
