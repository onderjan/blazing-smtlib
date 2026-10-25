module

public import BSmtLib.Facts.Proofs.Lexer.Consumers.Ready
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor
import all BSmtLib.Span
import all BSmtLib.Lexer.Error

@[expose] public section

/-!
# What the consumer does at an entry, as `Runs` states it

The session of the naive lexer that discards (`discardSession`, `discard_session`), and what
follows a break as `BSmtLibSpec.Lexer.AfterBreak` states it (`afterBreak_hold`). `event`: what the
consumer does at an entry that the naive lexer hands over at a boundary, holding no result, is
what `BSmtLibSpec.Lexer.Runs` states, given what the lexer does after it in each case.
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.VEvent

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.Consumers.Ready
open BSmtLib.Facts.Proofs.Lexer.Consumers.Stream BSmtLib.Facts.Proofs.Lexer.Consumers.VEnd
open BSmtLib.Facts.Proofs.Lexer.Consumers.VHold BSmtLib.Facts.Proofs.Lexer.Consumers.VSession
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps BSmtLib.Facts.Proofs.Lexer.VNaive.Facts
open BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix.Lexeme
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Lexer.Internal.VNaive

section
variable (consumer : BSmtLibSpec.Lexer.Consumer) (sv : BSmtLibSpec.Lexicon.Version)
    (input : List UInt8)
  (ended : Bool)

/-- The session of a lexer that discards from `s` under the version, holding the result `held`
(if `holding`), after the entries `taken`: before the end of the input, it stands discarding;
at the end, it returns the held result, or else hands the end-of-file token over, located at
`s`, at which a consumer that fails leaves the version it switches to. -/
def discardSession (version : Version) (s : Span.Location) (holding : Bool)
    (held : Option (Span.Located consumer.Result)) (taken : List Handed) :
    BSmtLibSpec.Lexer.Session consumer.Result consumer.Error :=
  if ended then
    if holding then
      match held with
      | some result => ⟨taken, .finished result.value (toLocation result.location), sv, none⟩
      | none => ⟨taken, .running, sv, none⟩
    else
      match consumer.answer (taken ++ [BSmtLibSpec.Lexer.endOfFileAt (toLocation s)]) with
      | .break result =>
        ⟨taken ++ [BSmtLibSpec.Lexer.endOfFileAt (toLocation s)], .finished result
            (toLocation s), sv,
          none⟩
      | .fail error =>
        ⟨taken ++ [BSmtLibSpec.Lexer.endOfFileAt (toLocation s)], .failed (.consumer error),
          fromVersion (((consumer.switchTo (taken ++ [BSmtLibSpec.Lexer.endOfFileAt
              (toLocation s)])).map
            toVersion).getD version),
          some (toLocation s)⟩
      | .continue => ⟨taken ++ [BSmtLibSpec.Lexer.endOfFileAt (toLocation s)], .running, sv, none⟩
  else
    ⟨taken, match held with
      | some result => .holding result.value (toLocation result.location)
      | none => .running, fromVersion version, some (toLocation s)⟩

/-- A lexer that discards from its location has the session `discardSession`. -/
theorem discard_session {s : Span.Location} {version : Version} {holding : Bool} (D : Core)
    (bytes : List UInt8) (held : Option (Span.Located consumer.Result)) (taken : List Handed)
    (ha : D.activity = .discarding s) (hv : D.version = version)
    (hl : D.location = s) (hh : D.holding = holding)
    (hi : D.initialVersion = toVersion sv) (hheld : holding = false → held = none) :
    vSession consumer D held bytes ended taken =
      discardSession consumer sv ended version s holding held taken := by
  obtain ⟨core', h, hv', ha', hl', hh', hi'⟩ :=
    vBytes_discarding consumer bytes D held taken ha
  rw [hl] at hl'
  unfold vSession discardSession
  rw [h]
  cases ended with
  | false =>
    simp only [Bool.false_eq_true, ite_false, sessionOf, hv', hv, discardedOf, ha',
      Option.map_some]
    cases held <;> rfl
  | true =>
    simp only [ite_true]
    cases holding with
    | true =>
      rw [vEnd_held consumer core' taken (.inr ⟨s, ha'⟩) (hh'.trans hh)]
      simp only [ite_true, eofResult, sessionOf, reset_version core' sv (hi'.trans hi),
        discardedOf_reset, Option.map_none]
      cases held <;> rfl
    | false =>
      rw [hheld rfl]
      simp only [Bool.false_eq_true, ite_false]
      have hr := handOverAt_reply consumer core' (eofAt core'.location) (eofAt_valid _)
        (hh'.trans hh) taken
      have heof : lexemeEntry consumer.concrete core'.version (eofAt core'.location) =
          some (BSmtLibSpec.Lexer.endOfFileAt (toLocation s)) := by
        rw [hl']; exact lexemeEntry_of_handed (lexemeHanded_eofAt_location _ s)
      simp only [reply, heof] at hr
      cases hans : consumer.answer (taken ++ [BSmtLibSpec.Lexer.endOfFileAt (toLocation s)]) with
      | fail e =>
        simp only [hans] at hr
        rw [vEnd_eof consumer core' taken (.inr ⟨s, ha'⟩) (hh'.trans hh) hr]
        simp only [sessionOf, failureOf, hv']
        congr 2
        · rw [hv]; unfold coreAfterError; split <;> rfl
        · unfold coreAfterError
          split <;> simp [discardedOf, ha', Activity.discardStart]
      | «break» r =>
        simp only [hans] at hr
        rw [vEnd_eof consumer core' taken (.inr ⟨s, ha'⟩) (hh'.trans hh) hr]
        simp only [eofResult, sessionOf, Option.map_none, discardedOf_reset]
        rw [reset_version _ sv (by simp [coreAfter]; split <;> exact hi'.trans hi)]
        simp [hl']
      | «continue» =>
        simp only [hans] at hr
        rw [vEnd_eof consumer core' taken (.inr ⟨s, ha'⟩) (hh'.trans hh) hr]
        simp only [eofResult, sessionOf, Option.map_none, discardedOf_reset]
        rw [reset_version _ sv (by simp [coreAfter]; split <;> exact hi'.trans hi)]

theorem toLocation_take_offset {input : List UInt8} {o : Nat} (h : o ≤ input.length) :
    (toLocation (locAfter (input.take o))).offset = o := by
  simp [toLocation, locAfter_offset', h]

theorem fromVersion_getD (s : Option BSmtLibSpec.Lexicon.Version) (version : Version) :
    fromVersion ((s.map toVersion).getD version) = s.getD (fromVersion version) := by
  cases s <;> simp [fromVersion_toVersion]

/-- The naive lexer at the boundary `o`, holding no result, does with the consumer what `Runs`
states, from the entries ready from `o` on. -/
def BoundaryRuns (o : Nat) : Prop :=
  ∀ (version : Version) (core : Core) (taken : List Handed),
    core.version = version → core.activity = .idle → core.location = locAfter (input.take o) →
    core.holding = false → core.initialVersion = toVersion sv →
    BSmtLibSpec.Lexer.Runs fedRun consumer sv input ended (fromVersion version)
      (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
          (fromVersion version) input ended o).handed
      (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
          (fromVersion version) input ended o).failed
      taken (vSession consumer core none (input.drop o) ended taken)

theorem streamFrom_false_taken (version : Version) (ended : Bool) (location : Span.Location)
    (bytes : List UInt8) : ∀ l ∈ (streamFrom version false ended location bytes).1, (Taken l) := by
  have ht := lexBytes_taken (version := version) (location := location) bytes (st := .idle) trivial
  unfold streamFrom
  rw [lexBytesW_false, endStepW_false]
  revert ht
  cases lexBytes version .idle location bytes with
  | error ls => exact id
  | ok r =>
    obtain ⟨st, location', ls⟩ := r
    rintro ⟨hst, hls⟩
    cases ended with
    | false => exact hls
    | true =>
      simp only [ite_true]
      cases he : endStep st location' with
      | none => exact hls
      | some ls' =>
        intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact hls l hl
        · exact endStep_taken he hst l hl

theorem settle_not_finished {α ε : Type} (start : BSmtLibSpec.Lexicon.Version) (taken : List Handed)
    (outcome : BSmtLibSpec.Lexer.Outcome α ε) (h : outcome.isFinished = false)
    (version : BSmtLibSpec.Lexicon.Version) (d : Option BSmtLibSpec.Lexer.Location) :
    BSmtLibSpec.Lexer.settle start taken outcome version d = ⟨taken, outcome, version, d⟩ := by
  simp [BSmtLibSpec.Lexer.settle, h]

theorem settle_finished {α ε : Type} (start : BSmtLibSpec.Lexicon.Version) (taken : List Handed)
    (result : α) (location : BSmtLibSpec.Lexer.Location)
    (version : BSmtLibSpec.Lexicon.Version) (d : Option BSmtLibSpec.Lexer.Location) :
    BSmtLibSpec.Lexer.settle (ε := ε) start taken (.finished result location) version d =
      ⟨taken, .finished result location, start, none⟩ := by
  simp [BSmtLibSpec.Lexer.settle, BSmtLibSpec.Lexer.Outcome.isFinished]

theorem lexemeEntry_some {concrete : Bool} {version : Version} {l : Lexeme} {hd : Handed}
    (h : lexemeEntry concrete version l = some hd) :
    hd.start = toLocation l.start ∧ hd.end = toLocation l.end ∧
      (hd.type = .endOfFile ↔ (l.category == .endOfFile) = true) := by
  unfold lexemeEntry at h
  cases hh : lexemeHanded version l with
  | some x =>
    rw [hh] at h
    cases h
    exact lexemeHanded_some hh
  | none =>
    rw [hh] at h
    cases concrete with
    | false => cases h
    | true =>
      simp only [ite_true, Option.some.injEq] at h
      subst h
      refine ⟨rfl, rfl, ?_⟩
      have hc : (toTokenType l.category).isSome = false := by
        unfold lexemeHanded at hh
        cases ht : toTokenType l.category with
        | none => rfl
        | some _ => rw [ht] at hh; cases hh
      unfold lexemeLayout
      cases hcat : l.category <;> simp_all [toTokenType]
      · rw [show (Token.TokenCategory.whitespace == Token.TokenCategory.comment) = false from rfl,
          show (Token.TokenCategory.whitespace == Token.TokenCategory.endOfFile) = false from rfl]
        simp
      · rw [show (Token.TokenCategory.comment == Token.TokenCategory.comment) = true from rfl,
          show (Token.TokenCategory.comment == Token.TokenCategory.endOfFile) = false from rfl]
        simp

/-- Every lexeme of the run from a boundary is an entry the consumer takes. -/
theorem stream_entry (version : Version) (o : Nat) :
    ∀ l ∈ (stream version consumer.concrete input ended o).1,
      ∃ hd, lexemeEntry consumer.concrete version l = some hd := by
  intro l hl
  cases hc : consumer.concrete with
  | true =>
    unfold lexemeEntry
    cases lexemeHanded version l <;> simp
  | false =>
    rw [hc] at hl
    obtain ⟨hd, hhd⟩ := lexemeHanded_of_taken (version := version)
      (streamFrom_false_taken version ended _ _ l hl)
    exact ⟨hd, lexemeEntry_of_handed hhd⟩

/-- What follows a break, as `AfterBreak` states it, is what the naive lexer does while it holds
the result (`holdSession`). -/
theorem afterBreak_hold (version : Version) (o : Nat) (ho : o ≤ input.length)
    (taken : List Handed) (x : Span.Located consumer.Result)
    (hx : x.location = locAfter (input.take o)) :
    ∃ outcome, BSmtLibSpec.Lexer.AfterBreak x.value (toLocation (locAfter (input.take o)))
        (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
            (fromVersion version) input ended o).handed
        (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
            (fromVersion version) input ended o).failed
        outcome ∧
      holdSession consumer sv version taken x (stream version consumer.concrete input ended o) =
        BSmtLibSpec.Lexer.settle sv taken outcome (fromVersion version) none := by
  rw [ready_stream consumer.concrete version input ended o ho]
  have hent := stream_entry consumer input ended version o
  generalize hS : stream version consumer.concrete input ended o = S at hent
  obtain ⟨L, fl⟩ := S
  dsimp only
  cases L with
  | nil =>
    cases fl with
    | true =>
      refine ⟨.failed .lexical, .lexical, ?_⟩
      rw [settle_not_finished _ _ _ rfl]; simp [holdSession]
    | false =>
      refine ⟨.holding x.value (toLocation (locAfter (input.take o))), .held, ?_⟩
      rw [settle_not_finished _ _ _ rfl]; simp [holdSession, hx]
  | cons l rest =>
    obtain ⟨hd, hhd⟩ := hent l (by simp)
    obtain ⟨hs, -, htype⟩ := lexemeEntry_some hhd
    have hh : entriesOf consumer.concrete version (l :: rest) =
        hd :: entriesOf consumer.concrete version rest := by
      simp [entriesOf, hhd]
    rw [hh]
    cases he : l.category == .endOfFile with
    | true =>
      refine ⟨.finished x.value (toLocation (locAfter (input.take o))), .ends (htype.mpr he), ?_⟩
      rw [settle_finished]; simp [holdSession, he, hx]
    | false =>
      refine ⟨.failed (.trailing hd.start), .trailing ?_, ?_⟩
      · intro h; rw [htype.mp h] at he; cases he
      · rw [settle_not_finished _ _ _ rfl]; simp [holdSession, he, hs]

/-- What the consumer does at an entry that the naive lexer hands over at a boundary, holding no
result, is what `Runs` states, given what the lexer does after it in each case. -/
theorem event (hb : consumer.BreaksAtEnd) {version : Version} {l : Lexeme} {hd : Handed}
    {o : Nat} {taken : List Handed} (hl : lexemeEntry consumer.concrete version l = some hd)
    (hne : (l.category == .endOfFile) = false)
    (hend : l.end = locAfter (input.take o)) (ho : o ≤ input.length)
    (IH : BoundaryRuns consumer sv input ended o)
    (sess : BSmtLibSpec.Lexer.Session consumer.Result consumer.Error)
    (hfail : ∀ e, consumer.answer (taken ++ [hd]) = .fail e →
      sess = ⟨taken ++ [hd], .failed (.consumer e),
        fromVersion (((consumer.switchTo (taken ++ [hd])).map toVersion).getD version),
        if consumer.discards (taken ++ [hd]) then some (toLocation l.end) else none⟩)
    (hcont : consumer.answer (taken ++ [hd]) = .continue →
      consumer.discards (taken ++ [hd]) = false →
      ∃ B : Core,
        B.version = ((consumer.switchTo (taken ++ [hd])).map toVersion).getD version ∧
        B.activity = .idle ∧ B.location = locAfter (input.take o) ∧ B.holding = false ∧
        B.initialVersion = toVersion sv ∧
        sess = vSession consumer B none (input.drop o) ended (taken ++ [hd]))
    (hdisc : consumer.answer (taken ++ [hd]) = .continue →
      consumer.discards (taken ++ [hd]) = true →
      sess = discardSession consumer sv ended
        (((consumer.switchTo (taken ++ [hd])).map toVersion).getD version) l.end false none
        (taken ++ [hd]))
    (hbrk : ∀ r, consumer.answer (taken ++ [hd]) = .break r →
      consumer.discards (taken ++ [hd]) = false →
      sess = holdSession consumer sv
        (((consumer.switchTo (taken ++ [hd])).map toVersion).getD version) (taken ++ [hd])
        (Span.Located.Internal.new r l.end)
        (stream (((consumer.switchTo (taken ++ [hd])).map toVersion).getD version)
          consumer.concrete input ended o))
    (hbrkd : ∀ r, consumer.answer (taken ++ [hd]) = .break r →
      consumer.discards (taken ++ [hd]) = true →
      sess = discardSession consumer sv ended
        (((consumer.switchTo (taken ++ [hd])).map toVersion).getD version) l.end true
        (some (Span.Located.Internal.new r l.end)) (taken ++ [hd])) :
    BSmtLibSpec.Lexer.Runs fedRun consumer sv input ended (fromVersion version)
      (hd :: (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete (fromVersion version) input ended
        o).handed)
      (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
          (fromVersion version) input ended o).failed
      taken sess := by
  obtain ⟨hs, he, htype⟩ := lexemeEntry_some hl
  have hne' : hd.type ≠ .endOfFile := fun h => by rw [htype.mp h] at hne; cases hne
  have hoff : hd.end.offset = o := by rw [he, hend]; exact toLocation_take_offset ho
  have hfol : ∀ s : Option BSmtLibSpec.Lexicon.Version,
      BSmtLibSpec.Lexer.following fedRun consumer.concrete input ended hd.end.offset s
          (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete (fromVersion version) input ended
            o).handed
          (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete (fromVersion version) input ended
            o).failed =
        BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
            (s.getD (fromVersion version)) input ended
          o := by
    intro s
    cases s <;> simp [BSmtLibSpec.Lexer.following, hoff]
  have hv : ∀ s : Option BSmtLibSpec.Lexicon.Version,
      s.getD (fromVersion version) = fromVersion ((s.map toVersion).getD version) :=
    fun s => (fromVersion_getD s version).symm
  cases hans : consumer.answer (taken ++ [hd]) with
  | fail e =>
    rw [hfail e hans]
    have := BSmtLibSpec.Lexer.Runs.fails (feed := fedRun) (consumer := consumer)
      (start := sv) (input := input) (ended := ended) (version := fromVersion version)
      (ready := (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
          (fromVersion version) input ended
        o).handed)
      (failed := (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
          (fromVersion version) input ended
        o).failed)
      (taken := taken) (token := hd) hans
    rwa [settle_not_finished _ _ _ rfl, hv, he] at this
  | «continue» =>
    cases hdi : consumer.discards (taken ++ [hd]) with
    | false =>
      obtain ⟨B, hB1, hB2, hB3, hB4, hB5, hsess⟩ := hcont hans hdi
      rw [hsess]
      refine BSmtLibSpec.Lexer.Runs.continues hne' hans hdi ?_
      rw [hfol, hv]
      rw [← hB1]
      exact IH B.version B (taken ++ [hd]) rfl hB2 hB3 hB4 hB5
    | true =>
      rw [hdisc hans hdi]
      unfold discardSession
      cases ended with
      | false =>
        have := BSmtLibSpec.Lexer.Runs.discardsWaiting (feed := fedRun)
          (consumer := consumer) (start := sv) (input := input) (version := fromVersion version)
          (ready := (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
              (fromVersion version) input
            false o).handed)
          (failed := (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
              (fromVersion version) input
            false o).failed) (taken := taken) (token := hd) hne' hans hdi rfl
        rw [settle_not_finished _ _ _ rfl, hv, he] at this
        exact this
      | true =>
        simp only [ite_true, Bool.false_eq_true, ite_false, ← he]
        have hab : (taken ++ [hd]) ++ [BSmtLibSpec.Lexer.endOfFileAt hd.end] =
            taken ++ [hd, BSmtLibSpec.Lexer.endOfFileAt hd.end] := by simp
        cases hans2 : consumer.answer (taken ++ [hd, BSmtLibSpec.Lexer.endOfFileAt hd.end]) with
        | «break» r =>
          rw [hab, hans2]
          have := BSmtLibSpec.Lexer.Runs.discardsToEnd (feed := fedRun)
            (consumer := consumer) (start := sv) (input := input) (version := fromVersion version)
            (ready := (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
                (fromVersion version) input
              true o).handed)
            (failed := (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
                (fromVersion version) input
              true o).failed) (taken := taken) (token := hd) hne' hans hdi rfl hans2
          rw [settle_finished] at this
          exact this
        | fail e =>
          rw [hab, hans2]
          have := BSmtLibSpec.Lexer.Runs.discardsFailsAtEnd (feed := fedRun)
            (consumer := consumer) (start := sv) (input := input) (version := fromVersion version)
            (ready := (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
                (fromVersion version) input
              true o).handed)
            (failed := (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
                (fromVersion version) input
              true o).failed) (taken := taken) (token := hd) hne' hans hdi rfl hans2
          rw [settle_not_finished _ _ _ rfl, ← fromVersion_getD, ← fromVersion_getD] at this
          exact this
        | «continue» =>
          exfalso
          exact hb (taken ++ [hd]) (BSmtLibSpec.Lexer.endOfFileAt hd.end) rfl
              (by rw [hab]; exact hans2)
  | «break» r =>
    cases hdi : consumer.discards (taken ++ [hd]) with
    | false =>
      rw [hbrk r hans hdi]
      obtain ⟨outcome, hafter, hset⟩ := afterBreak_hold consumer sv input ended
        (((consumer.switchTo (taken ++ [hd])).map toVersion).getD version) o ho (taken ++ [hd])
        (Span.Located.Internal.new r l.end) hend
      rw [hset, ← hv]
      refine BSmtLibSpec.Lexer.Runs.breaks hne' hans hdi ?_
      rw [hfol, hv, he, hend]
      exact hafter
    | true =>
      rw [hbrkd r hans hdi]
      unfold discardSession
      cases ended with
      | false =>
        have := BSmtLibSpec.Lexer.Runs.discardsHeld (feed := fedRun)
          (consumer := consumer) (start := sv) (input := input) (version := fromVersion version)
          (ready := (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
              (fromVersion version) input
            false o).handed)
          (failed := (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
              (fromVersion version) input
            false o).failed) (taken := taken) (token := hd) hne' hans hdi rfl
        rw [settle_not_finished _ _ _ rfl, hv, he] at this
        exact this
      | true =>
        have := BSmtLibSpec.Lexer.Runs.discardsEnds (feed := fedRun)
          (consumer := consumer) (start := sv) (input := input) (version := fromVersion version)
          (ready := (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
              (fromVersion version) input
            true o).handed)
          (failed := (BSmtLibSpec.Lexer.readyFrom fedRun consumer.concrete
              (fromVersion version) input
            true o).failed) (taken := taken) (token := hd) hne' hans hdi rfl
        rw [settle_finished, he] at this
        exact this

end

end BSmtLib.Facts.Proofs.Lexer.Consumers.VEvent
