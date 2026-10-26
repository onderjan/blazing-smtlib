module

public import BSmtLib.Facts.Proofs.PublicApi.Collector
public import BSmtLib.Facts.Proofs.Lexer.Consumers.Ports
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor

@[expose] public section

/-!
# The collector's run, as the naive lexer's pure run gives it

`collect_stream`: what the library's lexer with the collector writes down is the lexemes of the
naive lexer's pure run over the input joined, whitespace and comments included, with their
categories and offsets; and it fails exactly where the pure run does. It rests on the collector
against the adapter's consumer (`Collector.collect_lexing`), the library's lexer against the
naive one (`Consumers.Ports.lexing_lexer_vNaive`), and what the naive lexer does with a consumer
of the specification formalism (`BSmtLibSpec`) (`Consumers.VNaive.vNaive_runs`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.Lexing

open BSmtLib.Facts.PublicApi.Adapters
open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.PublicApi.Collector
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.Consumers.Ready
open BSmtLib.Facts.Proofs.Lexer.Consumers.Stream BSmtLib.Facts.Proofs.Lexer.Consumers.VEvent
open BSmtLib.Facts.Proofs.Lexer.Consumers.VHold BSmtLib.Facts.Proofs.Lexer.Consumers.VNaive
open BSmtLib.Facts.Proofs.Lexer.VNaive.Facts BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Lexer.Internal.VNaive
open BSmtLibSpec.Lexer (Handed)

/-! ## The concrete collector, as `Runs` states -/

theorem concreteCollector_breaksAtEnd : concreteCollector.BreaksAtEnd := by
  intro taken token hty
  simp [concreteCollector, hty]

/-- The concrete collector takes every entry ready and fails exactly where the lexer fails. -/
theorem runs_concrete
    {feed : BSmtLibSpec.Lexicon.Version → List BSmtLibSpec.Regex.Chars → Bool →
      BSmtLibSpec.Lexer.Fed}
    {start : BSmtLibSpec.Lexicon.Version} {input : BSmtLibSpec.Regex.Chars} {ended : Bool}
    {version : BSmtLibSpec.Lexicon.Version} {ready : List Handed} {failed : Bool}
    {taken : List Handed}
    {S : BSmtLibSpec.Lexer.Session concreteCollector.Result concreteCollector.Error}
    (h : BSmtLibSpec.Lexer.Runs feed concreteCollector start input ended version ready
    failed taken S)
    (hready : CollectorReady ready failed) :
    S.taken = taken ++ ready ∧ S.outcome.isFailed = failed := by
  induction h with
  | waiting => rw [settle_not_finished _ _ _ rfl]; exact ⟨by simp, rfl⟩
  | lexical => rw [settle_not_finished _ _ _ rfl]; exact ⟨by simp, rfl⟩
  | fails hans =>
    simp only [concreteCollector] at hans
    split at hans <;> cases hans
  | ends hty hans =>
    obtain ⟨tokens, eof, he, ht, hl⟩ := hready
    cases tokens with
    | cons t tokens =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact absurd hty (ht _ (by simp))
    | nil =>
      simp only [List.nil_append] at he
      subst he
      rcases hl with h0 | ⟨e, he, -, hf⟩
      · cases h0
      · simp only [List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [settle_finished]
        exact ⟨by simp, hf.symm⟩
  | continues hty hans hdi hrun ih =>
    refine (ih ?_).imp
        (fun h => by rw [h]; simp [BSmtLibSpec.Lexer.following, concreteCollector]) id
    show CollectorReady _ _
    obtain ⟨tokens, eof, he, ht, hl⟩ := hready
    cases tokens with
    | cons t tokens =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨tokens, eof, rfl, fun t' h' => ht t' (by simp [h']), hl⟩
    | nil =>
      simp only [List.nil_append] at he
      subst he
      rcases hl with h0 | ⟨e, he, he2, -⟩
      · cases h0
      · simp only [List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he
        exact absurd he2 hty
  | breaks hty hans =>
    simp only [concreteCollector, List.getLast?_append, List.getLast?_singleton] at hans
    split at hans
    · simp_all
    · cases hans
  | discardsHeld _ _ hdi => simp [concreteCollector] at hdi
  | discardsEnds _ _ hdi => simp [concreteCollector] at hdi
  | discardsWaiting _ _ hdi => simp [concreteCollector] at hdi
  | discardsToEnd _ _ hdi => simp [concreteCollector] at hdi
  | discardsFailsAtEnd _ _ hdi => simp [concreteCollector] at hdi

/-! ## The entries of lexemes -/

/-- What the collector writes down of a lexeme: its category and its offsets. -/
def lexEntry (l : Lexeme) : Entry := (l.category, l.start.offset, l.«end».offset)

theorem cat_beq (a b : Token.TokenCategory) : (a == b) = (a.ctorIdx == b.ctorIdx) := by
  cases a <;> cases b <;> rfl

theorem lexemeEntry_true (version : Version) (l : Lexeme) :
    ∃ hd, lexemeEntry true version l = some hd ∧ entryOf hd = lexEntry l ∧
      (hd.type = .endOfFile ↔ (l.category == .endOfFile) = true) := by
  unfold lexemeEntry lexemeHanded lexemeLayout
  cases hc : l.category <;>
    simp only [toTokenType, Option.map_some, Option.map_none, ↓reduceIte] <;>
    refine ⟨_, rfl, ?_, ?_⟩ <;>
    first
      | (simp only [entryOf, lexEntry, hc, toLocation]; rfl)
      | (dsimp only; decide)

theorem entriesOf_map (version : Version) (ls : List Lexeme) :
    (entriesOf true version ls).map entryOf = ls.map lexEntry := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    obtain ⟨hd, h1, h2, -⟩ := lexemeEntry_true version l
    simp only [entriesOf, List.filterMap_cons, h1, List.map_cons] at ih ⊢
    rw [h2, ih]

theorem entriesOf_noEof {version : Version} {ls : List Lexeme} (h : NoEof ls) :
    ∀ t ∈ entriesOf true version ls, t.type ≠ .endOfFile := by
  intro t ht hte
  obtain ⟨l, hl, hlt⟩ := List.mem_filterMap.mp ht
  obtain ⟨hd, h1, -, h3⟩ := lexemeEntry_true version l
  rw [h1] at hlt
  cases hlt
  have := h l hl
  rw [h3.mp hte] at this
  cases this

/-- The entries of a run, as the concrete collector takes them. -/
theorem streamFrom_ready (version : Version) (ended : Bool) (location : Span.Location)
    (bytes : List UInt8) :
    CollectorReady (entriesOf true version (streamFrom version true ended location bytes).1)
      (streamFrom version true ended location bytes).2 := by
  have hn := lexBytesW_noEof version true bytes .idle location
  simp only [lexemesOf] at hn
  unfold streamFrom
  revert hn
  cases lexBytesW version true .idle location bytes with
  | error ls =>
    intro hn
    exact ⟨entriesOf true version ls, [], by simp, entriesOf_noEof hn, .inl rfl⟩
  | ok x =>
    obtain ⟨st, location', ls⟩ := x
    intro hn
    cases ended with
    | false => exact ⟨entriesOf true version ls, [], by simp, entriesOf_noEof hn, .inl rfl⟩
    | true =>
      simp only [ite_true]
      cases he : endStepW true st location' with
      | none => exact ⟨entriesOf true version ls, [], by simp, entriesOf_noEof hn, .inl rfl⟩
      | some ls' =>
        dsimp only
        obtain ⟨e, he', -, hte⟩ := lexemeEntry_true version (eofLexeme location')
        have hte : e.type = .endOfFile := hte.mpr rfl
        rcases endStepW_cases he with rfl | ⟨l, rfl, -⟩
        · refine ⟨entriesOf true version ls, [e], ?_, entriesOf_noEof hn,
            .inr ⟨e, rfl, hte, rfl⟩⟩
          simp [entriesOf, List.filterMap_append, he']
        · have hl : (l.category == .endOfFile) = false := by
            cases st with
            | idle => simp [endStepW] at he
            | token p =>
              simp only [endStepW] at he
              split at he
              · cases he
              · rename_i l' hf
                simp only [Option.some.injEq, List.cons.injEq] at he
                obtain ⟨rfl, -⟩ := he
                exact finish_token_ne_eof hf
              · cases he
          refine ⟨entriesOf true version (ls ++ [l]), [e], ?_, entriesOf_noEof ?_,
            .inr ⟨e, rfl, hte, rfl⟩⟩
          · simp only [entriesOf, List.filterMap_append]
            rw [show [l, eofLexeme location'] = [l] ++ [eofLexeme location'] from rfl,
              List.filterMap_append]
            simp [he']
          · intro l' hl'
            rcases List.mem_append.mp hl' with hl' | hl'
            · exact hn l' hl'
            · simp at hl'; subst hl'; exact hl

/-! ## The collector's run -/

/-- The library's lexer with the collector writes down the lexemes of the naive lexer's pure run
over the input joined, and fails exactly where it does. -/
theorem collect_stream (version : Version) (slices : List ByteList) :
    (collect version slices).2 = (stream version true slices.flatten true 0).1.map lexEntry ∧
      (collect version slices).1.toBool = !(stream version true slices.flatten true 0).2 := by
  obtain ⟨h1, h2⟩ := collect_lexing version slices
  rw [BSmtLib.Facts.Proofs.Lexer.Consumers.Ports.lexing_lexer_vNaive] at h1 h2
  have hr := vNaive_runs concreteCollector concreteCollector_breaksAtEnd (fromVersion version)
    slices true
  have hseg := ready_stream true version slices.flatten true 0 (Nat.zero_le _)
  rw [show concreteCollector.concrete = true from rfl, hseg] at hr
  obtain ⟨ht, hf⟩ := runs_concrete hr (by
    simpa [stream] using streamFrom_ready version true (locAfter (slices.flatten.take 0))
      (slices.flatten.drop 0))
  rw [ht, List.nil_append, entriesOf_map] at h1
  rw [hf] at h2
  exact ⟨h1, h2⟩

/-! ## A run that ends with `)` -/

theorem finish_true_ne_none {p : Pending} {location : Span.Location} :
    finish true p location ≠ .none := by
  simp only [finish]
  repeat' split
  all_goals simp_all

theorem finish_token_ne_close {ws : Bool} {p : Pending} {location : Span.Location} {l : Lexeme}
    (h : finish ws p location = .token l) : l.category ≠ .parenClose := by
  simp only [finish] at h
  repeat' split at h
  all_goals cases h
  all_goals first | (intro hc; cases hc) | (cases ‹Radix› <;> intro hc <;> cases hc)

/-- The run from the start of the input over the bytes, and then the end of the input. -/
theorem stream_zero (version : Version) (input : List UInt8) :
    stream version true input true 0 =
      streamFrom version true true Span.Location.initial input := by
  simp [stream, locAfter, advanceLoc]

/-- A run that finishes without an error, with a `)` as its last lexeme before the end of file,
has nothing in progress after the bytes: the lexemes before the end of file are those of the
bytes. -/
theorem lexBytes_of_close {version : Version} {input : List UInt8} {ls : List Lexeme}
    (h : streamFrom version true true Span.Location.initial input = (ls, false))
    (hclose : (ls.map lexEntry).dropLast.getLast?.map (·.1) = some .parenClose) :
    ∃ location, lexBytesW version true .idle Span.Location.initial input =
      .ok (.idle, location, ls.dropLast) := by
  unfold streamFrom at h
  cases hr : lexBytesW version true .idle Span.Location.initial input with
  | error ls' => rw [hr] at h; cases h
  | ok x =>
    obtain ⟨st, location, ls₀⟩ := x
    rw [hr] at h
    simp only [ite_true] at h
    cases he : endStepW true st location with
    | none => rw [he] at h; cases h
    | some ls' =>
      rw [he] at h
      simp only [Prod.mk.injEq, and_true] at h
      subst h
      rcases endStepW_cases he with rfl | ⟨l, rfl, -⟩
      · cases st with
        | idle =>
          refine ⟨location, ?_⟩
          rw [List.dropLast_concat]
        | token p =>
          exfalso
          simp only [endStepW] at he
          split at he
          · exact finish_true_ne_none ‹_›
          · simp at he
          · cases he
      · exfalso
        cases st with
        | idle => simp [endStepW] at he
        | token p =>
          simp only [endStepW] at he
          split at he
          · cases he
          · rename_i l' hf
            simp only [Option.some.injEq, List.cons.injEq] at he
            obtain ⟨rfl, -⟩ := he
            simp only [List.map_append, List.map_cons, List.map_nil] at hclose
            rw [show ∀ (A : List Entry) (x y : Entry), A ++ [x, y] = (A ++ [x]) ++ [y] by simp,
              List.dropLast_concat, List.getLast?_concat] at hclose
            simp only [Option.map_some, Option.some.injEq] at hclose
            exact finish_token_ne_close hf hclose
          · cases he

/-! ## Composition at a `)` -/

/-- The run over bytes after bytes that leave nothing in progress: the lexemes of the first
bytes, then those of the run over the rest on its own, moved past the first bytes. -/
theorem streamFrom_append {version : Version} {first rest : List UInt8}
    {location : Span.Location} {ls : List Lexeme}
    (h : lexBytesW version true .idle Span.Location.initial first = .ok (.idle, location, ls)) :
    streamFrom version true true Span.Location.initial (first ++ rest) =
      (ls ++ (streamFrom version true true Span.Location.initial rest).1.map
          (Lexeme.shift (locAfter first)),
        (streamFrom version true true Span.Location.initial rest).2) := by
  have hloc := lexBytesW_location first h
  have hsh := lexBytesW_shift version true (locAfter first) rest .idle Span.Location.initial
  rw [locShift_initial] at hsh
  unfold streamFrom
  rw [lexBytesW_append, h, hloc]
  rw [show St.shift (locAfter first) .idle = .idle from rfl] at hsh
  rw [show advanceLoc Span.Location.initial first = locAfter first from rfl]
  dsimp only
  rw [hsh]
  cases hr : lexBytesW version true .idle Span.Location.initial rest with
  | error ls' => simp [shiftRun, withBefore]
  | ok x =>
    obtain ⟨st, l2, ls2⟩ := x
    simp only [shiftRun, withBefore, ite_true]
    rw [endStepW_shift]
    cases endStepW true st l2 with
    | none => simp
    | some ls3 => simp

theorem map_lexEntry_shift (base : Span.Location) (ls : List Lexeme) :
    (ls.map (Lexeme.shift base)).map lexEntry = shift base.offset (ls.map lexEntry) := by
  simp only [shift, List.map_map]
  congr 1
  funext l
  simp [lexEntry, Lexeme.shift, locShift, Nat.add_comm]

/-- An input that the library's lexer with the collector lexes to the end, with a `)` as its last
token, is lexed as a prefix of every input it starts. -/
theorem composes (version : Version) (first rest : ByteList)
    (result : Option (Span.Located Unit)) (entries : List Entry)
    (h : collect version [first] = (.ok result, entries))
    (hclose : entries.dropLast.getLast?.map (·.1) = some .parenClose) :
    (collect version [first ++ rest]).2 =
        entries.dropLast ++ shift first.length (collect version [rest]).2 ∧
      (collect version [first ++ rest]).1.toBool = (collect version [rest]).1.toBool := by
  obtain ⟨e1, b1⟩ := collect_stream version [first]
  obtain ⟨e2, b2⟩ := collect_stream version [first ++ rest]
  obtain ⟨e3, b3⟩ := collect_stream version [rest]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, stream_zero] at e1 b1 e2 b2 e3 b3
  rw [h] at e1 b1
  dsimp only at e1 b1
  have hS : streamFrom version true true Span.Location.initial first =
      ((streamFrom version true true Span.Location.initial first).1, false) := by
    refine Prod.ext rfl ?_
    revert b1
    cases (streamFrom version true true Span.Location.initial first).2 <;> simp [Except.toBool]
  rw [e1] at hclose
  obtain ⟨loc, hl⟩ := lexBytes_of_close hS hclose
  rw [streamFrom_append hl] at e2 b2
  refine ⟨?_, ?_⟩
  · rw [e2, e3, e1, List.map_append, map_lexEntry_shift, locAfter_offset', List.map_dropLast]
  · rw [b2, b3]

end BSmtLib.Facts.Proofs.PublicApi.Lexing
