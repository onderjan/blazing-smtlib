module

public import BSmtLib.Facts.Proofs.PublicApi.Slicing
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Error
import all BSmtLib.Span

@[expose] public section

/-!
# The collector's run on an input that a run ending with `)` starts

The collector's run on one slice ends as the naive lexer's pure run over its bytes says
(`collect_pure`): with the error of the byte where the pure run fails, with the error of
finishing the token in progress at the end, or with the result located at the end of the input.
It rests on the collector against the naive lexer with the concrete collector
(`Slicing.collect_naive`) and on what that lexer does at the end of the input (`VEof`).

The pure run is the same from any location, with its locations moved by where it starts
(`lexBytesF_shift`). A run that ends with `)` leaves nothing in progress, so the run over a longer
input that it starts goes on as the run over the rest alone, moved past it: it hands over the same
entries, moved (`Lexing.streamFrom_append`), and ends with the same result or error, moved
(`pureResult_append`, `composes`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.Composes

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Facts.PublicApi.Adapters
open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.PublicApi.Collector BSmtLib.Facts.Proofs.PublicApi.Lexing
open BSmtLib.Facts.Proofs.PublicApi.Slicing BSmtLib.Facts.Proofs.PublicApi.VCollector
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.Consumers.Stream
open BSmtLib.Facts.Proofs.Lexer.Consumers.Ready BSmtLib.Facts.Proofs.Lexer.Consumers.VHold
open BSmtLib.Facts.Proofs.Lexer.Consumers.RunE BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps
open BSmtLib.Facts.Proofs.Lexer.Consumers.VEnd BSmtLib.Facts.Proofs.Lexer.Consumers.VSession
open BSmtLib.Facts.Proofs.Lexer.VNaive.Facts BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel
open BSmtLib.Lexer.Internal.VNaive
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer

/-! ## The result of a run on one slice -/

/-- The result of the collector's run on the bytes as one slice, as the naive lexer's pure run
over them says: the error of the byte where it fails, the error of finishing the token in
progress at the end of the input, or the result located at the end of the input. -/
def pureResult (version : Version) (bs : List UInt8) :
    Except (LexerError Empty) (Option (Span.Located Unit)) :=
  match lexBytesF version true .idle Span.Location.initial bs with
  | .error (_, f) => .error (LexerError.Internal.new (.lexical f.kind) f.span none)
  | .ok (st, location, _) =>
    match finishLs true st location with
    | none => .error (LexerError.Internal.new (.lexical (finishFail true st location).kind)
        (finishFail true st location).span none)
    | some _ => .ok (some (Span.Located.Internal.new () location))

theorem lexicalKey_kind {ε : Type} {c : LexerErrorKind (Option ε)} {s s' : Span}
    {k : LexicalErrorKind} (h : lexicalKey c s = some (k, s')) : c = .lexical k := by
  unfold lexicalKey at h
  split at h
  · split at h
    · cases h
    · cases h; rfl
  · cases h

/-- The naive lexer with the concrete collector at the end of the input, from a lexer state that
is the pure run's state and holds no result: where finishing the token in progress fails, it
fails with that failure's kind and span; else it breaks with the result located at the end. -/
theorem vEnd_cc_exact (core : Core) (st : St) (hact : core.activity = st.activity)
    (hh : core.holding = false) (taken : List Handed) :
    match finishLs true st core.location with
    | none => ∃ e, (vEnd concreteCollector core taken).1.1 = .error e ∧
        e.kind = .lexical (finishFail true st core.location).kind ∧
        e.span = (finishFail true st core.location).span
    | some _ => (vEnd concreteCollector core taken).1.1 =
        .ok (.break (Span.Located.Internal.new () core.location)) := by
  have hR := (VEof.vEnd_eofRes concreteCollector core st taken (.inl hact)).1
  unfold EofRes at hR
  rw [hh] at hR
  generalize (vEnd concreteCollector core taken).1.1 = res at hR ⊢
  cases hf : finishLs true st core.location with
  | none =>
    have ho : eofOut concreteCollector false true core.version taken st core.location = none := by
      simp only [eofOut, hf, Option.map_none]
    rw [show concreteCollector.concrete = true from rfl, ho] at hR
    obtain ⟨h1, -⟩ := hR
    cases res with
    | ok _ => cases h1
    | error e =>
      simp only [Except.mapError, Except.error.injEq, preciseOf, preciseFailure,
        Prod.mk.injEq] at h1
      exact ⟨e, rfl, lexicalKey_kind h1.2, (lexicalKey_span h1.2).symm⟩
  | some ls =>
    have hls : NoEof ls := by
      unfold finishLs at hf
      split at hf
      · cases hf; simp [NoEof]
      · split at hf
        · cases hf; simp [NoEof]
        · cases hf
          rename_i l hfl
          intro l' hl'
          simp only [List.mem_singleton] at hl'
          subst hl'
          exact finish_token_ne_eof hfl
        · cases hf
    obtain ⟨p', hp, -⟩ := handAll_cc ls ⟨taken, core.version⟩ hls
    obtain ⟨r, l, p'', hw⟩ := hand1_cc_eof p' core.location
    have ho : eofOut concreteCollector false true core.version taken st core.location =
        some (.wait r l p'', none) := by
      simp only [eofOut, hf, Option.map_some, pending, hp, eofHand, Bool.false_eq_true,
        ↓reduceIte, hw]
    rw [show concreteCollector.concrete = true from rfl, ho] at hR
    obtain ⟨h1, -⟩ := hR
    cases res with
    | error _ => cases h1
    | ok _ => cases h1; rfl

/-- The naive lexer with the concrete collector, fed the bytes as one slice and then the end of
the input, ends as the pure run over them says. -/
theorem single_matches (version : Version) (bs : List UInt8) :
    Matches (pureResult version bs)
      ((runInputE VOps (VOps.new concreteCollector {} version) true [bs]).run []).1.1 := by
  have hx := vBytes_cc_exact (Core.initial version) .idle rfl rfl bs []
  rw [show (Core.initial version).version = version from rfl,
    show (Core.initial version).location = Span.Location.initial from rfl] at hx
  have hp : (Core.Plain (Core.initial version)) := trivial
  rw [runInputE_cons,
    show VOps.new concreteCollector {} version = ⟨{}, Core.initial version, none⟩ from rfl,
    BSmtLib.Facts.Proofs.Lexer.Consumers.VFlatten.lexSliceStep_ops concreteCollector
      (Core.initial version) hp none bs []]
  unfold pureResult
  generalize vBytes concreteCollector (Core.initial version) none bs [] = R at hx ⊢
  obtain ⟨⟨res, core'⟩, taken'⟩ := R
  dsimp only at hx
  generalize lexBytesF version true .idle Span.Location.initial bs = L at hx ⊢
  cases L with
  | error x =>
    obtain ⟨ls, f⟩ := x
    dsimp only at hx ⊢
    subst hx
    exact ⟨⟨f.kind, rfl, rfl⟩, rfl, rfl⟩
  | ok x =>
    obtain ⟨st', loc', ls⟩ := x
    obtain ⟨rfl, h2, h3, h4, -⟩ := hx
    dsimp only
    rw [runInputE_nil_true]
    simp only [BSmtLib.Facts.Proofs.Lexer.Consumers.VFlatten.withHeld_v,
      BSmtLib.Facts.Proofs.Lexer.Consumers.VFlatten.held_v, Option.or_self]
    rw [lexOps_lexEofStep]
    have hc := vEnd_cc_exact core' st' h3 h2 taken'
    rw [h4] at hc
    generalize vEnd concreteCollector core' taken' = R at hc ⊢
    obtain ⟨⟨r, c''⟩, t''⟩ := R
    dsimp only at hc ⊢
    cases hf : finishLs true st' loc' with
    | none =>
      rw [hf] at hc
      obtain ⟨e, rfl, hk, hs⟩ := hc
      exact ⟨⟨_, rfl, hk⟩, hs.symm, rfl⟩
    | some _ =>
      rw [hf] at hc
      subst hc
      rfl

/-- The collector's run on one slice ends as the naive lexer's pure run over its bytes says. -/
theorem collect_pure (version : Version) (bs : List UInt8) :
    (collect version [bs]).1 = pureResult version bs := by
  have hm := (collect_naive version [bs]).2
  have hF := BSmtLib.Facts.Proofs.Lexer.Consumers.VFlattenE.runInputE_flatten concreteCollector
    true (X1BatchInCoreLexer.Chunks.cutAll [bs]) (Core.initial version) none [] trivial
  rw [X1BatchInCoreLexer.Chunks.flatten_cutAll] at hF
  rw [show (⟨{}, Core.initial version, none⟩ : VOps.Lexer concreteCollector) =
    VOps.new concreteCollector {} version from rfl] at hF
  rw [hF.1] at hm
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hm
  exact matches_unique hm (single_matches version bs)

/-! ## Moving the run with its failure -/

/-- The outcome of a pure run with its failure, moved. -/
def shiftRunF (base : Span.Location) : RunF → RunF
  | .ok (st, location, ls) =>
    .ok (St.shift base st, locShift base location, ls.map (Lexeme.shift base))
  | .error (ls, f) => .error (ls.map (Lexeme.shift base), LexFailure.shift base f)

theorem shiftRunF_withBeforeF (base : Span.Location) (ls : List Lexeme) (e : RunF) :
    shiftRunF base (withBeforeF ls e) =
      withBeforeF (ls.map (Lexeme.shift base)) (shiftRunF base e) := by
  cases e with
  | ok r => obtain ⟨st, location, ls'⟩ := r; simp [withBeforeF, shiftRunF]
  | error r => obtain ⟨ls', f⟩ := r; simp [withBeforeF, shiftRunF]

theorem startFail_shift (version : Version) (ws : Bool) (base location : Span.Location)
    (c : UInt8) :
    startFail version ws (locShift base location) c =
      LexFailure.shift base (startFail version ws location c) := by
  unfold startFail
  rw [start_shift]
  cases start version ws location c <;> simp only [Started.shift, failAtByte_shift]

theorem failW_shift (version : Version) (ws : Bool) (base : Span.Location) (st : St)
    (location : Span.Location) (c : UInt8) :
    failW version ws (St.shift base st) (locShift base location) c =
      LexFailure.shift base (failW version ws st location c) := by
  cases st with
  | idle => exact startFail_shift version ws base location c
  | token p =>
    simp only [failW, St.shift]
    rw [advance_shift]
    cases advance ws p location c <;> simp only [Advanced.shift, startFail_shift]

theorem lexBytesF_shift (version : Version) (ws : Bool) (base : Span.Location)
    (bytes : List UInt8) :
    ∀ (st : St) (location : Span.Location),
      lexBytesF version ws (St.shift base st) (locShift base location) bytes =
        shiftRunF base (lexBytesF version ws st location bytes) := by
  induction bytes with
  | nil => intro st location; rfl
  | cons c bytes ih =>
    intro st location
    simp only [lexBytesF]
    rw [byteStepW_shift]
    cases byteStepW version ws st location c with
    | none => simp [shiftStep, shiftRunF, failedBeforeW_shift, failW_shift]
    | some r =>
      obtain ⟨st', ls⟩ := r
      simp only [shiftStep, Option.map_some]
      rw [locShift_afterByte, ih, shiftRunF_withBeforeF]

theorem lexBytesF_append (version : Version) (ws : Bool) (st : St) (location : Span.Location)
    (a b : List UInt8) :
    lexBytesF version ws st location (a ++ b) =
      match lexBytesF version ws st location a with
      | .ok (st', location', ls) => withBeforeF ls (lexBytesF version ws st' location' b)
      | .error e => .error e := by
  induction a generalizing st location with
  | nil =>
    simp only [List.nil_append, lexBytesF, withBeforeF_nil]
  | cons c a ih =>
    simp only [List.cons_append, lexBytesF]
    cases byteStepW version ws st location c with
    | none => rfl
    | some r =>
      obtain ⟨st', ls⟩ := r
      simp only [ih]
      cases lexBytesF version ws st' (location.afterByte c) a with
      | error e => obtain ⟨ls', f⟩ := e; rfl
      | ok r' =>
        obtain ⟨st'', location'', ls'⟩ := r'
        exact withBeforeF_withBeforeF ls ls' _

theorem finishLs_shift (ws : Bool) (base : Span.Location) (st : St) (location : Span.Location) :
    finishLs ws (St.shift base st) (locShift base location) =
      (finishLs ws st location).map (List.map (Lexeme.shift base)) := by
  cases st with
  | idle => rfl
  | token p =>
    simp only [finishLs, St.shift]
    rw [finish_shift]
    cases finish ws p location <;> rfl

theorem finishFail_shift (ws : Bool) (base : Span.Location) (st : St)
    (location : Span.Location) :
    finishFail ws (St.shift base st) (locShift base location) =
      LexFailure.shift base (finishFail ws st location) := by
  cases st with
  | idle => exact failAtEnd_shift .unexpectedByte base location location
  | token p =>
    simp only [finishFail, St.shift]
    rw [finish_shift]
    cases finish ws p location <;> simp only [Finished.shift, failAtEnd_shift]

/-- A location moved by `locShift` is moved as `Moved` states. -/
theorem moved_locShift (base location : Span.Location) :
    Moved base location (locShift base location) :=
  ⟨rfl, rfl, rfl⟩

/-- The result of the pure run over bytes after bytes that leave nothing in progress is that of
the run over the rest on its own, moved past the first bytes. -/
theorem pureResult_append {version : Version} {first rest : List UInt8}
    {location : Span.Location} {ls : List Lexeme}
    (h : lexBytesF version true .idle Span.Location.initial first = .ok (.idle, location, ls)) :
    MovedResult (locAfter first) (pureResult version rest)
      (pureResult version (first ++ rest)) := by
  have hloc : location = locAfter first := by
    have hw := plain_lexBytesF version true first .idle Span.Location.initial
    rw [h] at hw
    exact lexBytesW_location first hw.symm
  subst hloc
  have hsh := lexBytesF_shift version true (locAfter first) rest .idle Span.Location.initial
  rw [locShift_initial, show St.shift (locAfter first) .idle = .idle from rfl] at hsh
  unfold pureResult
  rw [lexBytesF_append, h]
  dsimp only
  rw [hsh]
  cases lexBytesF version true .idle Span.Location.initial rest with
  | error x =>
    obtain ⟨ls', f⟩ := x
    exact ⟨rfl, moved_locShift _ _, moved_locShift _ _, trivial⟩
  | ok x =>
    obtain ⟨st', loc', ls'⟩ := x
    dsimp only [shiftRunF, withBeforeF]
    rw [finishLs_shift, finishFail_shift]
    cases finishLs true st' loc' with
    | none => exact ⟨rfl, moved_locShift _ _, moved_locShift _ _, trivial⟩
    | some _ => exact moved_locShift _ _

/-! ## Composition at a `)` -/

/-- An input that the library's lexer with the collector lexes to the end, with a `)` as its last
token, is lexed as a prefix of every input it starts: the longer input's entries are its own but
the end of file and then the rest's, moved, and its result is the rest's, moved. -/
theorem composes (version : Version) (first rest : ByteList)
    (result : Option (Span.Located Unit)) (entries : List Entry)
    (h : collect version [first] = (.ok result, entries))
    (hclose : entries.dropLast.getLast?.map (·.1) = some .parenClose) :
    (collect version [first ++ rest]).2 =
        entries.dropLast ++ shift first.length (collect version [rest]).2 ∧
      MovedResult (locationAfter first) (collect version [rest]).1
        (collect version [first ++ rest]).1 := by
  obtain ⟨e1, b1⟩ := collect_stream version [first]
  obtain ⟨e2, -⟩ := collect_stream version [first ++ rest]
  obtain ⟨e3, -⟩ := collect_stream version [rest]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, stream_zero] at e1 b1 e2 e3
  rw [h] at e1 b1
  dsimp only at e1 b1
  have hS : streamFrom version true true Span.Location.initial first =
      ((streamFrom version true true Span.Location.initial first).1, false) := by
    refine Prod.ext rfl ?_
    revert b1
    cases (streamFrom version true true Span.Location.initial first).2 <;> simp [Except.toBool]
  rw [e1] at hclose
  obtain ⟨loc, hl⟩ := lexBytes_of_close hS hclose
  have hF : lexBytesF version true .idle Span.Location.initial first =
      .ok (.idle, loc, (streamFrom version true true Span.Location.initial first).1.dropLast) := by
    have hw := plain_lexBytesF version true first .idle Span.Location.initial
    rw [hl] at hw
    revert hw
    cases lexBytesF version true .idle Span.Location.initial first with
    | error x => intro hw; cases hw
    | ok x => intro hw; cases hw; rfl
  rw [streamFrom_append hl] at e2
  refine ⟨?_, ?_⟩
  · rw [e2, e3, e1, List.map_append, map_lexEntry_shift, locAfter_offset', List.map_dropLast]
  · rw [collect_pure, collect_pure]
    exact pureResult_append hF

end BSmtLib.Facts.Proofs.PublicApi.Composes
