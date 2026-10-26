module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
import all BSmtLib.Lexer.Internal.WRustPort.Slice

@[expose] public section

/-!
# What a step of the Rust port keeps, with every consumer

A step of the Rust port's loop over a slice (`WRustPort.lexStep`) lexes the slice from the
lexer's index `start` to an index after it. It keeps the correspondence with the naive lexer: if
the lexer state is the naive lexer's pure state at `start` (`StepPre`), then after the step it
is the pure state at the index the step returns, with the lexemes not yet handed over in its
batch, and what the adapter's consumer does with the lexemes of the run over the rest of the
slice is what it would have done from `start` (`StepPost`). If the step is interrupted, either
the naive lexer's run fails, with a lexical error, and the consumer and the batch of the lexer
state are where the run fails after the lexemes of the batch are handed over, or the consumer
stopped, and the interruption is that stop (`StepFails`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step

open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Batch
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model BSmtLib.Lexer.Error
open BSmtLib.Lexer.Internal.VNaive

/-- The lexer state at the index `start` of the slice is the naive lexer's pure state `st` at
`location`, and its batch holds the lexemes `held`, with their contents in the slice. -/
structure StepPre (C : BSmtLibSpec.Lexer.Consumer) (v : Version) (hd : Bool)
    (iv : Version)
    (input : ByteSlice) (st : St) (location : Span.Location) (held : List Lexeme) (start : Nat)
    (c : WP.WCore) : Prop where
  fixed : Fixed v hd iv c
  base : c.base = start
  agrees : StAgrees v C.concrete st c
  loc : LocAt c c.offset c.base start location
  holds : Holds c.batch held
  bytes : c.batch.bytes = input.byteArray

/-- The interruption is a lexical error other than trailing input. -/
def IsLexical {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} (e : WP.Intr C floor) : Prop :=
  ∃ kind : LexicalErrorKind, e.result = .error (.lexical kind) ∧ kind ≠ .unexpectedTrailingToken

/-- The failure of the naive lexer that the interruption is, if it is a lexical error. -/
def intrFailure {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} (e : WP.Intr C floor) :
    LexFailure where
  kind := match e.result with
    | .error (.lexical kind) => kind
    | _ => .unexpectedByte
  span := e.span
  location := e.location

theorem mkAtByte_position (position : Nat) :
    (Lexer.Internal.WRustPort.Slice.TokenEnd.mkAtByte position).position = position := (rfl)

theorem mkAtByte_atByte (position : Nat) :
    (Lexer.Internal.WRustPort.Slice.TokenEnd.mkAtByte position).atByte = true := (rfl)

theorem eof_position : Lexer.Internal.WRustPort.Slice.TokenEnd.EOF.position = 0 := (rfl)

theorem eof_atByte : Lexer.Internal.WRustPort.Slice.TokenEnd.EOF.atByte = false := (rfl)

theorem failure_congr {k k' : LexicalErrorKind} {a b c a' b' c' : Span.Location} (hk : k = k')
    (h1 : a = a') (h2 : b = b') (h3 : c = c') :
    ({ kind := k, span := Span.Internal.newUnchecked a b, location := c } : LexFailure) =
      { kind := k', span := Span.Internal.newUnchecked a' b', location := c' } := by
  subst hk h1 h2 h3; rfl

/-- Closes the goal that a failure of the naive lexer at the location `h` is that of an
interruption, from the facts about indices in the context. -/
macro "failure_eq" h:term : tactic => `(tactic| (
  have hlocf := $h
  obtain ⟨_, _, _⟩ := id hlocf
  (try rw [BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure.locAt_eq hlocf])
  simp only [intrFailure,
    BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed.failAtByte_def,
    BSmtLib.Span.Location.afterByte,
    BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed.failAtEnd_def,
    BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes.afterColumns,
    BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure.locOf,
    BSmtLib.Lexer.Internal.WRustPort.LexerCore.locationAt,
    BSmtLib.Lexer.Internal.WRustPort.LexerCore.offsetAt, BSmtLib.Span.Location.afterColumn,
    BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes.prep_nil,
    BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step.mkAtByte_position,
    BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step.mkAtByte_atByte,
    BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step.eof_position,
    BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step.eof_atByte, Bool.false_eq_true, ↓reduceIte]
  first
  | refine BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step.failure_congr ?_ ?_ ?_ ?_
  | (congr 2; refine BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step.failure_congr ?_ ?_ ?_ ?_)
  all_goals first
    | (with_reducible rfl)
    | ((try simp only [BSmtLib.Span.Location.Internal.new_inj,
          BSmtLib.Span.Location.Internal.offset_new, BSmtLib.Span.Location.Internal.line_new,
          BSmtLib.Span.Location.Internal.column_new, true_and, and_true]) <;> omega)
    | rfl))

/-- After a step, the lexer state at the index `next` and the tokens taken are as the naive lexer's
run leaves them. The step and the run start from the naive lexer's pure state `st` at `location`
at the index `start`, under the version `ver`, with the tokens taken `coll` and the lexemes
`held`. -/
def StepPost (C : BSmtLibSpec.Lexer.Consumer) (v : Version) (hd : Bool) (iv : Version)
    (input : ByteSlice) (st : St) (location : Span.Location) (start : Nat) (ver : Version)
    (coll : List Handed) (held : List Lexeme) (next : Nat) (c : WP.WCore) (coll' : List Handed) :
    Prop :=
  ∃ st' location' held', Fixed v hd iv c ∧ c.base ≤ next ∧ StAgrees v C.concrete st' c ∧
    LocAt c c.offset c.base next location' ∧ Holds c.batch held' ∧
    c.batch.bytes = input.byteArray ∧
    outcome C hd (pending C hd ver coll held) (feedFrom v C.concrete input st location start) =
      outcome C hd (pending C hd c.version coll' held')
        (feedFrom v C.concrete input st' location' next)

/-- Why a step was interrupted. The step starts from the naive lexer's pure state `st` at
`location` at the index `start`, under the version `ver`, with the tokens taken `coll` and the
lexemes `held`, and is interrupted by `e` with the lexer state `c` and the tokens taken `coll'`.
Either the naive lexer's run fails with a lexical error, and what is left to do is to hand over
the lexemes of the batch of the lexer state; or the consumer stopped, at the stop `e` is, which
leaves the lexer discarding if it makes it discard. -/
def StepFails (C : BSmtLibSpec.Lexer.Consumer) {floor : Option Nat} (v : Version) (hd : Bool)
    (iv : Version) (input : ByteSlice) (st : St) (location : Span.Location) (start : Nat)
    (ver : Version) (coll : List Handed) (held : List Lexeme) (e : WP.Intr C floor)
    (c : WP.WCore)
    (coll' : List Handed) : Prop :=
  (IsLexical e ∧ ∃ held', Holds c.batch held' ∧ Fixed v hd iv c ∧
    c.batch.bytes = input.byteArray ∧
    outcome C hd (pending C hd ver coll held) (feedFrom v C.concrete input st location start) =
      outcome C hd (pending C hd c.version coll' held') (.error ([], intrFailure e))) ∨
  (∃ stop p, outcome C hd (pending C hd ver coll held)
      (feedFrom v C.concrete input st location start) = .stopped stop p ∧
    Matches stop e ∧ coll' = p.taken ∧ c.version = p.ver ∧ Holds c.batch [] ∧
    c.recovers = false ∧ c.holding = hd ∧ c.discardedFrom = stop.discards ∧
    c.recoveryState = none ∧ c.initialVersion = iv ∧ c.batch.bytes = input.byteArray)

section

variable {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat}

/-- What the consumer does after a stop on lexemes, whatever follows. -/
theorem outcome_of_stops {hd : Bool} {ver : Version} {coll : List Handed} {ls : List Lexeme}
    {e : WP.Intr C floor} {p : Prog} {d : Option Span.Location} (h : Stops C hd ver coll ls e p d)
    (rest : Consumers.Pure.RunF) :
    ∃ stop, outcome C hd (pending C hd ver coll ls) rest = .stopped stop p ∧ Matches stop e ∧
      stop.discards = d := by
  unfold Stops at h
  cases hp : pending C hd ver coll ls with
  | cont p' => rw [hp] at h; exact h.elim
  | stop st p' =>
    rw [hp] at h
    obtain ⟨rfl, hd', hm⟩ := h
    exact ⟨st, outcome_stop C hd st p rest, hm, hd'.symm⟩
  | wait r l p' =>
    rw [hp] at h
    obtain ⟨rfl, hd', hm⟩ := h
    subst hd'
    have hm' : ∀ next, Matches (C := C) (.brk r l next) e :=
      fun _ => .inl (hm.resolve_right fun ⟨_, h', _⟩ => nomatch h')
    cases rest with
    | ok e' =>
      obtain ⟨st, location, ls'⟩ := e'
      cases ls' with
      | nil => exact ⟨.brk r l none, rfl, hm' none, rfl⟩
      | cons l2 ls' =>
        refine ⟨.brk r l (some l2), ?_, hm' _, rfl⟩
        simp only [outcome, handAll_cons, hand1, handAll_stop, Model.finish]
    | error r =>
      obtain ⟨ls', f⟩ := r
      cases ls' with
      | nil => exact ⟨.brk r l none, rfl, hm' none, rfl⟩
      | cons l2 ls' =>
        refine ⟨.brk r l (some l2), ?_, hm' _, rfl⟩
        simp only [outcome, handAll_cons, hand1, handAll_stop, Model.finish]

variable {v : Version} {hd : Bool} {iv : Version} {input : ByteSlice} {st : St}
  {location : Span.Location} {start : Nat} {ver : Version} {coll : List Handed}
      {held : List Lexeme}

/-- A step interrupted where the consumer stopped. -/
theorem stepFails_of_stops {ver1 : Version} {coll1 : List Handed} {held1 : List Lexeme}
    {rest : Consumers.Pure.RunF}
    (h : outcome C hd (pending C hd ver coll held) (feedFrom v C.concrete input st location start) =
      outcome C hd (pending C hd ver1 coll1 held1) rest)
    {e : WP.Intr C floor} {p : Prog} {d : Option Span.Location}
    (hs : Stops C hd ver1 coll1 held1 e p d)
    {c : WP.WCore}
    (hv : c.version = p.ver) (hb : Holds c.batch []) (hr : c.recovers = false)
    (hh : c.holding = hd) (hd' : c.discardedFrom = d) (hrs : c.recoveryState = none)
    (hi : c.initialVersion = iv) (hby : c.batch.bytes = input.byteArray) :
    StepFails C v hd iv input st location start ver coll held e c p.taken := by
  obtain ⟨stop, h1, h2, h3⟩ := outcome_of_stops hs rest
  exact .inr ⟨stop, p, h.trans h1, h2, rfl, hv, hb, hr, hh, hd'.trans h3.symm, hrs, hi, hby⟩

/-- A step interrupted where the naive lexer's run fails before it finishes a lexeme, with the
consumer and the batch it started with. -/
theorem stepFails_here {e : WP.Intr C floor}
    (h : feedFrom v C.concrete input st location start = .error ([], intrFailure e))
    {c : WP.WCore} (hH : Holds c.batch held)
    (hfix : Fixed v hd iv c) (hv : c.version = ver)
    (he : IsLexical e := by refine ⟨_, rfl, ?_⟩; simp)
    (hby : c.batch.bytes = input.byteArray := by
      first | assumption | exact hpre.bytes) :
    StepFails C v hd iv input st location start ver coll held e c coll := by
  refine .inl ⟨he, held, hH, hfix, hby, ?_⟩
  rw [h, hv]

/-- A step's postcondition from a later state, whose outcome is that of the earlier one. -/
theorem StepPost.trans {st1 : St} {location1 : Span.Location} {start1 : Nat} {ver1 : Version}
    {coll1 : List Handed} {held1 : List Lexeme} {next : Nat} {c : WP.WCore} {coll' : List Handed}
    (h1 : outcome C hd (pending C hd ver coll held)
        (feedFrom v C.concrete input st location start) =
      outcome C hd (pending C hd ver1 coll1 held1)
        (feedFrom v C.concrete input st1 location1 start1))
    (h2 : StepPost C v hd iv input st1 location1 start1 ver1 coll1 held1 next c coll') :
    StepPost C v hd iv input st location start ver coll held next c coll' := by
  obtain ⟨st', location', held', h3, h4, h5, h6, h7, h8, h9⟩ := h2
  exact ⟨st', location', held', h3, h4, h5, h6, h7, h8, h1.trans h9⟩

/-- A step's failure from a later state, whose outcome is that of the earlier one. -/
theorem StepFails.trans {st1 : St} {location1 : Span.Location} {start1 : Nat} {ver1 : Version}
    {coll1 : List Handed} {held1 : List Lexeme}
    (h1 : outcome C hd (pending C hd ver coll held)
        (feedFrom v C.concrete input st location start) =
      outcome C hd (pending C hd ver1 coll1 held1)
        (feedFrom v C.concrete input st1 location1 start1))
    {e : WP.Intr C floor} {c : WP.WCore} {coll' : List Handed}
    (h2 : StepFails C v hd iv input st1 location1 start1 ver1 coll1 held1 e c coll') :
    StepFails C v hd iv input st location start ver coll held e c coll' := by
  rcases h2 with ⟨he, held', hH, hfix, hby, h⟩ | ⟨stop, p, h, rest⟩
  · exact .inl ⟨he, held', hH, hfix, hby, h1.trans h⟩
  · exact .inr ⟨stop, p, h1.trans h, rest⟩

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step
