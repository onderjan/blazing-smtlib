import BSmtLib.Proofs.V1NaiveWRustPort.Agree
import BSmtLib.Proofs.V1NaiveWRustPort.Runs

/-!
# What a step of the Rust port keeps

A step of the Rust port's loop over a slice (`WRustPort.lexStep`) lexes the slice from the
lexer's index `start` to an index after it. It keeps the correspondence with the naive lexer: if
the lexer state is the naive lexer's pure state at `start` (`StepPre`), then after the step it
is the pure state at the index the step returns, with the lexemes not yet handed over in its
batch, and the adapter's consumer is left at the end of the slice with what it would have been
left with from `start` (`StepPost`). If the step is interrupted, the consumer would have failed,
or the naive lexer's run fails, and the consumer and the batch of the lexer state hold the
lexemes the run finishes before the failure (`StepFails`).
-/

namespace BSmtLib.Proofs.Lexer.V1NaiveWRustPort

open BSmtLib.Proofs.Adapter V1Naive BSmtLib.Proofs.Simulation

/-- The lexer state at the index `start` of the slice is the naive lexer's pure state `st` at
`location`, under the version, and its batch holds the lexemes `held`, with their contents in
the slice. -/
structure StepPre (v : Version) (input : ByteSlice) (st : St) (location : Location)
    (held : List Lexeme) (start : Nat) (c : WCore) : Prop where
  fixed : Fixed v c
  base : c.base = start
  agrees : StAgrees v st c
  loc : LocAt c c.offset c.base start location
  holds : Holds c.batch held
  bytes : c.batch.bytes = input.byteArray

/-- The lexer state at the index `next` and the consumer are, after a step from the naive
lexer's pure state `st` at `location` at the index `start`, with the consumer `coll` and the
lexemes `held`, as the naive lexer's run from there leaves them. -/
def StepPost (v : Version) (input : ByteSlice) (st : St) (location : Location) (start : Nat)
    (coll : Collector) (held : List Lexeme) (next : Nat) (c : WCore) (coll' : Collector) : Prop :=
  ∃ st' location' held', Fixed v c ∧ c.base ≤ next ∧ StAgrees v st' c ∧
    LocAt c c.offset c.base next location' ∧ Holds c.batch held' ∧
    c.batch.bytes = input.byteArray ∧
    outcome v (pending v coll held) (feedFrom v input st location start) =
      outcome v (pending v coll' held') (feedFrom v input st' location' next)

/-- The step from the naive lexer's pure state `st` at `location` at the index `start`, with
the consumer `coll` and the lexemes `held`, interrupted with the lexer state `c` and the
consumer `coll'`: the consumer would have failed, or the naive lexer's run fails, and the
consumer and the batch of the lexer state hold what the consumer records of the lexemes the run
finishes before the failure, under the version, in a lexer that does not recover. -/
def StepFails (v : Version) (input : ByteSlice) (st : St) (location : Location) (start : Nat)
    (coll : Collector) (held : List Lexeme) (c : WCore) (coll' : Collector) : Prop :=
  match outcome v (pending v coll held) (feedFrom v input st location start) with
  | some (.ok _) => False
  | some (.error hs) =>
    ∃ held', Holds c.batch held' ∧ c.version = v ∧ c.recovers = false ∧
      pending v coll' held' = some hs
  | none => True

/-- A step interrupted where the consumer would have failed. -/
theorem stepFails_of_none {v : Version} {input : ByteSlice} {st : St} {location : Location}
    {start : Nat} {coll : Collector} {held : List Lexeme} {c : WCore} {coll' : Collector}
    (h : outcome v (pending v coll held) (feedFrom v input st location start) = none) :
    StepFails v input st location start coll held c coll' := by
  unfold StepFails
  rw [h]
  trivial

/-- A step interrupted where the naive lexer's run fails before it finishes a lexeme, with the
consumer and the batch it started with. -/
theorem stepFails_here {v : Version} {input : ByteSlice} {st : St} {location : Location}
    {start : Nat} {coll : Collector} {held : List Lexeme} {c : WCore}
    (h : feedFrom v input st location start = .error []) (hH : Holds c.batch held)
    (hv : c.version = v) (hr : c.recovers = false) :
    StepFails v input st location start coll held c coll := by
  unfold StepFails
  rw [h, outcome_error_nil]
  cases hp : pending v coll held with
  | none => trivial
  | some hs => exact ⟨held, hH, hv, hr, hp⟩

end BSmtLib.Proofs.Lexer.V1NaiveWRustPort
