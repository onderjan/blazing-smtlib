import BSmtLib.Spec.Parser

/-!
# Programs that read what a parser receives

A program is what a parser does, written out as data: it receives the next item, makes a
handler call and goes on with what the handler returned, ends the script, switches the version,
or stops because what it received is not what it expected. `Program.run` runs a program on
items with points, a handler, a producer and a policy, as the traversal runs, taking
an item for each receipt.

A program decides what to do next only from what it has received and what the handler
returned, so what it does before the arrival of an item depends only on the items before it.
That is what makes a program the form in which the placement of the calls can be proved.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Parser

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal

/-- What a parser does, as data, with the handler's values `values` and the result `α`. -/
inductive Program (values : Values) (α : Type) : Type where
  /-- The result. -/
  | done (result : α)
  /-- Receive the next item, with the start of the script at its arrival if `start`. -/
  | receive (start : Bool) (next : Received → Program values α)
  /-- Make the handler call, and go on with what it returns. -/
  | call {returns : Returns} (request : Call values returns)
      (next : values.of returns → Program values α)
  /-- End the script. -/
  | endScript (next : Program values α)
  /-- Have the producer discard the rest of the input. -/
  | discard (next : Program values α)
  /-- Switch to the version, after the given number of declarations. -/
  | switch (declarations : Nat) (version : Version) (next : Program values α)
  /-- Stop: what was received is not what was expected. -/
  | stuck

namespace Program

variable {values : Values}

/-- The program, then the program its result chooses. -/
def bind {α β : Type} : Program values α → (α → Program values β) → Program values β
  | .done result, f => f result
  | .receive start next, f => .receive start fun item => (next item).bind f
  | .call request next, f => .call request fun value => (next value).bind f
  | .endScript next, f => .endScript (next.bind f)
  | .discard next, f => .discard (next.bind f)
  | .switch declarations version next, f => .switch declarations version (next.bind f)
  | .stuck, _ => .stuck

instance : Monad (Program values) where
  pure := .done
  bind := bind

@[simp] theorem pure_eq {α : Type} (a : α) : (pure a : Program values α) = .done a := rfl

@[simp] theorem done_bind {α β : Type} (a : α) (f : α → Program values β) :
    (Program.done a >>= f) = f a := rfl

@[simp] theorem receive_bind {α β : Type} (start : Bool) (next : Received → Program values α)
    (f : α → Program values β) :
    (Program.receive start next >>= f) = .receive start fun item => next item >>= f := rfl

@[simp] theorem call_bind {α β : Type} {returns : Returns} (request : Call values returns)
    (next : values.of returns → Program values α) (f : α → Program values β) :
    (Program.call request next >>= f) = .call request fun value => next value >>= f := rfl

@[simp] theorem endScript_bind {α β : Type} (next : Program values α)
    (f : α → Program values β) : (Program.endScript next >>= f) = .endScript (next >>= f) :=
  rfl

@[simp] theorem discard_bind {α β : Type} (next : Program values α)
    (f : α → Program values β) : (Program.discard next >>= f) = .discard (next >>= f) :=
  rfl

@[simp] theorem switch_bind {α β : Type} (declarations : Nat) (version : Version)
    (next : Program values α) (f : α → Program values β) :
    (Program.switch declarations version next >>= f) =
      .switch declarations version (next >>= f) := rfl

@[simp] theorem stuck_bind {α β : Type} (f : α → Program values β) :
    ((Program.stuck : Program values α) >>= f) = .stuck := rfl

theorem bind_bind {α β γ : Type} (p : Program values α) (f : α → Program values β)
    (g : β → Program values γ) : (p >>= f) >>= g = p >>= fun a => f a >>= g := by
  induction p with
  | done => rfl
  | receive start next ih => simp [ih]
  | call request next ih => simp [ih]
  | endScript next ih => simp [ih]
  | discard next ih => simp [ih]
  | switch declarations version next ih => simp [ih]
  | stuck => rfl

/-- Receive the next item. -/
def next : Program values Received := .receive false .done

/-- Receive the next item and go on with the reader of what starts with it. -/
def parseWith {α : Type} (reader : Received → Program values α) : Program values α :=
  next >>= reader

/-- Make the handler call. -/
def emit {returns : Returns} (request : Call values returns) : Program values (values.of returns) :=
  .call request .done

/-- Make a call that returns a handled sort. -/
def emitSort (request : Call values .sort) : Program values values.sort := emit request

/-- Make a call that returns a handled s-expression. -/
def emitSExpr (request : Call values .sExpr) : Program values values.sExpr := emit request

/-- Make a call that returns a handled attribute. -/
def emitAttribute (request : Call values .attribute) : Program values values.«attribute» :=
  emit request

/-- Make a call that returns a handled term. -/
def emitTerm (request : Call values .term) : Program values values.term := emit request

/-- Make a call that returns a scope value. -/
def emitScope (request : Call values .scope) : Program values values.scope := emit request

/-- Make a call that returns nothing. -/
def emitUnit (request : Call values .nothing) : Program values Unit := emit request

/-! ## Running a program -/

section

variable {m : Type → Type} [Monad m] {ε : Type}
variable (points : Points m) (handler : Handler m ε values)
variable (producer : Producer m) (policy : VersionPolicy)

/-- The handler's answer to a call that returns a handled sort. -/
def callSort (request : Call values .sort) : Run m ε values.sort := Traversal.call handler request

/-- The handler's answer to a call that returns a handled s-expression. -/
def callSExpr (request : Call values .sExpr) : Run m ε values.sExpr :=
  Traversal.call handler request

/-- The handler's answer to a call that returns a handled attribute. -/
def callAttribute (request : Call values .attribute) : Run m ε values.«attribute» :=
  Traversal.call handler request

/-- The handler's answer to a call that returns a handled term. -/
def callTerm (request : Call values .term) : Run m ε values.term := Traversal.call handler request

/-- The handler's answer to a call that returns a scope value. -/
def callScope (request : Call values .scope) : Run m ε values.scope :=
  Traversal.call handler request

/-- The handler's answer to a call that returns nothing. -/
def callUnit (request : Call values .nothing) : Run m ε Unit := Traversal.call handler request

/-- The failure of a program that is stuck or runs out of items: a syntax error, since a
program can only get stuck on items that are not a script. Which syntax error does not matter:
on the items of a script, no program of a parser gets stuck. -/
def stuckFailure : Cause ε := .syntax .unsupportedVersion

/-- The program run on the items, with the result and the items it did not take. -/
def run {α : Type} : Program values α → List Received → Run m ε (α × List Received)
  | .done result, items => pure (result, items)
  | .receive start next, item :: items => do
    Traversal.receive points item (if start then ExceptT.lift handler.startScript else pure ())
    run (next item) items
  | .receive _ _, [] => throw stuckFailure
  | .call request next, items => do
    let value ← Traversal.call handler request
    run (next value) items
  | .endScript next, items => do
    ExceptT.lift handler.endScript
    run next items
  | .discard next, items => do
    ExceptT.lift producer.discardRest
    run next items
  | .switch declarations version next, items => do
    switchVersion handler producer policy declarations version
    run next items
  | .stuck, _ => throw stuckFailure

@[simp] theorem run_done {α : Type} (a : α) (items : List Received) :
    run points handler producer policy (.done a) items = pure (a, items) := rfl

variable [LawfulMonad m] in
theorem run_bind {α β : Type} (p : Program values α) (f : α → Program values β)
    (items : List Received) :
    run points handler producer policy (p >>= f) items =
      run points handler producer policy p items >>= fun (a, rest) =>
        run points handler producer policy (f a) rest := by
  induction p generalizing items with
  | done => simp
  | receive start next ih =>
    cases items with
    | nil => simp [run]
    | cons item items => simp [run, ih]
  | call request next ih => simp [run, ih]
  | endScript next ih => simp [run, ih]
  | discard next ih => simp [run, ih]
  | switch declarations version next ih => simp [run, ih]
  | stuck => simp [run]

theorem run_receive {α : Type} (start : Bool) (next : Received → Program values α)
    (item : Received) (items : List Received) :
    run points handler producer policy (.receive start next) (item :: items) =
      (Traversal.receive points item (if start then ExceptT.lift handler.startScript else pure ())
        >>= fun _ => run points handler producer policy (next item) items) := rfl

theorem run_next (item : Received) (items : List Received) :
    run points handler producer policy next (item :: items) =
      Traversal.receive points item >>= fun _ => pure (item, items) := by
  simp [next, run]

theorem run_parseWith {α : Type} (reader : Received → Program values α) (item : Received)
    (items : List Received) :
    run points handler producer policy (parseWith reader) (item :: items) =
      Traversal.receive points item >>= fun _ =>
        run points handler producer policy (reader item) items := by
  simp [parseWith, next, run]

theorem run_next_bind {α : Type} (f : Received → Program values α) (item : Received)
    (items : List Received) :
    run points handler producer policy (next >>= f) (item :: items) =
      Traversal.receive points item >>= fun _ =>
        run points handler producer policy (f item) items := by
  simp [next, run]

theorem run_emit_bind {α : Type} {returns : Returns} (request : Call values returns)
    (f : values.of returns → Program values α) (items : List Received) :
    run points handler producer policy (emit request >>= f) items =
      Traversal.call handler request >>= fun value =>
        run points handler producer policy (f value) items := by
  simp [emit, run]

theorem run_emit {returns : Returns} (request : Call values returns) (items : List Received) :
    run points handler producer policy (emit request) items =
      Traversal.call handler request >>= fun value => pure (value, items) := by
  simp [emit, run]

theorem run_emitSort (request : Call values .sort) (items : List Received) :
    run points handler producer policy (emitSort request) items =
      (callSort handler request >>= fun value => pure (value, items) :
        Run m ε (values.sort × List Received)) := run_emit _ _ _ _ _ _

theorem run_emitSExpr (request : Call values .sExpr) (items : List Received) :
    run points handler producer policy (emitSExpr request) items =
      (callSExpr handler request >>= fun value => pure (value, items) :
        Run m ε (values.sExpr × List Received)) := run_emit _ _ _ _ _ _

theorem run_emitAttribute (request : Call values .attribute) (items : List Received) :
    run points handler producer policy (emitAttribute request) items =
      (callAttribute handler request >>= fun value => pure (value, items) :
        Run m ε (values.«attribute» × List Received)) := run_emit _ _ _ _ _ _

theorem run_emitTerm (request : Call values .term) (items : List Received) :
    run points handler producer policy (emitTerm request) items =
      (callTerm handler request >>= fun value => pure (value, items) :
        Run m ε (values.term × List Received)) := run_emit _ _ _ _ _ _

theorem run_emitScope (request : Call values .scope) (items : List Received) :
    run points handler producer policy (emitScope request) items =
      (callScope handler request >>= fun value => pure (value, items) :
        Run m ε (values.scope × List Received)) := run_emit _ _ _ _ _ _

theorem run_emitUnit (request : Call values .nothing) (items : List Received) :
    run points handler producer policy (emitUnit request) items =
      (callUnit handler request >>= fun value => pure (value, items) :
        Run m ε (Unit × List Received)) := run_emit _ _ _ _ _ _

end

end Program

end BSmtLib.SpecChecks.Parser
