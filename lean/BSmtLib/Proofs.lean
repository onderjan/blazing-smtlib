import BSmtLib.Trusted
import BSmtLib.Proofs.Adapters
import BSmtLib.Proofs.AdapterSteps
import BSmtLib.Proofs.Consumers.VNaive
import BSmtLib.Proofs.Consumers.Ports

/-!
# Proofs about the lexers

The chain of lexers that leads from the specification to the library's lexer, and what is
proved of them against the specification: each, as the adapter feeds it with the consumer that
answers as a consumer of the spec does (`Adapter.lexing`), is `Spec.Lexer.CorrectWithConsumers`:
it is correct with the collector of the spec, handles every consumer that breaks at the end of
the input, and is reset by the end of the input. That each is then also `Spec.Lexer.Sequential`
and `Spec.Lexer.WholeInputCorrect` follows by `BSmtLib.SpecChecks`, which proves both of every
lexer that is correct.
-/

/-!
## What holds

Each theorem below proves a property of the specification of a lexer of the chain, from the
modules imported above. Each is followed by the axioms its proof uses: only those of Lean's
standard library, no `sorry` and no axiom of its own. The build fails if that changes.
-/

namespace BSmtLib.Proofs

open BSmtLib.Spec

/-! ### With every consumer -/

/-- The naive lexer, fed by the adapter with every consumer of the spec, is correct with every
consumer. -/
theorem Lexer.VNaive.correctWithConsumers :
    Spec.Lexer.CorrectWithConsumers (Adapter.lexing Adapter.VNaive.lexOps) :=
  Lexer.VNaive.correctWithConsumers_vNaive

/--
info: 'BSmtLib.Proofs.Lexer.VNaive.correctWithConsumers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.VNaive.correctWithConsumers

/-- The Rust port, fed by the adapter with every consumer of the spec, is correct with every
consumer: it does with every consumer what the naive lexer does. -/
theorem Lexer.WRustPort.correctWithConsumers :
    Spec.Lexer.CorrectWithConsumers (Adapter.lexing Adapter.WRustPort.lexOps) :=
  Adapter.correctWithConsumers_wRustPort

/--
info: 'BSmtLib.Proofs.Lexer.WRustPort.correctWithConsumers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.WRustPort.correctWithConsumers

/-- The lexer with the batch kept in its state, fed by the adapter with every consumer of the
spec, is correct with every consumer: it does with every consumer what the Rust port does. -/
theorem Lexer.X1BatchInCore.correctWithConsumers :
    Spec.Lexer.CorrectWithConsumers (Adapter.lexing Adapter.X1BatchInCore.lexOps) :=
  Adapter.correctWithConsumers_x1BatchInCore

/--
info: 'BSmtLib.Proofs.Lexer.X1BatchInCore.correctWithConsumers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.X1BatchInCore.correctWithConsumers

/-- The library's lexer, fed by the adapter with every consumer of the spec, is correct with
every consumer: it does with every consumer what the lexer with the batch kept in its state does
with each slice too large for the positions of the library's lexer cut into chunks, and the
naive lexer does not tell how its input is cut. -/
theorem Lexer.correctWithConsumers :
    Spec.Lexer.CorrectWithConsumers (Adapter.lexing Adapter.Lexer.lexOps) :=
  Adapter.correctWithConsumers_lexer

/--
info: 'BSmtLib.Proofs.Lexer.correctWithConsumers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.correctWithConsumers

/-! ### With the collector

Each theorem below is the first part of the one above for the same lexer: the lexer, fed by the
adapter slices and then, if the input has ended, the end of the input, with the collector of the
spec (`Spec.Lexer.Lexing.fed`), which takes every token, does not take whitespace and comments,
and breaks at the end of the input, is correct.
-/

/-- The naive lexer, fed by the adapter slices and then, if the input has ended, the end of the
input, with the collector of the spec, is correct. -/
theorem Lexer.VNaive.correct :
    Spec.Lexer.Correct (Adapter.lexing Adapter.VNaive.lexOps).fed :=
  Lexer.VNaive.correctWithConsumers.1

/--
info: 'BSmtLib.Proofs.Lexer.VNaive.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.VNaive.correct

/-- The Rust port, fed by the adapter slices and then, if the input has ended, the end of the
input, with the collector of the spec, is correct. -/
theorem Lexer.WRustPort.correct :
    Spec.Lexer.Correct (Adapter.lexing Adapter.WRustPort.lexOps).fed :=
  Lexer.WRustPort.correctWithConsumers.1

/--
info: 'BSmtLib.Proofs.Lexer.WRustPort.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.WRustPort.correct

/-- The lexer with the batch kept in its state, fed by the adapter slices and then, if the input
has ended, the end of the input, with the collector of the spec, is correct. -/
theorem Lexer.X1BatchInCore.correct :
    Spec.Lexer.Correct (Adapter.lexing Adapter.X1BatchInCore.lexOps).fed :=
  Lexer.X1BatchInCore.correctWithConsumers.1

/--
info: 'BSmtLib.Proofs.Lexer.X1BatchInCore.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.X1BatchInCore.correct

/-- The library's lexer, fed by the adapter slices and then, if the input has ended, the end of
the input, with the collector of the spec, is correct. -/
theorem Lexer.correct : Spec.Lexer.Correct (Adapter.lexing Adapter.Lexer.lexOps).fed :=
  Lexer.correctWithConsumers.1

/--
info: 'BSmtLib.Proofs.Lexer.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.correct

/-! ## What is trusted

A reader of the theorems above trusts the specification (`BSmtLib.Spec`), the statements in this
file, and the definitions in `BSmtLib.Proofs.Adapters`, which put the lexers into the spec's
shapes: the adapters. The lexers of the chain are what the theorems are about and need no trust;
everything else Lean checks. The check below lists the adapters, every definition that the
statements of the theorems in this file rest on outside the specification, the library, the
lexers of the chain and Lean (`BSmtLib.Trusted`), and fails the build if one of them is declared
outside `BSmtLib.Proofs.Adapters`.
-/

/--
info: 8 theorems, stated with 27 adapters:
BSmtLib.Proofs.Adapters:
  BSmtLib.Proofs.Adapter.AnswerM
  BSmtLib.Proofs.Adapter.Answering
  BSmtLib.Proofs.Adapter.Answering.consume
  BSmtLib.Proofs.Adapter.Answering.entry
  BSmtLib.Proofs.Adapter.Answering.requests
  BSmtLib.Proofs.Adapter.Answering.switched
  BSmtLib.Proofs.Adapter.LexOps
  BSmtLib.Proofs.Adapter.LexOps.next
  BSmtLib.Proofs.Adapter.LexOps.runInput
  BSmtLib.Proofs.Adapter.LexOps.standing
  BSmtLib.Proofs.Adapter.Lexer.lexOps
  BSmtLib.Proofs.Adapter.VNaive.lexOps
  BSmtLib.Proofs.Adapter.WRustPort.lexOps
  BSmtLib.Proofs.Adapter.X1BatchInCore.lexOps
  BSmtLib.Proofs.Adapter.eofResult
  BSmtLib.Proofs.Adapter.failureOf
  BSmtLib.Proofs.Adapter.fromVersion
  BSmtLib.Proofs.Adapter.instConsumeAnsweringResultOptionError
  BSmtLib.Proofs.Adapter.instConsumeFromAnsweringBatchCursorAnswerMResultOptionError
  BSmtLib.Proofs.Adapter.lexing
  BSmtLib.Proofs.Adapter.toContent
  BSmtLib.Proofs.Adapter.toHanded
  BSmtLib.Proofs.Adapter.toLayout
  BSmtLib.Proofs.Adapter.toLocation
  BSmtLib.Proofs.Adapter.toReservedKind
  BSmtLib.Proofs.Adapter.toTokenType
  BSmtLib.Proofs.Adapter.toVersion
-/
#guard_msgs in
#adapters within BSmtLib.Proofs.Adapters

end BSmtLib.Proofs
