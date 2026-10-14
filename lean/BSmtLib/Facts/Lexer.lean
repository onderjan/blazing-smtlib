import BSmtLib.Facts.Trusted
import BSmtLib.Facts.Lexer.Adapters
import BSmtLib.Facts.Proofs.Lexer.AdapterSteps
import BSmtLib.Facts.Proofs.Lexer.Consumers.VNaive
import BSmtLib.Facts.Proofs.Lexer.Consumers.Ports

/-!
# Proofs about the lexers

The chain of lexers that leads from the specification to the library's lexer, and what is
proved of them against the specification: each, as the adapter feeds it with the consumer that
answers as a consumer of the spec does (`Adapters.lexing`), is
`BSmtLibSpec.Lexer.CorrectWithConsumers`: it is correct with the collector of the spec, handles
every consumer that breaks at the end of the input, and is reset by the end of the input. That each
is then also `BSmtLibSpec.Lexer.Sequential` and `BSmtLibSpec.Lexer.WholeInputCorrect` follows by
`BSmtLibSpec.Facts.Lexicon`, which proves both of every lexer that is correct.
-/

/-!
## What holds

Each theorem below proves a property of the specification of a lexer of the chain, from the
modules imported above. Each is followed by the axioms its proof uses: only those of Lean's
standard library, no `sorry` and no axiom of its own. The build fails if that changes.
-/

namespace BSmtLib.Facts

/-! ### With every consumer -/

/-- The naive lexer, fed by the adapter with every consumer of the spec, is correct with every
consumer. -/
theorem Lexer.VNaive.correctWithConsumers :
    BSmtLibSpec.Lexer.CorrectWithConsumers (Adapters.lexing Adapters.VNaive.lexOps) :=
  Proofs.Lexer.Consumers.VNaive.correctWithConsumers_vNaive

/--
info: 'BSmtLib.Facts.Lexer.VNaive.correctWithConsumers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.VNaive.correctWithConsumers

/-- The Rust port, fed by the adapter with every consumer of the spec, is correct with every
consumer: it does with every consumer what the naive lexer does. -/
theorem Lexer.WRustPort.correctWithConsumers :
    BSmtLibSpec.Lexer.CorrectWithConsumers (Adapters.lexing Adapters.WRustPort.lexOps) :=
  Proofs.Lexer.Consumers.Ports.correctWithConsumers_wRustPort

/--
info: 'BSmtLib.Facts.Lexer.WRustPort.correctWithConsumers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.WRustPort.correctWithConsumers

/-- The lexer with the batch kept in its state, fed by the adapter with every consumer of the
spec, is correct with every consumer: it does with every consumer what the Rust port does. -/
theorem Lexer.X1BatchInCore.correctWithConsumers :
    BSmtLibSpec.Lexer.CorrectWithConsumers (Adapters.lexing Adapters.X1BatchInCore.lexOps) :=
  Proofs.Lexer.Consumers.Ports.correctWithConsumers_x1BatchInCore

/--
info: 'BSmtLib.Facts.Lexer.X1BatchInCore.correctWithConsumers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.X1BatchInCore.correctWithConsumers

/-- The library's lexer, fed by the adapter with every consumer of the spec, is correct with
every consumer: it does with every consumer what the lexer with the batch kept in its state does
with each slice too large for the positions of the library's lexer cut into chunks, and the
naive lexer does not tell how its input is cut. -/
theorem Lexer.correctWithConsumers :
    BSmtLibSpec.Lexer.CorrectWithConsumers (Adapters.lexing Adapters.Lexer.lexOps) :=
  Proofs.Lexer.Consumers.Ports.correctWithConsumers_lexer

/--
info: 'BSmtLib.Facts.Lexer.correctWithConsumers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.correctWithConsumers

/-! ### With the collector

Each theorem below is the first part of the one above for the same lexer: the lexer, fed by the
adapter slices and then, if the input has ended, the end of the input, with the collector of the
spec (`BSmtLibSpec.Lexer.Lexing.fed`), which takes every token, does not take whitespace and
comments, and breaks at the end of the input, is correct.
-/

/-- The naive lexer, fed by the adapter slices and then, if the input has ended, the end of the
input, with the collector of the spec, is correct. -/
theorem Lexer.VNaive.correct :
    BSmtLibSpec.Lexer.Correct (Adapters.lexing Adapters.VNaive.lexOps).fed :=
  Lexer.VNaive.correctWithConsumers.1

/--
info: 'BSmtLib.Facts.Lexer.VNaive.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.VNaive.correct

/-- The Rust port, fed by the adapter slices and then, if the input has ended, the end of the
input, with the collector of the spec, is correct. -/
theorem Lexer.WRustPort.correct :
    BSmtLibSpec.Lexer.Correct (Adapters.lexing Adapters.WRustPort.lexOps).fed :=
  Lexer.WRustPort.correctWithConsumers.1

/--
info: 'BSmtLib.Facts.Lexer.WRustPort.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.WRustPort.correct

/-- The lexer with the batch kept in its state, fed by the adapter slices and then, if the input
has ended, the end of the input, with the collector of the spec, is correct. -/
theorem Lexer.X1BatchInCore.correct :
    BSmtLibSpec.Lexer.Correct (Adapters.lexing Adapters.X1BatchInCore.lexOps).fed :=
  Lexer.X1BatchInCore.correctWithConsumers.1

/--
info: 'BSmtLib.Facts.Lexer.X1BatchInCore.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.X1BatchInCore.correct

/-- The library's lexer, fed by the adapter slices and then, if the input has ended, the end of
the input, with the collector of the spec, is correct. -/
theorem Lexer.correct : BSmtLibSpec.Lexer.Correct (Adapters.lexing Adapters.Lexer.lexOps).fed :=
  Lexer.correctWithConsumers.1

/--
info: 'BSmtLib.Facts.Lexer.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.correct

/-! ## What is trusted

A reader of the theorems above trusts the specification (`BSmtLibSpec`), the statements in this
file, and the definitions in `BSmtLib.Facts.Lexer.Adapters`, which put the lexers into the spec's
shapes: the adapters. The lexers of the chain are what the theorems are about and need no trust;
everything else Lean checks. The check below lists the adapters, every definition that the
statements of the theorems in this file rest on outside the specification, the library, the
lexers of the chain and Lean (`BSmtLib.Facts.Trusted`), and fails the build if one of them is
declared outside `BSmtLib.Facts.Lexer.Adapters`.
-/

/--
info: 8 theorems, stated with 27 adapters:
BSmtLib.Facts.Lexer.Adapters:
  BSmtLib.Facts.Lexer.Adapters.AnswerM
  BSmtLib.Facts.Lexer.Adapters.Answering
  BSmtLib.Facts.Lexer.Adapters.Answering.consume
  BSmtLib.Facts.Lexer.Adapters.Answering.entry
  BSmtLib.Facts.Lexer.Adapters.Answering.requests
  BSmtLib.Facts.Lexer.Adapters.Answering.switched
  BSmtLib.Facts.Lexer.Adapters.LexOps
  BSmtLib.Facts.Lexer.Adapters.LexOps.next
  BSmtLib.Facts.Lexer.Adapters.LexOps.runInput
  BSmtLib.Facts.Lexer.Adapters.LexOps.standing
  BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps
  BSmtLib.Facts.Lexer.Adapters.VNaive.lexOps
  BSmtLib.Facts.Lexer.Adapters.WRustPort.lexOps
  BSmtLib.Facts.Lexer.Adapters.X1BatchInCore.lexOps
  BSmtLib.Facts.Lexer.Adapters.eofResult
  BSmtLib.Facts.Lexer.Adapters.failureOf
  BSmtLib.Facts.Lexer.Adapters.fromVersion
  BSmtLib.Facts.Lexer.Adapters.instConsumeAnsweringResultOptionError
  BSmtLib.Facts.Lexer.Adapters.instConsumeFromAnsweringBatchCursorAnswerMResultOptionError
  BSmtLib.Facts.Lexer.Adapters.lexing
  BSmtLib.Facts.Lexer.Adapters.toContent
  BSmtLib.Facts.Lexer.Adapters.toHanded
  BSmtLib.Facts.Lexer.Adapters.toLayout
  BSmtLib.Facts.Lexer.Adapters.toLocation
  BSmtLib.Facts.Lexer.Adapters.toReservedKind
  BSmtLib.Facts.Lexer.Adapters.toTokenType
  BSmtLib.Facts.Lexer.Adapters.toVersion
-/
#guard_msgs in
#adapters within BSmtLib.Facts.Lexer.Adapters

end BSmtLib.Facts
