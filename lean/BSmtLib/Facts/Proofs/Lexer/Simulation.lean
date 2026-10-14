module

public import BSmtLib.Facts.Proofs.Lexer.Simulation.Relation
public import BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
public import BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes

@[expose] public section

/-!
# Simulation of one lexer's steps by another's

The framework in which the links between the lexers of the chain are proved, in parts:

- `Simulation.Steps`: the steps of the lexers, an exception over the lexer's state over the
  consumer's, and their simulation by a map of the states, from every state (`Sim`) or under
  conditions on the states, with an invariant for the states the steps are interrupted in
  (`SimF`, `SimP`);
- `Simulation.Couple`: computations coupled with related values, in any monad (`MCouple`), in
  the consumer's monad (`Couple`), and on the lexers' states (`ISim`);
- `Simulation.Relation`: the simulation of the steps under a relation of the states (`SimR`);
- `Simulation.Batch`: batches that hold the same tokens and cursors over them (`Agree`,
  `CursorAgree`), and consumers that do not tell such cursors apart (`ConsumesAlike`);
- `Simulation.Bytes`: byte arrays, views of them, and the content buffer.
-/
