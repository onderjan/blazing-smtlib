module

public import BSmtLibSpec.Facts.Proofs.Parser.Bridge

@[expose] public section

/-!
# Facts about the parser

The traversal, for every handler:

- it makes the calls of a parser that goes by the items it receives;
- its calls rebuild the script;
- its calls are placed by the items before them.

Each theorem below proves a property of the specification formalism (`BSmtLibSpec`), from the
modules imported above. Each is followed by the axioms its proof uses: only those of Lean's standard
library, no `sorry` and no axiom of its own. The build fails if that changes.
-/

namespace BSmtLibSpec.Facts

/-!
### The traversal as a parser

`Parser.parseScript` is a program that makes the traversal's calls going by the items a parser
receives rather than by the syntax tree: it receives an item, and decides from it and from what
it received before what to do next. It makes the calls of the traversal of every script, for
every handler, so the traversal can be carried out by a parser that has only the items so far.
-/

/--
For every handler in a lawful monad, points, producer and policy, the traversal of a
script makes what `Parser.parseScript` makes run on what a parser receives for the script, given
fuel larger than ten times the size of the script; whatever follows is left untouched.
-/
theorem Parser.script_eq_parse {m : Type → Type} [Monad m] [LawfulMonad m] {ε : Type}
    {values : BSmtLibSpec.Parser.Traversal.Values} (points : BSmtLibSpec.Parser.Traversal.Points m)
    (handler : BSmtLibSpec.Parser.Traversal.Handler m ε values)
    (producer : BSmtLibSpec.Parser.Traversal.Producer m)
    (policy : BSmtLibSpec.Parser.VersionPolicy) {version : Lexicon.Version}
    {commands : List Grammar.Tree.Command} (h : Grammar.Script version commands)
    (rest : List BSmtLibSpec.Parser.Traversal.Received) {n : Nat} (hn : 10 * sizeOf commands < n) :
    Proofs.Parser.Program.run points handler producer policy
        (Proofs.Parser.Parse.parseScript n version)
        (BSmtLibSpec.Parser.Properties.received commands ++ rest) =
      (BSmtLibSpec.Parser.Traversal.script points handler producer policy version commands >>= fun
          _ =>
        pure ((), rest)) :=
  Proofs.Parser.Simulation.run_script version commands rest h hn

/--
info: 'BSmtLibSpec.Facts.Parser.script_eq_parse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.script_eq_parse

/-!
### What a recording shows

`Parser.Recovery.recover` rebuilds the commands of a script from the calls of its recording
alone: each call stands for the tree it reports, built from what the earlier calls it names
stand for.
-/

/-- The traversal of a script takes exactly what a parser receives for it, each item arriving
and then processed, in order. -/
theorem Parser.takesItsTokens : BSmtLibSpec.Parser.Properties.TakesItsTokens :=
  fun _ _ h => Proofs.Parser.Calls.record_items h

/--
info: 'BSmtLibSpec.Facts.Parser.takesItsTokens' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.takesItsTokens

/-- The calls of the recording of a script rebuild the script. -/
theorem Parser.recoverRebuilds {version : Lexicon.Version} {commands : List Grammar.Tree.Command}
    (h : Grammar.Script version commands) :
    Proofs.Parser.Recovery.recover version
      ((BSmtLibSpec.Parser.Properties.record version commands).filter
          BSmtLibSpec.Parser.Properties.Event.isCall) = some commands :=
  Proofs.Parser.Calls.recover_record h

/--
info: 'BSmtLibSpec.Facts.Parser.recoverRebuilds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.recoverRebuilds

/-- Two scripts from the same version whose traversals make the same calls are the same
script. -/
theorem Parser.callsDetermineScript : BSmtLibSpec.Parser.Properties.CallsDetermineScript := by
  intro version commands commands' h h' hcalls
  have := Proofs.Parser.Calls.recover_record h
  rw [hcalls, Proofs.Parser.Calls.recover_record h'] at this
  exact (Option.some.inj this).symm

/--
info: 'BSmtLibSpec.Facts.Parser.callsDetermineScript' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.callsDetermineScript

/-- What the traversal of a script has done before an item arrives, and before it is processed,
depends only on the items before it. -/
theorem Parser.placementDetermined : BSmtLibSpec.Parser.Properties.PlacementDetermined := by
  intro version commands commands' count h h' ht
  let n := 10 * (sizeOf commands + sizeOf commands') + 1
  rw [Proofs.Parser.Calls.record_eq_trace h (n := n)
      (by omega), Proofs.Parser.Calls.record_eq_trace h' (n := n) (by omega)]
  exact ⟨Proofs.Parser.Placement.eventsBefore_trace _ _ _ _ _ ht,
    Proofs.Parser.Placement.eventsBeforeProcessing_trace _ _ _ _ _ ht
        (Proofs.Parser.Placement.received_length h h' ht)⟩

/--
info: 'BSmtLibSpec.Facts.Parser.placementDetermined' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.placementDetermined

/-!
### Every handler is placed as the recording

The properties of the traversal are stated on recordings. `Parser.cutRun` is the traversal of a
script with any handler, points, producer and policy, stopped at the arrival of the item
at a given position: what such a run has done before that item arrives. The two theorems below
carry `BSmtLibSpec.Parser.Properties.PlacementDetermined` over to every handler: the cut runs of two
scripts from the same version are equal when what a parser receives for them agrees before the cut,
and the cut runs of two scripts are equal when their recordings do.
They are checks of the formalism, not properties stated in it.
-/

/--
For every handler in a lawful monad, points, producer and policy, what the traversals of
two valid scripts from the same version have done before the item at position `count` arrives
is the same when what a parser receives for them agrees before that item.
-/
theorem Parser.cutRunsAgree {m : Type → Type} [Monad m] [LawfulMonad m] {ε : Type}
    {values : BSmtLibSpec.Parser.Traversal.Values} (points : BSmtLibSpec.Parser.Traversal.Points m)
    (handler : BSmtLibSpec.Parser.Traversal.Handler m ε values)
    (producer : BSmtLibSpec.Parser.Traversal.Producer m)
    (policy : BSmtLibSpec.Parser.VersionPolicy) (count : Nat) {version : Lexicon.Version}
    {commands commands' : List Grammar.Tree.Command} (h : Grammar.Script version commands)
    (h' : Grammar.Script version commands')
    (ht : (BSmtLibSpec.Parser.Properties.received commands).take count =
      (BSmtLibSpec.Parser.Properties.received commands').take count) :
    Proofs.Parser.Bridge.cutRun points handler producer policy count version commands =
      Proofs.Parser.Bridge.cutRun points handler producer policy count version commands' :=
  Proofs.Parser.Bridge.cutRun_eq points handler producer policy count h h' ht

/--
info: 'BSmtLibSpec.Facts.Parser.cutRunsAgree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.cutRunsAgree

/--
For every handler in a lawful monad, points, producer and policy, what the traversals of
two valid scripts have done before the item at position `count` arrives is the same when their
recordings agree before that item: a recording stands for the run with every handler.
-/
theorem Parser.cutRunsAgreeByRecord {m : Type → Type} [Monad m] [LawfulMonad m] {ε : Type}
    {values : BSmtLibSpec.Parser.Traversal.Values} (points : BSmtLibSpec.Parser.Traversal.Points m)
    (handler : BSmtLibSpec.Parser.Traversal.Handler m ε values)
    (producer : BSmtLibSpec.Parser.Traversal.Producer m)
    (policy : BSmtLibSpec.Parser.VersionPolicy) (count : Nat) {version version' : Lexicon.Version}
    {commands commands' : List Grammar.Tree.Command} (h : Grammar.Script version commands)
    (h' : Grammar.Script version' commands')
    (he : BSmtLibSpec.Parser.Properties.eventsBefore count
    (BSmtLibSpec.Parser.Properties.record version commands) =
      BSmtLibSpec.Parser.Properties.eventsBefore count
          (BSmtLibSpec.Parser.Properties.record version' commands')) :
    Proofs.Parser.Bridge.cutRun points handler producer policy count version commands =
      Proofs.Parser.Bridge.cutRun points handler producer policy count version' commands' :=
  Proofs.Parser.Bridge.cutRun_eq_of_record points handler producer policy count h h' he

/--
info: 'BSmtLibSpec.Facts.Parser.cutRunsAgreeByRecord' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.cutRunsAgreeByRecord

/--
For every handler in a lawful monad, points, producer and policy, what the traversals of
two valid scripts have done when the item at position `count` is rejected, before it is
processed and without its own arrival, is the same when their recordings agree before the
processing of that item.
-/
theorem Parser.processingCutRunsAgreeByRecord {m : Type → Type} [Monad m] [LawfulMonad m]
    {ε : Type} {values : BSmtLibSpec.Parser.Traversal.Values}
    (points : BSmtLibSpec.Parser.Traversal.Points m)
    (handler : BSmtLibSpec.Parser.Traversal.Handler m ε values)
    (producer : BSmtLibSpec.Parser.Traversal.Producer m)
    (policy : BSmtLibSpec.Parser.VersionPolicy) (count : Nat) {version version' : Lexicon.Version}
    {commands commands' : List Grammar.Tree.Command} (h : Grammar.Script version commands)
    (h' : Grammar.Script version' commands')
    (he : BSmtLibSpec.Parser.Properties.eventsBeforeProcessing count
    (BSmtLibSpec.Parser.Properties.record version commands) =
      BSmtLibSpec.Parser.Properties.eventsBeforeProcessing count
          (BSmtLibSpec.Parser.Properties.record version' commands')) :
    Proofs.Parser.Bridge.processingCutRun points handler producer policy count version commands =
      Proofs.Parser.Bridge.processingCutRun points handler producer policy count version' commands'
          :=
  Proofs.Parser.Bridge.processingCutRun_eq_of_record points handler producer policy count h h' he

/--
info: 'BSmtLibSpec.Facts.Parser.processingCutRunsAgreeByRecord' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Parser.processingCutRunsAgreeByRecord

end BSmtLibSpec.Facts
