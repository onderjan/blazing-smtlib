import BSmtLibSpec.Facts.Proofs.Lexer.Streaming
import BSmtLibSpec.Facts.Proofs.Lexer.StreamingFacts
import BSmtLibSpec.Facts.Proofs.Lexer.Consumers

/-!
# Facts of a lexer

A lexer fed in slices: what its properties ask for exists, and a lexer that is correct hands over
more as it is fed more or the end of the input, and is correct on whole inputs. A lexer and its
consumers: what a lexer does with a consumer is determined, and the input after a switch of the
version is located as in the whole input.

Each theorem below proves a property of the specification, from the modules imported above.
Each is followed by the axioms its proof uses: only those of Lean's standard library, no
`sorry` and no axiom of its own. The build fails if that changes.
-/

namespace BSmtLibSpec.Facts

/-!
### A lexer fed in slices

`BSmtLibSpec.Lexer.HandsOverMaximal` asks for the tokens maximal to hand over on the longest viable
start of the input; both exist and are unique, so it is not vacuous. `BSmtLibSpec.Lexer.Sequential`
and `BSmtLibSpec.Lexer.WholeInputCorrect` are not a part of `BSmtLibSpec.Lexer.Correct`, as they
follow from it, for every lexer.
-/

/-- Every input has exactly one longest viable start. -/
theorem Lexer.longestViableStart_existsUnique (version : Lexicon.Version)
    (input : Regex.Chars) :
    ∃ start, BSmtLibSpec.Lexer.LongestViableStart version input start ∧
      ∀ start', BSmtLibSpec.Lexer.LongestViableStart version input start' → start' = start :=
  let ⟨start, h⟩ := Proofs.Lexer.StreamingFacts.exists_longestViableStart version input
  ⟨start, h, fun _ h' => Proofs.Lexer.StreamingFacts.longestViableStart_unique h' h⟩

/--
info: 'BSmtLibSpec.Facts.Lexer.longestViableStart_existsUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.longestViableStart_existsUnique

/-- On a viable input, exactly one list of tokens is maximal to hand over. -/
theorem Lexer.handoverMaximal_existsUnique {version : Lexicon.Version}
    {input : Regex.Chars} (h : Lexicon.Properties.Viable version input) :
    ∃ tokens, BSmtLibSpec.Lexer.HandoverMaximal version input tokens ∧
      ∀ tokens', BSmtLibSpec.Lexer.HandoverMaximal version input tokens' → tokens' = tokens :=
  let ⟨tokens, ht⟩ := Proofs.Lexer.StreamingFacts.exists_handoverMaximal h
  ⟨tokens, ht, fun _ h' => Proofs.Lexer.Streaming.handoverMaximal_unique h h' ht⟩

/--
info: 'BSmtLibSpec.Facts.Lexer.handoverMaximal_existsUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.handoverMaximal_existsUnique

/-- A lexer that is `Correct` is `Sequential`: fed more slices, or the end of the input, it has
handed over what it had and possibly more, and once it has failed, it stays failed. -/
theorem Lexer.sequential {feed : Lexicon.Version → List Regex.Chars → Bool → BSmtLibSpec.Lexer.Fed}
    (h : BSmtLibSpec.Lexer.Correct feed) :
    ∀ version slices more, BSmtLibSpec.Lexer.Sequential feed version slices more :=
  Proofs.Lexer.StreamingFacts.sequential_of_correct h

/--
info: 'BSmtLibSpec.Facts.Lexer.sequential' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.sequential

/-- A lexer that is `Correct` is `WholeInputCorrect`: fed slices and then the end of the input,
it has not failed and has handed over the tokens of the tokenisation of the input followed by
the end-of-file token exactly when the input has a tokenisation. -/
theorem Lexer.wholeInputCorrect
    {feed : Lexicon.Version → List Regex.Chars → Bool → BSmtLibSpec.Lexer.Fed}
    (h : BSmtLibSpec.Lexer.Correct feed) :
    ∀ version slices handed, BSmtLibSpec.Lexer.WholeInputCorrect feed version slices handed :=
  Proofs.Lexer.StreamingFacts.wholeInputCorrect_of_correct h

/--
info: 'BSmtLibSpec.Facts.Lexer.wholeInputCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.wholeInputCorrect

/-!
### A lexer and its consumers

`BSmtLibSpec.Lexer.Runs` states what a lexer does with a consumer relative to what it hands over to
the collector. What it does is determined by the input and the consumer, so the result it holds or
returns, where its discarding began and the version in force are too. The input after a switch
of the version is read on its own and located in the whole input; locating it so agrees with
locating its characters in the whole input, and from the start of the input, the tokens ready
are those the lexer hands over to the collector. The collector meets the obligation of every
consumer.
-/

/-- What a lexer does with a consumer, from any point on, is determined. -/
theorem Lexer.runsDetermined
    {feed : Lexicon.Version → List Regex.Chars → Bool → BSmtLibSpec.Lexer.Fed}
    {consumer : BSmtLibSpec.Lexer.Consumer} {start : Lexicon.Version} {input : Regex.Chars}
    {ended : Bool} {version : Lexicon.Version} {ready : List BSmtLibSpec.Lexer.Handed}
    {failed : Bool}
    {taken : List BSmtLibSpec.Lexer.Handed}
    {session session' : BSmtLibSpec.Lexer.Session consumer.Result consumer.Error}
    (h : BSmtLibSpec.Lexer.Runs feed consumer start input ended version ready failed taken session)
    (h' : BSmtLibSpec.Lexer.Runs feed consumer start input ended version ready failed taken
    session') :
    session = session' :=
  Proofs.Lexer.Consumers.runs_unique h h'

/--
info: 'BSmtLibSpec.Facts.Lexer.runsDetermined' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.runsDetermined

/-- Locating characters of an input read on its own after `before`, then moving the location
past `before`, is locating them in the whole input. -/
theorem Lexer.locateAfter (before input : Regex.Chars) (offset : Nat) :
    BSmtLibSpec.Lexer.locate (before ++ input) (before.length + offset) =
      (BSmtLibSpec.Lexer.locate input offset).after before :=
  Proofs.Lexer.Consumers.locate_after before input offset

/--
info: 'BSmtLibSpec.Facts.Lexer.locateAfter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.locateAfter

/-- From the start of the input, the tokens ready are those the lexer hands over to the
collector. -/
theorem Lexer.segmentAtStart (feed : Lexicon.Version → List Regex.Chars → Bool →
    BSmtLibSpec.Lexer.Fed)
    (version : Lexicon.Version) (input : Regex.Chars) (ended : Bool) :
    BSmtLibSpec.Lexer.segment feed version input ended 0 = feed version [input] ended :=
  Proofs.Lexer.Consumers.segment_zero feed version input ended

/--
info: 'BSmtLibSpec.Facts.Lexer.segmentAtStart' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.segmentAtStart

/-- The collector breaks at the end of the input. -/
theorem Lexer.collectorBreaksAtEnd : BSmtLibSpec.Lexer.collector.BreaksAtEnd :=
  Proofs.Lexer.Consumers.collector_breaksAtEnd

/--
info: 'BSmtLibSpec.Facts.Lexer.collectorBreaksAtEnd' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Lexer.collectorBreaksAtEnd

end BSmtLibSpec.Facts
