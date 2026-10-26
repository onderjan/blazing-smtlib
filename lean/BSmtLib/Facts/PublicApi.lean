module

public import BSmtLib.Facts.Trusted
public import BSmtLib.Facts.PublicApi.Adapters.Chain
public import BSmtLib.Facts.PublicApi.Adapters.Builder
public import BSmtLib.Facts.Proofs.PublicApi.Reprinting
public import BSmtLib.Facts.Proofs.PublicApi.Composes
public import BSmtLib.Facts.Proofs.PublicApi.Resets
public import BSmtLib.Facts.Proofs.PublicApi.Slicing
public import BSmtLib.Facts.Proofs.PublicApi.Lossless
public import BSmtLib.Facts.Proofs.PublicApi.Agree
public import BSmtLib.Facts.Proofs.PublicApi.ReaderResets
public import BSmtLib.Facts.Proofs.PublicApi.SlicingC
public import BSmtLib.Facts.Proofs.PublicApi.ReaderSlicing
public import BSmtLib.Facts.Proofs.PublicApi.Builds

@[expose] public section

/-!
# What holds of the public API

Theorems about the library's public API whose statements rest on little beyond it:

- the names a user writes (`BSmtLib.Lexer`, `BSmtLib.Reader`, the handler classes, …);
- bytes and lists;
- the small definitions below `BSmtLib.Facts.PublicApi.Adapters`.

The mainline theorems among them are stated in `BSmtLib.Facts`, with the same adapters; this
module states the others.

One statement here names more: `builds_commands` builds the command trees of the specification
formalism (`BSmtLibSpec`), so it names them and the formalism's versions. In `BSmtLib.Facts`,
`lexers_agree` names the lexers of the chain, which it compares. The other statements name nothing
of the formalism and none of the library's internals. The proofs go through both, and through the
other facts.

A theorem that claims a handler or a printer to exist says what it does and not how:
the witness is not trusted. Where several properties of one witness are claimed, they are claimed
of the same witness, so that a property that would hold of a trivial witness is pinned by the
others.

Two checks at the end list what the statements rest on beside Lean and the public API
(`BSmtLib.Facts.Trusted`):

- `#adapters` lists the small definitions, which are this part's adapters;
- `#trusts` lists, for each theorem, those and also the constants of the formalism and of the
  lexers of the chain that it names.
-/

namespace BSmtLib.Facts.PublicApi

open BSmtLib.Parser
open BSmtLib.Facts.PublicApi.Adapters BSmtLib.Facts.PublicApi.Adapters.Content
open BSmtLib.Facts.PublicApi.Adapters.Reprinter BSmtLib.Facts.PublicApi.Adapters.Chain
open BSmtLib.Facts.PublicApi.Adapters.Builder
open BSmtLib (Version)
open BSmtLib.Span (Located)

/-! ## Composition and reset -/

/--
The library's lexer lexes an input as a prefix of every input it starts, if it lexes the input to
the end and its last token before the end of the input is a `)`, with no whitespace or comment
after it. For the longer input:

- its tokens are those of the prefix but the end of the input, and then the tokens of the rest as
  the rest alone has them, moved by the length of the prefix;
- it ends as the rest alone ends, moved past the prefix (`MovedResult`): with the same result, its
  location moved, or with an error of the same cause, its span and where it continues from moved.

A location is moved past the prefix as `Moved` states: the offset and the line of the end of the
prefix (`locationAfter`) are added to its own, and on the first line of the rest so is the
column. The lexer's consumer takes every token.
-/
theorem lexing_composes (version : Version) (first rest : ByteList) (result : Option (Located Unit))
    (entries : List Entry) (h : collect version [first] = (.ok result, entries))
    (hclose : entries.dropLast.getLast?.map (·.1) = some .parenClose) :
    (collect version [first ++ rest]).2 =
        entries.dropLast ++ shift first.length (collect version [rest]).2 ∧
      MovedResult (locationAfter first) (collect version [rest]).1
        (collect version [first ++ rest]).1 :=
  Proofs.PublicApi.Composes.composes version first rest result entries h hclose

/--
info: 'BSmtLib.Facts.PublicApi.lexing_composes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lexing_composes

/--
After it has lexed an input to the end without an error, the library's lexer lexes the next input
as a new lexer created with the version does. Its consumer takes every token.
-/
theorem lexing_resets (version : Version) (first : List ByteList) (log : List Entry)
    (result : Option (Located Unit)) (lexer : Lexer Collector)
    (h : (collectWith (Lexer.new Collector.mk version) first).run [] = (.ok (result, lexer), log))
    (next : List ByteList) :
    (resultOf <$> collectWith lexer next).run [] =
      (resultOf <$> collectWith (Lexer.new Collector.mk version) next).run [] :=
  Proofs.PublicApi.Resets.resets version first log result lexer h next

/--
info: 'BSmtLib.Facts.PublicApi.lexing_resets' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lexing_resets

/--
The end of an input resets the script reader.

There is a handler told contents only, with a printer as in `Facts.reprinting` (`Reprints20`,
`ReprintsExactly25Plus`). After the script reader over it, allowing every version and starting in
any of them, read an input to the end, it reads the next input as a new script reader over its
handler does, allowing every version and starting in the same version.
-/
theorem reading_resets :
    ∃ r : Reprinter, r.Reprints20 ∧ r.ReprintsExactly25Plus ∧
      ∀ version first next result before after,
        readThrough (r.reader version) first = .ok (result, before, after) →
          r.observe (readThrough after next) =
            r.observe (readThrough (Reader.script after.handler allVersions version) next) :=
  ⟨Proofs.PublicApi.Reprinting.recorder, Proofs.PublicApi.Reprinting.recorder_Reprints20,
    Proofs.PublicApi.Reprinting.recorder_ReprintsExactly25Plus,
    Proofs.PublicApi.ReaderResets.recorder_resets⟩

/--
info: 'BSmtLib.Facts.PublicApi.reading_resets' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reading_resets

/-! ## Building the commands -/

/--
There is a handler told contents only over which the script reader builds the commands of every
file. The handler's state is the version in force and a list of commands of the formalism. Its
sorts, s-expressions, attributes and terms are those of the formalism. The reader starts in the
file's initial version, with the handler holding that version and no commands; it reads the file
to the end and leaves the file's commands in the handler.
-/
theorem builds_commands :
    ∃ inst : ContentHandler (BSmtLibSpec.Lexicon.Version × List BSmtLibSpec.Grammar.Tree.Command),
      inst.«Sort» = BSmtLibSpec.Grammar.Tree.Sort ∧
      inst.SExpr = BSmtLibSpec.Grammar.Tree.SExpr ∧
      inst.Attribute = BSmtLibSpec.Grammar.Tree.Attribute ∧
      inst.Term = BSmtLibSpec.Grammar.Tree.Term ∧
      ∀ version slices commands, BSmtLibSpec.Grammar.File version slices.flatten commands →
        ∃ result before after,
          readThrough (Reader.script (version, []) allVersions (libVersion version)) slices =
            .ok (some result, before, after) ∧
          after.handler.2.reverse = commands :=
  Proofs.PublicApi.Builds.builds_commands

/--
info: 'BSmtLib.Facts.PublicApi.builds_commands' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms builds_commands

/-! ## What the statements rest on -/

/--
info: 4 theorems, stated with 60 adapters:
BSmtLib.Facts.PublicApi.Adapters:
  BSmtLib.Facts.PublicApi.Adapters.ByteList
  BSmtLib.Facts.PublicApi.Adapters.CollectM
  BSmtLib.Facts.PublicApi.Adapters.Collector
  BSmtLib.Facts.PublicApi.Adapters.Entry
  BSmtLib.Facts.PublicApi.Adapters.FinalLayout
  BSmtLib.Facts.PublicApi.Adapters.Layout
  BSmtLib.Facts.PublicApi.Adapters.Moved
  BSmtLib.Facts.PublicApi.Adapters.MovedResult
  BSmtLib.Facts.PublicApi.Adapters.SameSpelling
  BSmtLib.Facts.PublicApi.Adapters.SameSpellings
  BSmtLib.Facts.PublicApi.Adapters.Spaced
  BSmtLib.Facts.PublicApi.Adapters.allVersions
  BSmtLib.Facts.PublicApi.Adapters.collect
  BSmtLib.Facts.PublicApi.Adapters.collectWith
  BSmtLib.Facts.PublicApi.Adapters.feed
  BSmtLib.Facts.PublicApi.Adapters.instConsumeCollectorUnitEmpty
  BSmtLib.Facts.PublicApi.Adapters.instConsumeFromCollectorLexerCursorCollectMUnitEmpty
  BSmtLib.Facts.PublicApi.Adapters.locationAfter
  BSmtLib.Facts.PublicApi.Adapters.readThrough
  BSmtLib.Facts.PublicApi.Adapters.readUpTo
  BSmtLib.Facts.PublicApi.Adapters.resultOf
  BSmtLib.Facts.PublicApi.Adapters.shift
  BSmtLib.Facts.PublicApi.Adapters.unescape20
BSmtLib.Facts.PublicApi.Adapters.Builder:
  BSmtLib.Facts.PublicApi.Adapters.Builder.libVersion
BSmtLib.Facts.PublicApi.Adapters.Content:
  BSmtLib.Facts.PublicApi.Adapters.Content.AttributeValueNode
  BSmtLib.Facts.PublicApi.Adapters.Content.Constant
  BSmtLib.Facts.PublicApi.Adapters.Content.Constructor
  BSmtLib.Facts.PublicApi.Adapters.Content.ContentHandler
  BSmtLib.Facts.PublicApi.Adapters.Content.ContentHandler.instCommandHandler
  BSmtLib.Facts.PublicApi.Adapters.Content.ContentHandler.instHandler
  BSmtLib.Facts.PublicApi.Adapters.Content.Identifier
  BSmtLib.Facts.PublicApi.Adapters.Content.Index
  BSmtLib.Facts.PublicApi.Adapters.Content.Pattern
  BSmtLib.Facts.PublicApi.Adapters.Content.SExprNode
  BSmtLib.Facts.PublicApi.Adapters.Content.Signature
  BSmtLib.Facts.PublicApi.Adapters.Content.Symbol
  BSmtLib.Facts.PublicApi.Adapters.Content.SymbolOrWildcard
  BSmtLib.Facts.PublicApi.Adapters.Content.TermNode
  BSmtLib.Facts.PublicApi.Adapters.Content.contentOf
  BSmtLib.Facts.PublicApi.Adapters.Content.ofAttributeValueNode
  BSmtLib.Facts.PublicApi.Adapters.Content.ofConstant
  BSmtLib.Facts.PublicApi.Adapters.Content.ofConstructor
  BSmtLib.Facts.PublicApi.Adapters.Content.ofIdentifier
  BSmtLib.Facts.PublicApi.Adapters.Content.ofIndex
  BSmtLib.Facts.PublicApi.Adapters.Content.ofPairs
  BSmtLib.Facts.PublicApi.Adapters.Content.ofPattern
  BSmtLib.Facts.PublicApi.Adapters.Content.ofSExprNode
  BSmtLib.Facts.PublicApi.Adapters.Content.ofSignature
  BSmtLib.Facts.PublicApi.Adapters.Content.ofSymbol
  BSmtLib.Facts.PublicApi.Adapters.Content.ofSymbolOrWildcard
  BSmtLib.Facts.PublicApi.Adapters.Content.ofTermNode
BSmtLib.Facts.PublicApi.Adapters.Reprinter:
  BSmtLib.Facts.PublicApi.Adapters.Reprinter
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.Reprints20
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.ReprintsExactly25Plus
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.from25
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.instContentHandlerH
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.observe
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.only20
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.reader
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.readerWith
-/
#guard_msgs in
#adapters within BSmtLib.Facts.PublicApi

/--
info: BSmtLib.Facts.PublicApi.builds_commands:
  small: Adapters.Builder.libVersion, Adapters.ByteList, Adapters.Content.AttributeValueNode,
    Adapters.Content.Constant, Adapters.Content.Constructor, Adapters.Content.ContentHandler,
    Adapters.Content.ContentHandler.instCommandHandler, Adapters.Content.ContentHandler.instHandler,
    Adapters.Content.Identifier, Adapters.Content.Index, Adapters.Content.Pattern,
    Adapters.Content.SExprNode, Adapters.Content.Signature, Adapters.Content.Symbol,
    Adapters.Content.SymbolOrWildcard, Adapters.Content.TermNode, Adapters.Content.contentOf,
    Adapters.Content.ofAttributeValueNode, Adapters.Content.ofConstant,
    Adapters.Content.ofConstructor, Adapters.Content.ofIdentifier, Adapters.Content.ofIndex,
    Adapters.Content.ofPairs, Adapters.Content.ofPattern, Adapters.Content.ofSExprNode,
    Adapters.Content.ofSignature, Adapters.Content.ofSymbol, Adapters.Content.ofSymbolOrWildcard,
    Adapters.Content.ofTermNode, Adapters.allVersions, Adapters.feed, Adapters.readThrough
  spec: BSmtLibSpec.Grammar.File, BSmtLibSpec.Grammar.Tree.Attribute,
    BSmtLibSpec.Grammar.Tree.Command, BSmtLibSpec.Grammar.Tree.SExpr, BSmtLibSpec.Grammar.Tree.Sort,
    BSmtLibSpec.Grammar.Tree.Term, BSmtLibSpec.Lexicon.Version
BSmtLib.Facts.PublicApi.lexing_composes:
  small: Adapters.ByteList, Adapters.CollectM, Adapters.Collector, Adapters.Entry, Adapters.Moved,
    Adapters.MovedResult, Adapters.collect, Adapters.collectWith,
    Adapters.instConsumeCollectorUnitEmpty,
    Adapters.instConsumeFromCollectorLexerCursorCollectMUnitEmpty, Adapters.locationAfter,
    Adapters.resultOf, Adapters.shift
BSmtLib.Facts.PublicApi.lexing_resets:
  small: Adapters.ByteList, Adapters.CollectM, Adapters.Collector, Adapters.Entry,
    Adapters.collectWith, Adapters.instConsumeCollectorUnitEmpty,
    Adapters.instConsumeFromCollectorLexerCursorCollectMUnitEmpty, Adapters.resultOf
BSmtLib.Facts.PublicApi.reading_resets:
  small: Adapters.ByteList, Adapters.Content.AttributeValueNode, Adapters.Content.Constant,
    Adapters.Content.Constructor, Adapters.Content.ContentHandler,
    Adapters.Content.ContentHandler.instCommandHandler, Adapters.Content.ContentHandler.instHandler,
    Adapters.Content.Identifier, Adapters.Content.Index, Adapters.Content.Pattern,
    Adapters.Content.SExprNode, Adapters.Content.Signature, Adapters.Content.Symbol,
    Adapters.Content.SymbolOrWildcard, Adapters.Content.TermNode, Adapters.Content.contentOf,
    Adapters.Content.ofAttributeValueNode, Adapters.Content.ofConstant,
    Adapters.Content.ofConstructor, Adapters.Content.ofIdentifier, Adapters.Content.ofIndex,
    Adapters.Content.ofPairs, Adapters.Content.ofPattern, Adapters.Content.ofSExprNode,
    Adapters.Content.ofSignature, Adapters.Content.ofSymbol, Adapters.Content.ofSymbolOrWildcard,
    Adapters.Content.ofTermNode, Adapters.FinalLayout, Adapters.Layout, Adapters.Reprinter,
    Adapters.Reprinter.Reprints20, Adapters.Reprinter.ReprintsExactly25Plus,
    Adapters.Reprinter.from25, Adapters.Reprinter.instContentHandlerH, Adapters.Reprinter.observe,
    Adapters.Reprinter.only20, Adapters.Reprinter.reader, Adapters.Reprinter.readerWith,
    Adapters.SameSpelling, Adapters.SameSpellings, Adapters.Spaced, Adapters.allVersions,
    Adapters.feed, Adapters.readThrough, Adapters.readUpTo, Adapters.unescape20
-/
#guard_msgs in
#trusts within BSmtLib.Facts.PublicApi

end BSmtLib.Facts.PublicApi
