module

public import BSmtLib.Facts.Trusted
public import BSmtLib.Facts.PublicApi.Adapters.Chain
public import BSmtLib.Facts.PublicApi.Adapters.Builder
public import BSmtLib.Facts.PublicApi.Adapters.Constructs
public import BSmtLib.Facts.Proofs.PublicApi.Reprinting

@[expose] public section

/-!
# What holds without the specification

Theorems about the library's public API whose statements rest on almost nothing: the names a
user writes (`BSmtLib.Lexer`, `BSmtLib.Reader`, the handler classes, …), bytes, lists, and the
small definitions below `BSmtLib.Facts.PublicApi.Adapters`. The proofs may go through the
specification and the other facts; the statements do not.

A theorem that claims a handler, a printer or a layer to exist says what it does and not how:
the witness is not trusted. Where several properties of one witness are claimed, they are claimed
of the same witness, so that a property that would hold of a trivial witness is pinned by the
others.

`#adapters` and `#trusts` at the end list what the statements rest on beside Lean and the public
API (`BSmtLib.Facts.Trusted`): the first the small definitions, which are this part's adapters,
the second, for each theorem, also the constants of the specification and of the lexers of the
chain that it names.
-/

namespace BSmtLib.Facts.PublicApi

open BSmtLib.Parser
open BSmtLib.Facts.PublicApi.Adapters BSmtLib.Facts.PublicApi.Adapters.Content
open BSmtLib.Facts.PublicApi.Adapters.Reprinter BSmtLib.Facts.PublicApi.Adapters.Chain
open BSmtLib.Facts.PublicApi.Adapters.Builder
open BSmtLib.Token (Version)

/-! ## Reprinting -/

/--
There is a handler told contents only, with a printer, such that on every input, in any slices,
that the script reader over the handler reads to the end, printing what the handler was told,
with layout between the tokens, gives back the input up to where the reader began to discard it:
on every input but for the spelling of string literals that stand for the same bytes in 2.0, and
exactly where the reader allows only the versions from 2.5 on and starts in one of them.
-/
theorem reprinting : ∃ r : Reprinter, r.Reprints ∧ r.ReprintsExactly :=
  ⟨Proofs.PublicApi.Reprinting.recorder, Proofs.PublicApi.Reprinting.recorder_Reprints,
    Proofs.PublicApi.Reprinting.recorder_ReprintsExactly⟩

/--
info: 'BSmtLib.Facts.PublicApi.reprinting' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reprinting

/-! ## Spans of constructs -/

/--
There is a handler told contents only, with a printer, as in `reprinting`, and a layer between
the lexer and the script parser over that handler, such that on an input that the reader reads
to the end the layer knows where each command and each construct within it is, as the
specification reads them, and where the reader fails with a syntax or a handler error the layer
gives the error with the constructs open there.
-/
theorem construct_spans :
    ∃ (r : Reprinter) (layer : SpanLayer r),
      r.Reprints ∧ layer.SpansExact ∧ layer.HoldsBackErrors := by
  sorry

/--
info: 'BSmtLib.Facts.PublicApi.construct_spans' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms construct_spans

/-! ## Lossless lexing -/

/--
The library's lexer, with a consumer that takes every token, whitespace and comments included,
fed an input in any slices and then the end of the input, hands over tokens whose spans cover the
input without a gap or an overlap, ending with the end of the input; or, at an error, tokens that
cover the input from its start up to at most where the error is.
-/
theorem lexing_lossless (version : Version) (slices : List ByteList) :
    match collect version slices with
    | (.ok _, entries) => Tiles entries 0 slices.flatten.length
    | (.error error, entries) => ∃ stop, Tiles entries 0 stop ∧ stop ≤ error.span.start.offset := by
  sorry

/--
info: 'BSmtLib.Facts.PublicApi.lexing_lossless' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lexing_lossless

/-! ## Slicing invariance -/

/--
The library's lexer, with a consumer that takes every token, hands over the same tokens and ends
the same way however the input is cut into slices.
-/
theorem lexing_slicing (version : Version) (slices : List ByteList) :
    collect version slices = collect version [slices.flatten] := by
  sorry

/--
info: 'BSmtLib.Facts.PublicApi.lexing_slicing' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lexing_slicing

/--
There is a handler told contents only, with a printer, as in `reprinting`, such that the script
reader over the handler ends the same way, with the same printed tokens and the same location
where it began to discard, however the input is cut into slices.
-/
theorem reading_slicing :
    ∃ r : Reprinter, r.Reprints ∧
      ∀ version slices, r.observe (readThrough (r.reader version) slices) =
        r.observe (readThrough (r.reader version) [slices.flatten]) := by
  sorry

/--
info: 'BSmtLib.Facts.PublicApi.reading_slicing' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reading_slicing

/-! ## Composition and reset -/

/--
The library's lexer, with a consumer that takes every token: an input that it lexes to the end
with a `)` as its last token is lexed as a prefix of every input it starts: the tokens of the
longer input are its tokens, but the end of the input, and then the tokens of the rest, as the
rest alone has them, moved by its length; and the longer input ends as the rest does.
-/
theorem lexing_composes (version : Version) (first rest : ByteList) (result : Option (Located Unit))
    (entries : List Entry) (h : collect version [first] = (.ok result, entries))
    (hclose : entries.dropLast.getLast?.map (·.1) = some .parenClose) :
    (collect version [first ++ rest]).2 =
        entries.dropLast ++ shift first.length (collect version [rest]).2 ∧
      (collect version [first ++ rest]).1.toBool = (collect version [rest]).1.toBool := by
  sorry

/--
info: 'BSmtLib.Facts.PublicApi.lexing_composes' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lexing_composes

/--
The library's lexer, with a consumer that takes every token: after the end of an input, it lexes
the next input as a new lexer from the version does.
-/
theorem lexing_resets (version : Version) (first : List ByteList) (log : List Entry)
    (result : Option (Located Unit)) (lexer : Lexer Collector)
    (h : (collectWith (Lexer.new Collector.mk version) first).run [] = (.ok (result, lexer), log))
    (next : List ByteList) :
    (resultOf <$> collectWith lexer next).run [] =
      (resultOf <$> collectWith (Lexer.new Collector.mk version) next).run [] := by
  sorry

/--
info: 'BSmtLib.Facts.PublicApi.lexing_resets' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lexing_resets

/--
There is a handler told contents only, with a printer, as in `reprinting`, such that the script
reader over the handler, after it read an input to the end, reads the next input as a new
script reader over its handler does.
-/
theorem reading_resets :
    ∃ r : Reprinter, r.Reprints ∧
      ∀ version first next result before after,
        readThrough (r.reader version) first = .ok (result, before, after) →
          r.observe (readThrough after next) =
            r.observe (readThrough (Reader.script after.handler allVersions version) next) := by
  sorry

/--
info: 'BSmtLib.Facts.PublicApi.reading_resets' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reading_resets

/-! ## The lexers of the chain agree -/

/--
The naive lexer, the Rust port, the lexer with the batch kept in its state and the library's
lexer, each with a consumer that takes every token, hand over the same tokens and end the same
way, failing with errors of the same cause, on every input in any slices. Where an error is
located is not compared.
-/
theorem lexers_agree (version : Version) (slices : List ByteList) :
    causeOnly (collectV version slices) = causeOnly (collect version slices) ∧
      causeOnly (collectW version slices) = causeOnly (collect version slices) ∧
      causeOnly (collectX1 version slices) = causeOnly (collect version slices) := by
  sorry

/--
info: 'BSmtLib.Facts.PublicApi.lexers_agree' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lexers_agree

/-! ## Building the commands -/

/--
There is a handler told contents only, whose state is a list of commands of the specification
and whose sorts, s-expressions, attributes and terms are those of the specification, such that
the script reader over it, from no commands, reads every file to the end and builds the file's
commands.
-/
theorem builds_commands :
    ∃ inst : ContentHandler (List BSmtLibSpec.Grammar.Tree.Command),
      inst.«Sort» = BSmtLibSpec.Grammar.Tree.Sort ∧
      inst.SExpr = BSmtLibSpec.Grammar.Tree.SExpr ∧
      inst.Attribute = BSmtLibSpec.Grammar.Tree.Attribute ∧
      inst.Term = BSmtLibSpec.Grammar.Tree.Term ∧
      ∀ version slices commands, BSmtLibSpec.Grammar.File version slices.flatten commands →
        ∃ result before after,
          readThrough (Reader.script [] allVersions (libVersion version)) slices =
            .ok (some result, before, after) ∧
          after.handler.reverse = commands := by
  sorry

/--
info: 'BSmtLib.Facts.PublicApi.builds_commands' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms builds_commands

/-! ## What the statements rest on -/

/--
info: 10 theorems, stated with 78 adapters:
BSmtLib.Facts.PublicApi.Adapters:
  BSmtLib.Facts.PublicApi.Adapters.ByteList
  BSmtLib.Facts.PublicApi.Adapters.CollectM
  BSmtLib.Facts.PublicApi.Adapters.Collector
  BSmtLib.Facts.PublicApi.Adapters.Entry
  BSmtLib.Facts.PublicApi.Adapters.Layout
  BSmtLib.Facts.PublicApi.Adapters.SameSpelling
  BSmtLib.Facts.PublicApi.Adapters.SameSpellings
  BSmtLib.Facts.PublicApi.Adapters.Spaced
  BSmtLib.Facts.PublicApi.Adapters.Tiles
  BSmtLib.Facts.PublicApi.Adapters.allVersions
  BSmtLib.Facts.PublicApi.Adapters.collect
  BSmtLib.Facts.PublicApi.Adapters.collectWith
  BSmtLib.Facts.PublicApi.Adapters.feed
  BSmtLib.Facts.PublicApi.Adapters.instConsumeCollectorUnitEmpty
  BSmtLib.Facts.PublicApi.Adapters.instConsumeFromCollectorBatchCursorCollectMUnitEmpty
  BSmtLib.Facts.PublicApi.Adapters.readThrough
  BSmtLib.Facts.PublicApi.Adapters.readUpTo
  BSmtLib.Facts.PublicApi.Adapters.resultOf
  BSmtLib.Facts.PublicApi.Adapters.shift
  BSmtLib.Facts.PublicApi.Adapters.unescape20
BSmtLib.Facts.PublicApi.Adapters.Builder:
  BSmtLib.Facts.PublicApi.Adapters.Builder.libVersion
  BSmtLib.Facts.PublicApi.Adapters.Builder.specVersion
BSmtLib.Facts.PublicApi.Adapters.Chain:
  BSmtLib.Facts.PublicApi.Adapters.Chain.causeOnly
  BSmtLib.Facts.PublicApi.Adapters.Chain.collectBy
  BSmtLib.Facts.PublicApi.Adapters.Chain.collectV
  BSmtLib.Facts.PublicApi.Adapters.Chain.collectW
  BSmtLib.Facts.PublicApi.Adapters.Chain.collectX1
BSmtLib.Facts.PublicApi.Adapters.Constructs:
  BSmtLib.Facts.PublicApi.Adapters.Constructs.IsKind
  BSmtLib.Facts.PublicApi.Adapters.Constructs.ReadAs
  BSmtLib.Facts.PublicApi.Adapters.Constructs.StartsAs
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.SpanLayer.HoldsBackErrors
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.SpanLayer.SpansExact
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
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.Construct
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.HeldBack
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.Kind
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.Reprints
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.ReprintsExactly
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.SpanLayer
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.SpanLayer.bytesOf
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.Trimmed
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.bytesIn
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.from25
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.instConsumeFromWBatchCursorIdUnitHeldBackErrorH
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.instConsumeWUnitHeldBackErrorH
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.instContentHandlerH
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.instDecidableEqKind
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.lexThrough
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.observe
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
BSmtLib.Facts.PublicApi.construct_spans:
  small: Adapters.Builder.specVersion, Adapters.ByteList, Adapters.Constructs.IsKind,
    Adapters.Constructs.ReadAs, Adapters.Constructs.StartsAs, Adapters.Content.AttributeValueNode,
    Adapters.Content.Constant, Adapters.Content.Constructor, Adapters.Content.ContentHandler,
    Adapters.Content.ContentHandler.instCommandHandler, Adapters.Content.ContentHandler.instHandler,
    Adapters.Content.Identifier, Adapters.Content.Index, Adapters.Content.Pattern,
    Adapters.Content.SExprNode, Adapters.Content.Signature, Adapters.Content.Symbol,
    Adapters.Content.SymbolOrWildcard, Adapters.Content.TermNode, Adapters.Content.contentOf,
    Adapters.Content.ofAttributeValueNode, Adapters.Content.ofConstant,
    Adapters.Content.ofConstructor, Adapters.Content.ofIdentifier, Adapters.Content.ofIndex,
    Adapters.Content.ofPairs, Adapters.Content.ofPattern, Adapters.Content.ofSExprNode,
    Adapters.Content.ofSignature, Adapters.Content.ofSymbol, Adapters.Content.ofSymbolOrWildcard,
    Adapters.Content.ofTermNode, Adapters.Layout, Adapters.Reprinter, Adapters.Reprinter.Construct,
    Adapters.Reprinter.HeldBack, Adapters.Reprinter.Kind, Adapters.Reprinter.Reprints,
    Adapters.Reprinter.SpanLayer, Adapters.Reprinter.SpanLayer.HoldsBackErrors,
    Adapters.Reprinter.SpanLayer.SpansExact, Adapters.Reprinter.SpanLayer.bytesOf,
    Adapters.Reprinter.Trimmed, Adapters.Reprinter.bytesIn,
    Adapters.Reprinter.instConsumeFromWBatchCursorIdUnitHeldBackErrorH,
    Adapters.Reprinter.instConsumeWUnitHeldBackErrorH, Adapters.Reprinter.instContentHandlerH,
    Adapters.Reprinter.instDecidableEqKind, Adapters.Reprinter.lexThrough, Adapters.Reprinter.reader,
    Adapters.Reprinter.readerWith, Adapters.SameSpelling, Adapters.SameSpellings, Adapters.Spaced,
    Adapters.allVersions, Adapters.feed, Adapters.readThrough, Adapters.readUpTo,
    Adapters.unescape20
  spec: BSmtLibSpec.Grammar.Syntax.IsAttribute, BSmtLibSpec.Grammar.Syntax.IsCommand,
    BSmtLibSpec.Grammar.Syntax.IsSExpr, BSmtLibSpec.Grammar.Syntax.IsSort,
    BSmtLibSpec.Grammar.Syntax.IsTerm, BSmtLibSpec.Grammar.SyntaxToken,
    BSmtLibSpec.Grammar.SyntaxToken.ofToken, BSmtLibSpec.Grammar.Tree.Attribute,
    BSmtLibSpec.Grammar.Tree.Command, BSmtLibSpec.Grammar.Tree.SExpr, BSmtLibSpec.Grammar.Tree.Sort,
    BSmtLibSpec.Grammar.Tree.Term, BSmtLibSpec.Lexicon.Token,
    BSmtLibSpec.Lexicon.Tokenization.Exactly, BSmtLibSpec.Lexicon.Tokenization.From,
    BSmtLibSpec.Lexicon.Version
BSmtLib.Facts.PublicApi.lexers_agree:
  small: Adapters.ByteList, Adapters.Chain.causeOnly, Adapters.Chain.collectBy,
    Adapters.Chain.collectV, Adapters.Chain.collectW, Adapters.Chain.collectX1, Adapters.CollectM,
    Adapters.Collector, Adapters.Entry, Adapters.collect, Adapters.collectWith,
    Adapters.instConsumeCollectorUnitEmpty,
    Adapters.instConsumeFromCollectorBatchCursorCollectMUnitEmpty, Adapters.resultOf
  chain: BSmtLib.Lexer.Internal.VNaive.Lexer, BSmtLib.Lexer.Internal.VNaive.Lexer.AfterEofError,
    BSmtLib.Lexer.Internal.VNaive.Lexer.AfterError, BSmtLib.Lexer.Internal.VNaive.Lexer.lexEof,
    BSmtLib.Lexer.Internal.VNaive.Lexer.lexSlice, BSmtLib.Lexer.Internal.VNaive.Lexer.new,
    BSmtLib.Lexer.Internal.WRustPort.Lexer, BSmtLib.Lexer.Internal.WRustPort.Lexer.AfterEofError,
    BSmtLib.Lexer.Internal.WRustPort.Lexer.AfterError, BSmtLib.Lexer.Internal.WRustPort.Lexer.lexEof,
    BSmtLib.Lexer.Internal.WRustPort.Lexer.lexSlice, BSmtLib.Lexer.Internal.WRustPort.Lexer.new,
    BSmtLib.Lexer.Internal.X1BatchInCore.Lexer.lexEof,
    BSmtLib.Lexer.Internal.X1BatchInCore.Lexer.lexSlice
BSmtLib.Facts.PublicApi.lexing_composes:
  small: Adapters.ByteList, Adapters.CollectM, Adapters.Collector, Adapters.Entry, Adapters.collect,
    Adapters.collectWith, Adapters.instConsumeCollectorUnitEmpty,
    Adapters.instConsumeFromCollectorBatchCursorCollectMUnitEmpty, Adapters.resultOf, Adapters.shift
BSmtLib.Facts.PublicApi.lexing_lossless:
  small: Adapters.ByteList, Adapters.CollectM, Adapters.Collector, Adapters.Entry, Adapters.Tiles,
    Adapters.collect, Adapters.collectWith, Adapters.instConsumeCollectorUnitEmpty,
    Adapters.instConsumeFromCollectorBatchCursorCollectMUnitEmpty, Adapters.resultOf
BSmtLib.Facts.PublicApi.lexing_resets:
  small: Adapters.ByteList, Adapters.CollectM, Adapters.Collector, Adapters.Entry,
    Adapters.collectWith, Adapters.instConsumeCollectorUnitEmpty,
    Adapters.instConsumeFromCollectorBatchCursorCollectMUnitEmpty, Adapters.resultOf
BSmtLib.Facts.PublicApi.lexing_slicing:
  small: Adapters.ByteList, Adapters.CollectM, Adapters.Collector, Adapters.Entry, Adapters.collect,
    Adapters.collectWith, Adapters.instConsumeCollectorUnitEmpty,
    Adapters.instConsumeFromCollectorBatchCursorCollectMUnitEmpty, Adapters.resultOf
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
    Adapters.Content.ofTermNode, Adapters.Layout, Adapters.Reprinter, Adapters.Reprinter.Reprints,
    Adapters.Reprinter.instContentHandlerH, Adapters.Reprinter.observe, Adapters.Reprinter.reader,
    Adapters.Reprinter.readerWith, Adapters.SameSpelling, Adapters.SameSpellings, Adapters.Spaced,
    Adapters.allVersions, Adapters.feed, Adapters.readThrough, Adapters.readUpTo,
    Adapters.unescape20
BSmtLib.Facts.PublicApi.reading_slicing:
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
    Adapters.Content.ofTermNode, Adapters.Layout, Adapters.Reprinter, Adapters.Reprinter.Reprints,
    Adapters.Reprinter.instContentHandlerH, Adapters.Reprinter.observe, Adapters.Reprinter.reader,
    Adapters.Reprinter.readerWith, Adapters.SameSpelling, Adapters.SameSpellings, Adapters.Spaced,
    Adapters.allVersions, Adapters.feed, Adapters.readThrough, Adapters.readUpTo,
    Adapters.unescape20
BSmtLib.Facts.PublicApi.reprinting:
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
    Adapters.Content.ofTermNode, Adapters.Layout, Adapters.Reprinter, Adapters.Reprinter.Reprints,
    Adapters.Reprinter.ReprintsExactly, Adapters.Reprinter.from25,
    Adapters.Reprinter.instContentHandlerH, Adapters.Reprinter.reader, Adapters.Reprinter.readerWith,
    Adapters.SameSpelling, Adapters.SameSpellings, Adapters.Spaced, Adapters.allVersions,
    Adapters.feed, Adapters.readThrough, Adapters.readUpTo, Adapters.unescape20
-/
#guard_msgs in
#trusts within BSmtLib.Facts.PublicApi

end BSmtLib.Facts.PublicApi
