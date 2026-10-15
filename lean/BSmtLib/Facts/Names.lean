module

public import BSmtLib
public import BSmtLib.Lexer.Internal.VNaive
public import BSmtLib.Lexer.Internal.X1BatchInCore
public import BSmtLib.Facts
public import BSmtLibSpec.Facts
public import BSmtLib.Facts.Reexports
public import BSmtLib.Facts.Counterparts

@[expose] public section

/-!
# The naming rule, the re-exports and the Rust counterparts, checked

The checks of `BSmtLib.Facts.Naming`, `BSmtLib.Facts.Reexports` and `BSmtLib.Facts.Counterparts`
on the library, the lexers of the chain, the specification and the facts of both, pinned by
`#guard_msgs`: a declaration added in the wrong place, a stale or missing re-export, a name that
resolves elsewhere than it did, or a public name of the library with neither a Rust counterpart
nor a `LEAN:` reason fails the build.
-/

/-! The naming rule, with its exceptions: the views of the cursor's tokens as syntax tokens,
declared where `SyntaxToken` is, which `Token.lean` cannot import. -/

/--
info: 6428 declarations in 361 modules; 87 add to a sibling's type:
BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix:
  BSmtLib.Facts.Proofs.Lexer.VNaive.Run.St.Taken
BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Pure:
  BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree.LocAt.afterByte
  BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree.LocAt.afterColumns
  BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree.LocAt.lineFeed
BSmtLib.Facts.Proofs.Parser.Commands.FunsRec:
  BSmtLib.Facts.Proofs.Parser.Commands.Elements.HasLength.bind_effect
BSmtLib.Facts.Proofs.Parser.List:
  BSmtLib.Facts.Proofs.Parser.Drive.Runs.first
BSmtLib.Facts.Proofs.Parser.Refused:
  BSmtLib.Facts.Proofs.Parser.Drive.Runs.second
BSmtLib.Facts.Proofs.Parser.Term:
  BSmtLib.Facts.Proofs.Parser.Drive.Runs.of_map_program
  BSmtLib.Facts.Proofs.Parser.Drive.Runs.tokens_eq
BSmtLib.Facts.Proofs.Reader.Lexes.Congr:
  BSmtLib.Facts.Proofs.Reader.Lexes.Requests.AnswersAlike.kind
BSmtLib.Facts.Proofs.Reader.Param.UnaryCalls:
  BSmtLib.Facts.Proofs.Reader.Param.Unary.UL.tryCatch
BSmtLib.Facts.Proofs.Reader.Param.Walk:
  BSmtLib.Facts.Proofs.Reader.Param.Basic.Relator.dite_same
  BSmtLib.Facts.Proofs.Reader.Param.Basic.Relator.ite_same
  BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.bind_eq
  BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.dite
  BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.getThe
  BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.ite
  BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.liftM
  BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.modifyThe
  BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.pure_eq
  BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.set_eq
  BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.bind_eq
  BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.dite
  BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.getThe
  BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.ite
  BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.modifyGetThe
  BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.modifyThe
  BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.pure_eq
  BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.run_rel
BSmtLib.Facts.PublicApi.Adapters.Constructs:
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.SpanLayer.HoldsBackErrors
  BSmtLib.Facts.PublicApi.Adapters.Reprinter.SpanLayer.SpansExact
BSmtLibSpec.Grammar.File:
  BSmtLibSpec.Grammar.Tree.Command.declaredVersion
  BSmtLibSpec.Grammar.Tree.Command.modeAfter
  BSmtLibSpec.Grammar.Tree.Command.namesNoVersion
BSmtLibSpec.Grammar.Syntax:
  BSmtLibSpec.Grammar.Tree.Attribute.Valid
  BSmtLibSpec.Grammar.Tree.Attribute.tokens
  BSmtLibSpec.Grammar.Tree.AttributeValue.Valid
  BSmtLibSpec.Grammar.Tree.AttributeValue.tokens
  BSmtLibSpec.Grammar.Tree.Command.Valid
  BSmtLibSpec.Grammar.Tree.Command.tokens
  BSmtLibSpec.Grammar.Tree.ConstructorDec.Valid
  BSmtLibSpec.Grammar.Tree.ConstructorDec.tokens
  BSmtLibSpec.Grammar.Tree.DatatypeDec.Valid
  BSmtLibSpec.Grammar.Tree.DatatypeDec.tokens
  BSmtLibSpec.Grammar.Tree.FunctionDec.Valid
  BSmtLibSpec.Grammar.Tree.FunctionDec.tokens
  BSmtLibSpec.Grammar.Tree.FunctionDef.Valid
  BSmtLibSpec.Grammar.Tree.FunctionDef.tokens
  BSmtLibSpec.Grammar.Tree.Identifier.Valid
  BSmtLibSpec.Grammar.Tree.Identifier.tokens
  BSmtLibSpec.Grammar.Tree.Index.Valid
  BSmtLibSpec.Grammar.Tree.Index.tokens
  BSmtLibSpec.Grammar.Tree.Pattern.Valid
  BSmtLibSpec.Grammar.Tree.Pattern.tokens
  BSmtLibSpec.Grammar.Tree.PropLiteral.Valid
  BSmtLibSpec.Grammar.Tree.PropLiteral.tokens
  BSmtLibSpec.Grammar.Tree.QualIdentifier.Valid
  BSmtLibSpec.Grammar.Tree.QualIdentifier.tokens
  BSmtLibSpec.Grammar.Tree.Quantifier.word
  BSmtLibSpec.Grammar.Tree.SExpr.Valid
  BSmtLibSpec.Grammar.Tree.SExpr.ValidAll
  BSmtLibSpec.Grammar.Tree.SExpr.tokens
  BSmtLibSpec.Grammar.Tree.SExpr.tokensAll
  BSmtLibSpec.Grammar.Tree.SelectorDec.Valid
  BSmtLibSpec.Grammar.Tree.SelectorDec.tokens
  BSmtLibSpec.Grammar.Tree.Sort.Valid
  BSmtLibSpec.Grammar.Tree.Sort.ValidAll
  BSmtLibSpec.Grammar.Tree.Sort.tokens
  BSmtLibSpec.Grammar.Tree.Sort.tokensAll
  BSmtLibSpec.Grammar.Tree.SortDec.tokens
  BSmtLibSpec.Grammar.Tree.SortedVar.Valid
  BSmtLibSpec.Grammar.Tree.SortedVar.tokens
  BSmtLibSpec.Grammar.Tree.SpecConstant.token
  BSmtLibSpec.Grammar.Tree.SymbolOrWildcard.Valid
  BSmtLibSpec.Grammar.Tree.SymbolOrWildcard.token
  BSmtLibSpec.Grammar.Tree.Term.Valid
  BSmtLibSpec.Grammar.Tree.Term.ValidAll
  BSmtLibSpec.Grammar.Tree.Term.ValidBindings
  BSmtLibSpec.Grammar.Tree.Term.ValidCases
  BSmtLibSpec.Grammar.Tree.Term.bindingTokens
  BSmtLibSpec.Grammar.Tree.Term.caseTokens
  BSmtLibSpec.Grammar.Tree.Term.tokens
  BSmtLibSpec.Grammar.Tree.Term.tokensAll
BSmtLibSpec.Lexer:
  BSmtLibSpec.Lexicon.Category.type
  BSmtLibSpec.Lexicon.Token.handed
  BSmtLibSpec.Lexicon.Token.reservedKind
BSmtLibSpec.Reader:
  BSmtLibSpec.Lexer.Handed.received
2 exceptions:
  BSmtLib.Token.BatchCursor.TokenWindow.syntax in BSmtLib.Token.SyntaxToken
  BSmtLib.Token.BatchCursor.syntax in BSmtLib.Token.SyntaxToken
-/
#guard_msgs in
#naming except BSmtLib.Token.BatchCursor.syntax BSmtLib.Token.BatchCursor.TokenWindow.syntax

/-! The re-exports, for the `pub use` lines of the Rust crate: the generated module
`BSmtLib.Reexports` is what `BSmtLib.Facts.Reexports.render` makes now, and every second name
resolves. -/

/-- info: 95 items re-exported, with 438 members -/
#guard_msgs in
#reexports

/-! The names that users of the Rust crate write, without the prefix `Smt`, for the items that
have a counterpart, and what they resolve to. The items without one: `SmtMultiple` and
`SmtMultipleIntoIter` (`multiple.rs`); `lexer::SmtFailFast` and `lexer::SmtRecovering`,
whose counterparts are the constructors of `BSmtLib.Lexer.Recovery`; `parser::SmtCommandRule`,
`parser::SmtCommandPayloadParser` and `parser::SmtParseState`. -/

/--
info: BSmtLib.BytesView ↦ BSmtLib.Bytes.BytesView
BSmtLib.AttributeValueNode ↦ BSmtLib.Nodes.AttributeValueNode
BSmtLib.Constructor ↦ BSmtLib.Nodes.Constructor
BSmtLib.Identifier ↦ BSmtLib.Nodes.Identifier
BSmtLib.Index ↦ BSmtLib.Nodes.Index
BSmtLib.Pattern ↦ BSmtLib.Nodes.Pattern
BSmtLib.QualifiedIdent ↦ BSmtLib.Nodes.QualifiedIdent
BSmtLib.Quantifier ↦ BSmtLib.Nodes.Quantifier
BSmtLib.SExprNode ↦ BSmtLib.Nodes.SExprNode
BSmtLib.Signature ↦ BSmtLib.Nodes.Signature
BSmtLib.SpecConstant ↦ BSmtLib.Nodes.SpecConstant
BSmtLib.SymbolOrWildcard ↦ BSmtLib.Nodes.SymbolOrWildcard
BSmtLib.TermNode ↦ BSmtLib.Nodes.TermNode
BSmtLib.BinDigits ↦ BSmtLib.Plain.BinDigits
BSmtLib.BinDigitsView ↦ BSmtLib.Plain.BinDigitsView
BSmtLib.Comment ↦ BSmtLib.Plain.Comment
BSmtLib.CommentView ↦ BSmtLib.Plain.CommentView
BSmtLib.Decimal ↦ BSmtLib.Plain.Decimal
BSmtLib.DecimalView ↦ BSmtLib.Plain.DecimalView
BSmtLib.DisallowedByteVecError ↦ BSmtLib.Plain.DisallowedByteVecError
BSmtLib.HexDigits ↦ BSmtLib.Plain.HexDigits
BSmtLib.HexDigitsView ↦ BSmtLib.Plain.HexDigitsView
BSmtLib.Keyword ↦ BSmtLib.Plain.Keyword
BSmtLib.KeywordView ↦ BSmtLib.Plain.KeywordView
BSmtLib.Numeral ↦ BSmtLib.Plain.Numeral
BSmtLib.NumeralView ↦ BSmtLib.Plain.NumeralView
BSmtLib.StringContent ↦ BSmtLib.Plain.StringContent
BSmtLib.StringContentView ↦ BSmtLib.Plain.StringContentView
BSmtLib.Symbol ↦ BSmtLib.Plain.Symbol
BSmtLib.SymbolView ↦ BSmtLib.Plain.SymbolView
BSmtLib.Whitespace ↦ BSmtLib.Plain.Whitespace
BSmtLib.WhitespaceView ↦ BSmtLib.Plain.WhitespaceView
BSmtLib.Located ↦ BSmtLib.Span.Located
BSmtLib.Location ↦ BSmtLib.Span.Location
BSmtLib.CommandHandler ↦ BSmtLib.Traits.CommandHandler
BSmtLib.Handler ↦ BSmtLib.Traits.Handler
BSmtLib.Token.Reserved ↦ BSmtLib.Token.Reserved
BSmtLib.Token.CommandNameReserved ↦ BSmtLib.Token.Reserved.CommandNameReserved
BSmtLib.Token.GeneralReserved ↦ BSmtLib.Token.Reserved.GeneralReserved
BSmtLib.Lexer.LexError ↦ BSmtLib.Lexer.Error.LexError
BSmtLib.Lexer.LexErrorCause ↦ BSmtLib.Lexer.Error.LexErrorCause
BSmtLib.Lexer.LexicalErrorKind ↦ BSmtLib.Lexer.Error.LexicalErrorKind
BSmtLib.Lexer.LexRecovery ↦ BSmtLib.Lexer.Recovery.LexRecovery
BSmtLib.Parser.Category.ClosedAttributeParser ↦ BSmtLib.Parser.Category.Attribute.ClosedAttributeParser
BSmtLib.Parser.Category.ClosedMultipleAttributeParser ↦ BSmtLib.Parser.Category.Attribute.ClosedMultipleAttributeParser
BSmtLib.Parser.Category.ClosedMaximumParser ↦ BSmtLib.Parser.Category.Combinator.ClosedMaximumParser
BSmtLib.Parser.Category.ClosedMultipleParser ↦ BSmtLib.Parser.Category.Combinator.ClosedMultipleParser
BSmtLib.Parser.Category.ClosedParser ↦ BSmtLib.Parser.Category.Combinator.ClosedParser
BSmtLib.Parser.Category.OpenedParser ↦ BSmtLib.Parser.Category.Combinator.OpenedParser
BSmtLib.Parser.Category.PairParser ↦ BSmtLib.Parser.Category.Combinator.PairParser
BSmtLib.Parser.Category.ParenMaximumParser ↦ BSmtLib.Parser.Category.Combinator.ParenMaximumParser
BSmtLib.Parser.Category.ParenMultipleParser ↦ BSmtLib.Parser.Category.Combinator.ParenMultipleParser
BSmtLib.Parser.Category.ParenParser ↦ BSmtLib.Parser.Category.Combinator.ParenParser
BSmtLib.Parser.Category.IdentParser ↦ BSmtLib.Parser.Category.Ident.IdentParser
BSmtLib.Parser.Category.PatternParser ↦ BSmtLib.Parser.Category.Pattern.PatternParser
BSmtLib.Parser.Category.QualifiedIdentParser ↦ BSmtLib.Parser.Category.QualifiedIdent.QualifiedIdentParser
BSmtLib.Parser.Category.SExprParser ↦ BSmtLib.Parser.Category.SExpr.SExprParser
BSmtLib.Parser.Category.SortParser ↦ BSmtLib.Parser.Category.Sort.SortParser
BSmtLib.Parser.Category.SortedVarParser ↦ BSmtLib.Parser.Category.SortedVar.SortedVarParser
BSmtLib.Parser.Category.TermParser ↦ BSmtLib.Parser.Category.Term.TermParser
BSmtLib.Parser.Category.CloseParenParser ↦ BSmtLib.Parser.Category.Token.CloseParenParser
BSmtLib.Parser.Category.KeywordParser ↦ BSmtLib.Parser.Category.Token.KeywordParser
BSmtLib.Parser.Category.NumeralParser ↦ BSmtLib.Parser.Category.Token.NumeralParser
BSmtLib.Parser.Category.OpenParenParser ↦ BSmtLib.Parser.Category.Token.OpenParenParser
BSmtLib.Parser.Category.StringParser ↦ BSmtLib.Parser.Category.Token.StringParser
BSmtLib.Parser.Category.SymbolParser ↦ BSmtLib.Parser.Category.Token.SymbolParser
BSmtLib.Parser.ParseAdapter ↦ BSmtLib.Parser.Adapter.ParseAdapter
BSmtLib.Parser.ClosedAttributeParser ↦ BSmtLib.Parser.Category.Attribute.ClosedAttributeParser
BSmtLib.Parser.ClosedMultipleAttributeParser ↦ BSmtLib.Parser.Category.Attribute.ClosedMultipleAttributeParser
BSmtLib.Parser.ClosedMaximumParser ↦ BSmtLib.Parser.Category.Combinator.ClosedMaximumParser
BSmtLib.Parser.ClosedMultipleParser ↦ BSmtLib.Parser.Category.Combinator.ClosedMultipleParser
BSmtLib.Parser.ClosedParser ↦ BSmtLib.Parser.Category.Combinator.ClosedParser
BSmtLib.Parser.OpenedParser ↦ BSmtLib.Parser.Category.Combinator.OpenedParser
BSmtLib.Parser.PairParser ↦ BSmtLib.Parser.Category.Combinator.PairParser
BSmtLib.Parser.ParenMaximumParser ↦ BSmtLib.Parser.Category.Combinator.ParenMaximumParser
BSmtLib.Parser.ParenMultipleParser ↦ BSmtLib.Parser.Category.Combinator.ParenMultipleParser
BSmtLib.Parser.ParenParser ↦ BSmtLib.Parser.Category.Combinator.ParenParser
BSmtLib.Parser.IdentParser ↦ BSmtLib.Parser.Category.Ident.IdentParser
BSmtLib.Parser.PatternParser ↦ BSmtLib.Parser.Category.Pattern.PatternParser
BSmtLib.Parser.QualifiedIdentParser ↦ BSmtLib.Parser.Category.QualifiedIdent.QualifiedIdentParser
BSmtLib.Parser.SExprParser ↦ BSmtLib.Parser.Category.SExpr.SExprParser
BSmtLib.Parser.SortParser ↦ BSmtLib.Parser.Category.Sort.SortParser
BSmtLib.Parser.SortedVarParser ↦ BSmtLib.Parser.Category.SortedVar.SortedVarParser
BSmtLib.Parser.TermParser ↦ BSmtLib.Parser.Category.Term.TermParser
BSmtLib.Parser.ParenSortedVarsParser ↦ BSmtLib.Parser.Category.ParenSortedVarsParser
BSmtLib.Parser.CloseParenParser ↦ BSmtLib.Parser.Category.Token.CloseParenParser
BSmtLib.Parser.KeywordParser ↦ BSmtLib.Parser.Category.Token.KeywordParser
BSmtLib.Parser.NumeralParser ↦ BSmtLib.Parser.Category.Token.NumeralParser
BSmtLib.Parser.OpenParenParser ↦ BSmtLib.Parser.Category.Token.OpenParenParser
BSmtLib.Parser.StringParser ↦ BSmtLib.Parser.Category.Token.StringParser
BSmtLib.Parser.SymbolParser ↦ BSmtLib.Parser.Category.Token.SymbolParser
BSmtLib.Parser.CommandParser ↦ BSmtLib.Parser.Command.CommandParser
BSmtLib.Parser.CommandOutcome ↦ BSmtLib.Parser.Command.CommandOutcome
BSmtLib.Parser.ScriptParser ↦ BSmtLib.Parser.Script.ScriptParser
-/
#guard_msgs in
#resolves
  BSmtLib.BytesView
  BSmtLib.AttributeValueNode
  BSmtLib.Constructor
  BSmtLib.Identifier
  BSmtLib.Index
  BSmtLib.Pattern
  BSmtLib.QualifiedIdent
  BSmtLib.Quantifier
  BSmtLib.SExprNode
  BSmtLib.Signature
  BSmtLib.SpecConstant
  BSmtLib.SymbolOrWildcard
  BSmtLib.TermNode
  BSmtLib.BinDigits
  BSmtLib.BinDigitsView
  BSmtLib.Comment
  BSmtLib.CommentView
  BSmtLib.Decimal
  BSmtLib.DecimalView
  BSmtLib.DisallowedByteVecError
  BSmtLib.HexDigits
  BSmtLib.HexDigitsView
  BSmtLib.Keyword
  BSmtLib.KeywordView
  BSmtLib.Numeral
  BSmtLib.NumeralView
  BSmtLib.StringContent
  BSmtLib.StringContentView
  BSmtLib.Symbol
  BSmtLib.SymbolView
  BSmtLib.Whitespace
  BSmtLib.WhitespaceView
  BSmtLib.Located
  BSmtLib.Location
  BSmtLib.CommandHandler
  BSmtLib.Handler
  BSmtLib.Token.Reserved
  BSmtLib.Token.CommandNameReserved
  BSmtLib.Token.GeneralReserved
  BSmtLib.Lexer.LexError
  BSmtLib.Lexer.LexErrorCause
  BSmtLib.Lexer.LexicalErrorKind
  BSmtLib.Lexer.LexRecovery
  BSmtLib.Parser.Category.ClosedAttributeParser
  BSmtLib.Parser.Category.ClosedMultipleAttributeParser
  BSmtLib.Parser.Category.ClosedMaximumParser
  BSmtLib.Parser.Category.ClosedMultipleParser
  BSmtLib.Parser.Category.ClosedParser
  BSmtLib.Parser.Category.OpenedParser
  BSmtLib.Parser.Category.PairParser
  BSmtLib.Parser.Category.ParenMaximumParser
  BSmtLib.Parser.Category.ParenMultipleParser
  BSmtLib.Parser.Category.ParenParser
  BSmtLib.Parser.Category.IdentParser
  BSmtLib.Parser.Category.PatternParser
  BSmtLib.Parser.Category.QualifiedIdentParser
  BSmtLib.Parser.Category.SExprParser
  BSmtLib.Parser.Category.SortParser
  BSmtLib.Parser.Category.SortedVarParser
  BSmtLib.Parser.Category.TermParser
  BSmtLib.Parser.Category.CloseParenParser
  BSmtLib.Parser.Category.KeywordParser
  BSmtLib.Parser.Category.NumeralParser
  BSmtLib.Parser.Category.OpenParenParser
  BSmtLib.Parser.Category.StringParser
  BSmtLib.Parser.Category.SymbolParser
  BSmtLib.Parser.ParseAdapter
  BSmtLib.Parser.ClosedAttributeParser
  BSmtLib.Parser.ClosedMultipleAttributeParser
  BSmtLib.Parser.ClosedMaximumParser
  BSmtLib.Parser.ClosedMultipleParser
  BSmtLib.Parser.ClosedParser
  BSmtLib.Parser.OpenedParser
  BSmtLib.Parser.PairParser
  BSmtLib.Parser.ParenMaximumParser
  BSmtLib.Parser.ParenMultipleParser
  BSmtLib.Parser.ParenParser
  BSmtLib.Parser.IdentParser
  BSmtLib.Parser.PatternParser
  BSmtLib.Parser.QualifiedIdentParser
  BSmtLib.Parser.SExprParser
  BSmtLib.Parser.SortParser
  BSmtLib.Parser.SortedVarParser
  BSmtLib.Parser.TermParser
  BSmtLib.Parser.ParenSortedVarsParser
  BSmtLib.Parser.CloseParenParser
  BSmtLib.Parser.KeywordParser
  BSmtLib.Parser.NumeralParser
  BSmtLib.Parser.OpenParenParser
  BSmtLib.Parser.StringParser
  BSmtLib.Parser.SymbolParser
  BSmtLib.Parser.CommandParser
  BSmtLib.Parser.CommandOutcome
  BSmtLib.Parser.ScriptParser

/-! The Rust counterparts: every public name of the library has one among the public items of
the Rust crate (`BSmtLib.Facts.RustItems`, generated from its documentation), or a `LEAN:` reason
at its declaration; the names with a reason are listed. -/

/--
info: 293 public names with a Rust counterpart; 48 with a `LEAN:` reason instead:
  BSmtLib.ControlFlow
  BSmtLib.Lexer.AfterEof
  BSmtLib.Lexer.AfterEofError
  BSmtLib.Lexer.AfterError
  BSmtLib.Lexer.PendingEof
  BSmtLib.Lexer.PendingEof.lexEof
  BSmtLib.Lexer.Recovery.Recovers
  BSmtLib.Lexer.modifyConsumer
  BSmtLib.Nodes.AttributeValueNode
  BSmtLib.Nodes.Constructor
  BSmtLib.Nodes.Identifier
  BSmtLib.Nodes.Identifier.newSimple
  BSmtLib.Nodes.Quantifier
  BSmtLib.Nodes.SExprNode
  BSmtLib.Nodes.Signature
  BSmtLib.Nodes.SpecConstant
  BSmtLib.Nodes.Symbol
  BSmtLib.Nodes.SymbolOrWildcard
  BSmtLib.Nodes.TermNode
  BSmtLib.Parser.Category.Combinator.ParenMultipleParser.new
  BSmtLib.Parser.Category.Combinator.ParenParser.new
  BSmtLib.Parser.ParseState
  BSmtLib.Parser.ParseState.new
  BSmtLib.Plain.Numeral.fromNat
  BSmtLib.Plain.Symbol.isAllowed
  BSmtLib.Plain.Symbol.new
  BSmtLib.Reader.BufRead
  BSmtLib.Reader.BufReader
  BSmtLib.Reader.BufReader.new
  BSmtLib.Reader.ReadError.ofLex
  BSmtLib.Reader.ReadError.ofParse
  BSmtLib.Reader.ReadFailure
  BSmtLib.Reader.modifyHandler
  BSmtLib.Token.BatchCursor.Consumed
  BSmtLib.Token.BatchCursor.HasNext
  BSmtLib.Token.BatchCursor.TokenWindow
  BSmtLib.Token.BatchCursor.TokenWindow.Consumed
  BSmtLib.Token.BatchCursor.TokenWindow.category
  BSmtLib.Token.BatchCursor.TokenWindow.content
  BSmtLib.Token.BatchCursor.TokenWindow.next?
  BSmtLib.Token.BatchCursor.TokenWindow.span
  BSmtLib.Token.BatchCursor.TokenWindow.syntax
  BSmtLib.Token.BatchCursor.category
  BSmtLib.Token.BatchCursor.content
  BSmtLib.Token.BatchCursor.span
  BSmtLib.Token.BatchTag
  BSmtLib.Token.Reserved.CommandNameReserved.all
  BSmtLib.Token.Reserved.GeneralReserved.all
-/
#guard_msgs in
#counterparts
