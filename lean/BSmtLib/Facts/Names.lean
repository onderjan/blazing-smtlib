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
declared where `SyntaxToken` is, which `Token.lean` cannot import, and the error of writing a
token, declared there as it names `Reserved`, whose module imports `Token.lean`. -/

/--
info: 8167 declarations in 451 modules; 85 add to a sibling's type:
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
4 exceptions:
  BSmtLib.Token.BatchCursor.TokenWindow.syntax in BSmtLib.Token.SyntaxToken
  BSmtLib.Token.BatchCursor.syntax in BSmtLib.Token.SyntaxToken
  BSmtLib.Token.WriteError in BSmtLib.Token.SyntaxToken
  BSmtLib.Token.WriteErrorCause in BSmtLib.Token.SyntaxToken
-/
#guard_msgs in
#naming except BSmtLib.Token.BatchCursor.syntax BSmtLib.Token.BatchCursor.TokenWindow.syntax
  BSmtLib.Token.WriteError BSmtLib.Token.WriteErrorCause

/-! The re-exports, for the `pub use` lines of the Rust crate: the generated module
`BSmtLib.Reexports` is what `BSmtLib.Facts.Reexports.render` makes now, and every second name
resolves. -/

/-- info: 144 items re-exported, with 710 members -/
#guard_msgs in
#reexports

/-! The names that users of the Rust crate write, without the prefix `Smt`, for the items that
have a counterpart, and what they resolve to. The items without one: `SmtMultiple`, which is
`BSmtLib.Multiple` itself, and the iterators of `multiple.rs` (`SmtMultipleIntoIter` and the
others), whose counterparts are `ForIn` instances; `lexer::SmtFailFast` and `lexer::SmtRecovering`,
whose counterparts are the constructors of `BSmtLib.Lexer.Recovery`; `parser::SmtCommandRule`,
`parser::SmtCommandPayloadParser` and `parser::SmtParseState`. -/

/--
info: BSmtLib.Bytes ↦ BSmtLib.Bytes
BSmtLib.BindingsBuf ↦ BSmtLib.Multiple.BindingsBuf
BSmtLib.Bindings ↦ BSmtLib.Multiple.Bindings
BSmtLib.ConstructorsBuf ↦ BSmtLib.Multiple.ConstructorsBuf
BSmtLib.Constructors ↦ BSmtLib.Multiple.Constructors
BSmtLib.FunctionSignaturesBuf ↦ BSmtLib.Multiple.FunctionSignaturesBuf
BSmtLib.FunctionSignatures ↦ BSmtLib.Multiple.FunctionSignatures
BSmtLib.MatchCases ↦ BSmtLib.Multiple.MatchCases
BSmtLib.NamedBuf ↦ BSmtLib.Multiple.NamedBuf
BSmtLib.Named ↦ BSmtLib.Multiple.Named
BSmtLib.SortAritiesBuf ↦ BSmtLib.Multiple.SortAritiesBuf
BSmtLib.SortArities ↦ BSmtLib.Multiple.SortArities
BSmtLib.SortedVarsBuf ↦ BSmtLib.Multiple.SortedVarsBuf
BSmtLib.SortedVars ↦ BSmtLib.Multiple.SortedVars
BSmtLib.SymbolsBuf ↦ BSmtLib.Multiple.SymbolsBuf
BSmtLib.Symbols ↦ BSmtLib.Multiple.Symbols
BSmtLib.AttributeValue ↦ BSmtLib.Nodes.AttributeValue
BSmtLib.Attributes ↦ BSmtLib.Nodes.Attributes
BSmtLib.Ident ↦ BSmtLib.Nodes.Ident
BSmtLib.IdentBuf ↦ BSmtLib.Nodes.IdentBuf
BSmtLib.Index ↦ BSmtLib.Nodes.Index
BSmtLib.IndexBuf ↦ BSmtLib.Nodes.IndexBuf
BSmtLib.Pattern ↦ BSmtLib.Nodes.Pattern
BSmtLib.PatternBuf ↦ BSmtLib.Nodes.PatternBuf
BSmtLib.QualifiedIdent ↦ BSmtLib.Nodes.QualifiedIdent
BSmtLib.QualifiedIdentBuf ↦ BSmtLib.Nodes.QualifiedIdentBuf
BSmtLib.QuantifierKind ↦ BSmtLib.Nodes.QuantifierKind
BSmtLib.SExpr ↦ BSmtLib.Nodes.SExpr
BSmtLib.SExprs ↦ BSmtLib.Nodes.SExprs
BSmtLib.FunctionSignature ↦ BSmtLib.Multiple.FunctionSignature
BSmtLib.Sorts ↦ BSmtLib.Nodes.Sorts
BSmtLib.SpecialConstant ↦ BSmtLib.Nodes.SpecialConstant
BSmtLib.SpecialConstantBuf ↦ BSmtLib.Nodes.SpecialConstantBuf
BSmtLib.SimplePattern ↦ BSmtLib.Nodes.SimplePattern
BSmtLib.SimplePatternBuf ↦ BSmtLib.Nodes.SimplePatternBuf
BSmtLib.Term ↦ BSmtLib.Nodes.Term
BSmtLib.Terms ↦ BSmtLib.Nodes.Terms
BSmtLib.BinDigitsBuf ↦ BSmtLib.Plain.BinDigitsBuf
BSmtLib.BinDigits ↦ BSmtLib.Plain.BinDigits
BSmtLib.CommentBuf ↦ BSmtLib.Plain.CommentBuf
BSmtLib.Comment ↦ BSmtLib.Plain.Comment
BSmtLib.DecimalBuf ↦ BSmtLib.Plain.DecimalBuf
BSmtLib.Decimal ↦ BSmtLib.Plain.Decimal
BSmtLib.DisallowedByteVecError ↦ BSmtLib.Plain.DisallowedByteVecError
BSmtLib.HexDigitsBuf ↦ BSmtLib.Plain.HexDigitsBuf
BSmtLib.HexDigits ↦ BSmtLib.Plain.HexDigits
BSmtLib.KeywordBuf ↦ BSmtLib.Plain.KeywordBuf
BSmtLib.Keyword ↦ BSmtLib.Plain.Keyword
BSmtLib.NumeralBuf ↦ BSmtLib.Plain.NumeralBuf
BSmtLib.Numeral ↦ BSmtLib.Plain.Numeral
BSmtLib.StringContentBuf ↦ BSmtLib.Plain.StringContentBuf
BSmtLib.StringContent ↦ BSmtLib.Plain.StringContent
BSmtLib.SymbolBuf ↦ BSmtLib.Plain.SymbolBuf
BSmtLib.Symbol ↦ BSmtLib.Plain.Symbol
BSmtLib.WhitespaceBuf ↦ BSmtLib.Plain.WhitespaceBuf
BSmtLib.Whitespace ↦ BSmtLib.Plain.Whitespace
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
  BSmtLib.Bytes
  BSmtLib.BindingsBuf
  BSmtLib.Bindings
  BSmtLib.ConstructorsBuf
  BSmtLib.Constructors
  BSmtLib.FunctionSignaturesBuf
  BSmtLib.FunctionSignatures
  BSmtLib.MatchCases
  BSmtLib.NamedBuf
  BSmtLib.Named
  BSmtLib.SortAritiesBuf
  BSmtLib.SortArities
  BSmtLib.SortedVarsBuf
  BSmtLib.SortedVars
  BSmtLib.SymbolsBuf
  BSmtLib.Symbols
  BSmtLib.AttributeValue
  BSmtLib.Attributes
  BSmtLib.Ident
  BSmtLib.IdentBuf
  BSmtLib.Index
  BSmtLib.IndexBuf
  BSmtLib.Pattern
  BSmtLib.PatternBuf
  BSmtLib.QualifiedIdent
  BSmtLib.QualifiedIdentBuf
  BSmtLib.QuantifierKind
  BSmtLib.SExpr
  BSmtLib.SExprs
  BSmtLib.FunctionSignature
  BSmtLib.Sorts
  BSmtLib.SpecialConstant
  BSmtLib.SpecialConstantBuf
  BSmtLib.SimplePattern
  BSmtLib.SimplePatternBuf
  BSmtLib.Term
  BSmtLib.Terms
  BSmtLib.BinDigitsBuf
  BSmtLib.BinDigits
  BSmtLib.CommentBuf
  BSmtLib.Comment
  BSmtLib.DecimalBuf
  BSmtLib.Decimal
  BSmtLib.DisallowedByteVecError
  BSmtLib.HexDigitsBuf
  BSmtLib.HexDigits
  BSmtLib.KeywordBuf
  BSmtLib.Keyword
  BSmtLib.NumeralBuf
  BSmtLib.Numeral
  BSmtLib.StringContentBuf
  BSmtLib.StringContent
  BSmtLib.SymbolBuf
  BSmtLib.Symbol
  BSmtLib.WhitespaceBuf
  BSmtLib.Whitespace
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
at its declaration; the names with a reason are listed. The other way round, every public item
of the Rust crate, trait implementation and structure with private fields has its Lean
counterpart, or a reason in `BSmtLib.Facts.RustOnly`; the items with a reason are listed. -/

/--
info: 470 public names with a Rust counterpart; 88 with a `LEAN:` reason instead:
  BSmtLib.Bytes.BytesBuf.eqSlice
  BSmtLib.Bytes.BytesBuf.eqView
  BSmtLib.Bytes.eqOwned
  BSmtLib.Bytes.eqSlice
  BSmtLib.ControlFlow
  BSmtLib.Lexer.AfterEof
  BSmtLib.Lexer.AfterEofError
  BSmtLib.Lexer.AfterError
  BSmtLib.Lexer.PendingEof
  BSmtLib.Lexer.PendingEof.lexEof
  BSmtLib.Lexer.Recovery.Recovers
  BSmtLib.Parser.Category.Combinator.ParenMultipleParser.new
  BSmtLib.Parser.Category.Combinator.ParenParser.new
  BSmtLib.Parser.Category.ParenSortedVarsParser.new
  BSmtLib.Parser.ParseState
  BSmtLib.Parser.ParseState.new
  BSmtLib.Plain.BinDigits.eqOwned
  BSmtLib.Plain.BinDigits.eqSlice
  BSmtLib.Plain.BinDigits.eqString
  BSmtLib.Plain.BinDigitsBuf.eqSlice
  BSmtLib.Plain.BinDigitsBuf.eqString
  BSmtLib.Plain.BinDigitsBuf.eqView
  BSmtLib.Plain.Comment.eqOwned
  BSmtLib.Plain.Comment.eqSlice
  BSmtLib.Plain.Comment.eqString
  BSmtLib.Plain.CommentBuf.eqSlice
  BSmtLib.Plain.CommentBuf.eqString
  BSmtLib.Plain.CommentBuf.eqView
  BSmtLib.Plain.Decimal.eqOwned
  BSmtLib.Plain.Decimal.eqSlice
  BSmtLib.Plain.Decimal.eqString
  BSmtLib.Plain.DecimalBuf.eqSlice
  BSmtLib.Plain.DecimalBuf.eqString
  BSmtLib.Plain.DecimalBuf.eqView
  BSmtLib.Plain.HexDigits.eqOwned
  BSmtLib.Plain.HexDigits.eqSlice
  BSmtLib.Plain.HexDigits.eqString
  BSmtLib.Plain.HexDigitsBuf.eqSlice
  BSmtLib.Plain.HexDigitsBuf.eqString
  BSmtLib.Plain.HexDigitsBuf.eqView
  BSmtLib.Plain.Keyword.eqOwned
  BSmtLib.Plain.Keyword.eqSlice
  BSmtLib.Plain.Keyword.eqString
  BSmtLib.Plain.KeywordBuf.eqSlice
  BSmtLib.Plain.KeywordBuf.eqString
  BSmtLib.Plain.KeywordBuf.eqView
  BSmtLib.Plain.Numeral.eqOwned
  BSmtLib.Plain.Numeral.eqSlice
  BSmtLib.Plain.Numeral.eqString
  BSmtLib.Plain.Numeral.toNat
  BSmtLib.Plain.NumeralBuf.eqSlice
  BSmtLib.Plain.NumeralBuf.eqString
  BSmtLib.Plain.NumeralBuf.eqView
  BSmtLib.Plain.NumeralBuf.fromNat
  BSmtLib.Plain.NumeralBuf.toNat
  BSmtLib.Plain.StringContent.eqOwned
  BSmtLib.Plain.StringContent.eqSlice
  BSmtLib.Plain.StringContent.eqString
  BSmtLib.Plain.StringContentBuf.eqSlice
  BSmtLib.Plain.StringContentBuf.eqString
  BSmtLib.Plain.StringContentBuf.eqView
  BSmtLib.Plain.Whitespace.eqOwned
  BSmtLib.Plain.Whitespace.eqSlice
  BSmtLib.Plain.Whitespace.eqString
  BSmtLib.Plain.WhitespaceBuf.eqSlice
  BSmtLib.Plain.WhitespaceBuf.eqString
  BSmtLib.Plain.WhitespaceBuf.eqView
  BSmtLib.Reader.BufRead
  BSmtLib.Reader.BufReader
  BSmtLib.Reader.BufReader.new
  BSmtLib.Reader.ReadError.ofLex
  BSmtLib.Reader.ReadError.ofParse
  BSmtLib.Reader.ReadFailure
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
---
info: 686 Rust items, 259 trait implementations with a counterpart class and 87 structures with private fields; 87 without a counterpart, with a reason:
  bytes::SmtBytes::iter
  bytes::SmtBytesBuf::from_boxed_slice
  bytes::SmtBytesBuf::into_boxed_slice
  bytes::SmtBytesBuf::iter
  impl core::default::Default for parser::category::combinator::SmtTuple3Parser
  impl core::default::Default for parser::category::combinator::SmtTuple4Parser
  impl core::default::Default for parser::category::combinator::SmtTuple5Parser
  impl core::default::Default for parser::category::combinator::SmtTuple6Parser
  impl core::default::Default for parser::category::combinator::SmtTuple7Parser
  impl core::default::Default for parser::category::combinator::SmtTuple8Parser
  impl core::default::Default for parser::state::SmtParseState
  impl core::fmt::Debug for nodes::SmtApplication
  impl core::fmt::Debug for nodes::SmtIndices
  impl core::fmt::Debug for nodes::SmtSimplePatterns
  impl core::fmt::Debug for nodes::SmtSort
  impl core::fmt::Debug for token::SmtToken
  impl parser::SmtParse for parser::category::combinator::SmtTuple3Parser
  impl parser::SmtParse for parser::category::combinator::SmtTuple4Parser
  impl parser::SmtParse for parser::category::combinator::SmtTuple5Parser
  impl parser::SmtParse for parser::category::combinator::SmtTuple6Parser
  impl parser::SmtParse for parser::category::combinator::SmtTuple7Parser
  impl parser::SmtParse for parser::category::combinator::SmtTuple8Parser
  impl token::SmtLookahead for token::SmtTokenWindow
  multiple::SmtConstructors::iter_mut
  multiple::SmtConstructorsIter
  multiple::SmtFunctionSignatures::iter
  multiple::SmtFunctionSignaturesIter
  multiple::SmtMatchCases::get_mut
  multiple::SmtMatchCases::iter
  multiple::SmtMatchCases::iter_mut
  multiple::SmtMatchCasesIntoIter
  multiple::SmtMultiple::as_mut_slice
  multiple::SmtMultiple::get_mut
  multiple::SmtMultiple::iter
  multiple::SmtMultiple::iter_mut
  multiple::SmtMultipleIntoIter
  multiple::SmtNamed::get_mut
  multiple::SmtNamed::iter
  multiple::SmtNamed::iter_mut
  multiple::SmtNamedIntoIter
  multiple::SmtSortArities::iter
  multiple::SmtSortAritiesIter
  multiple::SmtSymbols::iter
  multiple::SmtSymbolsIter
  nodes::SmtApplication
  nodes::SmtIndices
  nodes::SmtIndices::get
  nodes::SmtIndices::is_empty
  nodes::SmtIndices::iter
  nodes::SmtIndices::len
  nodes::SmtSimplePatterns
  nodes::SmtSimplePatterns::get
  nodes::SmtSimplePatterns::is_empty
  nodes::SmtSimplePatterns::iter
  nodes::SmtSimplePatterns::len
  nodes::SmtSort
  parser::SmtParse::Result
  parser::state::SmtParseState
  parser::state::SmtParseState::new
  plain::SmtBinDigits::iter
  plain::SmtBinDigitsBuf::iter
  plain::SmtComment::iter
  plain::SmtCommentBuf::iter
  plain::SmtDecimal::iter
  plain::SmtDecimalBuf::iter
  plain::SmtHexDigits::iter
  plain::SmtHexDigitsBuf::iter
  plain::SmtKeyword::iter
  plain::SmtKeywordBuf::iter
  plain::SmtNumeral::iter
  plain::SmtNumeral::to_u128
  plain::SmtNumeralBuf::from_u128
  plain::SmtNumeralBuf::iter
  plain::SmtNumeralBuf::to_u128
  plain::SmtStringContent::iter
  plain::SmtStringContentBuf::iter
  plain::SmtSymbol::iter
  plain::SmtSymbolBuf::iter
  plain::SmtWhitespace::iter
  plain::SmtWhitespaceBuf::iter
  token::SmtConsume::Error
  token::SmtConsume::IS_CONCRETE
  token::SmtConsume::Result
  token::SmtToken::category
  token::SmtToken::content
  token::SmtToken::span
  token::SmtTokenWindow
-/
#guard_msgs in
#counterparts
