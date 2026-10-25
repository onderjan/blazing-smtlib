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

/-! The naming rule, with its exceptions: the view of the cursor's token as a token,
`Token.fromLexerToken`, declared in `BSmtLib.Lexer.Cursor`, and the token's `intoOwned`, declared
in `BSmtLib.Token.TokenBuf`, as both modules import `Token.lean`; the constructor of the error of
writing a token, declared in `Token.lean`, as the token's `writeSmt` returns the error and
`Writer.lean` imports `Token.lean`; the stand-in of Rust's `BufReader`, declared in
`BSmtLib.Reader.BufRead`, which the lexer imports, as the reader's module imports the lexer's;
and the functions of the symbol that name the version and `Reserved`, declared in
`BSmtLib.Lexicon.Value.Versioned`, as the modules of both import `Lexicon.Value.lean`. -/

/--
info: 8298 declarations in 459 modules; 87 add to a sibling's type:
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
BSmtLib.Token:
  BSmtLib.Writer.WriteError
  BSmtLib.Writer.WriteErrorCause
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
12 exceptions:
  BSmtLib.Lexicon.Value.Symbol.intoVersioned in BSmtLib.Lexicon.Value.Versioned
  BSmtLib.Lexicon.Value.Symbol.isSymbolIn in BSmtLib.Lexicon.Value.Versioned
  BSmtLib.Lexicon.Value.Symbol.newIn in BSmtLib.Lexicon.Value.Versioned
  BSmtLib.Lexicon.Value.SymbolBuf.intoVersioned in BSmtLib.Lexicon.Value.Versioned
  BSmtLib.Lexicon.Value.SymbolBuf.isSimpleIn in BSmtLib.Lexicon.Value.Versioned
  BSmtLib.Lexicon.Value.SymbolBuf.isSymbolIn in BSmtLib.Lexicon.Value.Versioned
  BSmtLib.Lexicon.Value.SymbolBuf.newIn in BSmtLib.Lexicon.Value.Versioned
  BSmtLib.Reader.BufReader in BSmtLib.Reader.BufRead
  BSmtLib.Reader.BufReader.new in BSmtLib.Reader.BufRead
  BSmtLib.Token.fromLexerToken in BSmtLib.Lexer.Cursor
  BSmtLib.Token.intoOwned in BSmtLib.Token.TokenBuf
  BSmtLib.Writer.WriteError.Internal.new in BSmtLib.Token
-/
#guard_msgs in
#naming except BSmtLib.Token.fromLexerToken BSmtLib.Token.intoOwned
  BSmtLib.Writer.WriteError.Internal.new BSmtLib.Reader.BufReader BSmtLib.Reader.BufReader.new
  BSmtLib.Lexicon.Value.Symbol.newIn BSmtLib.Lexicon.Value.Symbol.isSymbolIn
  BSmtLib.Lexicon.Value.Symbol.intoVersioned BSmtLib.Lexicon.Value.SymbolBuf.newIn
  BSmtLib.Lexicon.Value.SymbolBuf.isSimpleIn BSmtLib.Lexicon.Value.SymbolBuf.isSymbolIn
  BSmtLib.Lexicon.Value.SymbolBuf.intoVersioned

/-! The re-exports, for the `pub use` lines of the Rust crate: the generated module
`BSmtLib.Reexports` is what `BSmtLib.Facts.Reexports.render` makes now, and every second name
resolves. -/

/-- info: 155 items re-exported, with 832 members -/
#guard_msgs in
#reexports

/-! The names that users of the Rust crate write, without the prefix `Smt`, for the items that
have a counterpart, and what they resolve to: first the items named like their modules, which
are the modules' own names (`SmtHandler`, `SmtReader`, `SmtVersion`, `SmtWriter`,
`grammar::SmtMultiple`, `lexicon::SmtBytes`, `token::SmtToken`, `token::SmtReserved`), then the
items of the `pub use` lines. The items without one: the iterators of `grammar/multiple.rs`
(`SmtMultipleIntoIter` and the others), whose counterparts are `ForIn` instances. -/

/--
info: BSmtLib.Handler ↦ BSmtLib.Handler
BSmtLib.Reader ↦ BSmtLib.Reader
BSmtLib.Version ↦ BSmtLib.Version
BSmtLib.Writer ↦ BSmtLib.Writer
BSmtLib.Grammar.Multiple ↦ BSmtLib.Grammar.Multiple
BSmtLib.Lexicon.Bytes ↦ BSmtLib.Lexicon.Bytes
BSmtLib.Token ↦ BSmtLib.Token
BSmtLib.Token.Reserved ↦ BSmtLib.Token.Reserved
BSmtLib.CommandHandler ↦ BSmtLib.Handler.CommandHandler
BSmtLib.NonstandardCommandError ↦ BSmtLib.Handler.NonstandardCommandError
BSmtLib.PartialCommandError ↦ BSmtLib.Handler.PartialCommandError
BSmtLib.PartialCommandHandler ↦ BSmtLib.Handler.PartialCommandHandler
BSmtLib.SyntaxChecker ↦ BSmtLib.Handler.SyntaxChecker
BSmtLib.readSmt ↦ BSmtLib.Reader.readSmt
BSmtLib.readSmtFile ↦ BSmtLib.Reader.readSmtFile
BSmtLib.ReadError ↦ BSmtLib.Reader.ReadError
BSmtLib.ReadErrorCause ↦ BSmtLib.Reader.ReadErrorCause
BSmtLib.ReadFailure ↦ BSmtLib.Reader.ReadFailure
BSmtLib.VersionPosture ↦ BSmtLib.Version.VersionPosture
BSmtLib.VersionPostureBuilder ↦ BSmtLib.Version.VersionPostureBuilder
BSmtLib.WriteError ↦ BSmtLib.Writer.WriteError
BSmtLib.WriteErrorCause ↦ BSmtLib.Writer.WriteErrorCause
BSmtLib.WriteStyle ↦ BSmtLib.Writer.WriteStyle
BSmtLib.WriterConfig ↦ BSmtLib.Writer.WriterConfig
BSmtLib.Grammar.Bindings ↦ BSmtLib.Grammar.Multiple.Bindings
BSmtLib.Grammar.Constructors ↦ BSmtLib.Grammar.Multiple.Constructors
BSmtLib.Grammar.ConstructorsBuf ↦ BSmtLib.Grammar.Multiple.ConstructorsBuf
BSmtLib.Grammar.FunctionSignature ↦ BSmtLib.Grammar.Multiple.FunctionSignature
BSmtLib.Grammar.FunctionSignatures ↦ BSmtLib.Grammar.Multiple.FunctionSignatures
BSmtLib.Grammar.FunctionSignaturesBuf ↦ BSmtLib.Grammar.Multiple.FunctionSignaturesBuf
BSmtLib.Grammar.MatchCases ↦ BSmtLib.Grammar.Multiple.MatchCases
BSmtLib.Grammar.MatchCasesBuf ↦ BSmtLib.Grammar.Multiple.MatchCasesBuf
BSmtLib.Grammar.NamedValues ↦ BSmtLib.Grammar.Multiple.NamedValues
BSmtLib.Grammar.NamedValuesBuf ↦ BSmtLib.Grammar.Multiple.NamedValuesBuf
BSmtLib.Grammar.SortArities ↦ BSmtLib.Grammar.Multiple.SortArities
BSmtLib.Grammar.SortAritiesBuf ↦ BSmtLib.Grammar.Multiple.SortAritiesBuf
BSmtLib.Grammar.SortedVars ↦ BSmtLib.Grammar.Multiple.SortedVars
BSmtLib.Grammar.Symbols ↦ BSmtLib.Grammar.Multiple.Symbols
BSmtLib.Grammar.SymbolsBuf ↦ BSmtLib.Grammar.Multiple.SymbolsBuf
BSmtLib.Grammar.AttributeValue ↦ BSmtLib.Grammar.Nodes.AttributeValue
BSmtLib.Grammar.EmptyArgumentsError ↦ BSmtLib.Grammar.Nodes.EmptyArgumentsError
BSmtLib.Grammar.Ident ↦ BSmtLib.Grammar.Nodes.Ident
BSmtLib.Grammar.IdentBuf ↦ BSmtLib.Grammar.Nodes.IdentBuf
BSmtLib.Grammar.Index ↦ BSmtLib.Grammar.Nodes.Index
BSmtLib.Grammar.IndexBuf ↦ BSmtLib.Grammar.Nodes.IndexBuf
BSmtLib.Grammar.IndicesBuf ↦ BSmtLib.Grammar.Nodes.IndicesBuf
BSmtLib.Grammar.Pattern ↦ BSmtLib.Grammar.Nodes.Pattern
BSmtLib.Grammar.PatternApplication ↦ BSmtLib.Grammar.Nodes.PatternApplication
BSmtLib.Grammar.PatternApplicationBuf ↦ BSmtLib.Grammar.Nodes.PatternApplicationBuf
BSmtLib.Grammar.PatternBuf ↦ BSmtLib.Grammar.Nodes.PatternBuf
BSmtLib.Grammar.QualifiedIdent ↦ BSmtLib.Grammar.Nodes.QualifiedIdent
BSmtLib.Grammar.QualifiedIdentBuf ↦ BSmtLib.Grammar.Nodes.QualifiedIdentBuf
BSmtLib.Grammar.QuantifierKind ↦ BSmtLib.Grammar.Nodes.QuantifierKind
BSmtLib.Grammar.SExpr ↦ BSmtLib.Grammar.Nodes.SExpr
BSmtLib.Grammar.SimplePattern ↦ BSmtLib.Grammar.Nodes.SimplePattern
BSmtLib.Grammar.SimplePatternBuf ↦ BSmtLib.Grammar.Nodes.SimplePatternBuf
BSmtLib.Grammar.SimplePatternsBuf ↦ BSmtLib.Grammar.Nodes.SimplePatternsBuf
BSmtLib.Grammar.SpecialConstant ↦ BSmtLib.Grammar.Nodes.SpecialConstant
BSmtLib.Grammar.SpecialConstantBuf ↦ BSmtLib.Grammar.Nodes.SpecialConstantBuf
BSmtLib.Grammar.Term ↦ BSmtLib.Grammar.Nodes.Term
BSmtLib.Lexicon.BytesBuf ↦ BSmtLib.Lexicon.Bytes.BytesBuf
BSmtLib.Lexicon.BinDigits ↦ BSmtLib.Lexicon.Value.BinDigits
BSmtLib.Lexicon.BinDigitsBuf ↦ BSmtLib.Lexicon.Value.BinDigitsBuf
BSmtLib.Lexicon.Comment ↦ BSmtLib.Lexicon.Value.Comment
BSmtLib.Lexicon.CommentBuf ↦ BSmtLib.Lexicon.Value.CommentBuf
BSmtLib.Lexicon.Decimal ↦ BSmtLib.Lexicon.Value.Decimal
BSmtLib.Lexicon.DecimalBuf ↦ BSmtLib.Lexicon.Value.DecimalBuf
BSmtLib.Lexicon.DisallowedByteVecError ↦ BSmtLib.Lexicon.Value.DisallowedByteVecError
BSmtLib.Lexicon.DisallowedBytesError ↦ BSmtLib.Lexicon.Value.DisallowedBytesError
BSmtLib.Lexicon.HexDigits ↦ BSmtLib.Lexicon.Value.HexDigits
BSmtLib.Lexicon.HexDigitsBuf ↦ BSmtLib.Lexicon.Value.HexDigitsBuf
BSmtLib.Lexicon.Keyword ↦ BSmtLib.Lexicon.Value.Keyword
BSmtLib.Lexicon.KeywordBuf ↦ BSmtLib.Lexicon.Value.KeywordBuf
BSmtLib.Lexicon.Numeral ↦ BSmtLib.Lexicon.Value.Numeral
BSmtLib.Lexicon.NumeralBuf ↦ BSmtLib.Lexicon.Value.NumeralBuf
BSmtLib.Lexicon.NumericOverflowError ↦ BSmtLib.Lexicon.Value.NumericOverflowError
BSmtLib.Lexicon.StringContent ↦ BSmtLib.Lexicon.Value.StringContent
BSmtLib.Lexicon.StringContentBuf ↦ BSmtLib.Lexicon.Value.StringContentBuf
BSmtLib.Lexicon.Symbol ↦ BSmtLib.Lexicon.Value.Symbol
BSmtLib.Lexicon.SymbolBuf ↦ BSmtLib.Lexicon.Value.SymbolBuf
BSmtLib.Lexicon.Whitespace ↦ BSmtLib.Lexicon.Value.Whitespace
BSmtLib.Lexicon.WhitespaceBuf ↦ BSmtLib.Lexicon.Value.WhitespaceBuf
BSmtLib.Lexer.LexerCursor ↦ BSmtLib.Lexer.Cursor.LexerCursor
BSmtLib.Lexer.LexerToken ↦ BSmtLib.Lexer.Cursor.LexerToken
BSmtLib.Lexer.LexerWindow ↦ BSmtLib.Lexer.Cursor.LexerWindow
BSmtLib.Lexer.LexerError ↦ BSmtLib.Lexer.Error.LexerError
BSmtLib.Lexer.LexerErrorCause ↦ BSmtLib.Lexer.Error.LexerErrorCause
BSmtLib.Lexer.LexerReadError ↦ BSmtLib.Lexer.Error.LexerReadError
BSmtLib.Lexer.LexerReadErrorCause ↦ BSmtLib.Lexer.Error.LexerReadErrorCause
BSmtLib.Lexer.LexicalErrorKind ↦ BSmtLib.Lexer.Error.LexicalErrorKind
BSmtLib.Lexer.LexicalExpected ↦ BSmtLib.Lexer.Error.LexicalExpected
BSmtLib.Lexer.FailFast ↦ BSmtLib.Lexer.Recovery.FailFast
BSmtLib.Lexer.LexerRecovery ↦ BSmtLib.Lexer.Recovery.LexerRecovery
BSmtLib.Lexer.Recover ↦ BSmtLib.Lexer.Recovery.Recover
BSmtLib.Lexer.Recovering ↦ BSmtLib.Lexer.Recovery.Recovering
BSmtLib.Token.CommandNameReserved ↦ BSmtLib.Token.Reserved.CommandNameReserved
BSmtLib.Token.GeneralReserved ↦ BSmtLib.Token.Reserved.GeneralReserved
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
BSmtLib.Parser.Category.Tuple3Parser ↦ BSmtLib.Parser.Category.Combinator.Tuple3Parser
BSmtLib.Parser.Category.Tuple4Parser ↦ BSmtLib.Parser.Category.Combinator.Tuple4Parser
BSmtLib.Parser.Category.Tuple5Parser ↦ BSmtLib.Parser.Category.Combinator.Tuple5Parser
BSmtLib.Parser.Category.Tuple6Parser ↦ BSmtLib.Parser.Category.Combinator.Tuple6Parser
BSmtLib.Parser.Category.Tuple7Parser ↦ BSmtLib.Parser.Category.Combinator.Tuple7Parser
BSmtLib.Parser.Category.Tuple8Parser ↦ BSmtLib.Parser.Category.Combinator.Tuple8Parser
BSmtLib.Parser.Category.IdentParser ↦ BSmtLib.Parser.Category.Ident.IdentParser
BSmtLib.Parser.Category.PatternParser ↦ BSmtLib.Parser.Category.Pattern.PatternParser
BSmtLib.Parser.Category.SimplePatternParser ↦ BSmtLib.Parser.Category.Pattern.SimplePatternParser
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
BSmtLib.Parser.Tuple3Parser ↦ BSmtLib.Parser.Category.Combinator.Tuple3Parser
BSmtLib.Parser.Tuple4Parser ↦ BSmtLib.Parser.Category.Combinator.Tuple4Parser
BSmtLib.Parser.Tuple5Parser ↦ BSmtLib.Parser.Category.Combinator.Tuple5Parser
BSmtLib.Parser.Tuple6Parser ↦ BSmtLib.Parser.Category.Combinator.Tuple6Parser
BSmtLib.Parser.Tuple7Parser ↦ BSmtLib.Parser.Category.Combinator.Tuple7Parser
BSmtLib.Parser.Tuple8Parser ↦ BSmtLib.Parser.Category.Combinator.Tuple8Parser
BSmtLib.Parser.IdentParser ↦ BSmtLib.Parser.Category.Ident.IdentParser
BSmtLib.Parser.PatternParser ↦ BSmtLib.Parser.Category.Pattern.PatternParser
BSmtLib.Parser.SimplePatternParser ↦ BSmtLib.Parser.Category.Pattern.SimplePatternParser
BSmtLib.Parser.QualifiedIdentParser ↦ BSmtLib.Parser.Category.QualifiedIdent.QualifiedIdentParser
BSmtLib.Parser.SExprParser ↦ BSmtLib.Parser.Category.SExpr.SExprParser
BSmtLib.Parser.SortParser ↦ BSmtLib.Parser.Category.Sort.SortParser
BSmtLib.Parser.SortedVarParser ↦ BSmtLib.Parser.Category.SortedVar.SortedVarParser
BSmtLib.Parser.TermParser ↦ BSmtLib.Parser.Category.Term.TermParser
BSmtLib.Parser.CloseParenParser ↦ BSmtLib.Parser.Category.Token.CloseParenParser
BSmtLib.Parser.KeywordParser ↦ BSmtLib.Parser.Category.Token.KeywordParser
BSmtLib.Parser.NumeralParser ↦ BSmtLib.Parser.Category.Token.NumeralParser
BSmtLib.Parser.OpenParenParser ↦ BSmtLib.Parser.Category.Token.OpenParenParser
BSmtLib.Parser.StringParser ↦ BSmtLib.Parser.Category.Token.StringParser
BSmtLib.Parser.SymbolParser ↦ BSmtLib.Parser.Category.Token.SymbolParser
BSmtLib.Parser.CommandParser ↦ BSmtLib.Parser.Command.CommandParser
BSmtLib.Parser.CommandRule ↦ BSmtLib.Parser.Command.CommandRule
BSmtLib.Parser.CommandPayloadParser ↦ BSmtLib.Parser.Command.CommandPayloadParser
BSmtLib.Parser.CommandOutcome ↦ BSmtLib.Parser.Command.CommandOutcome
BSmtLib.Parser.ScriptParser ↦ BSmtLib.Parser.Script.ScriptParser
-/
#guard_msgs in
#resolves
  BSmtLib.Handler
  BSmtLib.Reader
  BSmtLib.Version
  BSmtLib.Writer
  BSmtLib.Grammar.Multiple
  BSmtLib.Lexicon.Bytes
  BSmtLib.Token
  BSmtLib.Token.Reserved
  BSmtLib.CommandHandler
  BSmtLib.NonstandardCommandError
  BSmtLib.PartialCommandError
  BSmtLib.PartialCommandHandler
  BSmtLib.SyntaxChecker
  BSmtLib.readSmt
  BSmtLib.readSmtFile
  BSmtLib.ReadError
  BSmtLib.ReadErrorCause
  BSmtLib.ReadFailure
  BSmtLib.VersionPosture
  BSmtLib.VersionPostureBuilder
  BSmtLib.WriteError
  BSmtLib.WriteErrorCause
  BSmtLib.WriteStyle
  BSmtLib.WriterConfig
  BSmtLib.Grammar.Bindings
  BSmtLib.Grammar.Constructors
  BSmtLib.Grammar.ConstructorsBuf
  BSmtLib.Grammar.FunctionSignature
  BSmtLib.Grammar.FunctionSignatures
  BSmtLib.Grammar.FunctionSignaturesBuf
  BSmtLib.Grammar.MatchCases
  BSmtLib.Grammar.MatchCasesBuf
  BSmtLib.Grammar.NamedValues
  BSmtLib.Grammar.NamedValuesBuf
  BSmtLib.Grammar.SortArities
  BSmtLib.Grammar.SortAritiesBuf
  BSmtLib.Grammar.SortedVars
  BSmtLib.Grammar.Symbols
  BSmtLib.Grammar.SymbolsBuf
  BSmtLib.Grammar.AttributeValue
  BSmtLib.Grammar.EmptyArgumentsError
  BSmtLib.Grammar.Ident
  BSmtLib.Grammar.IdentBuf
  BSmtLib.Grammar.Index
  BSmtLib.Grammar.IndexBuf
  BSmtLib.Grammar.IndicesBuf
  BSmtLib.Grammar.Pattern
  BSmtLib.Grammar.PatternApplication
  BSmtLib.Grammar.PatternApplicationBuf
  BSmtLib.Grammar.PatternBuf
  BSmtLib.Grammar.QualifiedIdent
  BSmtLib.Grammar.QualifiedIdentBuf
  BSmtLib.Grammar.QuantifierKind
  BSmtLib.Grammar.SExpr
  BSmtLib.Grammar.SimplePattern
  BSmtLib.Grammar.SimplePatternBuf
  BSmtLib.Grammar.SimplePatternsBuf
  BSmtLib.Grammar.SpecialConstant
  BSmtLib.Grammar.SpecialConstantBuf
  BSmtLib.Grammar.Term
  BSmtLib.Lexicon.BytesBuf
  BSmtLib.Lexicon.BinDigits
  BSmtLib.Lexicon.BinDigitsBuf
  BSmtLib.Lexicon.Comment
  BSmtLib.Lexicon.CommentBuf
  BSmtLib.Lexicon.Decimal
  BSmtLib.Lexicon.DecimalBuf
  BSmtLib.Lexicon.DisallowedByteVecError
  BSmtLib.Lexicon.DisallowedBytesError
  BSmtLib.Lexicon.HexDigits
  BSmtLib.Lexicon.HexDigitsBuf
  BSmtLib.Lexicon.Keyword
  BSmtLib.Lexicon.KeywordBuf
  BSmtLib.Lexicon.Numeral
  BSmtLib.Lexicon.NumeralBuf
  BSmtLib.Lexicon.NumericOverflowError
  BSmtLib.Lexicon.StringContent
  BSmtLib.Lexicon.StringContentBuf
  BSmtLib.Lexicon.Symbol
  BSmtLib.Lexicon.SymbolBuf
  BSmtLib.Lexicon.Whitespace
  BSmtLib.Lexicon.WhitespaceBuf
  BSmtLib.Lexer.LexerCursor
  BSmtLib.Lexer.LexerToken
  BSmtLib.Lexer.LexerWindow
  BSmtLib.Lexer.LexerError
  BSmtLib.Lexer.LexerErrorCause
  BSmtLib.Lexer.LexerReadError
  BSmtLib.Lexer.LexerReadErrorCause
  BSmtLib.Lexer.LexicalErrorKind
  BSmtLib.Lexer.LexicalExpected
  BSmtLib.Lexer.FailFast
  BSmtLib.Lexer.LexerRecovery
  BSmtLib.Lexer.Recover
  BSmtLib.Lexer.Recovering
  BSmtLib.Token.CommandNameReserved
  BSmtLib.Token.GeneralReserved
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
  BSmtLib.Parser.Category.Tuple3Parser
  BSmtLib.Parser.Category.Tuple4Parser
  BSmtLib.Parser.Category.Tuple5Parser
  BSmtLib.Parser.Category.Tuple6Parser
  BSmtLib.Parser.Category.Tuple7Parser
  BSmtLib.Parser.Category.Tuple8Parser
  BSmtLib.Parser.Category.IdentParser
  BSmtLib.Parser.Category.PatternParser
  BSmtLib.Parser.Category.SimplePatternParser
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
  BSmtLib.Parser.Tuple3Parser
  BSmtLib.Parser.Tuple4Parser
  BSmtLib.Parser.Tuple5Parser
  BSmtLib.Parser.Tuple6Parser
  BSmtLib.Parser.Tuple7Parser
  BSmtLib.Parser.Tuple8Parser
  BSmtLib.Parser.IdentParser
  BSmtLib.Parser.PatternParser
  BSmtLib.Parser.SimplePatternParser
  BSmtLib.Parser.QualifiedIdentParser
  BSmtLib.Parser.SExprParser
  BSmtLib.Parser.SortParser
  BSmtLib.Parser.SortedVarParser
  BSmtLib.Parser.TermParser
  BSmtLib.Parser.CloseParenParser
  BSmtLib.Parser.KeywordParser
  BSmtLib.Parser.NumeralParser
  BSmtLib.Parser.OpenParenParser
  BSmtLib.Parser.StringParser
  BSmtLib.Parser.SymbolParser
  BSmtLib.Parser.CommandParser
  BSmtLib.Parser.CommandRule
  BSmtLib.Parser.CommandPayloadParser
  BSmtLib.Parser.CommandOutcome
  BSmtLib.Parser.ScriptParser

/-! The Rust counterparts: every public name of the library has one among the public items of
the Rust crate (`BSmtLib.Facts.RustItems`, generated from its documentation), or a `LEAN:` reason
at its declaration; the names with a reason are listed. The other way round, every public item
of the Rust crate, trait implementation and structure with private fields has its Lean
counterpart, or a reason in `BSmtLib.Facts.RustOnly`; the items with a reason are listed. -/

/--
info: 551 public names with a Rust counterpart; 88 with a `LEAN:` reason instead:
  BSmtLib.ControlFlow
  BSmtLib.Grammar.Nodes.Term.newApplication
  BSmtLib.Lexer.AfterEof
  BSmtLib.Lexer.AfterEofError
  BSmtLib.Lexer.AfterError
  BSmtLib.Lexer.Cursor.LexerCursor.Consumed
  BSmtLib.Lexer.Cursor.LexerCursor.HasNext
  BSmtLib.Lexer.Cursor.LexerCursor.category
  BSmtLib.Lexer.Cursor.LexerCursor.content
  BSmtLib.Lexer.Cursor.LexerCursor.span
  BSmtLib.Lexer.Cursor.LexerWindow.Consumed
  BSmtLib.Lexer.Cursor.LexerWindow.category
  BSmtLib.Lexer.Cursor.LexerWindow.content
  BSmtLib.Lexer.Cursor.LexerWindow.span
  BSmtLib.Lexer.Error.LexerReadError.ofLex
  BSmtLib.Lexer.PendingEof
  BSmtLib.Lexer.PendingEof.lexEof
  BSmtLib.Lexer.Recovery.Recovers
  BSmtLib.Lexicon.Bytes.BytesBuf.eqSlice
  BSmtLib.Lexicon.Bytes.BytesBuf.eqView
  BSmtLib.Lexicon.Bytes.eqOwned
  BSmtLib.Lexicon.Bytes.eqSlice
  BSmtLib.Lexicon.Value.BinDigits.eqOwned
  BSmtLib.Lexicon.Value.BinDigits.eqSlice
  BSmtLib.Lexicon.Value.BinDigits.eqString
  BSmtLib.Lexicon.Value.BinDigits.toNat
  BSmtLib.Lexicon.Value.BinDigitsBuf.eqSlice
  BSmtLib.Lexicon.Value.BinDigitsBuf.eqString
  BSmtLib.Lexicon.Value.BinDigitsBuf.eqView
  BSmtLib.Lexicon.Value.BinDigitsBuf.toNat
  BSmtLib.Lexicon.Value.Comment.eqOwned
  BSmtLib.Lexicon.Value.Comment.eqSlice
  BSmtLib.Lexicon.Value.Comment.eqString
  BSmtLib.Lexicon.Value.CommentBuf.eqSlice
  BSmtLib.Lexicon.Value.CommentBuf.eqString
  BSmtLib.Lexicon.Value.CommentBuf.eqView
  BSmtLib.Lexicon.Value.Decimal.eqOwned
  BSmtLib.Lexicon.Value.Decimal.eqSlice
  BSmtLib.Lexicon.Value.Decimal.eqString
  BSmtLib.Lexicon.Value.DecimalBuf.eqSlice
  BSmtLib.Lexicon.Value.DecimalBuf.eqString
  BSmtLib.Lexicon.Value.DecimalBuf.eqView
  BSmtLib.Lexicon.Value.HexDigits.eqOwned
  BSmtLib.Lexicon.Value.HexDigits.eqSlice
  BSmtLib.Lexicon.Value.HexDigits.eqString
  BSmtLib.Lexicon.Value.HexDigits.toNat
  BSmtLib.Lexicon.Value.HexDigitsBuf.eqSlice
  BSmtLib.Lexicon.Value.HexDigitsBuf.eqString
  BSmtLib.Lexicon.Value.HexDigitsBuf.eqView
  BSmtLib.Lexicon.Value.HexDigitsBuf.toNat
  BSmtLib.Lexicon.Value.Keyword.eqOwned
  BSmtLib.Lexicon.Value.Keyword.eqSlice
  BSmtLib.Lexicon.Value.Keyword.eqString
  BSmtLib.Lexicon.Value.KeywordBuf.eqSlice
  BSmtLib.Lexicon.Value.KeywordBuf.eqString
  BSmtLib.Lexicon.Value.KeywordBuf.eqView
  BSmtLib.Lexicon.Value.Numeral.eqOwned
  BSmtLib.Lexicon.Value.Numeral.eqSlice
  BSmtLib.Lexicon.Value.Numeral.eqString
  BSmtLib.Lexicon.Value.Numeral.toNat
  BSmtLib.Lexicon.Value.NumeralBuf.eqSlice
  BSmtLib.Lexicon.Value.NumeralBuf.eqString
  BSmtLib.Lexicon.Value.NumeralBuf.eqView
  BSmtLib.Lexicon.Value.NumeralBuf.fromNat
  BSmtLib.Lexicon.Value.NumeralBuf.toNat
  BSmtLib.Lexicon.Value.StringContent.eqOwned
  BSmtLib.Lexicon.Value.StringContent.eqSlice
  BSmtLib.Lexicon.Value.StringContent.eqString
  BSmtLib.Lexicon.Value.StringContentBuf.eqSlice
  BSmtLib.Lexicon.Value.StringContentBuf.eqString
  BSmtLib.Lexicon.Value.StringContentBuf.eqView
  BSmtLib.Lexicon.Value.Whitespace.eqOwned
  BSmtLib.Lexicon.Value.Whitespace.eqSlice
  BSmtLib.Lexicon.Value.Whitespace.eqString
  BSmtLib.Lexicon.Value.WhitespaceBuf.eqSlice
  BSmtLib.Lexicon.Value.WhitespaceBuf.eqString
  BSmtLib.Lexicon.Value.WhitespaceBuf.eqView
  BSmtLib.Parser.ParseState
  BSmtLib.Parser.ParseState.new
  BSmtLib.Reader.BufRead
  BSmtLib.Reader.BufReader
  BSmtLib.Reader.BufReader.new
  BSmtLib.Reader.ReadError.ofLex
  BSmtLib.Reader.ReadError.ofParse
  BSmtLib.Reader.ReadFailure
  BSmtLib.Token.BatchTag
  BSmtLib.Token.Reserved.CommandNameReserved.all
  BSmtLib.Token.Reserved.GeneralReserved.all
---
info: 789 Rust items, 421 trait implementations with a counterpart class and 104 structures with private fields; 153 without a counterpart, with a reason:
  fields of grammar::nodes::SmtPatternApplication
  fields of grammar::nodes::SmtPatternApplicationBuf
  grammar::multiple::SmtConstructors::iter_mut
  grammar::multiple::SmtConstructorsIter
  grammar::multiple::SmtFunctionSignatures::iter
  grammar::multiple::SmtFunctionSignaturesIter
  grammar::multiple::SmtMatchCases::get_mut
  grammar::multiple::SmtMatchCases::iter
  grammar::multiple::SmtMatchCases::iter_mut
  grammar::multiple::SmtMatchCasesIntoIter
  grammar::multiple::SmtMultiple::as_mut_slice
  grammar::multiple::SmtMultiple::get_mut
  grammar::multiple::SmtMultiple::iter
  grammar::multiple::SmtMultiple::iter_mut
  grammar::multiple::SmtMultipleIntoIter
  grammar::multiple::SmtNamedValues::get_mut
  grammar::multiple::SmtNamedValues::iter
  grammar::multiple::SmtNamedValues::iter_mut
  grammar::multiple::SmtNamedValuesIntoIter
  grammar::multiple::SmtSortArities::iter
  grammar::multiple::SmtSortAritiesIter
  grammar::multiple::SmtSymbols::iter
  grammar::multiple::SmtSymbolsIter
  grammar::nodes::SmtApplication
  grammar::nodes::SmtApplication::args
  grammar::nodes::SmtApplication::args_mut
  grammar::nodes::SmtApplication::function
  grammar::nodes::SmtApplication::function_mut
  grammar::nodes::SmtApplication::into_parts
  grammar::nodes::SmtApplication::new
  grammar::nodes::SmtIndices
  grammar::nodes::SmtIndices::empty
  grammar::nodes::SmtIndices::get
  grammar::nodes::SmtIndices::is_empty
  grammar::nodes::SmtIndices::iter
  grammar::nodes::SmtIndices::len
  grammar::nodes::SmtIndicesBuf::iter
  grammar::nodes::SmtSimplePatterns
  grammar::nodes::SmtSimplePatterns::get
  grammar::nodes::SmtSimplePatterns::is_empty
  grammar::nodes::SmtSimplePatterns::iter
  grammar::nodes::SmtSimplePatterns::len
  grammar::nodes::SmtSimplePatternsBuf::iter
  grammar::nodes::SmtSort
  impl core::default::Default for parser::category::combinator::SmtTuple3Parser
  impl core::default::Default for parser::category::combinator::SmtTuple4Parser
  impl core::default::Default for parser::category::combinator::SmtTuple5Parser
  impl core::default::Default for parser::category::combinator::SmtTuple6Parser
  impl core::default::Default for parser::category::combinator::SmtTuple7Parser
  impl core::default::Default for parser::category::combinator::SmtTuple8Parser
  impl core::default::Default for parser::state::SmtParseState
  impl core::fmt::Debug for grammar::multiple::SmtConstructorsIter
  impl core::fmt::Debug for grammar::multiple::SmtFunctionSignaturesIter
  impl core::fmt::Debug for grammar::multiple::SmtMatchCasesIntoIter
  impl core::fmt::Debug for grammar::multiple::SmtMultipleIntoIter
  impl core::fmt::Debug for grammar::multiple::SmtNamedValuesIntoIter
  impl core::fmt::Debug for grammar::multiple::SmtSortAritiesIter
  impl core::fmt::Debug for grammar::multiple::SmtSymbolsIter
  impl core::fmt::Debug for grammar::nodes::SmtApplication
  impl core::fmt::Debug for grammar::nodes::SmtIndices
  impl core::fmt::Debug for grammar::nodes::SmtSimplePatterns
  impl core::fmt::Debug for grammar::nodes::SmtSort
  impl core::fmt::Debug for lexer::SmtLexer
  impl core::fmt::Debug for lexer::cursor::SmtLexerCursor
  impl core::fmt::Debug for lexer::cursor::SmtLexerToken
  impl core::fmt::Debug for lexer::cursor::SmtLexerWindow
  impl core::fmt::Debug for parser::adapter::SmtParseAdapter
  impl core::fmt::Debug for parser::category::attribute::SmtClosedAttributeParser
  impl core::fmt::Debug for parser::category::attribute::SmtClosedMultipleAttributeParser
  impl core::fmt::Debug for parser::category::combinator::SmtClosedMaximumParser
  impl core::fmt::Debug for parser::category::combinator::SmtClosedMultipleParser
  impl core::fmt::Debug for parser::category::combinator::SmtClosedParser
  impl core::fmt::Debug for parser::category::combinator::SmtOpenedParser
  impl core::fmt::Debug for parser::category::combinator::SmtPairParser
  impl core::fmt::Debug for parser::category::combinator::SmtParenMaximumParser
  impl core::fmt::Debug for parser::category::combinator::SmtParenMultipleParser
  impl core::fmt::Debug for parser::category::combinator::SmtParenParser
  impl core::fmt::Debug for parser::category::combinator::SmtTuple3Parser
  impl core::fmt::Debug for parser::category::combinator::SmtTuple4Parser
  impl core::fmt::Debug for parser::category::combinator::SmtTuple5Parser
  impl core::fmt::Debug for parser::category::combinator::SmtTuple6Parser
  impl core::fmt::Debug for parser::category::combinator::SmtTuple7Parser
  impl core::fmt::Debug for parser::category::combinator::SmtTuple8Parser
  impl core::fmt::Debug for parser::category::ident::SmtIdentParser
  impl core::fmt::Debug for parser::category::pattern::SmtPatternParser
  impl core::fmt::Debug for parser::category::pattern::SmtSimplePatternParser
  impl core::fmt::Debug for parser::category::qualified_ident::SmtQualifiedIdentParser
  impl core::fmt::Debug for parser::category::s_expr::SmtSExprParser
  impl core::fmt::Debug for parser::category::sort::SmtSortParser
  impl core::fmt::Debug for parser::category::sorted_var::SmtSortedVarParser
  impl core::fmt::Debug for parser::category::term::SmtTermParser
  impl core::fmt::Debug for parser::category::token::SmtCloseParenParser
  impl core::fmt::Debug for parser::category::token::SmtKeywordParser
  impl core::fmt::Debug for parser::category::token::SmtNumeralParser
  impl core::fmt::Debug for parser::category::token::SmtOpenParenParser
  impl core::fmt::Debug for parser::category::token::SmtStringParser
  impl core::fmt::Debug for parser::category::token::SmtSymbolParser
  impl core::fmt::Debug for parser::command::SmtCommandParser
  impl core::fmt::Debug for parser::command::SmtCommandPayloadParser
  impl core::fmt::Debug for parser::script::SmtScriptParser
  impl core::fmt::Debug for parser::state::SmtParseState
  impl core::fmt::Debug for reader::SmtReader
  impl core::fmt::Debug for writer::SmtWriter
  impl parser::SmtParse for parser::category::combinator::SmtTuple3Parser
  impl parser::SmtParse for parser::category::combinator::SmtTuple4Parser
  impl parser::SmtParse for parser::category::combinator::SmtTuple5Parser
  impl parser::SmtParse for parser::category::combinator::SmtTuple6Parser
  impl parser::SmtParse for parser::category::combinator::SmtTuple7Parser
  impl parser::SmtParse for parser::category::combinator::SmtTuple8Parser
  impl token::SmtAppendTokens for grammar::nodes::SmtApplication
  impl token::SmtAppendTokens for grammar::nodes::SmtIndices
  impl token::SmtAppendTokens for grammar::nodes::SmtSimplePatterns
  impl token::SmtAppendTokens for grammar::nodes::SmtSort
  lexer::cursor::SmtLexerToken::category
  lexer::cursor::SmtLexerToken::content
  lexer::cursor::SmtLexerToken::span
  lexicon::bytes::SmtBytes::iter
  lexicon::bytes::SmtBytesBuf::from_boxed_slice
  lexicon::bytes::SmtBytesBuf::into_boxed_slice
  lexicon::bytes::SmtBytesBuf::iter
  lexicon::value::SmtBinDigits::iter
  lexicon::value::SmtBinDigits::to_u128
  lexicon::value::SmtBinDigitsBuf::iter
  lexicon::value::SmtBinDigitsBuf::to_u128
  lexicon::value::SmtComment::iter
  lexicon::value::SmtCommentBuf::iter
  lexicon::value::SmtDecimal::iter
  lexicon::value::SmtDecimalBuf::iter
  lexicon::value::SmtHexDigits::iter
  lexicon::value::SmtHexDigits::to_u128
  lexicon::value::SmtHexDigitsBuf::iter
  lexicon::value::SmtHexDigitsBuf::to_u128
  lexicon::value::SmtKeyword::iter
  lexicon::value::SmtKeywordBuf::iter
  lexicon::value::SmtNumeral::iter
  lexicon::value::SmtNumeral::to_u128
  lexicon::value::SmtNumeralBuf::from_u128
  lexicon::value::SmtNumeralBuf::iter
  lexicon::value::SmtNumeralBuf::to_u128
  lexicon::value::SmtStringContent::iter
  lexicon::value::SmtStringContentBuf::iter
  lexicon::value::SmtSymbol::iter
  lexicon::value::SmtSymbolBuf::iter
  lexicon::value::SmtWhitespace::iter
  lexicon::value::SmtWhitespaceBuf::iter
  parser::SmtParse::Result
  parser::state::SmtParseState
  parser::state::SmtParseState::new
  token::SmtConsume::Error
  token::SmtConsume::IS_CONCRETE
  token::SmtConsume::Result
  token::SmtTokensBuf::iter
  writer::SmtWriter::get_mut
-/
#guard_msgs in
#counterparts
