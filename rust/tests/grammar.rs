//! Public-API tests of the parse-result node types.

use std::convert::Infallible;
use std::fmt::Debug;

use blazing_smtlib::{
    SmtHandler, SmtVersion,
    grammar::{
        SmtApplication, SmtAttributeValue, SmtBindings, SmtConstructors, SmtEmptyArgumentsError,
        SmtFunctionSignature, SmtFunctionSignatures, SmtIdent, SmtIdentBuf, SmtIndex, SmtIndexBuf,
        SmtIndices, SmtIndicesBuf, SmtMatchCases, SmtMatchCasesBuf, SmtMultiple, SmtNamedValues,
        SmtPattern, SmtPatternApplication, SmtPatternApplicationBuf, SmtPatternBuf,
        SmtQualifiedIdent, SmtQualifiedIdentBuf, SmtQuantifierKind, SmtSExpr, SmtSimplePattern,
        SmtSimplePatternBuf, SmtSimplePatterns, SmtSimplePatternsBuf, SmtSort, SmtSortArities,
        SmtSortedVars, SmtSpecialConstant, SmtSpecialConstantBuf, SmtSymbols, SmtTerm,
    },
    lexicon::{
        SmtBinDigitsBuf, SmtDecimalBuf, SmtHexDigitsBuf, SmtKeyword, SmtNumeralBuf,
        SmtStringContentBuf, SmtSymbol, SmtSymbolBuf,
    },
};

/// Handler that is deliberately neither `Debug` nor `Clone`,
/// while all of its associated types are both.
struct OpaqueHandler;

impl SmtHandler for OpaqueHandler {
    type Error = Infallible;
    type SExpr = String;
    type Attribute = String;
    type Sort = String;
    type Term = String;
    type Scope = ();

    fn set_version(&mut self, _version: SmtVersion) {}

    fn handle_sort(&mut self, _sort: SmtSort<'_, Self>) -> Result<String, Infallible> {
        Ok(String::new())
    }
    fn handle_term(&mut self, _term: SmtTerm<'_, Self>) -> Result<String, Infallible> {
        Ok(String::new())
    }
    fn start_let(&mut self, _bindings: SmtBindings<'_, Self>) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_let(&mut self, _scope: (), body: String) -> Result<String, Infallible> {
        Ok(body)
    }
    fn handle_s_expr(&mut self, _expr: SmtSExpr<'_, Self>) -> Result<String, Infallible> {
        Ok(String::new())
    }
    fn handle_attribute(
        &mut self,
        _name: SmtKeyword<'_>,
        _value: Option<SmtAttributeValue<'_, Self>>,
    ) -> Result<String, Infallible> {
        Ok(String::new())
    }
    fn annotate_term(
        &mut self,
        term: String,
        _attributes: SmtMultiple<'_, Self::Attribute>,
    ) -> Result<String, Infallible> {
        Ok(term)
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _vars: SmtSortedVars<'_, Self>,
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _scope: (),
        body: String,
    ) -> Result<String, Infallible> {
        Ok(body)
    }
    fn start_lambda(&mut self, _vars: SmtSortedVars<'_, Self>) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_lambda(&mut self, _scope: (), body: String) -> Result<String, Infallible> {
        Ok(body)
    }
    fn start_match(&mut self, _scrutinee: &Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_match_case(
        &mut self,
        _scrutinee: &Self::Term,
        _pattern: SmtPattern<'_>,
    ) -> Result<Self::Scope, Self::Error> {
        Ok(())
    }
    fn end_match_case(
        &mut self,
        _scope: Self::Scope,
        _scrutinee: &Self::Term,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error> {
        Ok(body)
    }
    fn end_match(
        &mut self,
        _scrutinee: Self::Term,
        _cases: SmtMatchCases<'_, Self>,
    ) -> Result<Self::Term, Self::Error> {
        Ok(String::new())
    }
}

fn assert_debug_and_clone<T: Debug + Clone>() {}

fn assert_debug<T: Debug>() {}

/// The `H`-generic nodes must be `Debug` and `Clone` whenever the handler's
/// associated types are, regardless of the handler type itself.
///
/// This is a compile-time guard: it stops compiling if the manual impls are
/// replaced with derives, which would wrongly bound `H` instead of the
/// associated types actually stored in the nodes.
#[test]
fn nodes_are_debug_and_clone_with_an_opaque_handler() {
    assert_debug_and_clone::<SmtIndexBuf>();
    assert_debug_and_clone::<SmtIdentBuf>();
    assert_debug_and_clone::<SmtSpecialConstantBuf>();
    assert_debug_and_clone::<SmtSpecialConstant<'static>>();
    assert_debug_and_clone::<SmtQualifiedIdentBuf<OpaqueHandler>>();
    assert_debug_and_clone::<SmtIndex<'static>>();
    assert_debug_and_clone::<SmtIndices<'static>>();
    assert_debug_and_clone::<SmtIndicesBuf>();
    assert_debug_and_clone::<SmtIdent<'static>>();
    assert_debug_and_clone::<SmtQualifiedIdent<'static, OpaqueHandler>>();
    // the nodes handing values over cannot be cloned, but must still be debuggable
    assert_debug::<SmtSort<'static, OpaqueHandler>>();
    // the nodes handing values over cannot be cloned, but must still be debuggable
    assert_debug::<SmtApplication<'static, OpaqueHandler>>();
    assert_debug::<SmtTerm<'static, OpaqueHandler>>();
    assert_debug::<SmtNamedValues<'static, String>>();
    assert_debug::<SmtBindings<'static, OpaqueHandler>>();
    assert_debug::<SmtSortedVars<'static, OpaqueHandler>>();
    assert_debug::<SmtAttributeValue<'static, OpaqueHandler>>();
    assert_debug::<SmtSExpr<'static, OpaqueHandler>>();
    // the signature views hand their sorts over by reference, so they can be copied
    assert_debug_and_clone::<SmtFunctionSignature<'static, OpaqueHandler>>();
    assert_debug_and_clone::<SmtFunctionSignatures<'static, OpaqueHandler>>();
    assert_debug_and_clone::<SmtSymbols<'static>>();
    assert_debug_and_clone::<SmtSortArities<'static>>();
    // the constructors hand their selector sorts over, so they cannot be cloned
    assert_debug::<SmtConstructors<'static, OpaqueHandler>>();
    assert_debug_and_clone::<SmtSimplePatternBuf>();
    assert_debug_and_clone::<SmtPattern>();
    assert_debug_and_clone::<SmtSimplePattern<'static>>();
    assert_debug_and_clone::<SmtSimplePatterns<'static>>();
    assert_debug_and_clone::<SmtPattern<'static>>();
    assert_debug_and_clone::<SmtPatternApplication<'static>>();
    assert_debug_and_clone::<SmtSimplePatternsBuf>();
    assert_debug_and_clone::<SmtPatternBuf>();
    assert_debug_and_clone::<SmtPatternApplicationBuf>();
}

/// The owned lists are `Debug` and `Clone`, and their iterators `Debug`,
/// whenever the values they hold are, regardless of the handler type.
#[test]
fn lists_and_their_iterators_are_debug_with_an_opaque_handler() {
    use blazing_smtlib::grammar::{
        SmtConstructorsBuf, SmtConstructorsIter, SmtFunctionSignaturesBuf,
        SmtFunctionSignaturesIter, SmtMatchCasesIntoIter, SmtMultipleIntoIter, SmtNamedValuesBuf,
        SmtNamedValuesIntoIter, SmtSortAritiesBuf, SmtSortAritiesIter, SmtSymbolsBuf,
        SmtSymbolsIter,
    };

    assert_debug_and_clone::<SmtNamedValuesBuf<String>>();
    assert_debug_and_clone::<SmtMatchCasesBuf<OpaqueHandler>>();
    assert_debug_and_clone::<SmtSymbolsBuf>();
    assert_debug_and_clone::<SmtFunctionSignaturesBuf<OpaqueHandler>>();
    assert_debug_and_clone::<SmtSortAritiesBuf>();
    assert_debug_and_clone::<SmtConstructorsBuf<OpaqueHandler>>();
    assert_debug::<SmtMultipleIntoIter<'static, String>>();
    assert_debug::<SmtNamedValuesIntoIter<'static, String>>();
    assert_debug::<SmtMatchCasesIntoIter<'static, OpaqueHandler>>();
    assert_debug::<SmtSymbolsIter<'static>>();
    assert_debug::<SmtFunctionSignaturesIter<'static, OpaqueHandler>>();
    assert_debug::<SmtSortAritiesIter<'static>>();
    assert_debug::<SmtConstructorsIter<'static, OpaqueHandler>>();
}

/// The parsers, the parse state, the adapter, the lexer over it and the
/// reader are `Debug` for any handler, as they print none of its values.
#[test]
fn the_parsing_machinery_is_debug_with_an_opaque_handler() {
    use blazing_smtlib::{
        SmtReader,
        lexer::SmtLexer,
        parser::{
            SmtClosedAttributeParser, SmtClosedMultipleAttributeParser, SmtParenParser,
            SmtParseAdapter, SmtParseState, SmtPatternParser, SmtQualifiedIdentParser,
            SmtSExprParser, SmtSortParser, SmtSortedVarParser, SmtSymbolParser, SmtTermParser,
            SmtTuple3Parser,
        },
    };

    type H = OpaqueHandler;
    type S = SmtSymbolParser;
    assert_debug::<SmtPatternParser<H>>();
    assert_debug::<SmtQualifiedIdentParser<H>>();
    assert_debug::<SmtSortParser<H>>();
    assert_debug::<SmtSortedVarParser<H>>();
    assert_debug::<SmtSExprParser<H>>();
    assert_debug::<SmtTermParser<H>>();
    assert_debug::<SmtClosedAttributeParser<H>>();
    assert_debug::<SmtClosedMultipleAttributeParser<H>>();
    assert_debug::<SmtParenParser<H, S>>();
    assert_debug::<SmtTuple3Parser<H, S, S, S>>();
    assert_debug::<SmtParseState<H>>();
    assert_debug::<SmtParseAdapter<'static, H, SmtTermParser<H>>>();
    assert_debug::<SmtLexer<SmtParseAdapter<'static, H, SmtTermParser<H>>>>();
    assert_debug::<SmtReader<'static, H, SmtTermParser<H>>>();
}

#[test]
fn an_owned_list_and_its_clone_print_as_its_view_and_an_iterator_what_is_left() {
    use blazing_smtlib::grammar::{
        SmtConstructorsBuf, SmtFunctionSignaturesBuf, SmtNamedValuesBuf, SmtSortAritiesBuf,
        SmtSymbolsBuf,
    };

    let x = symbol_buf(b"x", false);
    let y = symbol_buf(b"a b", true);

    let mut values = SmtNamedValuesBuf::new();
    values.push(x.view(), "1".to_string());
    values.push(y.view(), "2".to_string());
    let printed = format!("{:?}", values.view_mut());
    assert_eq!(format!("{values:?}"), printed);
    assert_eq!(format!("{:?}", values.clone()), printed);
    let mut copy = values.clone();
    let mut iter = copy.view_mut().into_iter();
    iter.next();
    let last = format!("{:?}", (y.view(), "2"));
    assert_eq!(
        format!("{iter:?}"),
        format!("SmtNamedValuesIntoIter([{last}])")
    );

    let mut cases: SmtMatchCasesBuf<OpaqueHandler> = SmtMatchCasesBuf::new();
    cases.push(
        SmtPattern::Simple(SmtSimplePattern::Symbol(x.view())),
        "1".to_string(),
    );
    cases.push(
        SmtPattern::Simple(SmtSimplePattern::Wildcard),
        "2".to_string(),
    );
    let printed = format!("{:?}", cases.view_mut());
    assert_eq!(format!("{cases:?}"), printed);
    assert_eq!(format!("{:?}", cases.clone()), printed);
    let mut copy = cases.clone();
    let mut iter = copy.view_mut().into_iter();
    iter.next();
    let last = format!(
        "{:?}",
        (SmtPattern::Simple(SmtSimplePattern::Wildcard), "2")
    );
    assert_eq!(
        format!("{iter:?}"),
        format!("SmtMatchCasesIntoIter([{last}])")
    );

    let mut symbols = SmtSymbolsBuf::new();
    symbols.push(x.view());
    symbols.push(y.view());
    let printed = format!("{:?}", symbols.view());
    assert_eq!(format!("{symbols:?}"), printed);
    assert_eq!(format!("{:?}", symbols.clone()), printed);
    let mut iter = symbols.view().into_iter();
    iter.next();
    assert_eq!(
        format!("{iter:?}"),
        format!("SmtSymbolsIter([{:?}])", y.view())
    );

    let mut signatures = SmtFunctionSignaturesBuf::<OpaqueHandler>::new();
    signatures.push(x.view(), "Bool".to_string());
    signatures.push_param(y.view(), "Int".to_string());
    signatures.push(y.view(), "Int".to_string());
    let printed = format!("{:?}", signatures.view());
    assert_eq!(format!("{signatures:?}"), printed);
    assert_eq!(format!("{:?}", signatures.clone()), printed);
    let mut iter = signatures.view().into_iter();
    iter.next();
    let last = format!("{:?}", signatures.get(1).expect("two signatures"));
    assert_eq!(
        format!("{iter:?}"),
        format!("SmtFunctionSignaturesIter([{last}])")
    );

    let mut arities = SmtSortAritiesBuf::new();
    arities.push(x.view(), numeral_buf(b"0").view());
    arities.push(y.view(), numeral_buf(b"2").view());
    let printed = format!("{:?}", arities.view());
    assert_eq!(format!("{arities:?}"), printed);
    assert_eq!(format!("{:?}", arities.clone()), printed);
    let mut iter = arities.view().into_iter();
    iter.next();
    let last = format!("{:?}", (y.view(), numeral_buf(b"2").view()));
    assert_eq!(format!("{iter:?}"), format!("SmtSortAritiesIter([{last}])"));

    let mut constructors = SmtConstructorsBuf::<OpaqueHandler>::new();
    constructors.push(x.view());
    constructors.push(y.view());
    constructors.push_selector(x.view(), "Int".to_string());
    let printed = format!("{:?}", constructors.view_mut());
    assert_eq!(format!("{constructors:?}"), printed);
    assert_eq!(format!("{:?}", constructors.clone()), printed);
    let mut copy = constructors.clone();
    let mut iter = copy.view_mut().into_iter();
    iter.next();
    let last = format!("{:?}", (y.view(), [(x.view(), "Int")]));
    assert_eq!(
        format!("{iter:?}"),
        format!("SmtConstructorsIter([{last}])")
    );
}

fn symbol_buf(bytes: &[u8], quoted: bool) -> SmtSymbolBuf {
    let result = if quoted {
        SmtSymbolBuf::new_quoted(bytes.to_vec())
    } else {
        SmtSymbolBuf::new_unquoted(bytes.to_vec())
    };
    result.unwrap_or_else(|_| panic!("test symbol {bytes:?} should be allowed"))
}

fn numeral_buf(digits: &[u8]) -> SmtNumeralBuf {
    SmtNumeralBuf::new(digits.to_vec()).expect("test numeral should be allowed")
}

fn constructor_pattern<'a>(
    constructor: SmtSymbol<'a>,
    args: SmtSimplePatterns<'a>,
) -> SmtPattern<'a> {
    let application = SmtPatternApplication::new(constructor, args)
        .expect("test constructor pattern has arguments");
    SmtPattern::Application(application)
}

/// Writes a symbol as SMT-LIB text, with pipes if it is quoted.
fn render_symbol(symbol: SmtSymbol<'_>) -> String {
    let text = String::from_utf8_lossy(symbol.as_slice());
    if symbol.is_quoted() {
        format!("|{text}|")
    } else {
        text.into_owned()
    }
}

fn render_index(index: SmtIndex<'_>) -> String {
    match index {
        SmtIndex::Numeral(numeral) => String::from_utf8_lossy(numeral.as_slice()).into_owned(),
        SmtIndex::Symbol(symbol) => render_symbol(symbol),
    }
}

fn render_ident(ident: SmtIdent<'_>) -> String {
    if ident.indices.is_empty() {
        return render_symbol(ident.name);
    }
    let indices: Vec<String> = ident.indices.iter().map(render_index).collect();
    format!("(_ {} {})", render_symbol(ident.name), indices.join(" "))
}

fn render_simple_pattern(pattern: SmtSimplePattern<'_>) -> String {
    match pattern {
        SmtSimplePattern::Symbol(symbol) => render_symbol(symbol),
        SmtSimplePattern::Wildcard => "_".to_string(),
    }
}

fn render_pattern(pattern: SmtPattern<'_>) -> String {
    match pattern {
        SmtPattern::Simple(simple) => render_simple_pattern(simple),
        SmtPattern::Application(application) => {
            let args: Vec<String> = application
                .args()
                .iter()
                .map(render_simple_pattern)
                .collect();
            format!(
                "({} {})",
                render_symbol(application.constructor()),
                args.join(" ")
            )
        }
    }
}

/// Handler that writes the sorts, identifier terms and match terms it is
/// handed back as SMT-LIB text; it takes nothing else.
struct RenderHandler;

impl SmtHandler for RenderHandler {
    type Error = Infallible;
    type SExpr = ();
    type Attribute = ();
    type Sort = String;
    type Term = String;
    type Scope = ();

    fn set_version(&mut self, _version: SmtVersion) {}

    fn handle_sort(&mut self, sort: SmtSort<'_, Self>) -> Result<String, Infallible> {
        let ident = render_ident(sort.ident);
        if sort.args.is_empty() {
            return Ok(ident);
        }
        let args: Vec<String> = sort.args.into_iter().collect();
        Ok(format!("({ident} {})", args.join(" ")))
    }
    fn handle_term(&mut self, term: SmtTerm<'_, Self>) -> Result<String, Infallible> {
        match term {
            SmtTerm::QualifiedIdent(SmtQualifiedIdent { ident, sort: None }) => {
                Ok(render_ident(ident))
            }
            _ => panic!("the render handler takes only unqualified identifier terms"),
        }
    }
    fn start_let(&mut self, _bindings: SmtNamedValues<'_, Self::Term>) -> Result<(), Infallible> {
        panic!("the render handler takes no let")
    }
    fn end_let(&mut self, _scope: (), _body: String) -> Result<String, Infallible> {
        panic!("the render handler takes no let")
    }
    fn handle_s_expr(&mut self, _expr: SmtSExpr<'_, Self>) -> Result<(), Infallible> {
        panic!("the render handler takes no s-expression")
    }
    fn handle_attribute(
        &mut self,
        _name: SmtKeyword<'_>,
        _value: Option<SmtAttributeValue<'_, Self>>,
    ) -> Result<(), Infallible> {
        panic!("the render handler takes no attribute")
    }
    fn annotate_term(
        &mut self,
        _term: String,
        _attributes: SmtMultiple<'_, Self::Attribute>,
    ) -> Result<String, Infallible> {
        panic!("the render handler takes no annotation")
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _vars: SmtNamedValues<'_, Self::Sort>,
    ) -> Result<(), Infallible> {
        panic!("the render handler takes no quantifier")
    }
    fn end_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _scope: (),
        _body: String,
    ) -> Result<String, Infallible> {
        panic!("the render handler takes no quantifier")
    }
    fn start_lambda(&mut self, _vars: SmtNamedValues<'_, Self::Sort>) -> Result<(), Infallible> {
        panic!("the render handler takes no lambda")
    }
    fn end_lambda(&mut self, _scope: (), _body: String) -> Result<String, Infallible> {
        panic!("the render handler takes no lambda")
    }
    fn start_match(&mut self, _scrutinee: &Self::Term) -> Result<(), Self::Error> {
        panic!("the render handler is handed only finished match terms")
    }
    fn start_match_case(
        &mut self,
        _scrutinee: &Self::Term,
        _pattern: SmtPattern<'_>,
    ) -> Result<Self::Scope, Self::Error> {
        panic!("the render handler is handed only finished match terms")
    }
    fn end_match_case(
        &mut self,
        _scope: Self::Scope,
        _scrutinee: &Self::Term,
        _body: Self::Term,
    ) -> Result<Self::Term, Self::Error> {
        panic!("the render handler is handed only finished match terms")
    }
    fn end_match(
        &mut self,
        scrutinee: Self::Term,
        cases: SmtMatchCases<'_, Self>,
    ) -> Result<Self::Term, Self::Error> {
        let cases: Vec<String> = cases
            .into_iter()
            .map(|(pattern, body)| format!("({} {body})", render_pattern(pattern)))
            .collect();
        Ok(format!("(match {scrutinee} ({}))", cases.join(" ")))
    }
}

#[test]
fn owned_indices_view_back_what_was_pushed() {
    let mut indices = SmtIndicesBuf::new();
    assert!(indices.is_empty() && indices.view().is_empty());
    let pushed = [
        SmtIndexBuf::Numeral(numeral_buf(b"32")),
        SmtIndexBuf::Symbol(symbol_buf(b"x", false)),
        SmtIndexBuf::Symbol(symbol_buf(b"x", true)),
        SmtIndexBuf::Symbol(symbol_buf(b"a b", true)),
        SmtIndexBuf::Symbol(symbol_buf(b"", true)),
        SmtIndexBuf::Numeral(numeral_buf(b"0")),
    ];
    let expected = ["32", "x", "|x|", "|a b|", "||", "0"];
    // twice, the second time after clearing, which must leave nothing behind
    for round in 0..2 {
        for index in &pushed {
            indices.push(index.view());
        }
        assert_eq!(indices.len(), pushed.len(), "round {round}");
        assert!(!indices.is_empty(), "round {round}");
        let view = indices.view();
        assert_eq!(view.len(), pushed.len(), "round {round}");
        let rendered: Vec<String> = view.iter().map(render_index).collect();
        assert_eq!(rendered, expected, "round {round}");
        for (i, rendered) in expected.iter().enumerate() {
            let index = view.get(i).expect("a pushed index");
            assert_eq!(render_index(index), *rendered, "round {round}");
        }
        assert!(view.get(pushed.len()).is_none(), "round {round}");
        // the owned indices read the same as their view
        let rendered: Vec<String> = indices.iter().map(render_index).collect();
        assert_eq!(rendered, expected, "round {round}");
        assert_eq!(indices.iter().len(), pushed.len(), "round {round}");
        for (i, rendered) in expected.iter().enumerate() {
            let index = indices.get(i).expect("a pushed index");
            assert_eq!(render_index(index), *rendered, "round {round}");
        }
        assert!(indices.get(pushed.len()).is_none(), "round {round}");
        indices.clear();
        assert!(
            indices.is_empty() && indices.view().is_empty(),
            "round {round}"
        );
        assert_eq!(indices.len(), 0, "round {round}");
    }
}

/// Each owned node views back what it holds, in every variant, and an
/// identifier viewed and made owned again keeps its name and indices.
#[test]
fn owned_nodes_view_back_what_they_hold() {
    let numeral = SmtIndexBuf::Numeral(numeral_buf(b"32"));
    assert_eq!(render_index(numeral.view()), "32");
    let symbol = SmtIndexBuf::Symbol(symbol_buf(b"a b", true));
    assert_eq!(render_index(symbol.view()), "|a b|");

    let simple = SmtIdentBuf::new_simple(symbol_buf(b"x", false));
    assert!(simple.indices.is_empty());
    assert_eq!(render_ident(simple.view()), "x");
    let mut indexed = SmtIdentBuf::new_simple(symbol_buf(b"extract", false));
    indexed
        .indices
        .push(SmtIndex::Numeral(numeral_buf(b"7").view()));
    indexed
        .indices
        .push(SmtIndex::Symbol(symbol_buf(b"y", true).view()));
    assert_eq!(render_ident(indexed.view()), "(_ extract 7 |y|)");
    let again = indexed.view().into_owned();
    assert_eq!(render_ident(again.view()), "(_ extract 7 |y|)");

    let constants = [
        SmtSpecialConstantBuf::Numeral(numeral_buf(b"10")),
        SmtSpecialConstantBuf::Decimal(SmtDecimalBuf::new(b"1.5".to_vec()).expect("a decimal")),
        SmtSpecialConstantBuf::Hexadecimal(
            SmtHexDigitsBuf::new(b"1F".to_vec()).expect("hexadecimal digits"),
        ),
        SmtSpecialConstantBuf::Binary(SmtBinDigitsBuf::new(b"01".to_vec()).expect("binary digits")),
        SmtSpecialConstantBuf::String(
            SmtStringContentBuf::new(b"a b".to_vec()).expect("string content"),
        ),
    ];
    for constant in &constants {
        assert_eq!(&constant.view().into_owned(), constant);
    }

    let pattern = SmtSimplePatternBuf::Symbol(symbol_buf(b"h", false));
    assert_eq!(render_simple_pattern(pattern.view()), "h");
    assert_eq!(
        render_simple_pattern(SmtSimplePatternBuf::Wildcard.view()),
        "_"
    );
}

/// The empty indices hold nothing and stand for the indices of a simple
/// identifier built outside the library.
#[test]
fn empty_indices_hold_nothing() {
    let empty = SmtIndices::empty();
    assert!(empty.is_empty());
    assert_eq!(empty.len(), 0);
    assert!(empty.get(0).is_none());
    assert_eq!(empty.iter().count(), 0);
    let x = symbol_buf(b"x", false);
    let ident = SmtIdent {
        name: x.view(),
        indices: SmtIndices::empty(),
    };
    assert_eq!(render_ident(ident), "x");
}

/// Owned indices are debugged as their view, the list of indices, and a
/// clone keeps its indices when the original is cleared.
#[test]
fn owned_indices_debug_as_their_view_and_clone_apart() {
    let mut indices = SmtIndicesBuf::new();
    indices.push(SmtIndex::Numeral(numeral_buf(b"32").view()));
    indices.push(SmtIndex::Symbol(symbol_buf(b"x", false).view()));
    assert_eq!(format!("{indices:?}"), format!("{:?}", indices.view()));
    let copy = indices.clone();
    indices.clear();
    assert!(indices.is_empty());
    let rendered: Vec<String> = copy.iter().map(render_index).collect();
    assert_eq!(rendered, ["32", "x"]);
}

#[test]
fn owned_simple_patterns_view_back_what_was_pushed() {
    let mut patterns = SmtSimplePatternsBuf::new();
    assert!(patterns.is_empty() && patterns.view().is_empty());
    let x = symbol_buf(b"x", false);
    let quoted_x = symbol_buf(b"x", true);
    let spaced = symbol_buf(b"a b", true);
    let empty = symbol_buf(b"", true);
    let pushed = [
        SmtSimplePattern::Symbol(x.view()),
        SmtSimplePattern::Wildcard,
        SmtSimplePattern::Symbol(quoted_x.view()),
        SmtSimplePattern::Symbol(empty.view()),
        SmtSimplePattern::Symbol(spaced.view()),
        SmtSimplePattern::Wildcard,
    ];
    let expected = ["x", "_", "|x|", "||", "|a b|", "_"];
    for round in 0..2 {
        for pattern in pushed {
            patterns.push(pattern);
        }
        assert_eq!(patterns.len(), pushed.len(), "round {round}");
        assert!(!patterns.is_empty(), "round {round}");
        let view = patterns.view();
        assert_eq!(view.len(), pushed.len(), "round {round}");
        let rendered: Vec<String> = view.iter().map(render_simple_pattern).collect();
        assert_eq!(rendered, expected, "round {round}");
        for (i, rendered) in expected.iter().enumerate() {
            let pattern = view.get(i).expect("a pushed pattern");
            assert_eq!(render_simple_pattern(pattern), *rendered, "round {round}");
        }
        assert!(view.get(pushed.len()).is_none(), "round {round}");
        // the owned patterns read the same as their view
        let rendered: Vec<String> = patterns.iter().map(render_simple_pattern).collect();
        assert_eq!(rendered, expected, "round {round}");
        assert_eq!(patterns.iter().len(), pushed.len(), "round {round}");
        for (i, rendered) in expected.iter().enumerate() {
            let pattern = patterns.get(i).expect("a pushed pattern");
            assert_eq!(render_simple_pattern(pattern), *rendered, "round {round}");
        }
        assert!(patterns.get(pushed.len()).is_none(), "round {round}");
        patterns.clear();
        assert!(
            patterns.is_empty() && patterns.view().is_empty(),
            "round {round}"
        );
        assert_eq!(patterns.len(), 0, "round {round}");
    }
}

/// Owned constructor pattern arguments are debugged as their view, the list
/// of patterns, and a clone keeps its patterns when the original is cleared.
#[test]
fn owned_simple_patterns_debug_as_their_view_and_clone_apart() {
    let x = symbol_buf(b"x", false);
    let mut patterns = SmtSimplePatternsBuf::new();
    patterns.push(SmtSimplePattern::Symbol(x.view()));
    patterns.push(SmtSimplePattern::Wildcard);
    assert_eq!(format!("{patterns:?}"), format!("{:?}", patterns.view()));
    let copy = patterns.clone();
    patterns.clear();
    assert!(patterns.is_empty());
    let rendered: Vec<String> = copy.iter().map(render_simple_pattern).collect();
    assert_eq!(rendered, ["x", "_"]);
}

/// An application is built only with arguments, and its function and
/// arguments are read, changed and taken apart as they were given.
#[test]
fn an_application_is_built_only_with_arguments() {
    let f = symbol_buf(b"f", false);
    let function = || SmtQualifiedIdent::<OpaqueHandler> {
        ident: SmtIdent {
            name: f.view(),
            indices: SmtIndices::empty(),
        },
        sort: None,
    };
    let mut no_args: Vec<String> = Vec::new();
    let empty = SmtApplication::new(function(), SmtMultiple::new(&mut no_args));
    assert_eq!(empty.err(), Some(SmtEmptyArgumentsError));

    let mut args = vec!["x".to_string(), "y".to_string()];
    let mut application = SmtApplication::new(function(), SmtMultiple::new(&mut args))
        .expect("an application with arguments should be built");
    assert_eq!(render_ident(application.function().ident), "f");
    assert_eq!(application.function().sort, None);
    assert_eq!(application.args().as_slice(), ["x", "y"]);
    application.function_mut().sort = Some("Int".to_string());
    application.args_mut()[1].push('!');
    assert_eq!(application.function().sort.as_deref(), Some("Int"));
    assert_eq!(application.args().as_slice(), ["x", "y!"]);
    let (function, args) = application.into_parts();
    assert_eq!(render_ident(function.ident), "f");
    assert_eq!(function.sort.as_deref(), Some("Int"));
    assert_eq!(args.into_iter().collect::<Vec<_>>(), ["x", "y!"]);
}

/// A constructor pattern, borrowed or owned, is built only with arguments,
/// and views back and takes apart what it was given.
#[test]
fn a_constructor_pattern_is_built_only_with_arguments() {
    let cons = symbol_buf(b"cons", false);
    let no_args = SmtSimplePatternsBuf::new();
    let empty = SmtPatternApplication::new(cons.view(), no_args.view());
    assert_eq!(empty.err(), Some(SmtEmptyArgumentsError));
    let empty = SmtPatternApplicationBuf::new(cons.clone(), no_args.clone());
    assert_eq!(empty.err(), Some(SmtEmptyArgumentsError));

    let h = symbol_buf(b"h", true);
    let mut args = SmtSimplePatternsBuf::new();
    args.push(SmtSimplePattern::Symbol(h.view()));
    args.push(SmtSimplePattern::Wildcard);
    let view = SmtPatternApplication::new(cons.view(), args.view())
        .expect("a constructor pattern with arguments should be built");
    assert_eq!(render_symbol(view.constructor()), "cons");
    let rendered: Vec<String> = view.args().iter().map(render_simple_pattern).collect();
    assert_eq!(rendered, ["|h|", "_"]);
    let again = SmtPattern::Application(view).into_owned();
    assert_eq!(render_pattern(again.view()), "(cons |h| _)");

    let owned = SmtPatternApplicationBuf::new(cons.clone(), args.clone())
        .expect("an owned constructor pattern with arguments should be built");
    assert_eq!(render_symbol(owned.constructor().view()), "cons");
    let rendered: Vec<String> = owned.args().iter().map(render_simple_pattern).collect();
    assert_eq!(rendered, ["|h|", "_"]);
    assert_eq!(
        render_pattern(SmtPattern::Application(owned.view())),
        "(cons |h| _)"
    );
    let pattern = SmtPatternBuf::Application(owned);
    assert_eq!(render_pattern(pattern.view()), "(cons |h| _)");
    let SmtPatternBuf::Application(owned) = pattern else {
        panic!("an owned constructor pattern should stay one");
    };
    let (constructor, args) = owned.into_parts();
    assert_eq!(render_symbol(constructor.view()), "cons");
    let rendered: Vec<String> = args.iter().map(render_simple_pattern).collect();
    assert_eq!(rendered, ["|h|", "_"]);

    let simple = SmtPatternBuf::Simple(SmtSimplePatternBuf::Wildcard);
    assert_eq!(render_pattern(simple.view()), "_");
}

#[test]
fn owned_match_cases_view_back_what_was_pushed() {
    let cons = symbol_buf(b"cons", false);
    let h = symbol_buf(b"h", false);
    let t = symbol_buf(b"t q", true);
    let nil = symbol_buf(b"nil", true);
    let mut args = SmtSimplePatternsBuf::new();
    args.push(SmtSimplePattern::Symbol(h.view()));
    args.push(SmtSimplePattern::Symbol(t.view()));
    args.push(SmtSimplePattern::Wildcard);
    let mut cases = SmtMatchCasesBuf::<RenderHandler>::new();
    assert!(cases.is_empty() && cases.view_mut().is_empty());
    let expected = [
        ("(cons h |t q| _)", "h"),
        ("|nil|", "x"),
        ("_", "y"),
        ("(cons _)", "z"),
    ];
    for round in 0..2 {
        cases.push(
            constructor_pattern(cons.view(), args.view()),
            "h".to_string(),
        );
        cases.push(
            SmtPattern::Simple(SmtSimplePattern::Symbol(nil.view())),
            "x".to_string(),
        );
        cases.push(
            SmtPattern::Simple(SmtSimplePattern::Wildcard),
            "y".to_string(),
        );
        let mut wildcard = SmtSimplePatternsBuf::new();
        wildcard.push(SmtSimplePattern::Wildcard);
        cases.push(
            constructor_pattern(cons.view(), wildcard.view()),
            "z".to_string(),
        );
        assert_eq!(cases.len(), expected.len(), "round {round}");
        assert!(!cases.is_empty(), "round {round}");
        let view = cases.view_mut();
        assert_eq!(view.len(), expected.len(), "round {round}");
        for (i, (pattern, body)) in expected.iter().enumerate() {
            let (viewed, viewed_body) = view.get(i).expect("a pushed case");
            assert_eq!(render_pattern(viewed), *pattern, "round {round}");
            assert_eq!(viewed_body, body, "round {round}");
        }
        assert!(view.get(expected.len()).is_none(), "round {round}");
        let rendered: Vec<(String, String)> = view
            .iter()
            .map(|(pattern, body)| (render_pattern(pattern), body.clone()))
            .collect();
        let expected_owned: Vec<(String, String)> = expected
            .iter()
            .map(|(pattern, body)| (pattern.to_string(), body.to_string()))
            .collect();
        assert_eq!(rendered, expected_owned, "round {round}");
        cases.clear();
        assert!(
            cases.is_empty() && cases.view_mut().is_empty(),
            "round {round}"
        );
        assert_eq!(cases.len(), 0, "round {round}");
    }
}

/// The owned builders let code outside the library hand a handler an indexed
/// sort and a match term of its own making, as the parser would.
#[test]
fn a_handler_takes_an_indexed_sort_and_a_match_built_outside_the_library() {
    let mut handler = RenderHandler;

    let bit_vec = symbol_buf(b"BitVec", false);
    let width = numeral_buf(b"32");
    let mut indices = SmtIndicesBuf::new();
    indices.push(SmtIndex::Numeral(width.view()));
    let mut args = Vec::new();
    let sort = handler
        .handle_sort(SmtSort {
            ident: SmtIdent {
                name: bit_vec.view(),
                indices: indices.view(),
            },
            args: SmtMultiple::new(&mut args),
        })
        .unwrap_or_else(|never| match never {});
    assert_eq!(sort, "(_ BitVec 32)");

    let x = symbol_buf(b"x", false);
    let no_indices = SmtIndicesBuf::new();
    let scrutinee = handler
        .handle_term(SmtTerm::QualifiedIdent(SmtQualifiedIdent {
            ident: SmtIdent {
                name: x.view(),
                indices: no_indices.view(),
            },
            sort: None,
        }))
        .unwrap_or_else(|never| match never {});
    assert_eq!(scrutinee, "x");

    let cons = symbol_buf(b"cons", false);
    let h = symbol_buf(b"h", false);
    let t = symbol_buf(b"t", false);
    let mut args = SmtSimplePatternsBuf::new();
    args.push(SmtSimplePattern::Symbol(h.view()));
    args.push(SmtSimplePattern::Symbol(t.view()));
    let mut cases = SmtMatchCasesBuf::<RenderHandler>::new();
    cases.push(
        constructor_pattern(cons.view(), args.view()),
        scrutinee.clone(),
    );
    cases.push(
        SmtPattern::Simple(SmtSimplePattern::Wildcard),
        scrutinee.clone(),
    );
    let term = handler
        .end_match(scrutinee, cases.view_mut())
        .unwrap_or_else(|never| match never {});
    assert_eq!(term, "(match x (((cons h t) x) (_ x)))");
}
