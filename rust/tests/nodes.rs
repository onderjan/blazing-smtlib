//! Public-API tests of the parse-result node types.

use std::convert::Infallible;
use std::fmt::Debug;

use blazing_smtlib::{
    SmtApplication, SmtAttributeValue, SmtAttributes, SmtBindings, SmtConstructors,
    SmtFunctionSignature, SmtFunctionSignatures, SmtHandler, SmtIdent, SmtIdentBuf, SmtIndex,
    SmtIndexBuf, SmtIndices, SmtIndicesBuf, SmtKeyword, SmtMatchCases, SmtMatchCasesBuf,
    SmtMultiple, SmtNumeralBuf, SmtPattern, SmtQualifiedIdent, SmtQualifiedIdentBuf,
    SmtQuantifierKind, SmtSExpr, SmtSimplePattern, SmtSimplePatternBuf, SmtSimplePatterns,
    SmtSimplePatternsBuf, SmtSort, SmtSortArities, SmtSortedVars, SmtSpecialConstant,
    SmtSpecialConstantBuf, SmtSymbol, SmtSymbolBuf, SmtSymbols, SmtTerm, token::SmtVersion,
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
    fn start_let(&mut self, _bindings: SmtBindings<'_, Self::Term>) -> Result<(), Infallible> {
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
        _attributes: SmtAttributes<'_, Self>,
    ) -> Result<String, Infallible> {
        Ok(term)
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _vars: SmtSortedVars<'_, Self::Sort>,
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
    fn start_lambda(&mut self, _vars: SmtSortedVars<'_, Self::Sort>) -> Result<(), Infallible> {
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
    assert_debug_and_clone::<SmtIdent<'static>>();
    assert_debug_and_clone::<SmtQualifiedIdent<'static, OpaqueHandler>>();
    // the nodes handing values over cannot be cloned, but must still be debuggable
    assert_debug::<SmtSort<'static, OpaqueHandler>>();
    // the nodes handing values over cannot be cloned, but must still be debuggable
    assert_debug::<SmtApplication<'static, OpaqueHandler>>();
    assert_debug::<SmtTerm<'static, OpaqueHandler>>();
    assert_debug::<SmtBindings<'static, String>>();
    assert_debug::<SmtAttributeValue<'static, OpaqueHandler>>();
    assert_debug::<SmtSExpr<'static, OpaqueHandler>>();
    // the signature views hand their sorts over by reference, so they can be copied
    assert_debug_and_clone::<SmtFunctionSignature<'static, String>>();
    assert_debug_and_clone::<SmtFunctionSignatures<'static, String>>();
    assert_debug_and_clone::<SmtSymbols<'static>>();
    assert_debug_and_clone::<SmtSortArities<'static>>();
    // the constructors hand their selector sorts over, so they cannot be cloned
    assert_debug::<SmtConstructors<'static, String>>();
    assert_debug_and_clone::<SmtSimplePatternBuf>();
    assert_debug_and_clone::<SmtPattern>();
    assert_debug_and_clone::<SmtSimplePattern<'static>>();
    assert_debug_and_clone::<SmtSimplePatterns<'static>>();
    assert_debug_and_clone::<SmtPattern<'static>>();
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
        SmtPattern::Application { constructor, args } => {
            let args: Vec<String> = args.iter().map(render_simple_pattern).collect();
            format!("({} {})", render_symbol(constructor), args.join(" "))
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
        if sort.applied.is_empty() {
            return Ok(ident);
        }
        let applied: Vec<String> = sort.applied.into_iter().collect();
        Ok(format!("({ident} {})", applied.join(" ")))
    }
    fn handle_term(&mut self, term: SmtTerm<'_, Self>) -> Result<String, Infallible> {
        match term {
            SmtTerm::QualifiedIdent(SmtQualifiedIdent { ident, sort: None }) => {
                Ok(render_ident(ident))
            }
            _ => panic!("the render handler takes only unqualified identifier terms"),
        }
    }
    fn start_let(&mut self, _bindings: SmtBindings<'_, Self::Term>) -> Result<(), Infallible> {
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
        _attributes: SmtAttributes<'_, Self>,
    ) -> Result<String, Infallible> {
        panic!("the render handler takes no annotation")
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _vars: SmtSortedVars<'_, Self::Sort>,
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
    fn start_lambda(&mut self, _vars: SmtSortedVars<'_, Self::Sort>) -> Result<(), Infallible> {
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
    fn as_view(index: &SmtIndexBuf) -> SmtIndex<'_> {
        match index {
            SmtIndexBuf::Numeral(numeral) => SmtIndex::Numeral(numeral.as_view()),
            SmtIndexBuf::Symbol(symbol) => SmtIndex::Symbol(symbol.as_view()),
        }
    }
    let expected = ["32", "x", "|x|", "|a b|", "||", "0"];
    // twice, the second time after clearing, which must leave nothing behind
    for round in 0..2 {
        for index in &pushed {
            indices.push(as_view(index));
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
        indices.clear();
        assert!(
            indices.is_empty() && indices.view().is_empty(),
            "round {round}"
        );
        assert_eq!(indices.len(), 0, "round {round}");
    }
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
        SmtSimplePattern::Symbol(x.as_view()),
        SmtSimplePattern::Wildcard,
        SmtSimplePattern::Symbol(quoted_x.as_view()),
        SmtSimplePattern::Symbol(empty.as_view()),
        SmtSimplePattern::Symbol(spaced.as_view()),
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
        patterns.clear();
        assert!(
            patterns.is_empty() && patterns.view().is_empty(),
            "round {round}"
        );
        assert_eq!(patterns.len(), 0, "round {round}");
    }
}

#[test]
fn owned_match_cases_view_back_what_was_pushed() {
    let cons = symbol_buf(b"cons", false);
    let h = symbol_buf(b"h", false);
    let t = symbol_buf(b"t q", true);
    let nil = symbol_buf(b"nil", true);
    let mut args = SmtSimplePatternsBuf::new();
    args.push(SmtSimplePattern::Symbol(h.as_view()));
    args.push(SmtSimplePattern::Symbol(t.as_view()));
    args.push(SmtSimplePattern::Wildcard);
    let mut cases = SmtMatchCasesBuf::<RenderHandler>::new();
    assert!(cases.is_empty() && cases.view().is_empty());
    let expected = [
        ("(cons h |t q| _)", "h"),
        ("|nil|", "x"),
        ("_", "y"),
        ("(cons _)", "z"),
    ];
    for round in 0..2 {
        cases.push(
            SmtPattern::Application {
                constructor: cons.as_view(),
                args: args.view(),
            },
            "h".to_string(),
        );
        cases.push(
            SmtPattern::Simple(SmtSimplePattern::Symbol(nil.as_view())),
            "x".to_string(),
        );
        cases.push(
            SmtPattern::Simple(SmtSimplePattern::Wildcard),
            "y".to_string(),
        );
        let mut wildcard = SmtSimplePatternsBuf::new();
        wildcard.push(SmtSimplePattern::Wildcard);
        cases.push(
            SmtPattern::Application {
                constructor: cons.as_view(),
                args: wildcard.view(),
            },
            "z".to_string(),
        );
        assert_eq!(cases.len(), expected.len(), "round {round}");
        assert!(!cases.is_empty(), "round {round}");
        let view = cases.view();
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
        assert!(cases.is_empty() && cases.view().is_empty(), "round {round}");
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
    indices.push(SmtIndex::Numeral(width.as_view()));
    let mut applied = Vec::new();
    let sort = handler
        .handle_sort(SmtSort {
            ident: SmtIdent {
                name: bit_vec.as_view(),
                indices: indices.view(),
            },
            applied: SmtMultiple::new(&mut applied),
        })
        .unwrap_or_else(|never| match never {});
    assert_eq!(sort, "(_ BitVec 32)");

    let x = symbol_buf(b"x", false);
    let no_indices = SmtIndicesBuf::new();
    let scrutinee = handler
        .handle_term(SmtTerm::QualifiedIdent(SmtQualifiedIdent {
            ident: SmtIdent {
                name: x.as_view(),
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
    args.push(SmtSimplePattern::Symbol(h.as_view()));
    args.push(SmtSimplePattern::Symbol(t.as_view()));
    let mut cases = SmtMatchCasesBuf::<RenderHandler>::new();
    cases.push(
        SmtPattern::Application {
            constructor: cons.as_view(),
            args: args.view(),
        },
        scrutinee.clone(),
    );
    cases.push(
        SmtPattern::Simple(SmtSimplePattern::Wildcard),
        scrutinee.clone(),
    );
    let term = handler
        .end_match(scrutinee, cases.view())
        .unwrap_or_else(|never| match never {});
    assert_eq!(term, "(match x (((cons h t) x) (_ x)))");
}
