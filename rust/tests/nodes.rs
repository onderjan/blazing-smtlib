//! Public-API tests of the parse-result node types.

use std::convert::Infallible;
use std::fmt::Debug;

use blazing_smtlib::{
    SmtApplication, SmtAttributeValue, SmtAttributes, SmtBindings, SmtDatatypeConstructor,
    SmtFunctionSignature, SmtHandler, SmtIdent, SmtIdentView, SmtIndex, SmtIndexView, SmtIndices,
    SmtKeywordView, SmtPattern, SmtPatternView, SmtQualifiedIdent, SmtQualifiedIdentView,
    SmtQuantifierKind, SmtSExpr, SmtSimplePattern, SmtSimplePatternView, SmtSimplePatterns,
    SmtSort, SmtSpecialConstant, SmtSpecialConstantView, SmtSymbolView, SmtTerm,
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

    fn handle_sort(&mut self, _sort: SmtSort<'_, Self>) -> Result<String, Infallible> {
        Ok(String::new())
    }
    fn handle_term(&mut self, _term: SmtTerm<'_, Self>) -> Result<String, Infallible> {
        Ok(String::new())
    }
    fn start_let(&mut self, _bindings: SmtBindings<'_, Self>) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_let(&mut self, term: String) -> Result<String, Infallible> {
        Ok(term)
    }
    fn handle_s_expr(&mut self, _expr: SmtSExpr<'_, Self>) -> Result<String, Infallible> {
        Ok(String::new())
    }
    fn handle_attribute(
        &mut self,
        _name: SmtKeywordView<'_>,
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
        _name: SmtSymbolView<'_>,
        _sort: String,
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_quantifier(&mut self, term: String) -> Result<String, Infallible> {
        Ok(term)
    }
    fn start_lambda(&mut self, _name: SmtSymbolView<'_>, _sort: String) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_lambda(&mut self, term: String) -> Result<String, Infallible> {
        Ok(term)
    }
    fn start_match(&mut self, _scrutinee: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_match_case(&mut self, _pattern: SmtPatternView<'_>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_match_case(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_match(&mut self) -> Result<Self::Term, Self::Error> {
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
    assert_debug_and_clone::<SmtIndex>();
    assert_debug_and_clone::<SmtIdent>();
    assert_debug_and_clone::<SmtSpecialConstant>();
    assert_debug_and_clone::<SmtSpecialConstantView<'static>>();
    assert_debug_and_clone::<SmtQualifiedIdent<OpaqueHandler>>();
    assert_debug_and_clone::<SmtIndexView<'static>>();
    assert_debug_and_clone::<SmtIndices<'static>>();
    assert_debug_and_clone::<SmtIdentView<'static>>();
    assert_debug_and_clone::<SmtQualifiedIdentView<'static, OpaqueHandler>>();
    // the nodes handing values over cannot be cloned, but must still be debuggable
    assert_debug::<SmtSort<'static, OpaqueHandler>>();
    // the nodes handing values over cannot be cloned, but must still be debuggable
    assert_debug::<SmtApplication<'static, OpaqueHandler>>();
    assert_debug::<SmtTerm<'static, OpaqueHandler>>();
    assert_debug::<SmtBindings<'static, OpaqueHandler>>();
    assert_debug::<SmtAttributeValue<'static, OpaqueHandler>>();
    assert_debug::<SmtSExpr<'static, OpaqueHandler>>();
    assert_debug_and_clone::<SmtFunctionSignature<OpaqueHandler>>();
    assert_debug_and_clone::<SmtDatatypeConstructor<OpaqueHandler>>();
    assert_debug_and_clone::<SmtSimplePattern>();
    assert_debug_and_clone::<SmtPattern>();
    assert_debug_and_clone::<SmtSimplePatternView<'static>>();
    assert_debug_and_clone::<SmtSimplePatterns<'static>>();
    assert_debug_and_clone::<SmtPatternView<'static>>();
}
