//! Public-API tests of the parse-result node types.

use std::convert::Infallible;
use std::fmt::Debug;

use blazing_smtlib::{
    SmtApplication, SmtAttributeValue, SmtAttributes, SmtBindings, SmtDatatypeConstructor,
    SmtFunctionSignature, SmtHandler, SmtIdent, SmtIdentBuf, SmtIndex, SmtIndexBuf, SmtIndices,
    SmtKeyword, SmtMatchCases, SmtPattern, SmtQualifiedIdent, SmtQualifiedIdentBuf,
    SmtQuantifierKind, SmtSExpr, SmtSimplePattern, SmtSimplePatternBuf, SmtSimplePatterns, SmtSort,
    SmtSortedVars, SmtSpecialConstant, SmtSpecialConstantBuf, SmtTerm,
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
        _attributes: SmtAttributes<'_, Self>,
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
    assert_debug_and_clone::<SmtIdent<'static>>();
    assert_debug_and_clone::<SmtQualifiedIdent<'static, OpaqueHandler>>();
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
    assert_debug_and_clone::<SmtSimplePatternBuf>();
    assert_debug_and_clone::<SmtPattern>();
    assert_debug_and_clone::<SmtSimplePattern<'static>>();
    assert_debug_and_clone::<SmtSimplePatterns<'static>>();
    assert_debug_and_clone::<SmtPattern<'static>>();
}
