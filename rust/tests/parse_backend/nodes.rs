//! The handler interface that the parser tests write their handlers against.
//!
//! It is the Rust library's handler interface (`SmtHandler` and
//! `SmtCommandHandler`) with every argument owned: names and constants as the
//! library's owned types, lists as vectors. The library's views cannot be
//! built outside the library, so a handler written against them could not be
//! called with what the Lean driver reports. A handler written against this
//! interface is called by the Rust parser through an adapter (`super::rust`)
//! and by the Lean parser through the driver (`super::lean`).
//!
//! Where the Rust interface lends a value (the scrutinee of a `match`, the
//! sorts of a function signature), this interface lends it too.

use blazing_smtlib::{
    SmtIdentBuf, SmtKeywordBuf, SmtNumeralBuf, SmtPatternBuf, SmtQuantifierKind,
    SmtSpecialConstantBuf, SmtStringContentBuf, SmtSymbolBuf,
    token::{SmtReserved, SmtVersion},
};

/// A qualified identifier, with the sort it is qualified with by `as`.
#[derive(Debug, Clone)]
pub struct QualifiedIdent<S> {
    pub ident: SmtIdentBuf,
    pub sort: Option<S>,
}

/// A sort: its identifier and its argument sorts, none if it is not applied.
#[derive(Debug)]
pub struct Sort<S> {
    pub ident: SmtIdentBuf,
    pub applied: Vec<S>,
}

/// An application of a qualified identifier to its arguments.
#[derive(Debug)]
pub struct Application<S, T> {
    pub function: QualifiedIdent<S>,
    pub args: Vec<T>,
}

/// A term that binds nothing.
#[derive(Debug)]
pub enum Term<S, T> {
    SpecialConstant(SmtSpecialConstantBuf),
    QualifiedIdent(QualifiedIdent<S>),
    Application(Application<S, T>),
}

/// An s-expression, its items already handled.
#[derive(Debug)]
pub enum SExpr<X> {
    SpecialConstant(SmtSpecialConstantBuf),
    Symbol(SmtSymbolBuf),
    Reserved(SmtReserved),
    Keyword(SmtKeywordBuf),
    SExprs(Vec<X>),
}

/// The value of an attribute, the s-expressions of a list already handled.
#[derive(Debug)]
pub enum AttributeValue<X> {
    SpecialConstant(SmtSpecialConstantBuf),
    Symbol(SmtSymbolBuf),
    SExprs(Vec<X>),
}

/// The bindings of a `let`, in order.
pub type Bindings<T> = Vec<(SmtSymbolBuf, T)>;

/// Sorted variables, in order: of a binder, or the selectors of a constructor.
pub type SortedVars<S> = Vec<(SmtSymbolBuf, S)>;

/// The cases of a `match`, each its pattern and its handled body.
pub type MatchCases<T> = Vec<(SmtPatternBuf, T)>;

/// The constructors of a datatype, each with its selectors.
pub type Constructors<S> = Vec<(SmtSymbolBuf, SortedVars<S>)>;

/// The sorts that `declare-datatypes` declares, with their arities.
pub type SortArities = Vec<(SmtSymbolBuf, SmtNumeralBuf)>;

/// Symbols, such as the parameters of a sort definition.
pub type Symbols = Vec<SmtSymbolBuf>;

/// The signature of a defined function, its sorts lent.
#[derive(Debug)]
pub struct Signature<'a, S> {
    pub name: SmtSymbolBuf,
    pub params: Vec<(SmtSymbolBuf, &'a S)>,
    pub result_sort: &'a S,
}

impl<'a, S> Signature<'a, S> {
    pub fn name(&self) -> &SmtSymbolBuf {
        &self.name
    }

    pub fn params(&self) -> impl ExactSizeIterator<Item = (&SmtSymbolBuf, &'a S)> {
        self.params.iter().map(|(name, sort)| (name, *sort))
    }

    pub fn result_sort(&self) -> &'a S {
        self.result_sort
    }
}

/// The signatures of `define-funs-rec`, in order.
pub type Signatures<'a, S> = Vec<Signature<'a, S>>;

/// The payload the handler accepts a nonstandard command with, which selects
/// the parser of the payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NonstandardPayload {
    /// One term, then the closing parenthesis; the term is handed to
    /// `CommandHandler::nonstandard_term`.
    Term,
    /// The closing parenthesis, after which the parser switches the cursor
    /// to the version (`SmtCursor::set_version`).
    SwitchVersion(SmtVersion),
    /// The closing parenthesis, after which the parser has the cursor
    /// discard the rest of the input (`SmtCursor::discard_rest`).
    DiscardRest,
}

/// The handler of the categories that terms are built from (`SmtHandler`).
pub trait Handler {
    type Error;
    type SExpr;
    type Attribute;
    type Sort;
    type Term;
    type Scope;

    fn set_version(&mut self, version: SmtVersion);
    fn handle_sort(&mut self, sort: Sort<Self::Sort>) -> Result<Self::Sort, Self::Error>;
    fn handle_term(
        &mut self,
        term: Term<Self::Sort, Self::Term>,
    ) -> Result<Self::Term, Self::Error>;
    fn handle_s_expr(&mut self, expr: SExpr<Self::SExpr>) -> Result<Self::SExpr, Self::Error>;
    fn handle_attribute(
        &mut self,
        name: SmtKeywordBuf,
        value: Option<AttributeValue<Self::SExpr>>,
    ) -> Result<Self::Attribute, Self::Error>;
    fn annotate_term(
        &mut self,
        term: Self::Term,
        attributes: Vec<Self::Attribute>,
    ) -> Result<Self::Term, Self::Error>;
    fn start_let(&mut self, bindings: Bindings<Self::Term>) -> Result<Self::Scope, Self::Error>;
    fn end_let(&mut self, scope: Self::Scope, body: Self::Term) -> Result<Self::Term, Self::Error>;
    fn start_quantifier(
        &mut self,
        kind: SmtQuantifierKind,
        vars: SortedVars<Self::Sort>,
    ) -> Result<Self::Scope, Self::Error>;
    fn end_quantifier(
        &mut self,
        kind: SmtQuantifierKind,
        scope: Self::Scope,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
    fn start_lambda(&mut self, vars: SortedVars<Self::Sort>) -> Result<Self::Scope, Self::Error>;
    fn end_lambda(
        &mut self,
        scope: Self::Scope,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
    fn start_match(&mut self, scrutinee: &Self::Term) -> Result<(), Self::Error>;
    fn start_match_case(
        &mut self,
        scrutinee: &Self::Term,
        pattern: SmtPatternBuf,
    ) -> Result<Self::Scope, Self::Error>;
    fn end_match_case(
        &mut self,
        scope: Self::Scope,
        scrutinee: &Self::Term,
        term: Self::Term,
    ) -> Result<Self::Term, Self::Error>;
    fn end_match(
        &mut self,
        scrutinee: Self::Term,
        cases: MatchCases<Self::Term>,
    ) -> Result<Self::Term, Self::Error>;
}

/// The handler of commands and scripts (`SmtCommandHandler`).
///
/// A nonstandard command is accepted with one of the payloads of
/// `NonstandardPayload`; the Rust library hands the payload to a parser that
/// the handler chooses.
pub trait CommandHandler: Handler {
    fn nonstandard_command(
        &mut self,
        name: SmtSymbolBuf,
    ) -> Result<NonstandardPayload, Self::Error>;
    fn nonstandard_term(&mut self, term: Self::Term) -> Result<(), Self::Error>;
    fn command_echo(&mut self, value: SmtStringContentBuf) -> Result<(), Self::Error>;
    fn command_get_option(&mut self, option: SmtKeywordBuf) -> Result<(), Self::Error>;
    fn command_set_option(&mut self, option: Self::Attribute) -> Result<(), Self::Error>;
    fn command_get_info(&mut self, keyword: SmtKeywordBuf) -> Result<(), Self::Error>;
    fn command_set_info(&mut self, attribute: Self::Attribute) -> Result<(), Self::Error>;
    fn command_set_logic(&mut self, logic: SmtSymbolBuf) -> Result<(), Self::Error>;
    fn command_get_value(&mut self, terms: Vec<Self::Term>) -> Result<(), Self::Error>;
    fn command_get_assertions(&mut self) -> Result<(), Self::Error>;
    fn command_get_assignment(&mut self) -> Result<(), Self::Error>;
    fn command_get_model(&mut self) -> Result<(), Self::Error>;
    fn command_get_proof(&mut self) -> Result<(), Self::Error>;
    fn command_get_unsat_assumptions(&mut self) -> Result<(), Self::Error>;
    fn command_get_unsat_core(&mut self) -> Result<(), Self::Error>;
    fn command_declare_sort(
        &mut self,
        name: SmtSymbolBuf,
        arity: SmtNumeralBuf,
    ) -> Result<(), Self::Error>;
    fn command_declare_sort_parameter(&mut self, name: SmtSymbolBuf) -> Result<(), Self::Error>;
    fn command_declare_const(
        &mut self,
        name: SmtSymbolBuf,
        sort: Self::Sort,
    ) -> Result<(), Self::Error>;
    fn command_declare_fun(
        &mut self,
        name: SmtSymbolBuf,
        param_sorts: Vec<Self::Sort>,
        result_sort: Self::Sort,
    ) -> Result<(), Self::Error>;
    fn command_assert(&mut self, term: Self::Term) -> Result<(), Self::Error>;
    fn command_check_sat(&mut self) -> Result<(), Self::Error>;
    fn command_check_sat_assuming(
        &mut self,
        assumptions: Vec<Self::Term>,
    ) -> Result<(), Self::Error>;
    fn command_reset(&mut self) -> Result<(), Self::Error>;
    fn command_reset_assertions(&mut self) -> Result<(), Self::Error>;
    fn command_exit(&mut self) -> Result<(), Self::Error>;
    fn command_push(&mut self, amount: SmtNumeralBuf) -> Result<(), Self::Error>;
    fn command_pop(&mut self, amount: SmtNumeralBuf) -> Result<(), Self::Error>;
    fn start_define_sort(&mut self, name: SmtSymbolBuf, params: Symbols)
    -> Result<(), Self::Error>;
    fn end_define_sort(&mut self, sort: Self::Sort) -> Result<(), Self::Error>;
    fn start_define_fun(&mut self, signature: Signature<'_, Self::Sort>)
    -> Result<(), Self::Error>;
    fn command_define_const(
        &mut self,
        name: SmtSymbolBuf,
        sort: Self::Sort,
        body: Self::Term,
    ) -> Result<(), Self::Error>;
    fn end_define_fun(&mut self, term: Self::Term) -> Result<(), Self::Error>;
    fn start_define_fun_rec(
        &mut self,
        signature: Signature<'_, Self::Sort>,
    ) -> Result<(), Self::Error>;
    fn end_define_fun_rec(&mut self, body: Self::Term) -> Result<(), Self::Error>;
    fn start_define_funs_rec(
        &mut self,
        signatures: Signatures<'_, Self::Sort>,
    ) -> Result<(), Self::Error>;
    fn end_define_funs_rec(&mut self) -> Result<(), Self::Error>;
    fn start_recursive_body(
        &mut self,
        signature: Signature<'_, Self::Sort>,
    ) -> Result<(), Self::Error>;
    fn end_recursive_body(&mut self, term: Self::Term) -> Result<(), Self::Error>;
    fn start_declare_datatype(
        &mut self,
        name: SmtSymbolBuf,
        params: Symbols,
    ) -> Result<(), Self::Error>;
    fn end_declare_datatype(
        &mut self,
        constructors: Constructors<Self::Sort>,
    ) -> Result<(), Self::Error>;
    fn start_declare_datatypes(&mut self, introductions: SortArities) -> Result<(), Self::Error>;
    fn end_declare_datatypes(&mut self) -> Result<(), Self::Error>;
    fn start_datatype_declaration(&mut self, sort_params: Symbols) -> Result<(), Self::Error>;
    fn end_datatype_declaration(
        &mut self,
        constructors: Constructors<Self::Sort>,
    ) -> Result<(), Self::Error>;
}
