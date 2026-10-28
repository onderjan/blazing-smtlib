use std::{
    convert::Infallible,
    error::Error,
    fmt::{self, Debug},
};

use crate::{
    SmtVersion,
    grammar::{
        SmtAttributeValue, SmtBindings, SmtConstructors, SmtFunctionSignature,
        SmtFunctionSignatures, SmtMatchCases, SmtMultiple, SmtPattern, SmtQuantifierKind, SmtSExpr,
        SmtSort, SmtSortArities, SmtSortedVars, SmtSymbols, SmtTerm,
    },
    lexicon::{
        SmtCommandNameReserved, SmtKeyword, SmtNumeral, SmtStringContent, SmtSymbol, SmtSymbolBuf,
    },
    parser::SmtParse,
};

/// Handles grammar nodes (sorts, terms, etc.).
///
/// A handler is called in a post-order traversal over the SMT-LIB abstract
/// syntax tree, as detailed in the [grammar](crate::grammar) documentation: it
/// handles the inner items (terms, sorts, etc.) first, then the outer items
/// that only see the returned values. It can construct the abstract syntax tree
/// and/or perform any other processing, e.g. immediately evaluating constant
/// expressions.
///
/// The example below sketches a handler for an arithmetic solver that processes
/// symbols, numerals, and simple operations.
///
/// It puts the terms into a [`Vec`] and identifies them by their indices. It
/// supports `let` bindings, properly stashing shadowed bindings into
/// [`SmtHandler::Scope`] and restoring them when `let` ends. As a let binding
/// can be referenced in multiple locations, this means that the terms are no
/// longer organised in a tree, but a directed acyclic graph.
///
/// ```
/// # use std::collections::HashMap;
/// #
/// # use blazing_smtlib::{
/// #     SmtHandler, SmtReader, SmtVersion,
/// #     grammar::{
/// #         SmtAttributeValue, SmtBindings, SmtIdent, SmtMatchCases, SmtMultiple, SmtPattern,
/// #         SmtQualifiedIdent, SmtQuantifierKind, SmtSExpr, SmtSort, SmtSortedVars,
/// #         SmtSpecialConstant, SmtTerm,
/// #     },
/// #     lexicon::{SmtBytesBuf, SmtKeyword},
/// #     parser::SmtTermParser,
/// # };
///
/// #[derive(Debug)]
/// enum TermHandlerError { Unsupported, NonUniqueBindings }
///
/// #[derive(Debug, PartialEq, Eq)]
/// enum Operation { Add, Sub }
///
/// #[derive(Debug, PartialEq, Eq)]
/// enum Term {
///     Constant(u64),
///     Variable(SmtBytesBuf),
///     Operation(Operation, Vec<usize>),
/// }
///
/// struct TermHandler {
///     terms: Vec<Term>,
///     mappings: HashMap<SmtBytesBuf, usize>,
/// }
///
/// impl SmtHandler for TermHandler {
///     type Error = TermHandlerError;
///
///     type SExpr = ();
///     type Attribute = ();
///     type Sort = ();
///     type Term = usize;
///
///     type Scope = HashMap<SmtBytesBuf, Option<usize>>;
///
///     fn set_version(&mut self, _version: SmtVersion) {
///         // no version-dependent semantics
///     }
///
///     fn handle_sort(&mut self, sort: SmtSort<'_, Self>) -> Result<Self::Sort, Self::Error> {
///         if sort.ident.name.bytes().as_slice() == b"Int"
///             && sort.ident.indices.is_empty()
///             && sort.args.is_empty()
///         {
///             Ok(())
///         } else {
///             Err(TermHandlerError::Unsupported)
///         }
///     }
///
///     fn handle_term(&mut self, term: SmtTerm<'_, Self>) -> Result<Self::Term, Self::Error> {
///         let term = match term {
///             SmtTerm::SpecialConstant(SmtSpecialConstant::Numeral(numeral)) => {
///                 Term::Constant(numeral.to_u64().ok_or(TermHandlerError::Unsupported)?)
///             }
///             SmtTerm::QualifiedIdent(SmtQualifiedIdent {
///                 ident: SmtIdent { name, indices },
///                 sort: None,
///             }) if indices.is_empty() => {
///                 let name = name.bytes();
///                 // a variable bound by a let stands for the term it is bound to
///                 if let Some(&index) = self.mappings.get(name.as_slice()) {
///                     return Ok(index);
///                 }
///                 Term::Variable(name.into_owned())
///             }
///             SmtTerm::Application(application) => {
///                 let (function, args) = application.into_parts();
///                 if !function.ident.indices.is_empty() || function.sort.is_some() {
///                     return Err(TermHandlerError::Unsupported);
///                 }
///                 let op = match function.ident.name.bytes().as_slice() {
///                     b"+" => Operation::Add,
///                     b"-" => Operation::Sub,
///                     _ => return Err(TermHandlerError::Unsupported),
///                 };
///                 // the arguments are term indices that have already been handled
///                 Term::Operation(op, args.into_iter().collect())
///             }
///             _ => return Err(TermHandlerError::Unsupported),
///         };
///         let index = self.terms.len();
///         self.terms.push(term);
///         Ok(index)
///     }
///
///     fn handle_s_expr(&mut self, _expr: SmtSExpr<'_, Self>) -> Result<Self::SExpr, Self::Error> {
///         Err(TermHandlerError::Unsupported)
///     }
///
///     fn start_let(
///         &mut self,
///         bindings: SmtBindings<'_, Self>,
///     ) -> Result<Self::Scope, Self::Error> {
///         // put the bindings in the symbol map and remember the replaced bindings
///         let mut shadowed = HashMap::new();
///         for (name, term) in bindings {
///             let name = name.bytes().into_owned();
///             if shadowed.contains_key(&name) {
///                 // SMT-LIB prohibits binding a variable twice in one let
///                 return Err(TermHandlerError::NonUniqueBindings);
///             }
///             let previous = self.mappings.insert(name.clone(), term);
///             shadowed.insert(name, previous);
///         }
///         // the previous bindings form the scope that will be given to `end_let`
///         Ok(shadowed)
///     }
///
///     fn end_let(
///         &mut self,
///         scope: Self::Scope,
///         body: Self::Term,
///     ) -> Result<Self::Term, Self::Error> {
///         // restore the previous symbol map from the previous bindings
///         for (name, term) in scope {
///             match term {
///                 Some(term) => {
///                     // replace with a shadowed binding
///                     self.mappings.insert(name, term);
///                 }
///                 None => {
///                     // no binding was present, remove it
///                     self.mappings.remove(&name);
///                 }
///             }
///         }
///         Ok(body)
///     }
///
///     // ... attributes, annotations, quantifiers, lambda, match returning unsupported ...
/// #
/// #     fn handle_attribute(
/// #         &mut self,
/// #         _name: SmtKeyword<'_>,
/// #         _value: Option<SmtAttributeValue<'_, Self>>,
/// #     ) -> Result<Self::Attribute, Self::Error> {
/// #         Err(TermHandlerError::Unsupported)
/// #     }
/// #
/// #     fn annotate_term(
/// #         &mut self,
/// #         _term: Self::Term,
/// #         _attributes: SmtMultiple<'_, Self::Attribute>,
/// #     ) -> Result<Self::Term, Self::Error> {
/// #         Err(TermHandlerError::Unsupported)
/// #     }
/// #
/// #     fn start_quantifier(
/// #         &mut self,
/// #         _kind: SmtQuantifierKind,
/// #         _vars: SmtSortedVars<'_, Self>,
/// #     ) -> Result<Self::Scope, Self::Error> {
/// #         Err(TermHandlerError::Unsupported)
/// #     }
/// #
/// #     fn end_quantifier(
/// #         &mut self,
/// #         _kind: SmtQuantifierKind,
/// #         _scope: Self::Scope,
/// #         _body: Self::Term,
/// #     ) -> Result<Self::Term, Self::Error> {
/// #         Err(TermHandlerError::Unsupported)
/// #     }
/// #
/// #     fn start_lambda(
/// #         &mut self,
/// #         _vars: SmtSortedVars<'_, Self>,
/// #     ) -> Result<Self::Scope, Self::Error> {
/// #         Err(TermHandlerError::Unsupported)
/// #     }
/// #
/// #     fn end_lambda(
/// #         &mut self,
/// #         _scope: Self::Scope,
/// #         _body: Self::Term,
/// #     ) -> Result<Self::Term, Self::Error> {
/// #         Err(TermHandlerError::Unsupported)
/// #     }
/// #
/// #     fn start_match(&mut self, _scrutinee: &Self::Term) -> Result<(), Self::Error> {
/// #         Err(TermHandlerError::Unsupported)
/// #     }
/// #
/// #     fn start_match_case(
/// #         &mut self,
/// #         _scrutinee: &Self::Term,
/// #         _pattern: SmtPattern<'_>,
/// #     ) -> Result<Self::Scope, Self::Error> {
/// #         Err(TermHandlerError::Unsupported)
/// #     }
/// #
/// #     fn end_match_case(
/// #         &mut self,
/// #         _scope: Self::Scope,
/// #         _scrutinee: &Self::Term,
/// #         _term: Self::Term,
/// #     ) -> Result<Self::Term, Self::Error> {
/// #         Err(TermHandlerError::Unsupported)
/// #     }
/// #
/// #     fn end_match(
/// #         &mut self,
/// #         _scrutinee: Self::Term,
/// #         _cases: SmtMatchCases<'_, Self>,
/// #     ) -> Result<Self::Term, Self::Error> {
/// #         Err(TermHandlerError::Unsupported)
/// #     }
/// }
///
/// // read a term with subterms and handle it using the custom handler
/// let mut handler = TermHandler {
///     terms: Vec::new(),
///     mappings: HashMap::new(),
/// };
/// let mut reader = SmtReader::new(&mut handler, SmtTermParser::new(), SmtVersion::V2_7);
/// let located_outer_term = reader.read_all(b"(let ((b 5)) (- (+ a b b) c))").unwrap();
/// let a = SmtBytesBuf::from_vec(b"a".into());
/// let c = SmtBytesBuf::from_vec(b"c".into());
/// // `5` was added as a first term, then `a`;
/// // `b` was not added (twice) as its mapping pointed to index 0;
/// // then the addition, `c`, and subtraction were added
/// assert_eq!(
///     handler.terms,
///     vec![
///         Term::Constant(5),
///         Term::Variable(a),
///         Term::Operation(Operation::Add, vec![1, 0, 0]),
///         Term::Variable(c),
///         Term::Operation(Operation::Sub, vec![2, 3])
///     ]
/// );
/// // reading ends at byte 29, the end of input
/// assert_eq!(located_outer_term.location().offset(), 29);
/// // the outer term has index 4
/// assert_eq!(located_outer_term.into_value(), 4);
/// ```
pub trait SmtHandler {
    /// Error returned by the handler on failure.
    type Error;

    /// S-expression that has been handled.
    ///
    /// Returned by [`handle_s_expr`](Self::handle_s_expr).
    type SExpr;
    /// Attribute that has been handled.
    ///
    /// Returned by [`handle_attribute`](Self::handle_attribute).
    type Attribute;
    /// Sort that has been handled.
    ///
    /// Returned by [`handle_sort`](Self::handle_sort).
    type Sort;
    /// Term that has been handled.
    ///
    /// Returned by [`handle_term`](Self::handle_term), [`annotate_term`](Self::annotate_term),
    /// and the methods that end binders and `match`, such as [`end_let`](Self::end_let).
    type Term;

    /// Scope of a binder, returned at its start and given back at its end.
    ///
    /// The binders are `let`, the quantifiers, `lambda`, and the cases of `match`. The body of a
    /// binder is handled between its start and its end, so the handler can bring the bound
    /// variables into scope at the start and keep in the scope what it needs to restore at the
    /// end, e.g. the bindings that the bound variables shadow.
    ///
    /// A bound variable shadows the variables and user-defined function symbols of the same name
    /// in the enclosing scopes, but SMT-LIB prohibits it from having the name of a theory function
    /// symbol of the current logic. Library parsers do not check this.
    type Scope;

    /// Informs the handler of the version in force.
    ///
    /// A caller must set the version before it calls the other methods, so that the handler can
    /// process the nodes by the semantics of the version. A handler starts with
    /// [`SmtVersion::default`] in force.
    ///
    /// [`SmtParseAdapter`](crate::parser::SmtParseAdapter) calls this method before any other,
    /// and [`SmtScriptParser`](crate::parser::SmtScriptParser) calls it again when a script
    /// declares its version (`set-info :smt-lib-version`).
    fn set_version(&mut self, version: SmtVersion);

    /// Handles a sort.
    fn handle_sort(&mut self, sort: SmtSort<'_, Self>) -> Result<Self::Sort, Self::Error>;

    /// Handles a term (special constant, qualified identifier, or application).
    ///
    /// Annotations, binders and `match` terms are terms too, but are handled by methods of their
    /// own because of their structure: annotations by [`annotate_term`](Self::annotate_term),
    /// binders by pairs of methods that start and end their body, such as
    /// [`start_let`](Self::start_let) and [`end_let`](Self::end_let), and `match` terms by
    /// [`start_match`](Self::start_match) and the methods that follow it.
    fn handle_term(&mut self, term: SmtTerm<'_, Self>) -> Result<Self::Term, Self::Error>;

    /// Handles an S-expression.
    ///
    /// S-expressions mainly occur in attribute values, e.g. `a` and `(f x)` in
    /// `:my-attribute (a (f x))`.
    fn handle_s_expr(&mut self, expr: SmtSExpr<'_, Self>) -> Result<Self::SExpr, Self::Error>;

    /// Handles an attribute.
    ///
    /// The value is [`None`] for an attribute without a value, e.g. `:left-assoc`. Library
    /// parsers do not check well-formedness of the attribute content, e.g. that `:named` has a
    /// symbol value.
    fn handle_attribute(
        &mut self,
        name: SmtKeyword<'_>,
        value: Option<SmtAttributeValue<'_, Self>>,
    ) -> Result<Self::Attribute, Self::Error>;

    /// Annotates a term with attributes, e.g. `(! (> x 0) :named p)`.
    ///
    /// The caller guarantees that there is at least one attribute.
    ///
    /// SMT-LIB defines the name of a `:named` attribute at the annotation: the name can be used
    /// in what is handled after this method, in the rest of the command and after it. SMT-LIB
    /// requires the named term to be closed and the name to be fresh, and allows `:pattern` only
    /// on the body of a quantified term. Library parsers do not check this.
    fn annotate_term(
        &mut self,
        term: Self::Term,
        attributes: SmtMultiple<'_, Self::Attribute>,
    ) -> Result<Self::Term, Self::Error>;

    /// Starts a `let` term.
    ///
    /// The bound terms are handled outside the scope of the `let`, before this method is
    /// called: in `(let ((x 1) (y x)) (+ x y))`, the `x` bound to `y` is not the `x` that this
    /// `let` binds.
    ///
    /// SMT-LIB requires the binding names to be distinct. Library parsers do not check this.
    fn start_let(&mut self, bindings: SmtBindings<'_, Self>) -> Result<Self::Scope, Self::Error>;

    /// Ends a `let` term.
    ///
    /// Receives the scope returned by the corresponding [`start_let`](Self::start_let).
    fn end_let(&mut self, scope: Self::Scope, body: Self::Term) -> Result<Self::Term, Self::Error>;

    /// Starts a quantified term (`forall` or `exists`).
    ///
    /// The variable names need not be distinct: the binder stands for nested binders of one
    /// variable each, so a later variable shadows an earlier one of the same name.
    fn start_quantifier(
        &mut self,
        kind: SmtQuantifierKind,
        vars: SmtSortedVars<'_, Self>,
    ) -> Result<Self::Scope, Self::Error>;

    /// Ends a quantified term (`forall` or `exists`).
    ///
    /// Receives the scope returned by the corresponding
    /// [`start_quantifier`](Self::start_quantifier).
    fn end_quantifier(
        &mut self,
        kind: SmtQuantifierKind,
        scope: Self::Scope,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error>;

    /// Starts a `lambda` term.
    ///
    /// The variable names need not be distinct: the binder stands for nested binders of one
    /// variable each, so a later variable shadows an earlier one of the same name.
    ///
    /// Lambda terms were introduced in SMT-LIB 2.7.
    fn start_lambda(&mut self, vars: SmtSortedVars<'_, Self>) -> Result<Self::Scope, Self::Error>;

    /// Ends a `lambda` term.
    ///
    /// Receives the scope returned by the corresponding [`start_lambda`](Self::start_lambda).
    ///
    /// Lambda terms were introduced in SMT-LIB 2.7.
    fn end_lambda(
        &mut self,
        scope: Self::Scope,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error>;

    /// Starts a `match` term.
    ///
    /// The scrutinee is the term that is matched, e.g. `l` in
    /// `(match l ((nil 0) ((cons h t) h)))`. At least one case follows, each case started by
    /// [`start_match_case`](Self::start_match_case) and ended by
    /// [`end_match_case`](Self::end_match_case), after which [`end_match`](Self::end_match) ends
    /// the `match` term. A `match` in the body of a match case is nested properly: it ends
    /// before the match case does.
    ///
    /// Match terms were introduced in SMT-LIB 2.6.
    fn start_match(&mut self, scrutinee: &Self::Term) -> Result<(), Self::Error>;

    /// Starts a case of a `match` term.
    ///
    /// Returns the scope in which the body of the case is handled, e.g. with `h` and `t` bound
    /// for the pattern `(cons h t)`. The case belongs to the innermost `match` that has been
    /// started and not ended. A case ends before the next case of its `match` starts.
    ///
    /// A constructor pattern has at least one argument, and its arguments are variables or the
    /// wildcard `_`, even if a symbol has the name of a constructor, e.g. `nil` in `(cons h nil)`.
    /// A simple pattern, e.g. `nil` or `x`, can be a constructor or a variable: library parsers
    /// do not tell them apart. They do not check the names of constructors or their arities.
    ///
    /// SMT-LIB requires the variables of a constructor pattern to be distinct, e.g. it prohibits
    /// `(pair x x)`, while the wildcard can repeat, as in `(pair _ _)`. Library parsers do not
    /// check this.
    ///
    /// Match terms were introduced in SMT-LIB 2.6.
    fn start_match_case(
        &mut self,
        scrutinee: &Self::Term,
        pattern: SmtPattern<'_>,
    ) -> Result<Self::Scope, Self::Error>;

    /// Ends a case of a `match` term.
    ///
    /// Receives the scope returned by the corresponding
    /// [`start_match_case`](Self::start_match_case). The result of this method is given to
    /// [`end_match`](Self::end_match) as the case, next to its pattern.
    ///
    /// Match terms were introduced in SMT-LIB 2.6.
    fn end_match_case(
        &mut self,
        scope: Self::Scope,
        scrutinee: &Self::Term,
        term: Self::Term,
    ) -> Result<Self::Term, Self::Error>;

    /// Ends a `match` term.
    ///
    /// The cases are in the order of the input, each with its pattern and the result of
    /// [`end_match_case`](Self::end_match_case) for it. The caller guarantees that there is at
    /// least one case.
    ///
    /// SMT-LIB requires a variable pattern among the cases unless every constructor of the sort
    /// of the scrutinee has a case. Library parsers do not check this.
    ///
    /// Match terms were introduced in SMT-LIB 2.6.
    fn end_match(
        &mut self,
        scrutinee: Self::Term,
        cases: SmtMatchCases<'_, Self>,
    ) -> Result<Self::Term, Self::Error>;
}

/// Types of handled nodes (S-expressions, sorts, and terms).
///
/// The views of nodes are parametrised by these types. Every [`SmtHandler`] has them as its own
/// types of the same names. A program that builds views without a handler, e.g. to write them,
/// implements this trait on a type of its own.
pub trait SmtNodeTypes {
    /// Handled S-expression.
    type SExpr;
    /// Handled sort.
    type Sort;
    /// Handled term.
    type Term;
}

impl<H: SmtHandler + ?Sized> SmtNodeTypes for H {
    type SExpr = H::SExpr;
    type Sort = H::Sort;
    type Term = H::Term;
}

/// Handles commands.
pub trait SmtCommandHandler: SmtHandler {
    /// Parser of a nonstandard command.
    type NonstandardParser: SmtParse<Self, Result = ()>;

    /// Returns a parser that parses a nonstandard command with the given name.
    fn nonstandard_command(
        &mut self,
        name: SmtSymbol<'_>,
    ) -> Result<Self::NonstandardParser, Self::Error>;

    /// Echoes a string (`echo`).
    fn command_echo(&mut self, value: SmtStringContent<'_>) -> Result<(), Self::Error>;

    /// Gets the value of an option (`get-option`).
    fn command_get_option(&mut self, option: SmtKeyword<'_>) -> Result<(), Self::Error>;
    /// Sets an option (`set-option`).
    fn command_set_option(&mut self, option: Self::Attribute) -> Result<(), Self::Error>;
    /// Gets information (`get-info`).
    fn command_get_info(&mut self, keyword: SmtKeyword<'_>) -> Result<(), Self::Error>;
    /// Sets information (`set-info`).
    fn command_set_info(&mut self, attribute: Self::Attribute) -> Result<(), Self::Error>;

    /// Sets the logic (`set-logic`).
    fn command_set_logic(&mut self, logic: SmtSymbol<'_>) -> Result<(), Self::Error>;

    /// Gets the values of terms (`get-value`).
    fn command_get_value(&mut self, terms: SmtMultiple<'_, Self::Term>) -> Result<(), Self::Error>;
    /// Gets the assertions (`get-assertions`).
    fn command_get_assertions(&mut self) -> Result<(), Self::Error>;
    /// Gets the values of the named Boolean terms (`get-assignment`).
    fn command_get_assignment(&mut self) -> Result<(), Self::Error>;
    /// Gets the model (`get-model`).
    fn command_get_model(&mut self) -> Result<(), Self::Error>;
    /// Gets a proof (`get-proof`).
    fn command_get_proof(&mut self) -> Result<(), Self::Error>;
    /// Gets an unsatisfiable subset of the assumptions (`get-unsat-assumptions`).
    fn command_get_unsat_assumptions(&mut self) -> Result<(), Self::Error>;
    /// Gets an unsatisfiable core (`get-unsat-core`).
    fn command_get_unsat_core(&mut self) -> Result<(), Self::Error>;

    /// Declares a sort with an arity (`declare-sort`).
    ///
    /// As per the standard, the handler should return an error if `name`
    /// is a sort symbol or parameter that is already present in the current signature.
    fn command_declare_sort(
        &mut self,
        name: SmtSymbol<'_>,
        arity: SmtNumeral<'_>,
    ) -> Result<(), Self::Error>;

    /// Declares a global sort parameter (`declare-sort-parameter`).
    ///
    /// As per the standard, the handler should return an error
    /// if `name` is a sort symbol, sort parameter, or theory symbol
    /// that is already present in the current signature.
    fn command_declare_sort_parameter(&mut self, name: SmtSymbol<'_>) -> Result<(), Self::Error>;

    /// Declares a constant (`declare-const`).
    ///
    /// Semantically, `declare-const` is syntax sugar for
    /// `declare-fun` without any parameters.
    fn command_declare_const(
        &mut self,
        name: SmtSymbol<'_>,
        sort: Self::Sort,
    ) -> Result<(), Self::Error>;

    /// Declares a function (`declare-fun`).
    fn command_declare_fun(
        &mut self,
        name: SmtSymbol<'_>,
        param_sorts: SmtMultiple<'_, Self::Sort>,
        result_sort: Self::Sort,
    ) -> Result<(), Self::Error>;

    /// Asserts a term (`assert`).
    fn command_assert(&mut self, term: Self::Term) -> Result<(), Self::Error>;

    /// Checks satisfiability (`check-sat`).
    ///
    /// Semantically, command `check-sat` is syntax sugar for
    /// `check-sat-assuming` without additional assumptions.
    fn command_check_sat(&mut self) -> Result<(), Self::Error>;

    /// Checks satisfiability with additional assumptions (`check-sat-assuming`).
    ///
    /// The command `check-sat-assuming` triggers checking satisfiability
    /// of the conjunction of the assertions in the current context
    /// and additional assumptions given within the command.
    fn command_check_sat_assuming(
        &mut self,
        assumptions: SmtMultiple<'_, Self::Term>,
    ) -> Result<(), Self::Error>;

    /// Resets the solver to its initial state (`reset`).
    fn command_reset(&mut self) -> Result<(), Self::Error>;

    /// Empties the assertion stack (`reset-assertions`).
    fn command_reset_assertions(&mut self) -> Result<(), Self::Error>;

    /// Exits the solver (`exit`).
    fn command_exit(&mut self) -> Result<(), Self::Error>;

    /// Pushes `amount` empty assertion levels onto the assertion stack (`push`).
    ///
    /// If `amount` is 0, no levels are pushed (i.e. successful no-op).
    fn command_push(&mut self, amount: SmtNumeral<'_>) -> Result<(), Self::Error>;

    /// Pops `amount` assertion levels from the assertion stack (`pop`).
    ///
    /// If `amount` is 0, no levels are popped (i.e. successful no-op).
    ///
    /// As per the standard, the handler should return an error
    /// when popping more than the amount of remaining assertion levels
    /// beyond the inherent first assertion level.
    fn command_pop(&mut self, amount: SmtNumeral<'_>) -> Result<(), Self::Error>;

    /// Starts a sort definition (`define-sort`).
    ///
    /// The handler should bring `params` into scope as local sort parameters
    /// before the body sort is handled. As per the standard, they shadow
    /// previously user-declared sort symbols and parameters of the same name,
    /// but not theory sort symbols.
    ///
    /// As per the standard, the handler should return an error
    /// 1. if `name` is a sort symbol or parameter already present in the current signature,
    /// 2. if a theory sort symbol is used as a sort parameter.
    fn start_define_sort(
        &mut self,
        name: SmtSymbol<'_>,
        params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error>;

    /// Ends a sort definition (`define-sort`).
    ///
    /// As per the standard, the handler should return an error
    /// if `sort` is not a well-defined (polymorphic) sort with respect to the
    /// current signature extended with the sort parameters.
    fn end_define_sort(&mut self, sort: Self::Sort) -> Result<(), Self::Error>;

    /// Starts the body of a function definition (`define-fun`).
    fn start_define_fun(
        &mut self,
        signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error>;

    /// Defines a constant (`define-const`).
    ///
    /// The command `define-const` is syntax sugar for `define-fun`
    /// without parameters.
    fn command_define_const(
        &mut self,
        name: SmtSymbol<'_>,
        sort: Self::Sort,
        body: Self::Term,
    ) -> Result<(), Self::Error>;

    /// Ends the body of a function definition (`define-fun`).
    fn end_define_fun(&mut self, term: Self::Term) -> Result<(), Self::Error>;

    /// Starts a recursive function definition (`define-fun-rec`).
    fn start_define_fun_rec(
        &mut self,
        signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error>;

    /// Ends a recursive function definition (`define-fun-rec`).
    fn end_define_fun_rec(&mut self, body: Self::Term) -> Result<(), Self::Error>;

    /// Starts recursive function definitions (`define-funs-rec`).
    ///
    /// The parser guarantees:
    /// 1. This method is never nested before the corresponding `end_define_funs_rec`.
    /// 2. The parameter `signatures` is nonempty and contains all signatures
    ///    of functions to be defined.
    /// 3. Exactly one body per signature, in the same order, is delivered
    ///    between `start_recursive_body` and `end_recursive_body` before
    ///    the corresponding `end_define_funs_rec`.
    ///
    /// All signatures arrive before any body is started, as every body may
    /// refer to every defined function within the recursive function definitions.
    /// The function names in `signatures` are in scope from this method call onwards,
    /// while the function parameters are only in scope between the corresponding
    /// `start_recursive_body` and `end_recursive_body`.
    ///
    /// The command `define-fun-rec` is just syntax sugar for
    /// `define-funs-rec` with a single function. It is desugared before being handled.
    ///
    /// Consult the standard for proper handling.
    fn start_define_funs_rec(
        &mut self,
        signatures: SmtFunctionSignatures<'_, Self>,
    ) -> Result<(), Self::Error>;

    /// Ends recursive function definitions (`define-funs-rec`).
    ///
    /// The parser guarantees:
    /// 1. There is a pending unended `start_define_funs_rec`.
    /// 2. There is no pending unended `start_recursive_body`.
    ///
    /// The command `define-fun-rec` is just syntax sugar for
    /// `define-funs-rec` with a single function. It is desugared before being handled.
    ///
    /// Consult the standard for proper handling.
    fn end_define_funs_rec(&mut self) -> Result<(), Self::Error>;

    /// Starts the body of a recursive function (in `define-funs-rec`).
    ///
    /// The parser guarantees:
    /// 1. This method is only called between `start_define_funs_rec` and `end_define_funs_rec`.
    /// 2. This method is never nested before the corresponding `end_recursive_body`.
    /// 3. This body corresponds to the signature at the same index in `start_define_funs_rec`.
    /// 4. The body of this function definition is handled after this method is called
    ///    and before the respective `end_recursive_body` is called.
    ///
    /// The command `define-fun-rec` is just syntax sugar for
    /// `define-funs-rec` with a single function. It is desugared before being handled.
    ///
    /// Consult the standard for proper handling.
    fn start_recursive_body(
        &mut self,
        signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error>;

    /// Ends the body of a recursive function (in `define-funs-rec`).
    ///
    /// The parameter `term` is the result term of the function definition body.
    ///
    /// The parser guarantees:
    /// 1. This method is only called between `start_define_funs_rec` and `end_define_funs_rec`.
    /// 2. There is a pending unended `start_recursive_body`.
    ///
    /// Consult the standard for proper handling.
    fn end_recursive_body(&mut self, term: Self::Term) -> Result<(), Self::Error>;

    /// Starts a datatype declaration (`declare-datatype`).
    fn start_declare_datatype(
        &mut self,
        name: SmtSymbol<'_>,
        params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error>;

    /// Ends a datatype declaration (`declare-datatype`).
    fn end_declare_datatype(
        &mut self,
        constructors: SmtConstructors<'_, Self>,
    ) -> Result<(), Self::Error>;

    /// Starts datatype declarations (`declare-datatypes`).
    ///
    /// The parameter `introductions` contains ordered introductions of
    /// the name and arity of datatypes. The parser calls this method before any
    /// datatype declaration is started, as the sorts can be referenced by selector
    /// sorts of the datatypes.
    ///
    /// The parser guarantees:
    /// 1. This method is never nested before the corresponding `end_declare_datatypes`.
    /// 2. There is at least one datatype introduction, i.e. `introductions` is nonempty.
    /// 3. There is exactly one datatype per introduction,
    ///    arriving in the same order as the introductions.
    ///
    /// There are no other guarantees, including on arities.
    ///
    /// The command `declare-datatype` is just syntax sugar for
    /// `declare-datatypes` with a single introduction where the
    /// arity is the number of parameters of the datatype (zero if there are none).
    /// The command is desugared before being handled.
    ///
    /// Consult the standard for proper handling.
    fn start_declare_datatypes(
        &mut self,
        introductions: SmtSortArities<'_>,
    ) -> Result<(), Self::Error>;

    /// Ends datatype declarations (`declare-datatypes`).
    ///
    /// The parser guarantees:
    /// 1. There is a pending unended `start_declare_datatypes`.
    /// 2. There is no pending unended `start_datatype_declaration`.
    ///
    /// Consult the standard for proper handling.
    fn end_declare_datatypes(&mut self) -> Result<(), Self::Error>;

    /// Starts a datatype declaration (in `declare-datatypes`).
    ///
    /// The parser guarantees:
    /// 1. This method is only called between `start_declare_datatypes` and `end_declare_datatypes`.
    /// 2. This method is never nested before the corresponding `end_datatype_declaration`.
    /// 3. This declaration corresponds to the introduction at the same index
    ///    in `start_declare_datatypes`.
    /// 4. The sort parameters (`sort_params`) are nonempty exactly when the datatype is parametric.
    /// 5. The selector sorts of the datatype declaration are handled after this method is called
    ///    and before the respective `end_datatype_declaration` is called.
    ///
    /// There are no other guarantees, including on arities.
    ///
    /// Consult the standard for proper handling.
    fn start_datatype_declaration(
        &mut self,
        sort_params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error>;

    /// Ends a datatype declaration (in `declare-datatypes`).
    ///
    /// The parser guarantees:
    /// 1. This method is only called between `start_declare_datatypes` and `end_declare_datatypes`.
    /// 2. There is a pending unended `start_datatype_declaration`.
    /// 3. There is at least one datatype constructor, i.e. `constructors` is nonempty.
    ///
    /// There are no other guarantees, including on arities.
    ///
    /// Consult the standard for proper handling.
    fn end_datatype_declaration(
        &mut self,
        constructors: SmtConstructors<'_, Self>,
    ) -> Result<(), Self::Error>;
}

/// Error of a partial command handler (unsupported command or handler error).
///
/// Unsupported commands come in two varieties: standard and nonstandard.
#[derive(Debug, Clone)]
pub enum SmtPartialCommandError<E> {
    /// The handler does not implement the standard command.
    Unsupported(SmtCommandNameReserved),
    /// The handler does not implement the nonstandard command with the given name.
    UnsupportedNonstandard(SmtSymbolBuf),
    /// The handler failed.
    Handler(E),
}

impl<E> From<E> for SmtPartialCommandError<E> {
    fn from(err: E) -> Self {
        Self::Handler(err)
    }
}

impl<E: fmt::Display> fmt::Display for SmtPartialCommandError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported(command) => write!(f, "unsupported command `{}`", command.as_str()),
            Self::UnsupportedNonstandard(name) => {
                f.write_str("unsupported nonstandard command ")?;
                write_symbol(f, name)
            }
            Self::Handler(err) => err.fmt(f),
        }
    }
}

impl<E: Error + 'static> Error for SmtPartialCommandError<E> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Handler(err) => err.source(),
            Self::Unsupported(_) | Self::UnsupportedNonstandard(_) => None,
        }
    }
}

/// Writes the symbol for an error message.
///
/// It is converted to UTF-8 via lossy conversion and enclosed in backticks.
/// If quoted, the pipes are retained.
fn write_symbol(f: &mut fmt::Formatter<'_>, symbol: &SmtSymbolBuf) -> fmt::Result {
    let name = String::from_utf8_lossy(symbol.as_slice());
    if symbol.is_quoted() {
        write!(f, "`|{name}|`")
    } else {
        write!(f, "`{name}`")
    }
}

fn unsupported<T, E>(command: SmtCommandNameReserved) -> Result<T, SmtPartialCommandError<E>> {
    Err(SmtPartialCommandError::Unsupported(command))
}

/// Handles a subset of commands.
///
/// Every command it does not implement fails with
/// [`SmtPartialCommandError::Unsupported`] naming the command, or with
/// [`SmtPartialCommandError::UnsupportedNonstandard`] for a nonstandard command.
/// Each implementor is a [`SmtCommandHandler`].
pub trait SmtPartialCommandHandler:
    SmtHandler<Error = SmtPartialCommandError<Self::HandlerError>>
{
    /// Error of the handler itself.
    type HandlerError;

    /// Parser of a nonstandard command.
    type NonstandardParser: SmtParse<Self, Result = ()>;

    /// Returns a parser that parses a nonstandard command with the given name.
    fn nonstandard_command(
        &mut self,
        name: SmtSymbol<'_>,
    ) -> Result<Self::NonstandardParser, Self::Error> {
        Err(SmtPartialCommandError::UnsupportedNonstandard(
            name.into_owned(),
        ))
    }

    /// Echoes a string (`echo`).
    fn command_echo(&mut self, _value: SmtStringContent<'_>) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::Echo)
    }

    /// Gets the value of an option (`get-option`).
    fn command_get_option(&mut self, _option: SmtKeyword<'_>) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetOption)
    }
    /// Sets an option (`set-option`).
    fn command_set_option(&mut self, _option: Self::Attribute) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::SetOption)
    }
    /// Gets information (`get-info`).
    fn command_get_info(&mut self, _keyword: SmtKeyword<'_>) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetInfo)
    }
    /// Sets information (`set-info`).
    fn command_set_info(&mut self, _attribute: Self::Attribute) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::SetInfo)
    }

    /// Sets the logic (`set-logic`).
    fn command_set_logic(&mut self, _logic: SmtSymbol<'_>) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::SetLogic)
    }

    /// Gets the values of terms (`get-value`).
    fn command_get_value(
        &mut self,
        _terms: SmtMultiple<'_, Self::Term>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetValue)
    }
    /// Gets the assertions (`get-assertions`).
    fn command_get_assertions(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetAssertions)
    }
    /// Gets the values of the named Boolean terms (`get-assignment`).
    fn command_get_assignment(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetAssignment)
    }
    /// Gets the model (`get-model`).
    fn command_get_model(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetModel)
    }
    /// Gets a proof (`get-proof`).
    fn command_get_proof(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetProof)
    }
    /// Gets an unsatisfiable subset of the assumptions (`get-unsat-assumptions`).
    fn command_get_unsat_assumptions(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetUnsatAssumptions)
    }
    /// Gets an unsatisfiable core (`get-unsat-core`).
    fn command_get_unsat_core(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetUnsatCore)
    }

    /// Declares a sort with an arity (`declare-sort`).
    ///
    /// See [`SmtCommandHandler::command_declare_sort`].
    fn command_declare_sort(
        &mut self,
        _name: SmtSymbol<'_>,
        _arity: SmtNumeral<'_>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DeclareSort)
    }
    /// Declares a global sort parameter (`declare-sort-parameter`).
    ///
    /// See [`SmtCommandHandler::command_declare_sort_parameter`].
    fn command_declare_sort_parameter(&mut self, _name: SmtSymbol<'_>) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DeclareSortParameter)
    }
    /// Declares a constant (`declare-const`).
    ///
    /// See [`SmtCommandHandler::command_declare_const`].
    fn command_declare_const(
        &mut self,
        _name: SmtSymbol<'_>,
        _sort: Self::Sort,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DeclareConst)
    }
    /// Declares a function (`declare-fun`).
    fn command_declare_fun(
        &mut self,
        _name: SmtSymbol<'_>,
        _param_sorts: SmtMultiple<'_, Self::Sort>,
        _result_sort: Self::Sort,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DeclareFun)
    }

    /// Asserts a term (`assert`).
    fn command_assert(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::Assert)
    }
    /// Checks satisfiability (`check-sat`).
    ///
    /// See [`SmtCommandHandler::command_check_sat`].
    fn command_check_sat(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::CheckSat)
    }
    /// Checks satisfiability with additional assumptions (`check-sat-assuming`).
    ///
    /// See [`SmtCommandHandler::command_check_sat_assuming`].
    fn command_check_sat_assuming(
        &mut self,
        _assumptions: SmtMultiple<'_, Self::Term>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::CheckSatAssuming)
    }

    /// Resets the solver to its initial state (`reset`).
    fn command_reset(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::Reset)
    }
    /// Empties the assertion stack (`reset-assertions`).
    fn command_reset_assertions(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::ResetAssertions)
    }
    /// Exits the solver (`exit`).
    fn command_exit(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::Exit)
    }
    /// Pushes `amount` empty assertion levels onto the assertion stack (`push`).
    ///
    /// See [`SmtCommandHandler::command_push`].
    fn command_push(&mut self, _amount: SmtNumeral<'_>) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::Push)
    }
    /// Pops `amount` assertion levels from the assertion stack (`pop`).
    ///
    /// See [`SmtCommandHandler::command_pop`].
    fn command_pop(&mut self, _amount: SmtNumeral<'_>) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::Pop)
    }

    /// Starts a sort definition (`define-sort`).
    ///
    /// See [`SmtCommandHandler::start_define_sort`].
    fn start_define_sort(
        &mut self,
        _name: SmtSymbol<'_>,
        _params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DefineSort)
    }
    /// Ends a sort definition (`define-sort`).
    ///
    /// See [`SmtCommandHandler::end_define_sort`].
    fn end_define_sort(&mut self, _sort: Self::Sort) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DefineSort)
    }

    /// Starts the body of a function definition (`define-fun`).
    fn start_define_fun(
        &mut self,
        _signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DefineFun)
    }
    /// Ends the body of a function definition (`define-fun`).
    fn end_define_fun(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DefineFun)
    }
    /// Defines a constant (`define-const`).
    ///
    /// See [`SmtCommandHandler::command_define_const`].
    fn command_define_const(
        &mut self,
        _name: SmtSymbol<'_>,
        _sort: Self::Sort,
        _body: Self::Term,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DefineConst)
    }

    /// Starts a recursive function definition (`define-fun-rec`).
    fn start_define_fun_rec(
        &mut self,
        _signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DefineFunRec)
    }
    /// Ends a recursive function definition (`define-fun-rec`).
    fn end_define_fun_rec(&mut self, _body: Self::Term) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DefineFunRec)
    }

    /// Starts recursive function definitions (`define-funs-rec`).
    ///
    /// See [`SmtCommandHandler::start_define_funs_rec`].
    fn start_define_funs_rec(
        &mut self,
        _signatures: SmtFunctionSignatures<'_, Self>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DefineFunsRec)
    }
    /// Ends recursive function definitions (`define-funs-rec`).
    ///
    /// See [`SmtCommandHandler::end_define_funs_rec`].
    fn end_define_funs_rec(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DefineFunsRec)
    }
    /// Starts the body of a recursive function (in `define-funs-rec`).
    ///
    /// See [`SmtCommandHandler::start_recursive_body`].
    fn start_recursive_body(
        &mut self,
        _signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DefineFunsRec)
    }
    /// Ends the body of a recursive function (in `define-funs-rec`).
    ///
    /// See [`SmtCommandHandler::end_recursive_body`].
    fn end_recursive_body(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DefineFunsRec)
    }

    /// Starts a datatype declaration (`declare-datatype`).
    fn start_declare_datatype(
        &mut self,
        _name: SmtSymbol<'_>,
        _params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DeclareDatatype)
    }
    /// Ends a datatype declaration (`declare-datatype`).
    fn end_declare_datatype(
        &mut self,
        _constructors: SmtConstructors<'_, Self>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DeclareDatatype)
    }

    /// Starts datatype declarations (`declare-datatypes`).
    ///
    /// See [`SmtCommandHandler::start_declare_datatypes`].
    fn start_declare_datatypes(
        &mut self,
        _introductions: SmtSortArities<'_>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DeclareDatatypes)
    }
    /// Ends datatype declarations (`declare-datatypes`).
    ///
    /// See [`SmtCommandHandler::end_declare_datatypes`].
    fn end_declare_datatypes(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DeclareDatatypes)
    }
    /// Starts a datatype declaration (in `declare-datatypes`).
    ///
    /// See [`SmtCommandHandler::start_datatype_declaration`].
    fn start_datatype_declaration(
        &mut self,
        _sort_params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DeclareDatatypes)
    }
    /// Ends a datatype declaration (in `declare-datatypes`).
    ///
    /// See [`SmtCommandHandler::end_datatype_declaration`].
    fn end_datatype_declaration(
        &mut self,
        _constructors: SmtConstructors<'_, Self>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DeclareDatatypes)
    }
}

impl<T: SmtPartialCommandHandler> SmtCommandHandler for T {
    type NonstandardParser = <T as SmtPartialCommandHandler>::NonstandardParser;

    fn nonstandard_command(
        &mut self,
        name: SmtSymbol<'_>,
    ) -> Result<Self::NonstandardParser, Self::Error> {
        SmtPartialCommandHandler::nonstandard_command(self, name)
    }

    fn command_echo(&mut self, value: SmtStringContent<'_>) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_echo(self, value)
    }

    fn command_get_option(&mut self, option: SmtKeyword<'_>) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_get_option(self, option)
    }
    fn command_set_option(&mut self, option: Self::Attribute) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_set_option(self, option)
    }
    fn command_get_info(&mut self, keyword: SmtKeyword<'_>) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_get_info(self, keyword)
    }
    fn command_set_info(&mut self, attribute: Self::Attribute) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_set_info(self, attribute)
    }

    fn command_set_logic(&mut self, logic: SmtSymbol<'_>) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_set_logic(self, logic)
    }

    fn command_get_value(&mut self, terms: SmtMultiple<'_, Self::Term>) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_get_value(self, terms)
    }
    fn command_get_assertions(&mut self) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_get_assertions(self)
    }
    fn command_get_assignment(&mut self) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_get_assignment(self)
    }
    fn command_get_model(&mut self) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_get_model(self)
    }
    fn command_get_proof(&mut self) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_get_proof(self)
    }
    fn command_get_unsat_assumptions(&mut self) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_get_unsat_assumptions(self)
    }
    fn command_get_unsat_core(&mut self) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_get_unsat_core(self)
    }

    fn command_declare_sort(
        &mut self,
        name: SmtSymbol<'_>,
        arity: SmtNumeral<'_>,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_declare_sort(self, name, arity)
    }
    fn command_declare_sort_parameter(&mut self, name: SmtSymbol<'_>) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_declare_sort_parameter(self, name)
    }
    fn command_declare_const(
        &mut self,
        name: SmtSymbol<'_>,
        sort: Self::Sort,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_declare_const(self, name, sort)
    }
    fn command_declare_fun(
        &mut self,
        name: SmtSymbol<'_>,
        param_sorts: SmtMultiple<'_, Self::Sort>,
        result_sort: Self::Sort,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_declare_fun(self, name, param_sorts, result_sort)
    }

    fn command_assert(&mut self, term: Self::Term) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_assert(self, term)
    }
    fn command_check_sat(&mut self) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_check_sat(self)
    }
    fn command_check_sat_assuming(
        &mut self,
        assumptions: SmtMultiple<'_, Self::Term>,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_check_sat_assuming(self, assumptions)
    }

    fn command_reset(&mut self) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_reset(self)
    }
    fn command_reset_assertions(&mut self) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_reset_assertions(self)
    }
    fn command_exit(&mut self) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_exit(self)
    }
    fn command_push(&mut self, amount: SmtNumeral<'_>) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_push(self, amount)
    }
    fn command_pop(&mut self, amount: SmtNumeral<'_>) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_pop(self, amount)
    }

    fn start_define_sort(
        &mut self,
        name: SmtSymbol<'_>,
        params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::start_define_sort(self, name, params)
    }
    fn end_define_sort(&mut self, sort: Self::Sort) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::end_define_sort(self, sort)
    }

    fn start_define_fun(
        &mut self,
        signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::start_define_fun(self, signature)
    }
    fn command_define_const(
        &mut self,
        name: SmtSymbol<'_>,
        sort: Self::Sort,
        body: Self::Term,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::command_define_const(self, name, sort, body)
    }
    fn end_define_fun(&mut self, term: Self::Term) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::end_define_fun(self, term)
    }

    fn start_define_fun_rec(
        &mut self,
        signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::start_define_fun_rec(self, signature)
    }
    fn end_define_fun_rec(&mut self, body: Self::Term) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::end_define_fun_rec(self, body)
    }

    fn start_define_funs_rec(
        &mut self,
        signatures: SmtFunctionSignatures<'_, Self>,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::start_define_funs_rec(self, signatures)
    }
    fn end_define_funs_rec(&mut self) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::end_define_funs_rec(self)
    }
    fn start_recursive_body(
        &mut self,
        signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::start_recursive_body(self, signature)
    }
    fn end_recursive_body(&mut self, term: Self::Term) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::end_recursive_body(self, term)
    }

    fn start_declare_datatype(
        &mut self,
        name: SmtSymbol<'_>,
        params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::start_declare_datatype(self, name, params)
    }
    fn end_declare_datatype(
        &mut self,
        constructors: SmtConstructors<'_, Self>,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::end_declare_datatype(self, constructors)
    }

    fn start_declare_datatypes(
        &mut self,
        introductions: SmtSortArities<'_>,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::start_declare_datatypes(self, introductions)
    }
    fn end_declare_datatypes(&mut self) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::end_declare_datatypes(self)
    }
    fn start_datatype_declaration(
        &mut self,
        sort_params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::start_datatype_declaration(self, sort_params)
    }
    fn end_datatype_declaration(
        &mut self,
        constructors: SmtConstructors<'_, Self>,
    ) -> Result<(), Self::Error> {
        SmtPartialCommandHandler::end_datatype_declaration(self, constructors)
    }
}

/// Handler that checks compliance with SMT-LIB syntax.
///
/// This handler quietly swallows all standard categories and commands.
/// It does not allow any non-standard commands, failing with
/// [`SmtNonstandardCommandError`].
#[derive(Debug, Clone, Copy, Default)]
pub struct SmtSyntaxChecker;

/// Error encountering a nonstandard command.
///
/// Used by [`SmtSyntaxChecker`], which does not
/// support non-standard commands.
#[derive(Debug, Clone)]
pub struct SmtNonstandardCommandError(SmtSymbolBuf);

impl SmtNonstandardCommandError {
    /// Constructs the error for the nonstandard command named `name`.
    pub fn new(name: SmtSymbolBuf) -> Self {
        Self(name)
    }

    /// Returns the name of the nonstandard command.
    pub fn name(&self) -> &SmtSymbolBuf {
        &self.0
    }

    /// Converts into the name of the nonstandard command.
    pub fn into_name(self) -> SmtSymbolBuf {
        self.0
    }
}

impl fmt::Display for SmtNonstandardCommandError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("unsupported nonstandard command ")?;
        write_symbol(f, &self.0)
    }
}

impl Error for SmtNonstandardCommandError {}

impl SmtHandler for SmtSyntaxChecker {
    type Error = SmtNonstandardCommandError;

    type SExpr = ();
    type Attribute = ();
    type Sort = ();
    type Term = ();

    type Scope = ();

    fn set_version(&mut self, _version: SmtVersion) {}

    fn handle_sort(&mut self, _sort: SmtSort<'_, Self>) -> Result<Self::Sort, Self::Error> {
        Ok(())
    }

    #[inline]
    fn handle_term(&mut self, _term: SmtTerm<'_, Self>) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn handle_s_expr(&mut self, _expr: SmtSExpr<'_, Self>) -> Result<Self::SExpr, Self::Error> {
        Ok(())
    }

    fn handle_attribute(
        &mut self,
        _name: SmtKeyword<'_>,
        _value: Option<SmtAttributeValue<'_, Self>>,
    ) -> Result<Self::Attribute, Self::Error> {
        Ok(())
    }

    fn annotate_term(
        &mut self,
        _term: Self::Term,
        _attributes: SmtMultiple<'_, Self::Attribute>,
    ) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_let(&mut self, _bindings: SmtBindings<'_, Self>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_let(
        &mut self,
        _scope: Self::Scope,
        _body: Self::Term,
    ) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _vars: SmtSortedVars<'_, Self>,
    ) -> Result<Self::Scope, Self::Error> {
        Ok(())
    }
    fn end_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _scope: Self::Scope,
        _body: Self::Term,
    ) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_lambda(&mut self, _vars: SmtSortedVars<'_, Self>) -> Result<Self::Scope, Self::Error> {
        Ok(())
    }
    fn end_lambda(
        &mut self,
        _scope: Self::Scope,
        _body: Self::Term,
    ) -> Result<Self::Term, Self::Error> {
        Ok(())
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
        _term: Self::Term,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_match(
        &mut self,
        _scrutinee: Self::Term,
        _cases: SmtMatchCases<'_, Self>,
    ) -> Result<Self::Term, Self::Error> {
        Ok(())
    }
}

impl SmtCommandHandler for SmtSyntaxChecker {
    type NonstandardParser = Infallible;

    fn nonstandard_command(
        &mut self,
        name: SmtSymbol<'_>,
    ) -> Result<Self::NonstandardParser, Self::Error> {
        // reject nonstandard command
        Err(SmtNonstandardCommandError::new(name.into_owned()))
    }

    fn command_echo(&mut self, _value: SmtStringContent<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_option(&mut self, _option: SmtKeyword<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_option(&mut self, _option: Self::Attribute) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_info(&mut self, _keyword: SmtKeyword<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_info(&mut self, _attribute: Self::Attribute) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_logic(&mut self, _logic: SmtSymbol<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_value(
        &mut self,
        _terms: SmtMultiple<'_, Self::Term>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_assertions(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_assignment(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_model(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_proof(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_unsat_assumptions(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_unsat_core(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_sort(
        &mut self,
        _name: SmtSymbol<'_>,
        _arity: SmtNumeral<'_>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_sort_parameter(&mut self, _name: SmtSymbol<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_fun(
        &mut self,
        _name: SmtSymbol<'_>,
        _param_sorts: SmtMultiple<'_, Self::Sort>,
        _result_sort: Self::Sort,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_assert(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_check_sat(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_reset(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_reset_assertions(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_exit(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_push(&mut self, _amount: SmtNumeral<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_pop(&mut self, _amount: SmtNumeral<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_define_sort(
        &mut self,
        _name: SmtSymbol<'_>,
        _params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_define_sort(&mut self, _sort: Self::Sort) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_define_fun(
        &mut self,
        _signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_define_fun(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_define_funs_rec(
        &mut self,
        _signatures: SmtFunctionSignatures<'_, Self>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_recursive_body(
        &mut self,
        _signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_recursive_body(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_define_funs_rec(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_declare_datatypes(&mut self, _sorts: SmtSortArities<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_datatype_declaration(
        &mut self,
        _sort_params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_datatype_declaration(
        &mut self,
        _constructors: SmtConstructors<'_, Self>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_declare_datatypes(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_const(
        &mut self,
        _name: SmtSymbol<'_>,
        _sort: Self::Sort,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_check_sat_assuming(
        &mut self,
        _assumptions: SmtMultiple<'_, Self::Term>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_define_const(
        &mut self,
        _name: SmtSymbol<'_>,
        _sort: Self::Sort,
        _body: Self::Term,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_define_fun_rec(
        &mut self,
        _signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_define_fun_rec(&mut self, _body: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_declare_datatype(
        &mut self,
        _name: SmtSymbol<'_>,
        _params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_declare_datatype(
        &mut self,
        _constructors: SmtConstructors<'_, Self>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
}
