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
/// enum Operation { Add, Sub, Eq }
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
///                     b"=" => Operation::Eq,
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
/// // the term ends at byte 29
/// assert_eq!(located_outer_term.location().offset(), 29);
/// // the outer term has index 4
/// assert_eq!(located_outer_term.into_value(), 4);
/// ```
///
/// Commands are handled by [`SmtCommandHandler`], which extends this trait. Its documentation
/// continues the example with a handler of the commands of a script.
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
    /// requires the named term to contain no free variables and the name to be fresh, and allows
    /// `:pattern` only on the body of a quantified term. Library parsers do not check this.
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

/// Handles SMT-LIB commands.
///
/// A command handler is an [`SmtHandler`] that also handles the commands of a script, e.g.
/// [`command_assert`](Self::command_assert) gets the term that the command asserts. Such a
/// method is called once the command has been read to its closing parenthesis.
///
/// A definition or a datatype declaration is handled by a pair of methods instead, e.g.
/// [`start_define_fun`](Self::start_define_fun) and [`end_define_fun`](Self::end_define_fun):
/// the start method is called before the body is handled, so that the handler can bring the
/// parameters into scope, and the end method, like the other methods, once the command has been
/// read to its closing parenthesis. If reading fails within a command, the methods that would
/// follow are not called.
///
/// A command introduced in a later version than the one in force is not standard: its name is
/// a symbol, so it is handled by [`nonstandard_command`](Self::nonstandard_command).
///
/// For only implementing a partial list of SMT-LIB commands, [`SmtPartialCommandHandler`]
/// can be used: it is a command handler that fails on unimplemented commands with
/// [`SmtPartialCommandError::Unsupported`].
///
/// The example below continues the [`SmtHandler`] example: the term handler becomes a partial
/// command handler for a solver of integer arithmetic, which implements `set-logic`,
/// `declare-const`, `assert` and `check-sat`, and the nonstandard command `minimize`.
///
/// ```
/// # use std::collections::HashMap;
/// #
/// # use blazing_smtlib::{
/// #     SmtHandler, SmtPartialCommandError, SmtPartialCommandHandler, SmtReadErrorKind,
/// #     SmtVersion,
/// #     grammar::{
/// #         SmtAttributeValue, SmtBindings, SmtIdent, SmtMatchCases, SmtMultiple, SmtPattern,
/// #         SmtQualifiedIdent, SmtQuantifierKind, SmtSExpr, SmtSort, SmtSortedVars,
/// #         SmtSpecialConstant, SmtTerm,
/// #     },
/// #     lexicon::{SmtBytesBuf, SmtCommandNameReserved, SmtKeyword, SmtSymbol},
/// #     parser::{SmtClosedParser, SmtCommandPayloadParser, SmtCommandRule, SmtTermParser},
/// #     read_smt,
/// # };
/// #
/// # #[derive(Debug)]
/// # enum TermHandlerError { Unsupported, NonUniqueBindings }
/// #
/// # #[derive(Debug, PartialEq, Eq)]
/// # enum Operation { Add, Sub, Eq }
/// #
/// # #[derive(Debug, PartialEq, Eq)]
/// # enum Term {
/// #     Constant(u64),
/// #     Variable(SmtBytesBuf),
/// #     Operation(Operation, Vec<usize>),
/// # }
/// #
/// struct TermHandler {
///     terms: Vec<Term>,
///     mappings: HashMap<SmtBytesBuf, usize>,
///     // added for the commands
///     constants: Vec<SmtBytesBuf>,
///     assertions: Vec<usize>,
///     checks: usize,
///     objectives: Vec<usize>,
/// }
///
/// impl SmtHandler for TermHandler {
///     // a partial command handler also fails on the commands it does not implement
///     type Error = SmtPartialCommandError<TermHandlerError>;
///
///     // ... as in the `SmtHandler` example, with the errors converted by `into()` ...
/// #     type SExpr = ();
/// #     type Attribute = ();
/// #     type Sort = ();
/// #     type Term = usize;
/// #
/// #     type Scope = HashMap<SmtBytesBuf, Option<usize>>;
/// #
/// #     fn set_version(&mut self, _version: SmtVersion) {
/// #         // no version-dependent semantics
/// #     }
/// #
/// #     fn handle_sort(&mut self, sort: SmtSort<'_, Self>) -> Result<Self::Sort, Self::Error> {
/// #         if sort.ident.name.bytes().as_slice() == b"Int"
/// #             && sort.ident.indices.is_empty()
/// #             && sort.args.is_empty()
/// #         {
/// #             Ok(())
/// #         } else {
/// #             Err(TermHandlerError::Unsupported.into())
/// #         }
/// #     }
/// #
/// #     fn handle_term(&mut self, term: SmtTerm<'_, Self>) -> Result<Self::Term, Self::Error> {
/// #         let term = match term {
/// #             SmtTerm::SpecialConstant(SmtSpecialConstant::Numeral(numeral)) => {
/// #                 Term::Constant(numeral.to_u64().ok_or(TermHandlerError::Unsupported)?)
/// #             }
/// #             SmtTerm::QualifiedIdent(SmtQualifiedIdent {
/// #                 ident: SmtIdent { name, indices },
/// #                 sort: None,
/// #             }) if indices.is_empty() => {
/// #                 let name = name.bytes();
/// #                 // a variable bound by a let stands for the term it is bound to
/// #                 if let Some(&index) = self.mappings.get(name.as_slice()) {
/// #                     return Ok(index);
/// #                 }
/// #                 Term::Variable(name.into_owned())
/// #             }
/// #             SmtTerm::Application(application) => {
/// #                 let (function, args) = application.into_parts();
/// #                 if !function.ident.indices.is_empty() || function.sort.is_some() {
/// #                     return Err(TermHandlerError::Unsupported.into());
/// #                 }
/// #                 let op = match function.ident.name.bytes().as_slice() {
/// #                     b"+" => Operation::Add,
/// #                     b"-" => Operation::Sub,
/// #                     b"=" => Operation::Eq,
/// #                     _ => return Err(TermHandlerError::Unsupported.into()),
/// #                 };
/// #                 // the arguments are term indices that have already been handled
/// #                 Term::Operation(op, args.into_iter().collect())
/// #             }
/// #             _ => return Err(TermHandlerError::Unsupported.into()),
/// #         };
/// #         let index = self.terms.len();
/// #         self.terms.push(term);
/// #         Ok(index)
/// #     }
/// #
/// #     fn handle_s_expr(
/// #         &mut self,
/// #         _expr: SmtSExpr<'_, Self>,
/// #     ) -> Result<Self::SExpr, Self::Error> {
/// #         Err(TermHandlerError::Unsupported.into())
/// #     }
/// #
/// #     fn start_let(
/// #         &mut self,
/// #         bindings: SmtBindings<'_, Self>,
/// #     ) -> Result<Self::Scope, Self::Error> {
/// #         // put the bindings in the symbol map and remember the replaced bindings
/// #         let mut shadowed = HashMap::new();
/// #         for (name, term) in bindings {
/// #             let name = name.bytes().into_owned();
/// #             if shadowed.contains_key(&name) {
/// #                 // SMT-LIB prohibits binding a variable twice in one let
/// #                 return Err(TermHandlerError::NonUniqueBindings.into());
/// #             }
/// #             let previous = self.mappings.insert(name.clone(), term);
/// #             shadowed.insert(name, previous);
/// #         }
/// #         // the previous bindings form the scope that will be given to `end_let`
/// #         Ok(shadowed)
/// #     }
/// #
/// #     fn end_let(
/// #         &mut self,
/// #         scope: Self::Scope,
/// #         body: Self::Term,
/// #     ) -> Result<Self::Term, Self::Error> {
/// #         // restore the previous symbol map from the previous bindings
/// #         for (name, term) in scope {
/// #             match term {
/// #                 Some(term) => {
/// #                     // replace with a shadowed binding
/// #                     self.mappings.insert(name, term);
/// #                 }
/// #                 None => {
/// #                     // no binding was present, remove it
/// #                     self.mappings.remove(&name);
/// #                 }
/// #             }
/// #         }
/// #         Ok(body)
/// #     }
/// #
/// #     // ... attributes, annotations, quantifiers, lambda, match returning unsupported ...
/// #
/// #     fn handle_attribute(
/// #         &mut self,
/// #         _name: SmtKeyword<'_>,
/// #         _value: Option<SmtAttributeValue<'_, Self>>,
/// #     ) -> Result<Self::Attribute, Self::Error> {
/// #         Err(TermHandlerError::Unsupported.into())
/// #     }
/// #
/// #     fn annotate_term(
/// #         &mut self,
/// #         _term: Self::Term,
/// #         _attributes: SmtMultiple<'_, Self::Attribute>,
/// #     ) -> Result<Self::Term, Self::Error> {
/// #         Err(TermHandlerError::Unsupported.into())
/// #     }
/// #
/// #     fn start_quantifier(
/// #         &mut self,
/// #         _kind: SmtQuantifierKind,
/// #         _vars: SmtSortedVars<'_, Self>,
/// #     ) -> Result<Self::Scope, Self::Error> {
/// #         Err(TermHandlerError::Unsupported.into())
/// #     }
/// #
/// #     fn end_quantifier(
/// #         &mut self,
/// #         _kind: SmtQuantifierKind,
/// #         _scope: Self::Scope,
/// #         _body: Self::Term,
/// #     ) -> Result<Self::Term, Self::Error> {
/// #         Err(TermHandlerError::Unsupported.into())
/// #     }
/// #
/// #     fn start_lambda(
/// #         &mut self,
/// #         _vars: SmtSortedVars<'_, Self>,
/// #     ) -> Result<Self::Scope, Self::Error> {
/// #         Err(TermHandlerError::Unsupported.into())
/// #     }
/// #
/// #     fn end_lambda(
/// #         &mut self,
/// #         _scope: Self::Scope,
/// #         _body: Self::Term,
/// #     ) -> Result<Self::Term, Self::Error> {
/// #         Err(TermHandlerError::Unsupported.into())
/// #     }
/// #
/// #     fn start_match(&mut self, _scrutinee: &Self::Term) -> Result<(), Self::Error> {
/// #         Err(TermHandlerError::Unsupported.into())
/// #     }
/// #
/// #     fn start_match_case(
/// #         &mut self,
/// #         _scrutinee: &Self::Term,
/// #         _pattern: SmtPattern<'_>,
/// #     ) -> Result<Self::Scope, Self::Error> {
/// #         Err(TermHandlerError::Unsupported.into())
/// #     }
/// #
/// #     fn end_match_case(
/// #         &mut self,
/// #         _scope: Self::Scope,
/// #         _scrutinee: &Self::Term,
/// #         _term: Self::Term,
/// #     ) -> Result<Self::Term, Self::Error> {
/// #         Err(TermHandlerError::Unsupported.into())
/// #     }
/// #
/// #     fn end_match(
/// #         &mut self,
/// #         _scrutinee: Self::Term,
/// #         _cases: SmtMatchCases<'_, Self>,
/// #     ) -> Result<Self::Term, Self::Error> {
/// #         Err(TermHandlerError::Unsupported.into())
/// #     }
/// }
///
/// // the rule of the nonstandard command `(minimize t)`
/// #[derive(Default)]
/// struct Minimize;
///
/// impl SmtCommandRule<TermHandler> for Minimize {
///     // the payload is a term and the closing parenthesis of the command
///     type Parser = SmtClosedParser<TermHandler, SmtTermParser<TermHandler>>;
///
///     fn handle(
///         &mut self,
///         handler: &mut TermHandler,
///         term: usize,
///     ) -> Result<(), SmtPartialCommandError<TermHandlerError>> {
///         handler.objectives.push(term);
///         Ok(())
///     }
/// }
///
/// impl SmtPartialCommandHandler for TermHandler {
///     type HandlerError = TermHandlerError;
///     type NonstandardParser = SmtCommandPayloadParser<TermHandler, Minimize>;
///
///     fn nonstandard_command(
///         &mut self,
///         name: SmtSymbol<'_>,
///     ) -> Result<Self::NonstandardParser, Self::Error> {
///         if name.bytes().as_slice() == b"minimize" {
///             Ok(SmtCommandPayloadParser::default())
///         } else {
///             Err(SmtPartialCommandError::UnsupportedNonstandard(
///                 name.into_owned(),
///             ))
///         }
///     }
///
///     fn command_set_logic(&mut self, logic: SmtSymbol<'_>) -> Result<(), Self::Error> {
///         // only quantifier-free linear integer arithmetic
///         if logic.bytes().as_slice() == b"QF_LIA" {
///             Ok(())
///         } else {
///             Err(TermHandlerError::Unsupported.into())
///         }
///     }
///
///     fn command_declare_const(
///         &mut self,
///         name: SmtSymbol<'_>,
///         _sort: Self::Sort,
///     ) -> Result<(), Self::Error> {
///         // the sort is `Int`, as `handle_sort` refuses the others
///         self.constants.push(name.bytes().into_owned());
///         Ok(())
///     }
///
///     fn command_assert(&mut self, term: Self::Term) -> Result<(), Self::Error> {
///         self.assertions.push(term);
///         Ok(())
///     }
///
///     fn command_check_sat(&mut self) -> Result<(), Self::Error> {
///         // a solver would check the assertions here
///         self.checks += 1;
///         Ok(())
///     }
/// }
///
/// let script = b"
///     (set-logic QF_LIA)
///     (declare-const a Int)
///     (declare-const c Int)
///     (assert (let ((b 5)) (= (- (+ a b b) c) 0)))
///     (minimize c)
///     (check-sat)
///     (get-model)
/// ";
/// let mut handler = TermHandler {
///     terms: Vec::new(),
///     mappings: HashMap::new(),
///     constants: Vec::new(),
///     assertions: Vec::new(),
///     checks: 0,
///     objectives: Vec::new(),
/// };
/// let error = read_smt(&mut handler, &script[..]).unwrap_err();
/// // the script is handled up to `get-model`, which the handler does not implement
/// assert!(matches!(
///     error.kind(),
///     SmtReadErrorKind::Handler(SmtPartialCommandError::Unsupported(
///         SmtCommandNameReserved::GetModel
///     ))
/// ));
/// assert_eq!(handler.constants.len(), 2);
/// // the equality is the term with index 6, after `0` with index 5
/// assert_eq!(handler.assertions, vec![6]);
/// // `c` is the term with index 7
/// assert_eq!(handler.objectives, vec![7]);
/// assert_eq!(handler.checks, 1);
/// ```
pub trait SmtCommandHandler: SmtHandler {
    /// Parses the tokens after the name of a nonstandard command, up to and including its closing
    /// parenthesis.
    ///
    /// An example is an [`SmtCommandPayloadParser`](crate::parser::SmtCommandPayloadParser)
    /// with a rule whose parser is an [`SmtClosedParser`](crate::parser::SmtClosedParser). A
    /// handler that refuses every nonstandard command can use
    /// [`Infallible`](std::convert::Infallible).
    type NonstandardParser: SmtParse<Self, Result = ()>;

    /// Returns a parser that parses a nonstandard command with the given name.
    ///
    /// A command is nonstandard if its name is a symbol rather than the reserved word of a
    /// standard command. This includes a quoted symbol spelled like one, e.g. `|assert|`, and
    /// the name of a command introduced in a later version than the one in force, e.g.
    /// `define-const` before SMT-LIB 2.7.
    fn nonstandard_command(
        &mut self,
        name: SmtSymbol<'_>,
    ) -> Result<Self::NonstandardParser, Self::Error>;

    /// Echoes a string (`echo`).
    ///
    /// The string is given with its escapes resolved. SMT-LIB requires the string literal to be
    /// printed back as-is (with its quotation marks and properly escaped), so a handler that
    /// prints it must escape it again.
    ///
    /// The command was introduced in SMT-LIB 2.5.
    fn command_echo(&mut self, value: SmtStringContent<'_>) -> Result<(), Self::Error>;

    /// Gets the value of an option (`get-option`).
    fn command_get_option(&mut self, option: SmtKeyword<'_>) -> Result<(), Self::Error>;
    /// Sets an option (`set-option`).
    fn command_set_option(&mut self, option: Self::Attribute) -> Result<(), Self::Error>;
    /// Gets information (`get-info`).
    fn command_get_info(&mut self, keyword: SmtKeyword<'_>) -> Result<(), Self::Error>;
    /// Sets information (`set-info`).
    ///
    /// When a script is read, a version declaration `(set-info :smt-lib-version …)` is handled
    /// by this method before the version is switched: [`set_version`](SmtHandler::set_version)
    /// follows if the version is accepted, and reading fails otherwise.
    fn command_set_info(&mut self, attribute: Self::Attribute) -> Result<(), Self::Error>;

    /// Sets the logic (`set-logic`).
    fn command_set_logic(&mut self, logic: SmtSymbol<'_>) -> Result<(), Self::Error>;

    /// Gets the values of terms (`get-value`).
    ///
    /// The caller guarantees that there is at least one term.
    ///
    /// SMT-LIB requires the terms to contain no free variables and no quantifiers. Library
    /// parsers do not check this.
    fn command_get_value(&mut self, terms: SmtMultiple<'_, Self::Term>) -> Result<(), Self::Error>;
    /// Gets the assertions (`get-assertions`).
    fn command_get_assertions(&mut self) -> Result<(), Self::Error>;
    /// Gets the values of the named Boolean terms (`get-assignment`).
    fn command_get_assignment(&mut self) -> Result<(), Self::Error>;
    /// Gets the model (`get-model`).
    ///
    /// The command was introduced in SMT-LIB 2.5.
    fn command_get_model(&mut self) -> Result<(), Self::Error>;
    /// Gets a proof (`get-proof`).
    fn command_get_proof(&mut self) -> Result<(), Self::Error>;
    /// Gets an unsatisfiable subset of the assumptions (`get-unsat-assumptions`).
    ///
    /// The command was introduced in SMT-LIB 2.5.
    fn command_get_unsat_assumptions(&mut self) -> Result<(), Self::Error>;
    /// Gets an unsatisfiable core (`get-unsat-core`).
    fn command_get_unsat_core(&mut self) -> Result<(), Self::Error>;

    /// Declares a sort with an arity (`declare-sort`).
    ///
    /// SMT-LIB prohibits the name from being a sort symbol or sort parameter that is already in
    /// the current signature. Library parsers do not check this.
    fn command_declare_sort(
        &mut self,
        name: SmtSymbol<'_>,
        arity: SmtNumeral<'_>,
    ) -> Result<(), Self::Error>;

    /// Declares a global sort parameter (`declare-sort-parameter`).
    ///
    /// SMT-LIB prohibits the name from being a sort symbol, sort parameter or theory symbol that
    /// is already in the current signature. Library parsers do not check this.
    ///
    /// The command was introduced in SMT-LIB 2.7.
    fn command_declare_sort_parameter(&mut self, name: SmtSymbol<'_>) -> Result<(), Self::Error>;

    /// Declares a constant (`declare-const`).
    ///
    /// The command has the same semantic effect as `declare-fun` without parameters, e.g.
    /// `(declare-const c Int)` as `(declare-fun c () Int)`.
    ///
    /// The command was introduced in SMT-LIB 2.5.
    fn command_declare_const(
        &mut self,
        name: SmtSymbol<'_>,
        sort: Self::Sort,
    ) -> Result<(), Self::Error>;

    /// Declares a function (`declare-fun`).
    ///
    /// SMT-LIB prohibits the name from being a function symbol that is already in the current
    /// signature. Library parsers do not check this.
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
    /// The command has the same semantic effect as `check-sat-assuming` without assumptions.
    fn command_check_sat(&mut self) -> Result<(), Self::Error>;

    /// Checks satisfiability with additional assumptions (`check-sat-assuming`).
    ///
    /// The assumptions hold for this check only, together with the assertions. There may be
    /// none.
    ///
    /// The command was introduced in SMT-LIB 2.5. Before SMT-LIB 2.7, an assumption must be
    /// a symbol or its negation, e.g. `p` or `(not p)`: library parsers accept no other term
    /// there, and hand over each assumption as a term.
    fn command_check_sat_assuming(
        &mut self,
        assumptions: SmtMultiple<'_, Self::Term>,
    ) -> Result<(), Self::Error>;

    /// Resets the solver to its initial state (`reset`).
    ///
    /// The command was introduced in SMT-LIB 2.5.
    fn command_reset(&mut self) -> Result<(), Self::Error>;

    /// Empties the assertion stack (`reset-assertions`).
    ///
    /// The command was introduced in SMT-LIB 2.5.
    fn command_reset_assertions(&mut self) -> Result<(), Self::Error>;

    /// Exits the solver (`exit`).
    ///
    /// After calling this method, [`SmtScriptParser`](crate::parser::SmtScriptParser) discards
    /// the rest of the input, so no handler method is called for it.
    fn command_exit(&mut self) -> Result<(), Self::Error>;

    /// Pushes `amount` empty assertion levels onto the assertion stack (`push`).
    ///
    /// If `amount` is `0`, no levels are pushed.
    fn command_push(&mut self, amount: SmtNumeral<'_>) -> Result<(), Self::Error>;

    /// Pops `amount` assertion levels from the assertion stack (`pop`).
    ///
    /// If `amount` is `0`, no levels are popped.
    ///
    /// SMT-LIB requires `amount` to be smaller than the number of assertion levels, as the first
    /// level cannot be popped. Library parsers do not check this.
    fn command_pop(&mut self, amount: SmtNumeral<'_>) -> Result<(), Self::Error>;

    /// Starts a sort definition (`define-sort`).
    ///
    /// The parameters are in scope in the sort that follows, where they shadow the user-declared
    /// sort symbols and sort parameters of the same names, but not the theory sort symbols.
    ///
    /// SMT-LIB prohibits a parameter from being a theory sort symbol, and the name from being a
    /// sort symbol or sort parameter that is already in the current signature. Library parsers
    /// do not check this.
    fn start_define_sort(
        &mut self,
        name: SmtSymbol<'_>,
        params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error>;

    /// Ends a sort definition (`define-sort`).
    ///
    /// SMT-LIB treats a later sort `(s t1 … tn)` of the defined sort symbol `s` as an
    /// abbreviation of this sort, with `t1`, …, `tn` substituted for the parameters.
    fn end_define_sort(&mut self, sort: Self::Sort) -> Result<(), Self::Error>;

    /// Starts a function definition (`define-fun`).
    ///
    /// The parameters are in scope in the body, which is handled between this method and
    /// [`end_define_fun`](Self::end_define_fun). The function itself is not: SMT-LIB prohibits
    /// the body from containing it, and the name from being a function symbol that is already
    /// in the current signature. Library parsers do not check this.
    fn start_define_fun(
        &mut self,
        signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error>;

    /// Defines a constant (`define-const`).
    ///
    /// The command has the same semantic effect as `define-fun` without parameters, e.g.
    /// `(define-const c Int 1)` as `(define-fun c () Int 1)`.
    ///
    /// The command was introduced in SMT-LIB 2.7.
    fn command_define_const(
        &mut self,
        name: SmtSymbol<'_>,
        sort: Self::Sort,
        body: Self::Term,
    ) -> Result<(), Self::Error>;

    /// Ends a function definition (`define-fun`).
    fn end_define_fun(&mut self, term: Self::Term) -> Result<(), Self::Error>;

    /// Starts a recursive function definition (`define-fun-rec`).
    ///
    /// The function and its parameters are in scope in the body, which is handled between this
    /// method and [`end_define_fun_rec`](Self::end_define_fun_rec).
    ///
    /// SMT-LIB prohibits the name from being a function symbol that is already in the current
    /// signature. Library parsers do not check this.
    ///
    /// The command has the same semantic effect as `define-funs-rec` with one function.
    ///
    /// Recursive function definitions were introduced in SMT-LIB 2.5.
    fn start_define_fun_rec(
        &mut self,
        signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error>;

    /// Ends a recursive function definition (`define-fun-rec`).
    ///
    /// Recursive function definitions were introduced in SMT-LIB 2.5.
    fn end_define_fun_rec(&mut self, body: Self::Term) -> Result<(), Self::Error>;

    /// Starts recursive function definitions (`define-funs-rec`).
    ///
    /// The bodies follow in the order of the signatures, each started by
    /// [`start_recursive_body`](Self::start_recursive_body) and ended by
    /// [`end_recursive_body`](Self::end_recursive_body), after which
    /// [`end_define_funs_rec`](Self::end_define_funs_rec) ends the command. The caller
    /// guarantees that there is at least one signature, starts no more bodies than there are
    /// signatures, and ends the command only after one body per signature.
    ///
    /// The functions are in scope in every body, and the parameters of a function in its body.
    ///
    /// SMT-LIB requires the names of the functions to be distinct and prohibits them from being
    /// function symbols that are already in the current signature. Library parsers do not check
    /// this.
    ///
    /// Recursive function definitions were introduced in SMT-LIB 2.5.
    fn start_define_funs_rec(
        &mut self,
        signatures: SmtFunctionSignatures<'_, Self>,
    ) -> Result<(), Self::Error>;

    /// Ends recursive function definitions (`define-funs-rec`).
    ///
    /// Recursive function definitions were introduced in SMT-LIB 2.5.
    fn end_define_funs_rec(&mut self) -> Result<(), Self::Error>;

    /// Starts the body of a recursive function (in `define-funs-rec`).
    ///
    /// Receives the signature of the function whose body follows, the one at the same index in
    /// [`start_define_funs_rec`](Self::start_define_funs_rec), so that the handler can bring its
    /// parameters into scope.
    fn start_recursive_body(
        &mut self,
        signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error>;

    /// Ends the body of a recursive function (in `define-funs-rec`).
    ///
    /// Receives the body of the function whose signature
    /// [`start_recursive_body`](Self::start_recursive_body) received.
    fn end_recursive_body(&mut self, term: Self::Term) -> Result<(), Self::Error>;

    /// Starts a datatype declaration (`declare-datatype`).
    ///
    /// The parameters are those after `par`, and there are none for a declaration without
    /// `par`. The datatype and its parameters are in scope in the selector sorts, which are
    /// handled between this method and [`end_declare_datatype`](Self::end_declare_datatype).
    ///
    /// SMT-LIB prohibits the name from being a sort symbol that is already in the current
    /// signature. Library parsers do not check this.
    ///
    /// The command has the same semantic effect as `declare-datatypes` with one datatype whose
    /// arity is the number of parameters.
    ///
    /// Datatypes were introduced in SMT-LIB 2.6.
    fn start_declare_datatype(
        &mut self,
        name: SmtSymbol<'_>,
        params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error>;

    /// Ends a datatype declaration (`declare-datatype`).
    ///
    /// The constructors are in the order of the input, each with its selectors. The caller
    /// guarantees that there is at least one constructor. For each constructor `c`, SMT-LIB
    /// also declares the tester `(_ is c)`.
    ///
    /// SMT-LIB prohibits the constructors and selectors from being function symbols that are
    /// already in the current signature, which also prohibits repeating one. Library parsers do
    /// not check this.
    ///
    /// Datatypes were introduced in SMT-LIB 2.6.
    fn end_declare_datatype(
        &mut self,
        constructors: SmtConstructors<'_, Self>,
    ) -> Result<(), Self::Error>;

    /// Starts datatype declarations (`declare-datatypes`).
    ///
    /// Receives the name and arity of each datatype, so that every datatype is in scope in every
    /// declaration. The declarations follow in the same order, each started by
    /// [`start_datatype_declaration`](Self::start_datatype_declaration) and ended by
    /// [`end_datatype_declaration`](Self::end_datatype_declaration), after which
    /// [`end_declare_datatypes`](Self::end_declare_datatypes) ends the command. The caller
    /// guarantees that there is at least one datatype, starts no more declarations than there
    /// are datatypes, and ends the command only after one declaration per datatype.
    ///
    /// SMT-LIB prohibits the names of the datatypes from being sort symbols that are already in
    /// the current signature. Library parsers do not check this.
    ///
    /// Datatypes were introduced in SMT-LIB 2.6.
    fn start_declare_datatypes(
        &mut self,
        introductions: SmtSortArities<'_>,
    ) -> Result<(), Self::Error>;

    /// Ends datatype declarations (`declare-datatypes`).
    ///
    /// Datatypes were introduced in SMT-LIB 2.6.
    fn end_declare_datatypes(&mut self) -> Result<(), Self::Error>;

    /// Starts a datatype declaration (in `declare-datatypes`).
    ///
    /// The declaration is of the datatype at the same index in
    /// [`start_declare_datatypes`](Self::start_declare_datatypes). The parameters are those
    /// after `par`, and there are none for a declaration without `par`. They are in scope in the
    /// selector sorts, which are handled between this method and
    /// [`end_datatype_declaration`](Self::end_datatype_declaration).
    ///
    /// SMT-LIB requires a declaration to have `par` with as many parameters as the arity of its
    /// datatype if the arity is positive, and no `par` otherwise. Library parsers do not check
    /// this.
    fn start_datatype_declaration(
        &mut self,
        sort_params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error>;

    /// Ends a datatype declaration (in `declare-datatypes`).
    ///
    /// The constructors are in the order of the input, each with its selectors. The caller
    /// guarantees that there is at least one constructor. For each constructor `c`, SMT-LIB
    /// also declares the tester `(_ is c)`.
    ///
    /// SMT-LIB prohibits the constructors and selectors from being function symbols that are
    /// already in the current signature, which also prohibits repeating one. Library parsers do
    /// not check this.
    fn end_datatype_declaration(
        &mut self,
        constructors: SmtConstructors<'_, Self>,
    ) -> Result<(), Self::Error>;
}

/// Error of a partial command handler (unsupported command or handler error).
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

/// Handles a subset of SMT-LIB commands.
///
/// This trait can be used to implement only a subset of SMT-LIB commands without having to
/// implement the handler methods for the other commands. Every implementation of this trait is
/// also an [`SmtCommandHandler`], and every command that it does not implement fails with
/// [`SmtPartialCommandError::Unsupported`] for a standard command or with
/// [`SmtPartialCommandError::UnsupportedNonstandard`] for a nonstandard command.
///
/// The documentation of [`SmtCommandHandler`] has an example.
pub trait SmtPartialCommandHandler:
    SmtHandler<Error = SmtPartialCommandError<Self::HandlerError>>
{
    /// Error of the handler itself.
    type HandlerError;

    /// Parses the tokens after the name of a nonstandard command, up to and including its closing
    /// parenthesis.
    ///
    /// See [`SmtCommandHandler::NonstandardParser`].
    type NonstandardParser: SmtParse<Self, Result = ()>;

    /// Returns a parser that parses a nonstandard command with the given name.
    ///
    /// See [`SmtCommandHandler::nonstandard_command`].
    fn nonstandard_command(
        &mut self,
        name: SmtSymbol<'_>,
    ) -> Result<Self::NonstandardParser, Self::Error> {
        Err(SmtPartialCommandError::UnsupportedNonstandard(
            name.into_owned(),
        ))
    }

    /// Echoes a string (`echo`).
    ///
    /// See [`SmtCommandHandler::command_echo`].
    fn command_echo(&mut self, _value: SmtStringContent<'_>) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::Echo)
    }

    /// Gets the value of an option (`get-option`).
    ///
    /// See [`SmtCommandHandler::command_get_option`].
    fn command_get_option(&mut self, _option: SmtKeyword<'_>) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetOption)
    }
    /// Sets an option (`set-option`).
    ///
    /// See [`SmtCommandHandler::command_set_option`].
    fn command_set_option(&mut self, _option: Self::Attribute) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::SetOption)
    }
    /// Gets information (`get-info`).
    ///
    /// See [`SmtCommandHandler::command_get_info`].
    fn command_get_info(&mut self, _keyword: SmtKeyword<'_>) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetInfo)
    }
    /// Sets information (`set-info`).
    ///
    /// See [`SmtCommandHandler::command_set_info`].
    fn command_set_info(&mut self, _attribute: Self::Attribute) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::SetInfo)
    }

    /// Sets the logic (`set-logic`).
    ///
    /// See [`SmtCommandHandler::command_set_logic`].
    fn command_set_logic(&mut self, _logic: SmtSymbol<'_>) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::SetLogic)
    }

    /// Gets the values of terms (`get-value`).
    ///
    /// See [`SmtCommandHandler::command_get_value`].
    fn command_get_value(
        &mut self,
        _terms: SmtMultiple<'_, Self::Term>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetValue)
    }
    /// Gets the assertions (`get-assertions`).
    ///
    /// See [`SmtCommandHandler::command_get_assertions`].
    fn command_get_assertions(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetAssertions)
    }
    /// Gets the values of the named Boolean terms (`get-assignment`).
    ///
    /// See [`SmtCommandHandler::command_get_assignment`].
    fn command_get_assignment(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetAssignment)
    }
    /// Gets the model (`get-model`).
    ///
    /// See [`SmtCommandHandler::command_get_model`].
    fn command_get_model(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetModel)
    }
    /// Gets a proof (`get-proof`).
    ///
    /// See [`SmtCommandHandler::command_get_proof`].
    fn command_get_proof(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetProof)
    }
    /// Gets an unsatisfiable subset of the assumptions (`get-unsat-assumptions`).
    ///
    /// See [`SmtCommandHandler::command_get_unsat_assumptions`].
    fn command_get_unsat_assumptions(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::GetUnsatAssumptions)
    }
    /// Gets an unsatisfiable core (`get-unsat-core`).
    ///
    /// See [`SmtCommandHandler::command_get_unsat_core`].
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
    ///
    /// See [`SmtCommandHandler::command_declare_fun`].
    fn command_declare_fun(
        &mut self,
        _name: SmtSymbol<'_>,
        _param_sorts: SmtMultiple<'_, Self::Sort>,
        _result_sort: Self::Sort,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DeclareFun)
    }

    /// Asserts a term (`assert`).
    ///
    /// See [`SmtCommandHandler::command_assert`].
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
    ///
    /// See [`SmtCommandHandler::command_reset`].
    fn command_reset(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::Reset)
    }
    /// Empties the assertion stack (`reset-assertions`).
    ///
    /// See [`SmtCommandHandler::command_reset_assertions`].
    fn command_reset_assertions(&mut self) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::ResetAssertions)
    }
    /// Exits the solver (`exit`).
    ///
    /// See [`SmtCommandHandler::command_exit`].
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

    /// Starts a function definition (`define-fun`).
    ///
    /// See [`SmtCommandHandler::start_define_fun`].
    fn start_define_fun(
        &mut self,
        _signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DefineFun)
    }
    /// Ends a function definition (`define-fun`).
    ///
    /// See [`SmtCommandHandler::end_define_fun`].
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
    ///
    /// See [`SmtCommandHandler::start_define_fun_rec`].
    fn start_define_fun_rec(
        &mut self,
        _signature: SmtFunctionSignature<'_, Self>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DefineFunRec)
    }
    /// Ends a recursive function definition (`define-fun-rec`).
    ///
    /// See [`SmtCommandHandler::end_define_fun_rec`].
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
    ///
    /// See [`SmtCommandHandler::start_declare_datatype`].
    fn start_declare_datatype(
        &mut self,
        _name: SmtSymbol<'_>,
        _params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error> {
        unsupported(SmtCommandNameReserved::DeclareDatatype)
    }
    /// Ends a datatype declaration (`declare-datatype`).
    ///
    /// See [`SmtCommandHandler::end_declare_datatype`].
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
/// The checker accepts every node and every standard command, and refuses every nonstandard
/// command with [`SmtNonstandardCommandError`].
#[derive(Debug, Clone, Copy, Default)]
pub struct SmtSyntaxChecker;

/// Error due to a nonstandard command.
///
/// [`SmtSyntaxChecker`] returns it for every nonstandard command.
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
