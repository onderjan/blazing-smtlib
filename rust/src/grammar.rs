//! SMT-LIB grammar: identifiers, sorts, terms, attributes etc.
//!
//! SMT-LIB grammar encodes an abstract syntax tree. For example, the input
//! `(- (+ a b) c)` read as a term has the meaning of a rooted tree
//! of subterms.
//!
//! ```text
//! a   b   c
//!  \ /   /
//!   +   /
//!    \ /
//!     -
//! ```
//!
//! As **blazing-smtlib** is a streaming library, it never constructs the tree.
//! Instead, [parsers](crate::parser) call handlers that implement
//! [`SmtHandler`](crate::SmtHandler) in post-order traversal through the tree.
//! For the given example, [`SmtTermParser`](crate::parser::SmtTermParser) calls
//! [`SmtHandler::handle_term`](crate::SmtHandler::handle_term) multiple times
//! with the following arguments:
//! 1. [`SmtTerm::QualifiedIdent`] for `a`.
//! 2. [`SmtTerm::QualifiedIdent`] for `b`.
//! 3. [`SmtTerm::Application`] with the function `+` and the 2
//!    [`SmtHandler::Term`](crate::SmtHandler::Term) results returned for `a`
//!    and `b`.
//! 4. [`SmtTerm::QualifiedIdent`] for `c`.
//! 5. [`SmtTerm::Application`] with the function `-` and the 2
//!    [`SmtHandler::Term`](crate::SmtHandler::Term) results returned for
//!    `(+ a b)` and `c`.
//!
//! Other grammar nodes such as `let` and quantifier binders are handled through
//! [`SmtHandler`](crate::SmtHandler) methods of their own.
//!
//! The handler could construct the abstract syntax tree from the traversal, but
//! does not have to: it can act on the terms as they come, improving speed and
//! lowering memory consumption.
//!
//! The types in this module are views into the grammar nodes seen by the
//! handler (the node has information only about itself and the result values
//! for its already handled children), their owned versions, and iterators over
//! them. The types are generic over the trait
//! [`SmtNodeTypes`](crate::SmtNodeTypes) that defines the handled sort, term
//! and S-expression types and is blanket-implemented for every
//! [`SmtHandler`](crate::SmtHandler).

mod multiple;
mod nodes;

pub use multiple::*;
pub use nodes::*;
