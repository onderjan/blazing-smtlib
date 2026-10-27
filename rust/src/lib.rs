#![forbid(unsafe_code)]
// The crate page is the README, whose links point to docs.rs so that they work wherever the
// README is shown. Markdown takes the first definition of a link label, so these definitions,
// put before the README, make the crate page link within the crate instead.
#![doc = "[`SmtSyntaxChecker`]: crate::SmtSyntaxChecker"]
#![doc = "[`SmtHandler`]: crate::SmtHandler"]
#![doc = "[`SmtCommandHandler`]: crate::SmtCommandHandler"]
#![doc = "[`read_smt_file`]: crate::read_smt_file"]
#![doc = "[`SmtReader`]: crate::SmtReader"]
#![doc = "[`SmtLexer`]: crate::lexer::SmtLexer"]
#![doc = "[`SmtParse`]: crate::parser::SmtParse"]
#![doc = "[`SmtWriter`]: crate::SmtWriter"]
#![doc = include_str!("../README.md")]

mod handler;
mod reader;
mod version;
mod writer;

pub mod grammar;
pub mod lexer;
pub mod lexicon;
pub mod parser;
pub mod span;
pub mod token;

pub use crate::handler::*;
pub use crate::reader::*;
pub use crate::version::*;
pub use crate::writer::*;
