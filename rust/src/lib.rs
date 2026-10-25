#![forbid(unsafe_code)]
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
