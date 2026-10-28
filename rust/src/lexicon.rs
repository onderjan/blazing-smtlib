//! SMT-LIB lexicon: symbols, reserved words, keywords, numerals, etc.
//!
//! Each lexical category in SMT-LIB is represented by a type that views its
//! content (e.g. [`SmtNumeral`]) and a type that owns its content (e.g.
//! [`SmtNumeralBuf`]), similarly to [`std::path::Path`] and [`std::path::PathBuf`].
//! Words reserved in any version are represented by [`SmtReserved`].
//!
//! Only valid SMT-LIB values can be constructed.
//!
//! ```rust
//! # use blazing_smtlib::{SmtVersion, SmtWriter, SmtWriterConfig, lexicon::*};
//! // valid hexadecimal digits
//! let hex = SmtHexDigits::new(b"CaFE702").unwrap();
//! // not a valid numeral
//! assert_eq!(SmtNumeral::new(b"CaFE702"), Err(SmtDisallowedBytesError));
//!
//! // the value can be written out
//! let mut output = Vec::new();
//! let mut writer = SmtWriter::new(&mut output, SmtWriterConfig::new(SmtVersion::V2_7));
//! writer.write(&hex).unwrap();
//! assert_eq!(output, b"#xCaFE702");
//! ```
//!
//! Invalid symbols are not permitted, but as symbols and reserved words do not
//! carry version information, unquoted symbols can collide with reserved words
//! in some versions.
//!
//! ```rust
//! # use blazing_smtlib::{SmtVersion, SmtWriter, SmtWriterConfig, lexicon::*};
//! // no symbol can contain a pipe, even when quoted
//! assert_eq!(SmtSymbol::new_quoted(b"a|b").err(), Some(SmtDisallowedBytesError));
//!
//! // `lambda` is a reserved word in SMT-LIB 2.7
//! let reserved = SmtReserved::General(SmtGeneralReserved::Lambda);
//! assert!(!reserved.is_in_version(SmtVersion::V2_6));
//! assert!(reserved.is_in_version(SmtVersion::V2_7));
//!
//! // an unquoted symbol can be named `lambda` in SMT-LIB 2.6
//! let lambda = SmtSymbol::new_unquoted(b"lambda").unwrap();
//! assert!(!lambda.is_quoted());
//! assert!(lambda.is_symbol_in(SmtVersion::V2_6));
//! assert!(!lambda.is_symbol_in(SmtVersion::V2_7));
//!
//! // the symbol can be converted to another version
//! // or constructed specifically for it
//! assert!(lambda.into_versioned(SmtVersion::V2_7).is_quoted());
//! let lambda_26 = SmtSymbol::new_in(b"lambda", SmtVersion::V2_6).unwrap();
//! let lambda_27 = SmtSymbol::new_in(b"lambda", SmtVersion::V2_7).unwrap();
//! assert!(!lambda_26.is_quoted());
//! assert!(lambda_27.is_quoted());
//! ```
//!
//! This is not a problem when reading, as the [lexer](crate::lexer) will only
//! give out appropriate [tokens](crate::token) but can be when generating
//! SMT-LIB output or converting between versions. See documentation on
//! [tokens](crate::token) and [`SmtWriter`](crate::SmtWriter) for how collisions
//! between simple symbols and reserved words are handled.
//!
mod bytes;
mod reserved;
mod value;

pub use bytes::*;
pub use reserved::*;
pub use value::*;
