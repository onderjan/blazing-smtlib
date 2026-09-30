mod category;
mod command;
mod script;

pub use category::*;
pub use command::*;
pub use script::*;

use crate::SmtSpan;

#[derive(Debug)]
pub enum ParserErrorKind<E> {
    Category(CategoryErrorKind),
    Handler(E),
}

#[derive(Debug)]
struct ParserErrorInner<E> {
    kind: ParserErrorKind<E>,
    span: SmtSpan,
}

/// Error emitted by a parser, including the error span.
#[derive(Debug)]
pub struct ParserError<E>(Box<ParserErrorInner<E>>);

impl<E> ParserError<E> {
    #[cold]
    #[inline(never)]
    pub(crate) fn new(kind: ParserErrorKind<E>, span: SmtSpan) -> Self {
        // PERFORMANCE: error kind and span are boxed
        // so that parser results are not unnecessarily large
        // this method boxes them, which forces an allocation
        // so it is is marked cold and never-inline
        Self(Box::new(ParserErrorInner { kind, span }))
    }

    pub(crate) fn handler_error(err: E, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::Handler(err), span)
    }

    pub(crate) fn category_error(err: CategoryErrorKind, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::Category(err), span)
    }

    pub fn kind(&self) -> &ParserErrorKind<E> {
        &self.0.kind
    }

    pub fn span(&self) -> SmtSpan {
        self.0.span
    }

    pub fn into_kind(self) -> ParserErrorKind<E> {
        self.0.kind
    }
}

fn handle_err<O, E>(handled: Result<O, E>, span: SmtSpan) -> Result<O, ParserError<E>> {
    match handled {
        Ok(ok) => Ok(ok),
        Err(err) => Err(ParserError::handler_error(err, span)),
    }
}
