use std::ops::ControlFlow;

use crate::{SmtHandler, parser::ParserOrHandlerError, token::Token};

pub mod attribute;
pub mod index;
pub mod sort;
pub mod term;

pub trait CategoryParser<H: SmtHandler>
where
    Self: std::marker::Sized,
{
    type Result;

    fn init() -> Self;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserOrHandlerError<H>>;
}
