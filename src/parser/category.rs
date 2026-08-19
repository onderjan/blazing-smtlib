use std::ops::ControlFlow;

use crate::{SmtHandler, parser::ParserOrHandlerError, token::Token};

pub mod attribute;
pub mod index;
pub mod sort;
pub mod term;

/*
pub trait CategoryParser<H: SmtHandler>
where
    Self: std::marker::Sized,
{
    type Category;

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Category>, ParserOrHandlerError<H>>;
}

pub struct CategoryParserState<H: SmtHandler, C: CategoryParser<H>> {
    pub callback: CommandCallback<H, C::Category>,
    pub state: C,
}

impl<H: SmtHandler, C: CategoryParser<H>> CategoryParserState<H, C> {
    pub fn new(callback: CommandCallback<H, C::Category>, state: C) -> Self {
        Self { callback, state }
    }

    pub fn progress(
        mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<CommandProgress<H>, Self>, ParserOrHandlerError<H>> {
        match self.state.progress(handler, token)? {
            ControlFlow::Continue(()) => Ok(std::ops::ControlFlow::Continue(self)),
            ControlFlow::Break(sort) => Ok(ControlFlow::Break(
                (self.callback)(handler, sort).map_err(ParserOrHandlerError::HandlerError)?,
            )),
        }
    }
}
*/
