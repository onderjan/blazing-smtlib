use std::marker::PhantomData;

use crate::SmtHandler;

pub struct QualifiedIdentParser<H: SmtHandler> {
    phantom: PhantomData<H>,
}
