use std::fmt::Debug;

use itertools::Itertools;

use crate::reader::{
    parser::lexer::{LexerError, Token},
    smt::{
        Reserved, SmtApplication, SmtAttributeValue, SmtFunctionSignature, SmtIdent, SmtIndex,
        SmtQualifiedIdent, SmtSExpr, SmtSort, SmtSpecialConstant, SmtTerm, String8,
    },
};

mod char_class;
pub mod lexer;

pub trait SmtFold: Debug {
    type Error: Debug;
    type SExpr: Debug;
    type Attribute: Debug;
    type Sort: Debug;
    type Term: Debug;

    fn fold_s_expr(&mut self, expr: SmtSExpr<Self::SExpr>) -> Result<Self::SExpr, Self::Error>;
    fn fold_attribute(
        &mut self,
        name: String8,
        value: Option<SmtAttributeValue<Self::SExpr>>,
    ) -> Result<Self::Attribute, Self::Error>;
    fn fold_sort(&mut self, sort: SmtSort) -> Result<Self::Sort, Self::Error>;
    fn fold_term(&mut self, term: SmtTerm<Self::Term>) -> Result<Self::Term, Self::Error>;

    fn start_let(&mut self, bindings: Vec<(String8, Self::Term)>) -> Result<(), Self::Error>;
    fn end_let(&mut self, term: Self::Term) -> Result<Self::Term, Self::Error>;

    fn command_echo(&mut self, echo: String8) -> Result<(), Self::Error>;
    fn command_get_option(&mut self, option: String8) -> Result<(), Self::Error>;
    fn command_set_option(&mut self, option: Self::Attribute) -> Result<(), Self::Error>;

    fn command_get_info(&mut self, keyword: String8) -> Result<(), Self::Error>;
    fn command_set_info(&mut self, attribute: Self::Attribute) -> Result<(), Self::Error>;
    fn command_set_logic(&mut self, logic: String8) -> Result<(), Self::Error>;

    fn command_declare_const(&mut self, name: String8, sort: Self::Sort)
    -> Result<(), Self::Error>;
    fn command_assert(&mut self, term: Self::Term) -> Result<(), Self::Error>;
    fn command_check_sat(&mut self) -> Result<(), Self::Error>;

    fn command_reset(&mut self) -> Result<(), Self::Error>;
    fn command_reset_assertions(&mut self) -> Result<(), Self::Error>;
    fn command_exit(&mut self) -> Result<(), Self::Error>;

    fn start_define_fun(
        &mut self,
        signature: SmtFunctionSignature<Self::Sort>,
    ) -> Result<(), Self::Error>;
    fn end_define_fun(&mut self, term: Self::Term) -> Result<(), Self::Error>;
}

#[allow(dead_code)]
#[derive(Debug)]
pub enum ParserError<E: Debug> {
    LexerError(LexerError),
    FolderError(E),
    ExpectedToken(Token),
    ExpectedUnderscore,
    ExpectedSymbol,
    ExpectedKeyword,
    EmptyIdentIndices,
    InvalidIdent,
    InvalidAttributeValue,
    EmptyApplication,
    EmptyLetBindings,
    ExpectedIndexOrCloseParen,
    ExpectedApplicationOrBinder,
    ExpectedSExpr,
    ExpectedSort,
    ExpectedSortInner,
    ExpectedTerm,
    ExpectedCommand,
    ExpectedCommandName,
    UnsupportedCommand,
    SortApplicationNotSupported,
    ExpectedLetBinding,
}

#[derive(Debug)]
enum UnprocessedCommand {
    Echo,
    GetOption,
    SetOption,
    GetInfo,
    SetInfo,
    SetLogic,
    DeclareConst,
    DefineFun,
    Assert,
    CheckSat,
    Reset,
    ResetAssertions,
    Exit,
}

#[derive(Debug)]
struct SExprRest {
    start: usize,
    attribute: bool,
}

#[derive(Debug)]
enum IndexedIdentOuter {
    None,
    Sort,
    Term,
}

#[derive(Debug)]
struct IndexedIdentRest {
    name: String8,
    indices: Vec<SmtIndex>,
    outer: IndexedIdentOuter,
}

#[derive(Debug)]
enum Unprocessed {
    ParenOpen,
    ParenClose,
    Symbol,
    Keyword,
    String,
    IndexedIdentUnderscore,
    IndexedIdentName(IndexedIdentOuter),
    IndexedIdentRest(IndexedIdentRest),
    SExprRest(SExprRest),
    Attribute,
    AttributeValue,
    Sort,
    SortOrIdentInner,
    DefineFunVars,
    DefineFunTerm(usize),
    Term,
    Application,
    ApplicationRest(usize),
    LetBindings(usize),
    LetEnd,
    Command,
    CommandEnd(UnprocessedCommand),
}

#[derive(Debug)]
enum Processed<F: SmtFold> {
    Symbol(String8),
    Keyword(String8),
    String(String8),
    Ident(SmtIdent),
    AttributeName(String8),
    SExpr(F::SExpr),
    Attribute(F::Attribute),
    Sort(F::Sort),
    Term(F::Term),
}

pub struct Parser<F: SmtFold> {
    folder: F,
    unprocessed: Vec<Unprocessed>,
    processed: Vec<Processed<F>>,
}

impl<F: SmtFold> Parser<F> {
    pub fn new(folder: F) -> Self {
        Self {
            folder,
            unprocessed: Vec::new(),
            processed: Vec::new(),
        }
    }

    pub fn folder(&self) -> &F {
        &self.folder
    }

    pub fn folder_mut(&mut self) -> &mut F {
        &mut self.folder
    }

    fn expand_s_expr(&mut self, token: Token) -> Result<(), ParserError<F::Error>> {
        let expr = match token {
            Token::ParenOpen => {
                self.unprocessed.push(Unprocessed::SExprRest(SExprRest {
                    start: self.processed.len(),
                    attribute: false,
                }));
                return Ok(());
            }
            Token::Symbol(name) => SmtSExpr::Symbol(name),
            Token::Reserved(reserved) => SmtSExpr::Reserved(reserved),
            Token::Keyword(keyword) => SmtSExpr::Keyword(keyword),
            _ => {
                let Ok(constant) = special_constant(token) else {
                    return Err(ParserError::ExpectedSExpr);
                };
                SmtSExpr::SpecialConstant(constant)
            }
        };
        let expr = self
            .folder
            .fold_s_expr(expr)
            .map_err(ParserError::FolderError)?;
        self.processed.push(Processed::SExpr(expr));
        Ok(())
    }

    fn expand_attribute(&mut self, token: Token) -> Result<(), ParserError<F::Error>> {
        let Token::Keyword(keyword) = token else {
            return Err(ParserError::ExpectedKeyword);
        };

        self.processed.push(Processed::AttributeName(keyword));
        self.unprocessed.push(Unprocessed::AttributeValue);
        Ok(())
    }

    fn expand_sort(&mut self, token: Token) -> Result<(), ParserError<F::Error>> {
        match token {
            Token::ParenOpen => {
                // the rest of sort or ident
                self.unprocessed.extend([Unprocessed::SortOrIdentInner]);
            }
            Token::Symbol(name) => {
                // just the identifier
                let sort = SmtSort::Ident(SmtIdent::simple(name));
                let sort = self
                    .folder
                    .fold_sort(sort)
                    .map_err(ParserError::FolderError)?;
                self.processed.push(Processed::Sort(sort));
            }
            _ => return Err(ParserError::ExpectedSort),
        }
        Ok(())
    }

    fn process_indexed_ident_rest(
        &mut self,
        mut rest: IndexedIdentRest,
        token: Token,
    ) -> Result<(), ParserError<F::Error>> {
        match token {
            Token::Numeral(whole) => {
                // numeral index
                rest.indices.push(SmtIndex::Numeral(whole));
            }
            Token::Symbol(symbol) => {
                rest.indices.push(SmtIndex::Symbol(symbol));
            }
            Token::ParenClose => {
                let ident = SmtIdent {
                    name: rest.name,
                    indices: rest.indices,
                };
                match rest.outer {
                    IndexedIdentOuter::None => {
                        self.processed.push(Processed::Ident(ident));
                    }
                    IndexedIdentOuter::Sort => {
                        let sort = self
                            .folder
                            .fold_sort(SmtSort::Ident(ident))
                            .map_err(ParserError::FolderError)?;
                        self.processed.push(Processed::Sort(sort));
                    }
                    IndexedIdentOuter::Term => {
                        let term = self
                            .folder
                            .fold_term(SmtTerm::QualifiedIdent(SmtQualifiedIdent::Ident(ident)))
                            .map_err(ParserError::FolderError)?;
                        self.processed.push(Processed::Term(term));
                    }
                }
                return Ok(());
            }

            _ => return Err(ParserError::ExpectedIndexOrCloseParen),
        }
        self.unprocessed.push(Unprocessed::IndexedIdentRest(rest));
        Ok(())
    }

    fn process_sort_or_ident_inner(&mut self, token: Token) -> Result<(), ParserError<F::Error>> {
        match token {
            Token::Reserved(Reserved::Underscore) => {
                // the sort is given by an indexed ident
                self.unprocessed
                    .push(Unprocessed::IndexedIdentName(IndexedIdentOuter::Sort));
                Ok(())
            }
            _ => Err(ParserError::ExpectedSortInner),
        }
    }

    fn process_indexed_ident_underscore(
        &mut self,
        token: Token,
    ) -> Result<(), ParserError<F::Error>> {
        expect_token::<F>(token, Token::Reserved(Reserved::Underscore))?;
        self.unprocessed
            .push(Unprocessed::IndexedIdentName(IndexedIdentOuter::None));
        Ok(())
    }

    fn process_indexed_ident_name(
        &mut self,
        outer: IndexedIdentOuter,
        token: Token,
    ) -> Result<(), ParserError<F::Error>> {
        let Token::Symbol(name) = token else {
            return Err(ParserError::ExpectedSymbol);
        };
        self.unprocessed
            .push(Unprocessed::IndexedIdentRest(IndexedIdentRest {
                name,
                indices: Vec::new(),
                outer,
            }));
        Ok(())
    }

    fn process_s_expr_rest(
        &mut self,
        rest: SExprRest,
        token: Token,
    ) -> Result<(), ParserError<F::Error>> {
        if matches!(token, Token::ParenClose) {
            // end s-expr
            let mut exprs = Vec::new();
            for expr in self.processed.drain(rest.start..) {
                let Processed::SExpr(expr) = expr else {
                    panic!("Expected SExpr to contain SExprs")
                };
                exprs.push(expr);
            }
            if rest.attribute {
                let Processed::AttributeName(name) = self
                    .processed
                    .pop()
                    .expect("Attribute name should be present")
                else {
                    panic!("Attribute name expected");
                };
                let attribute = self
                    .folder
                    .fold_attribute(name, Some(SmtAttributeValue::Exprs(exprs)))
                    .map_err(ParserError::FolderError)?;
                self.processed.push(Processed::Attribute(attribute));
            } else {
                let expr = self
                    .folder
                    .fold_s_expr(SmtSExpr::Exprs(exprs))
                    .map_err(ParserError::FolderError)?;
                self.processed.push(Processed::SExpr(expr));
            }
            Ok(())
        } else {
            self.unprocessed.push(Unprocessed::SExprRest(rest));
            self.expand_s_expr(token)
        }
    }

    fn process_attribute_value(
        &mut self,
        token: Token,
    ) -> Result<Option<Token>, ParserError<F::Error>> {
        let mut enter = |value| {
            let Processed::AttributeName(name) = self
                .processed
                .pop()
                .expect("Attribute name should be present")
            else {
                panic!("Attribute name expected");
            };
            let attribute = self
                .folder
                .fold_attribute(name, Some(value))
                .map_err(ParserError::FolderError)?;
            self.processed.push(Processed::Attribute(attribute));
            Ok(())
        };

        match token {
            Token::ParenOpen => {
                // process value s-exprs
                self.unprocessed.push(Unprocessed::SExprRest(SExprRest {
                    start: self.processed.len(),
                    attribute: true,
                }));
            }
            Token::Symbol(symbol) => enter(SmtAttributeValue::Symbol(symbol))?,
            _ => {
                match special_constant(token) {
                    Ok(constant) => enter(SmtAttributeValue::SpecialConstant(constant))?,
                    Err(token) => {
                        // the attribute value has not been given, return the token
                        return Ok(Some(token));
                    }
                }
            }
        };
        Ok(None)
    }

    fn expand_term(&mut self, token: Token) -> Result<(), ParserError<F::Error>> {
        let term = match token {
            Token::ParenOpen => {
                // expand to inner
                self.unprocessed.push(Unprocessed::Application);
                return Ok(());
            }
            Token::Symbol(name) => {
                // simple ident term
                let qualified = SmtQualifiedIdent::Ident(SmtIdent::simple(name));
                SmtTerm::QualifiedIdent(qualified)
            }
            _ => {
                let Ok(constant) = special_constant(token) else {
                    return Err(ParserError::ExpectedTerm);
                };
                SmtTerm::SpecialConstant(constant)
            }
        };
        let term = self
            .folder
            .fold_term(term)
            .map_err(ParserError::FolderError)?;
        self.processed.push(Processed::Term(term));
        Ok(())
    }

    fn process_application(&mut self, token: Token) -> Result<(), ParserError<F::Error>> {
        match token {
            Token::Symbol(name) => {
                self.unprocessed
                    .push(Unprocessed::ApplicationRest(self.processed.len()));
                self.processed
                    .push(Processed::Ident(SmtIdent::simple(name)));
            }
            Token::Reserved(Reserved::Let) => {
                self.unprocessed.extend([
                    Unprocessed::LetBindings(self.processed.len()),
                    Unprocessed::ParenOpen,
                ]);
            }
            Token::Reserved(Reserved::Underscore) => {
                // this is not an application, but a term containing an indexed ident
                self.unprocessed
                    .push(Unprocessed::IndexedIdentName(IndexedIdentOuter::Term));
            }
            Token::ParenOpen => {
                // this is an application, but the but the first ident is an indexed ident
                self.unprocessed.extend([
                    Unprocessed::ApplicationRest(self.processed.len()),
                    Unprocessed::IndexedIdentUnderscore,
                ]);
            }
            _ => return Err(ParserError::ExpectedApplicationOrBinder),
        }
        Ok(())
    }

    fn process_application_rest(
        &mut self,
        start: usize,
        token: Token,
    ) -> Result<(), ParserError<F::Error>> {
        if matches!(token, Token::ParenClose) {
            // end application term
            let mut terms = Vec::new();

            // the first processed is a qualified identifier
            let mut iter = self.processed.drain(start..);
            let Some(Processed::Ident(ident)) = iter.next() else {
                panic!("Processed should have ident");
            };

            for term in iter {
                let Processed::Term(term) = term else {
                    panic!("Processed should contain terms")
                };
                terms.push(term);
            }
            let term = self
                .folder
                .fold_term(SmtTerm::Application(SmtApplication {
                    qualified: SmtQualifiedIdent::Ident(ident),
                    arguments: terms,
                }))
                .map_err(ParserError::FolderError)?;
            self.processed.push(Processed::Term(term));

            Ok(())
        } else {
            self.unprocessed.push(Unprocessed::ApplicationRest(start));
            self.expand_term(token)
        }
    }

    fn process_let_bindings(
        &mut self,
        start: usize,
        token: Token,
    ) -> Result<(), ParserError<F::Error>> {
        match token {
            Token::ParenOpen => {
                // read a binding
                self.unprocessed.extend([
                    Unprocessed::LetBindings(start),
                    Unprocessed::ParenClose,
                    Unprocessed::Term,
                    Unprocessed::Symbol,
                ]);
            }
            Token::ParenClose => {
                // end and collect bindings
                let mut bindings = Vec::new();
                let mut iter = self.processed.drain(start..);
                while let Some(name) = iter.next() {
                    let Processed::Symbol(name) = name else {
                        panic!("Binding name should be a symbol");
                    };

                    let Some(Processed::Term(term)) = iter.next() else {
                        panic!("Binding should have a term");
                    };
                    bindings.push((name, term));
                }

                self.folder
                    .start_let(bindings)
                    .map_err(ParserError::FolderError)?;

                self.unprocessed
                    .extend([Unprocessed::LetEnd, Unprocessed::Term]);
            }
            _ => return Err(ParserError::ExpectedLetBinding),
        }
        Ok(())
    }

    fn process_let_end(&mut self, token: Token) -> Result<(), ParserError<F::Error>> {
        expect_token::<F>(token, Token::ParenClose)?;
        let Some(Processed::Term(term)) = self.processed.pop() else {
            panic!("Let should have a term");
        };
        let term = self
            .folder
            .end_let(term)
            .map_err(ParserError::FolderError)?;
        self.processed.push(Processed::Term(term));
        Ok(())
    }

    fn process_define_fun_vars(&mut self, token: Token) -> Result<(), ParserError<F::Error>> {
        match token {
            Token::ParenOpen => {
                // read a sorted var
                self.unprocessed.extend([
                    Unprocessed::DefineFunVars,
                    Unprocessed::ParenClose,
                    Unprocessed::Sort,
                    Unprocessed::Symbol,
                ]);
            }
            Token::ParenClose => {
                // just end
            }
            _ => return Err(ParserError::ExpectedLetBinding),
        }
        Ok(())
    }

    fn process_define_fun_term(
        &mut self,
        start: usize,
        token: Token,
    ) -> Result<(), ParserError<F::Error>> {
        // collect the signature: the name symbol, sorted variables, and result sort

        let num_consumed = self.processed.len() - start;
        let num_params = (num_consumed - 2) / 2;
        let mut iter = self.processed.drain(start..);

        let Some(Processed::Symbol(name)) = iter.next() else {
            panic!("Function name should be a symbol");
        };

        let mut parameters = Vec::new();
        for _ in 0..num_params {
            let Some(Processed::Symbol(param_name)) = iter.next() else {
                panic!("Function parameter name should be a symbol");
            };
            let Some(Processed::Sort(param_type)) = iter.next() else {
                panic!("Function parameter type should be a sort");
            };
            parameters.push((param_name, param_type));
        }

        let Ok(Processed::Sort(result_sort)) = iter.exactly_one() else {
            panic!("Function result type should be a sort");
        };

        let signature = SmtFunctionSignature {
            name,
            parameters,
            result_sort,
        };

        self.folder
            .start_define_fun(signature)
            .map_err(ParserError::FolderError)?;

        self.expand_term(token)
    }

    fn expand_command(&mut self, token: Token) -> Result<(), ParserError<F::Error>> {
        let Token::Symbol(command_name) = token else {
            return Err(ParserError::ExpectedCommandName);
        };
        match command_name.0.as_slice() {
            b"echo" => {
                self.unprocessed.extend([
                    Unprocessed::CommandEnd(UnprocessedCommand::Echo),
                    Unprocessed::String,
                ]);
            }
            b"get-option" => {
                self.unprocessed.extend([
                    Unprocessed::CommandEnd(UnprocessedCommand::GetOption),
                    Unprocessed::Keyword,
                ]);
            }
            b"set-option" => {
                self.unprocessed.extend([
                    Unprocessed::CommandEnd(UnprocessedCommand::SetOption),
                    Unprocessed::Attribute,
                ]);
            }
            b"get-info" => {
                self.unprocessed.extend([
                    Unprocessed::CommandEnd(UnprocessedCommand::GetInfo),
                    Unprocessed::Keyword,
                ]);
            }
            b"set-info" => {
                self.unprocessed.extend([
                    Unprocessed::CommandEnd(UnprocessedCommand::SetInfo),
                    Unprocessed::Attribute,
                ]);
            }
            b"set-logic" => {
                self.unprocessed.extend([
                    Unprocessed::CommandEnd(UnprocessedCommand::SetLogic),
                    Unprocessed::Symbol,
                ]);
            }
            b"declare-fun" => {
                // funciton parameters in declarations not supported
                self.unprocessed.extend([
                    Unprocessed::CommandEnd(UnprocessedCommand::DeclareConst),
                    Unprocessed::Sort,
                    Unprocessed::ParenClose,
                    Unprocessed::ParenOpen,
                    Unprocessed::Symbol,
                ]);
            }
            b"define-fun" => {
                self.unprocessed.extend([
                    Unprocessed::CommandEnd(UnprocessedCommand::DefineFun),
                    Unprocessed::DefineFunTerm(self.processed.len()),
                    Unprocessed::Sort,
                    Unprocessed::DefineFunVars,
                    Unprocessed::ParenOpen,
                    Unprocessed::Symbol,
                ]);
            }
            b"declare-const" => {
                self.unprocessed.extend([
                    Unprocessed::CommandEnd(UnprocessedCommand::DeclareConst),
                    Unprocessed::Sort,
                    Unprocessed::Symbol,
                ]);
            }
            b"assert" => {
                self.unprocessed.extend([
                    Unprocessed::CommandEnd(UnprocessedCommand::Assert),
                    Unprocessed::Term,
                ]);
            }
            b"check-sat" => {
                self.unprocessed
                    .push(Unprocessed::CommandEnd(UnprocessedCommand::CheckSat));
            }
            b"reset" => {
                self.unprocessed
                    .push(Unprocessed::CommandEnd(UnprocessedCommand::Reset));
            }
            b"reset-assertions" => {
                self.unprocessed
                    .push(Unprocessed::CommandEnd(UnprocessedCommand::ResetAssertions));
            }
            b"exit" => {
                self.unprocessed
                    .push(Unprocessed::CommandEnd(UnprocessedCommand::Exit));
            }
            _ => return Err(ParserError::UnsupportedCommand),
        };

        Ok(())
    }

    fn process_command_end(
        &mut self,
        command: UnprocessedCommand,
    ) -> Result<(), ParserError<F::Error>> {
        match command {
            UnprocessedCommand::Echo => {
                let Some(Processed::String(echo)) = self.processed.pop() else {
                    panic!("Processed should end with echo string");
                };
                self.folder
                    .command_echo(echo)
                    .map_err(ParserError::FolderError)
            }
            UnprocessedCommand::SetLogic => {
                let Some(Processed::Symbol(logic)) = self.processed.pop() else {
                    panic!("Processed should end with logic symbol");
                };
                self.folder
                    .command_set_logic(logic)
                    .map_err(ParserError::FolderError)
            }
            UnprocessedCommand::GetOption => {
                let Some(Processed::Keyword(option)) = self.processed.pop() else {
                    panic!("Processed should end with keyword");
                };
                self.folder
                    .command_get_option(option)
                    .map_err(ParserError::FolderError)
            }
            UnprocessedCommand::SetOption => {
                let Some(Processed::Attribute(option)) = self.processed.pop() else {
                    panic!("Processed should end with attribute");
                };
                self.folder
                    .command_set_option(option)
                    .map_err(ParserError::FolderError)
            }
            UnprocessedCommand::GetInfo => {
                let Some(Processed::Keyword(info)) = self.processed.pop() else {
                    panic!("Processed should end with keyword");
                };
                self.folder
                    .command_get_info(info)
                    .map_err(ParserError::FolderError)
            }
            UnprocessedCommand::SetInfo => {
                let Some(Processed::Attribute(info)) = self.processed.pop() else {
                    panic!("Processed should end with attribute");
                };
                self.folder
                    .command_set_info(info)
                    .map_err(ParserError::FolderError)
            }
            UnprocessedCommand::DeclareConst => {
                let Some(Processed::Sort(sort)) = self.processed.pop() else {
                    panic!("Processed should end with sort");
                };
                let Some(Processed::Symbol(name)) = self.processed.pop() else {
                    panic!("Processed should end with symbol");
                };
                self.folder
                    .command_declare_const(name, sort)
                    .map_err(ParserError::FolderError)
            }
            UnprocessedCommand::DefineFun => {
                let Some(Processed::Term(term)) = self.processed.pop() else {
                    panic!("Function body should be a term");
                };

                self.folder
                    .end_define_fun(term)
                    .map_err(ParserError::FolderError)
            }
            UnprocessedCommand::Assert => {
                let Some(Processed::Term(term)) = self.processed.pop() else {
                    panic!("Processed should end with term");
                };
                self.folder
                    .command_assert(term)
                    .map_err(ParserError::FolderError)
            }
            UnprocessedCommand::CheckSat => self
                .folder
                .command_check_sat()
                .map_err(ParserError::FolderError),
            UnprocessedCommand::Reset => self
                .folder
                .command_reset()
                .map_err(ParserError::FolderError),
            UnprocessedCommand::ResetAssertions => self
                .folder
                .command_reset_assertions()
                .map_err(ParserError::FolderError),
            UnprocessedCommand::Exit => {
                self.folder.command_exit().map_err(ParserError::FolderError)
            }
        }?;
        assert_eq!(self.processed.len(), 0);
        Ok(())
    }

    pub fn parse_token(&mut self, token: Token) -> Result<(), ParserError<F::Error>> {
        let mut next_token = Some(token);
        while let Some(token) = next_token.take() {
            let Some(current) = self.unprocessed.pop() else {
                // no current unprocessed tokens
                // do nothing on eof, start processing a command on open paren
                match token {
                    Token::ParenOpen => {
                        self.unprocessed.push(Unprocessed::Command);
                        return Ok(());
                    }
                    Token::End => {
                        return Ok(());
                    }
                    _ => return Err(ParserError::ExpectedCommand),
                }
            };

            match current {
                Unprocessed::ParenOpen => expect_token::<F>(token, Token::ParenOpen),
                Unprocessed::ParenClose => expect_token::<F>(token, Token::ParenClose),
                Unprocessed::Symbol => {
                    let Token::Symbol(name) = token else {
                        return Err(ParserError::ExpectedSymbol);
                    };

                    self.processed.push(Processed::Symbol(name));
                    Ok(())
                }
                Unprocessed::Keyword => {
                    let Token::Keyword(name) = token else {
                        return Err(ParserError::ExpectedKeyword);
                    };

                    self.processed.push(Processed::Keyword(name));
                    Ok(())
                }
                Unprocessed::String => {
                    let Token::String(name) = token else {
                        return Err(ParserError::ExpectedSymbol);
                    };

                    self.processed.push(Processed::String(name));
                    Ok(())
                }
                Unprocessed::IndexedIdentUnderscore => self.process_indexed_ident_underscore(token),
                Unprocessed::IndexedIdentName(outer) => {
                    self.process_indexed_ident_name(outer, token)
                }
                Unprocessed::IndexedIdentRest(rest) => self.process_indexed_ident_rest(rest, token),
                Unprocessed::Attribute => self.expand_attribute(token),
                Unprocessed::Sort => self.expand_sort(token),
                Unprocessed::Term => self.expand_term(token),
                Unprocessed::Command => self.expand_command(token),
                Unprocessed::CommandEnd(command) => {
                    expect_token::<F>(token, Token::ParenClose)?;
                    self.process_command_end(command)?;
                    Ok(())
                }
                Unprocessed::SExprRest(start) => self.process_s_expr_rest(start, token),
                Unprocessed::AttributeValue => {
                    if let Some(token) = self.process_attribute_value(token)? {
                        // not processed yet
                        next_token = Some(token);
                    }
                    Ok(())
                }
                Unprocessed::SortOrIdentInner => self.process_sort_or_ident_inner(token),
                Unprocessed::Application => self.process_application(token),
                Unprocessed::ApplicationRest(rest) => self.process_application_rest(rest, token),
                Unprocessed::LetBindings(start) => self.process_let_bindings(start, token),
                Unprocessed::LetEnd => self.process_let_end(token),
                Unprocessed::DefineFunVars => self.process_define_fun_vars(token),
                Unprocessed::DefineFunTerm(start) => self.process_define_fun_term(start, token),
            }?;
        }
        Ok(())
    }
}

fn expect_token<F: SmtFold>(token: Token, expected: Token) -> Result<(), ParserError<F::Error>> {
    if token == expected {
        Ok(())
    } else {
        Err(ParserError::ExpectedToken(expected))
    }
}

fn special_constant(token: Token) -> Result<SmtSpecialConstant, Token> {
    Ok(match token {
        Token::Numeral(whole) => SmtSpecialConstant::Numeral(whole),
        Token::Decimal(decimal) => SmtSpecialConstant::Decimal(decimal),
        Token::Hexadecimal(whole) => SmtSpecialConstant::Hexadecimal(whole),
        Token::Binary(whole) => SmtSpecialConstant::Binary(whole),
        Token::String(string8) => SmtSpecialConstant::String(string8),
        _ => return Err(token),
    })
}
