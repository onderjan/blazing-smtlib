use std::{
    fs::File,
    io::{BufReader, Read},
};

use smt_parser_rs::{
    Parser, SmtAttributeValue, SmtFold, SmtFunctionSignature, SmtSExpr, SmtSort, SmtTerm, String8,
    lexer::Lexer,
};

#[derive(Debug)]
struct SyntaxChecker;

impl SmtFold for SyntaxChecker {
    type Error = ();
    type SExpr = ();
    type Attribute = ();
    type Sort = ();
    type Term = ();

    fn fold_s_expr(&mut self, _expr: SmtSExpr<Self::SExpr>) -> Result<Self::SExpr, Self::Error> {
        Ok(())
    }

    fn fold_attribute(
        &mut self,
        _name: String8,
        _value: Option<SmtAttributeValue<Self::SExpr>>,
    ) -> Result<Self::Attribute, Self::Error> {
        Ok(())
    }

    fn fold_sort(&mut self, _sort: SmtSort) -> Result<Self::Sort, Self::Error> {
        Ok(())
    }

    fn fold_term(&mut self, _term: SmtTerm<Self::Term>) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_let(&mut self, _bindings: Vec<(String8, Self::Term)>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_let(&mut self, _term: Self::Term) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn command_echo(&mut self, _echo: String8) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_option(&mut self, _option: String8) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_option(&mut self, _option: Self::Attribute) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_info(&mut self, _keyword: String8) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_info(&mut self, _attribute: Self::Attribute) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_logic(&mut self, _logic: String8) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_const(
        &mut self,
        _name: String8,
        _sort: Self::Sort,
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

    fn start_define_fun(
        &mut self,
        _signature: SmtFunctionSignature<Self::Sort>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_define_fun(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }
}

fn main() -> Result<(), u32> {
    let mut args = std::env::args();
    if args.len() != 2 {
        eprintln!("Usage: check-syntax <SMT-LIB2 file>");
        return Err(1);
    }
    // skip argument 0
    args.next().unwrap();
    let filename = args.next().unwrap();
    let file = match File::open(&filename) {
        Ok(ok) => ok,
        Err(err) => {
            eprintln!("Could not open file {:?}: {}", filename, err);
            return Err(2);
        }
    };

    let mut buf_reader = BufReader::new(file);
    let mut lexer = Lexer::new();
    let mut parser = Parser::new(SyntaxChecker);

    let mut total_bytes = 0;
    let mut c = 0;
    loop {
        match buf_reader.read(std::slice::from_mut(&mut c)) {
            Ok(num_bytes) => {
                if num_bytes == 0 {
                    break;
                }
                assert_eq!(num_bytes, 1);
                total_bytes += num_bytes;
                match lexer.lex_next(c) {
                    Ok(tokens) => {
                        for token in tokens {
                            match parser.parse_token(token) {
                                Ok(()) => {}
                                Err(err) => {
                                    eprintln!("Error parsing file {:?}: {:?}", filename, err);
                                    return Err(4);
                                }
                            }
                        }
                    }
                    Err(err) => {
                        eprintln!("Error lexing file {:?}: {:?}", filename, err);
                        return Err(4);
                    }
                }
            }
            Err(err) => {
                eprintln!("Error reading file {:?}: {}", filename, err);
                return Err(3);
            }
        }
    }

    eprintln!(
        "Successfully read SMT-LIB file {:?} ({} bytes)",
        filename, total_bytes
    );

    Ok(())
}
