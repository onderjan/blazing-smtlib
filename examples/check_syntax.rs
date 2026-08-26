use std::path::PathBuf;

use smt_parser_rs::{OnlyCheckSyntax, SmtReadError, read_smt_file};
fn main() -> Result<(), u32> {
    let mut args = std::env::args();
    if args.len() != 2 {
        eprintln!("Usage: check-syntax <SMT-LIB2 file>");
        return Err(1);
    }
    // skip argument 0, it usually contains the name of the executable
    let _executable_name = args.next().unwrap();
    let file_path = args.next().unwrap();

    match read_smt_file(&mut OnlyCheckSyntax, &PathBuf::from(file_path)) {
        Err(SmtReadError::ReadError(err)) => {
            eprintln!("Error reading file: {}", err);
            Err(2)
        }
        Err(SmtReadError::LexerError(err)) => {
            eprintln!("Error lexing file: {:?}", err);
            Err(3)
        }
        Err(SmtReadError::ParserError(err)) => {
            eprintln!("Error parsing file: {:?}", err);
            Err(4)
        }
        Ok(()) => {
            eprintln!("Successfully read SMT-LIB file");
            Ok(())
        }
    }
}
