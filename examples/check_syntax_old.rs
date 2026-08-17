use std::path::PathBuf;

use smt_parser_rs::{SmtProcessErrorOld, old::OnlyCheckSyntax, process_smt_file_old};
fn main() -> Result<(), u32> {
    let mut args = std::env::args();
    if args.len() != 2 {
        eprintln!("Usage: check-syntax <SMT-LIB2 file>");
        return Err(1);
    }
    // skip argument 0, it usually contains the name of the executable
    let _executable_name = args.next().unwrap();
    let file_path = args.next().unwrap();

    match process_smt_file_old(OnlyCheckSyntax, &PathBuf::from(file_path)) {
        Err(SmtProcessErrorOld::ReadError(err)) => {
            eprintln!("Error reading file: {}", err);
            Err(2)
        }
        Err(SmtProcessErrorOld::LexerError(err)) => {
            eprintln!("Error lexing file: {:?}", err);
            Err(3)
        }
        Err(SmtProcessErrorOld::ParserError(err)) => {
            eprintln!("Error parsing file: {:?}", err);
            Err(4)
        }
        Ok(OnlyCheckSyntax) => {
            eprintln!("Successfully read SMT-LIB file");
            Ok(())
        }
    }
}
