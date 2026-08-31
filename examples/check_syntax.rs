use std::path::PathBuf;

use smt_parser_rs::{
    CheckStandardSyntax,
    read::{SmtReadErrorKind, read_smt_file},
};
fn main() -> Result<(), u32> {
    let mut args = std::env::args();
    if args.len() != 2 {
        eprintln!("Usage: check-syntax <SMT-LIB2 file>");
        return Err(1);
    }
    // skip argument 0, it usually contains the name of the executable
    let _executable_name = args.next().unwrap();
    let file_path = args.next().unwrap();

    match read_smt_file(&mut CheckStandardSyntax, &PathBuf::from(file_path)) {
        Err(err) => match err.into_kind() {
            SmtReadErrorKind::Io(err) => {
                eprintln!("Error reading file: {}", err);
                Err(2)
            }
            SmtReadErrorKind::Lexer(err) => {
                eprintln!("Error lexing file: {:?}", err);
                Err(3)
            }
            SmtReadErrorKind::Parser(err) => {
                eprintln!("Error parsing file: {:?}", err);
                Err(4)
            }
            SmtReadErrorKind::Handler(err) => {
                eprintln!("Nonstandard command: {:?}", err.0);
                Err(5)
            }
        },

        Ok(()) => {
            eprintln!("Successfully read SMT-LIB file");
            Ok(())
        }
    }
}
