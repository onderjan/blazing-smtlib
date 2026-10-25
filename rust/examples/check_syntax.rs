use std::path::PathBuf;

use blazing_smtlib::{SmtReadErrorCause, SmtSyntaxChecker, read_smt_file};
fn main() -> Result<(), u32> {
    let mut args = std::env::args();
    if args.len() != 2 {
        eprintln!("Usage: check-syntax <SMT-LIB2 file>");
        return Err(1);
    }
    // skip argument 0, it usually contains the name of the executable
    let _executable_name = args.next().unwrap();
    let file_path = args.next().unwrap();

    match read_smt_file(&mut SmtSyntaxChecker, PathBuf::from(file_path)) {
        Err(err) => match err.cause() {
            SmtReadErrorCause::Io(err) => {
                eprintln!("Error reading file: {}", err);
                Err(2)
            }
            SmtReadErrorCause::Lexical(err) => {
                eprintln!("Error lexing file: {:?}", err);
                Err(3)
            }
            SmtReadErrorCause::Syntax(err) => {
                eprintln!("Error parsing file: {:?}", err);
                Err(4)
            }
            SmtReadErrorCause::Version(err) => {
                eprintln!("Unusable version: {:?}", err);
                Err(6)
            }
            SmtReadErrorCause::Handler(err) => {
                eprintln!("Nonstandard command: {:?}", err.name());
                Err(5)
            }
        },

        Ok(()) => {
            eprintln!("Successfully read SMT-LIB file");
            Ok(())
        }
    }
}
