import BSmtLib.Spec.Lexicon
import BSmtLib.Spec.Grammar
import BSmtLib.Spec.Lexer
import BSmtLib.Spec.Parser

/-!
# Our reading of the SMT-LIB 2 standard

Our formalised reading of the SMT-LIB standard, versions 2.0, 2.5, 2.6 and 2.7,
against which a lexer and a parser can be proved correct.
Its sources of truth are the specification files of the respective versions.

- `Lexicon` formalises the lexicon (lexical categories, tokens, and tokenisation).
- `Grammar` formalises the grammar for syntactic categories and commands.
  It does not include the syntax of theories, logics, and command responses,
  and considers restrictions for info flags and command options semantic.
- `Lexer` formalises the expected observable behaviour of a lexer under our reading.
- `Parser` formalises the expected observable behaviour of a parser under our reading.

## Version releases

The following standard version releases are followed:
 - Version 2.7: release 2026-09-09.
 - Version 2.6: release 2024-09-20.
 - Version 2.5: release 2015-06-28.
 - Version 2.0: release 2012-09-09.

Notably, reserved words are allowed in S-expressions from 2.6 release 2021-04-02 onwards.
Release 2017-07-18, the first release of 2.6, did not allow them.

## References to the standard

The documentation comments of every definition that is based on the standard
refer to the version of the standard and the relevant section of the specification.
Behaviour that did not change between versions is only referenced to the latest version.

We use the following comments at every definition that states a rule or a property based
on the standard, except where documented otherwise in the file-level documentation comment.

- **Standard:** the definition formalises a rule of the standard at the version and place given,
  and includes the version, section, and the name of production in Appendix B where relevant.
- **Reading:** our decision how to read the standard
  when it is silent, ambiguous, or seemingly contradictory.
- **Divergence:** our intentional divergence from the standard,
  only done in special cases where divergence is the sensible norm.
- **Extension:** our extension of the standard that does not diverge in spirit.
- **Scope:** our decision relevant to the scope of the formalisation.

Additionally, we use the following comment with a defined meaning:

- **Property:** a proposition that can be proven about the formalised reading
  or an implementation against the formalised reading.

## List of readings, divergences, extensions, and scope decisions

- Corrections: **K**, keywords take the 2.0 rule in every version; **F1**, `define-funs-rec`
  is a command name; **F3**, a simple symbol is not a reserved word; **F4**, the letters of
  2.5 Appendix B.
- Readings: **C**, a comment may run to the end of the input; **R1**, a token other than a
  parenthesis is followed by a delimiter; **S**, white space in 2.0 string literals; **P2**,
  any attribute in `set-option` and any keyword in `get-info`; **P3**, reserved words as
  s-expressions from 2.6 on; **P4**, how a version declaration takes effect; **P5**, `exit`
  ends a script.
- Extensions: **D**, a lexer accepts characters from 128 on in 2.0 input; the form of
  handed-over tokens; the version policies; the handler contract.
- Scope: **P1**, scripts only; **P6**, standard commands only.
-/
