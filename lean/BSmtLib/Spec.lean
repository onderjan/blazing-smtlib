import BSmtLib.Spec.Lexicon
import BSmtLib.Spec.Grammar
import BSmtLib.Spec.Lexer
import BSmtLib.Spec.Parser

/-!
# The specification of SMT-LIB

A formal version of the SMT-LIB standard, versions 2.0, 2.5, 2.6 and 2.7, against which a
lexer and a parser can be proved correct. Its source of truth is the standard itself.

- `Lexicon` and `Grammar` formalise the standard, and depend on no implementation.
- `Lexer` states what a lexer hands over and what it means for a lexer to be correct.
- `Parser` states what a parser of this library hands to its handler.

## How each definition relates to the standard

The documentation of every definition that states a rule or a claim begins with one or more
of these tags. The definitions of the regular-expression formalism, and helpers that state no
rule, carry none.

- **Standard:** formalises the rule of the standard at the place given, by version, section
  and production of Appendix B. A section without a version is the same in every version.
- **Correction:** the standard contradicts itself, and the definition takes the intended rule.
- **Reading:** the standard is silent or ambiguous, and the definition takes the strict
  reading.
- **Extension:** not in the standard; this specification's or this library's own.
- **Scope:** what the definition leaves out of the standard on purpose.
- **Claim:** a statement to be proved, about the specification or about an implementation.

## The named rulings

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
