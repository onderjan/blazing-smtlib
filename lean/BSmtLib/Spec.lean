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

Additionally, we use the following comment with a defined meaning:

- **Property:** a proposition that can be proven about the formalised reading
  or an implementation against the formalised reading. Properties are devised
  by us to formalise expectations about the implementation behaviour under SMT-LIB,
  and to form correctness theorems.

## List of readings

Lexicon:
- **R1**: consecutive non-parenthesis tokens must be separated (maximal-munch not allowed).
- **C**: an unterminated comment at the end of the input is not an error.
- **F4**: a letter is `a` to `z` or `A` to `Z`.
- **F3**: a simple symbol excludes reserved words.
- **K**: a keyword is `:` followed by simple-symbol characters,
         allowing reserved words and leading digits but not an empty continuation.
- **F1**: `define-funs-rec` is a command name (and a reserved word) from 2.5 on.
- **S**: a 2.0 string literal may contain TAB, CR, or LF.
- **D**: the limitation of 2.0 to US-ASCII limits the input, not the lexicon.

Syntactic modes:
- **P4**: a version declaration changes the syntax mode between commands after
  the closing parenthesis of the `set-info` command.
- **P5**: `exit` ends a script; the input after it is not parsed.
- **M3**: `reset` does not return to the initial version.

## Details and reasoning

### Lexicon

**R1**: The standard does not specify how adjacent tokens are separated.
A state-machine lexer that continues a token until it is no longer possible
and then immediately lexes from the normal states (maximal-munch) makes `123abc`
a valid sequence of a numeral `123` followed by a symbol `abc`, the same as `123 abc`.
We believe this is not the intention, so we require separation by parentheses,
comments, or whitespace.

**C**: In §3.1, it is specified that a comment ends with CR or LF, but does not specify
if this end must appear. As this would be a special error condition on comments,
which should fulfil the function of whitespace that has no error conditions,
we do not require the ending line break.

**F4**: In version 2.5 Appendix B, ⟨letter⟩ is written as `A | ··· | A | a | ··· | z`.
We believe this is a typo, and it is fixed in Appendix B of version 2.6 and 2.7.

**F3**: Only Appendix B of 2.7 specifies that a simple symbol is not a reserved word.
The previous versions did so in §3.1 but not in Appendix B. We believe this was a typo.

**K**: From version 2.5, ⟨keyword⟩ is written in Appendix B `:`⟨simple_symbol⟩.
This would forbid a keyword starting with a digit or naming a reserved word.
The standard itself gives an example of `:56` as a keyword, and the restriction
on reserved words is not syntactically necessary. Therefore, we allow leading digits
and reserved words in keywords, but still forbid `:` as a complete token.

**F1**: From 2.5 on, `define-funs-rec` is a command, but is not included in the list
of reserved words in Appendix B. We believe this is an unintentional omission,
as §3.1 makes every command name a reserved word.

**S**: Version 2.0 §3.1 defines a string literal as a sequence of printable ASCII characters.
Quoted symbols are defined using "printable ASCII characters (including space, tab, and
line-breaking characters)". As TAB, CR, and LF are not printable characters in ASCII,
we believe the string-literal printability includes TAB, CR, and LF in 2.0.
In later versions, these are explicitly allowed.

**D**: Version 2.0 §3.1 restricts source files to ASCII. We read this not as a lexical rule
that should be checked by the lexer, but a rule restricting the input: the driver is
responsible for enforcing it if needed, not the lexer. The ASCII rule is syntactically
unnecessary and was removed in later versions.

### Syntactic modes

**P4**: We consider a version declaration using `set-info` command with `:smt-lib-version`
to change the syntactic mode (including lexing) exactly after the closing parenthesis
of the `set-info` command: the command ends first, then the version switch occurs,
then new commands can be read in under a new version declaration.

**P5**: We consider `(exit)` to change the syntactic mode to a mode where all further
bytes are discarded, exactly after the closing parenthesis.

**M3**: We consider `(reset)` to be a reset of the semantic state, not the syntactic mode,
so a previous version declaration using `set-info` is still honoured after reset.

-/
