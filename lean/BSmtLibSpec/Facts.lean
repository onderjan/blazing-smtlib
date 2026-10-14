import BSmtLibSpec.Facts.Lexicon
import BSmtLibSpec.Facts.Lexer
import BSmtLibSpec.Facts.Grammar
import BSmtLibSpec.Facts.Parser
import BSmtLibSpec.Facts.Reader

/-!
# Checks of the specification

Proofs that the specification means what it says. They are not part of the specification and
are not trusted.

- Examples: the standard's own examples and lists, of the lexicon and of the grammar, what a
  lexer fed in slices hands over, and the calls the traversal makes for a few scripts.
- The lexicon: every input has at most one tokenisation.
- A lexer fed in slices: what its properties ask for exists, and a lexer that is correct hands
  over more as it is fed more or the end of the input, and is correct on whole inputs.
- Composition: reading can stop at the `)` of a command and start again on the rest, possibly
  in another version.
- A lexer and its consumers: what a lexer does with a consumer is determined, and the input
  after a switch of the version is located as in the whole input.
- Round trips: the tokens of an input can be printed back, exactly with the whitespace and
  comments between them and in a canonical layout without them, and are read back from what is
  printed.
- The grammar: the tokens of a tree determine the tree, and every file has at most one reading,
  from which it is reproduced.
- The traversal: it makes the calls of a parser that goes by the items it receives, its calls
  rebuild the script, and they are placed by the items before them, for every handler.
- Readers: the calls on a file determine the file, and a reader that lexes then parses reads
  files and finishes only on files.
-/
