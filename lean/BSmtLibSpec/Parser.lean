module

public import BSmtLibSpec.Parser.Traversal
public import BSmtLibSpec.Parser.VersionPolicy
public import BSmtLibSpec.Parser.Properties

@[expose] public section

/-!
# Parsers

What a parser of this library hands to its handler for each syntax tree and at which token, the
version policies that restrict the parse of a script, and the properties of the traversal.
None of it is in the standard. An error named in code, such as `UnsupportedVersion`, is the
error of the library's interface that the definition specifies.
-/
