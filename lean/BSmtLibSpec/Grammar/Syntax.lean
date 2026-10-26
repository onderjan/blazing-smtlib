module

public import BSmtLibSpec.Grammar

@[expose] public section

/-!
# The syntax of each category

The standard's production rules for scripts, in the versions 2.0, 2.5, 2.6 and 2.7. Each
syntactic category has two definitions, one case for each production:

- `tokens`, how a syntax tree of the category is written: the production read from left to
  right, with the tokens of its parts in their places;
- `Valid version`, the conditions that the production puts beside its tokens: that a version
  has it, that a repetition `+` is not empty, that two lists have the same length.

A sequence of tokens is of a category in a version exactly when it is the `tokens` of a tree
of that category that is `Valid` in that version (`IsTerm`, `IsCommand`). A tree is printed the
same in every version; only `Valid` depends on the version.

How each production is written is the standard's; the trees and the split into `tokens` and
`Valid` are how this specification records it.
-/

namespace BSmtLibSpec.Grammar

open BSmtLibSpec.Lexicon
open Regex (Chars chars)

namespace Tree

/-! ## How each category is written -/

/--
The token of a constant.

Standard: 2.7 §3.2; App. B ⟨spec_constant⟩.
-/
def SpecConstant.token : SpecConstant → SyntaxToken
  | .numeral digits => .numeral digits
  | .decimal text => .decimal text
  | .hexadecimal digits => .hexadecimal digits
  | .binary digits => .binary digits
  | .string content => .string content

mutual

/--
The tokens of an s-expression.

Standard: 2.7 §3.2 S-expressions; App. B ⟨s_expr⟩ ::= ⟨spec_constant⟩ | ⟨symbol⟩ | ⟨reserved⟩
| ⟨keyword⟩ | `(` ⟨s_expr⟩∗ `)`.
-/
def SExpr.tokens : SExpr → List SyntaxToken
  | .constant value => [value.token]
  | .symbol name => [.symbol name]
  | .reserved w => [.reserved w]
  | .keyword name => [.keyword name]
  | .list items => paren (SExpr.tokensAll items)

/-- The tokens of s-expressions, one after another. -/
def SExpr.tokensAll : List SExpr → List SyntaxToken
  | [] => []
  | first :: rest => first.tokens ++ SExpr.tokensAll rest

end

/--
The tokens of an index.

Standard: 2.7 §3.3 Identifiers; App. B ⟨index⟩ ::= ⟨numeral⟩ | ⟨symbol⟩.
-/
def Index.tokens : Index → List SyntaxToken
  | .numeral digits => [.numeral digits]
  | .symbol name => [.symbol name]

/--
The tokens of an identifier: the symbol alone if it has no indices.

Standard: 2.7 §3.3 Identifiers; App. B ⟨identifier⟩ ::= ⟨symbol⟩ | `(` `_` ⟨symbol⟩ ⟨index⟩+ `)`.
-/
def Identifier.tokens : Identifier → List SyntaxToken
  | ⟨symbol, []⟩ => [.symbol symbol]
  | ⟨symbol, indices⟩ => paren (word "_" :: .symbol symbol :: indices.flatMap Index.tokens)

mutual

/--
The tokens of a sort: the identifier alone if it has no arguments.

Standard: 2.7 §3.5 Sorts; App. B ⟨sort⟩ ::= ⟨identifier⟩ | `(` ⟨identifier⟩ ⟨sort⟩+ `)`.
-/
def Sort.tokens : «Sort» → List SyntaxToken
  | .mk identifier [] => identifier.tokens
  | .mk identifier arguments => paren (identifier.tokens ++ Sort.tokensAll arguments)

/-- The tokens of sorts, one after another. -/
def Sort.tokensAll : List «Sort» → List SyntaxToken
  | [] => []
  | first :: rest => first.tokens ++ Sort.tokensAll rest

end

/--
The tokens of an attribute value.

Standard: 2.7 §3.4 Attributes; App. B ⟨attribute_value⟩ ::= ⟨spec_constant⟩ | ⟨symbol⟩
| `(` ⟨s_expr⟩∗ `)`.
-/
def AttributeValue.tokens : AttributeValue → List SyntaxToken
  | .constant value => [value.token]
  | .symbol name => [.symbol name]
  | .list items => paren (SExpr.tokensAll items)

/--
The tokens of an attribute.

Standard: 2.7 §3.4 Attributes; App. B ⟨attribute⟩ ::= ⟨keyword⟩ | ⟨keyword⟩ ⟨attribute_value⟩.
-/
def Attribute.tokens : Attribute → List SyntaxToken
  | ⟨keyword, none⟩ => [.keyword keyword]
  | ⟨keyword, some value⟩ => .keyword keyword :: value.tokens

/--
The tokens of a qualified identifier.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨qual_identifier⟩ ::= ⟨identifier⟩
| `(` `as` ⟨identifier⟩ ⟨sort⟩ `)`.
-/
def QualIdentifier.tokens : QualIdentifier → List SyntaxToken
  | .plain identifier => identifier.tokens
  | .as identifier sort => paren (word "as" :: identifier.tokens ++ sort.tokens)

/--
The tokens of a sorted variable.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨sorted_var⟩ ::= `(` ⟨symbol⟩ ⟨sort⟩ `)`.
-/
def SortedVar.tokens : SortedVar → List SyntaxToken
  | ⟨symbol, sort⟩ => paren (.symbol symbol :: sort.tokens)

/--
The token of a symbol or the wildcard.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨pattern⟩, its ⟨symbol⟩ or `_`.
-/
def SymbolOrWildcard.token : SymbolOrWildcard → SyntaxToken
  | .symbol name => .symbol name
  | .wildcard => word "_"

/--
The tokens of a pattern.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨pattern⟩ ::= ⟨symbol_⟩ | `(` ⟨symbol⟩ ⟨symbol_⟩+ `)`.
-/
def Pattern.tokens : Pattern → List SyntaxToken
  | .single symbol => [symbol.token]
  | .constructor head arguments =>
    paren (.symbol head :: arguments.map SymbolOrWildcard.token)

/-- The reserved word of a quantifier. -/
def Quantifier.word : Quantifier → SyntaxToken
  | .«forall» => Grammar.word "forall"
  | .«exists» => Grammar.word "exists"

mutual

/--
The tokens of a term.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨term⟩.
-/
def Term.tokens : Term → List SyntaxToken
  /- ⟨spec_constant⟩ -/
  | .constant value => [value.token]
  /- ⟨qual_identifier⟩ -/
  | .identifier qualified => qualified.tokens
  /- `(` ⟨qual_identifier⟩ ⟨term⟩+ `)` -/
  | .application function arguments => paren (function.tokens ++ Term.tokensAll arguments)
  /- `(` `let` `(` ⟨var_binding⟩+ `)` ⟨term⟩ `)` -/
  | .«let» bindings body =>
    paren (word "let" :: paren (Term.bindingTokens bindings) ++ body.tokens)
  /- `(` `lambda` `(` ⟨sorted_var⟩+ `)` ⟨term⟩ `)` -/
  | .lambda variables body =>
    paren (word "lambda" :: paren (variables.flatMap SortedVar.tokens) ++ body.tokens)
  /- `(` `forall` `(` ⟨sorted_var⟩+ `)` ⟨term⟩ `)`, and the same with `exists` -/
  | .quantified quantifier variables body =>
    paren (quantifier.word :: paren (variables.flatMap SortedVar.tokens) ++ body.tokens)
  /- `(` `match` ⟨term⟩ `(` ⟨match_case⟩+ `)` `)` -/
  | .«match» scrutinee cases =>
    paren (word "match" :: scrutinee.tokens ++ paren (Term.caseTokens cases))
  /- `(` `!` ⟨term⟩ ⟨attribute⟩+ `)` -/
  | .annotated term attributes =>
    paren (word "!" :: term.tokens ++ attributes.flatMap Attribute.tokens)

/-- The tokens of terms, one after another. -/
def Term.tokensAll : List Term → List SyntaxToken
  | [] => []
  | first :: rest => first.tokens ++ Term.tokensAll rest

/--
The tokens of bindings, one after another.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨var_binding⟩ ::= `(` ⟨symbol⟩ ⟨term⟩ `)`.
-/
def Term.bindingTokens : List (Symbol × Term) → List SyntaxToken
  | [] => []
  | (symbol, term) :: rest => paren (.symbol symbol :: term.tokens) ++ Term.bindingTokens rest

/--
The tokens of the cases of a match, one after another.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨match_case⟩ ::= `(` ⟨pattern⟩ ⟨term⟩ `)`.
-/
def Term.caseTokens : List (Pattern × Term) → List SyntaxToken
  | [] => []
  | (pattern, term) :: rest => paren (pattern.tokens ++ term.tokens) ++ Term.caseTokens rest

end

/--
The tokens of a sort declaration.

Standard: 2.7 §3.11 Scripts; App. B ⟨sort_dec⟩ ::= `(` ⟨symbol⟩ ⟨numeral⟩ `)`.
-/
def SortDec.tokens : SortDec → List SyntaxToken
  | ⟨symbol, arity⟩ => paren [.symbol symbol, .numeral arity]

/--
The tokens of a selector declaration.

Standard: 2.7 §3.11 Scripts; App. B ⟨selector_dec⟩ ::= `(` ⟨symbol⟩ ⟨sort⟩ `)`.
-/
def SelectorDec.tokens : SelectorDec → List SyntaxToken
  | ⟨symbol, sort⟩ => paren (.symbol symbol :: sort.tokens)

/--
The tokens of a constructor declaration.

Standard: 2.7 §3.11 Scripts; App. B ⟨constructor_dec⟩ ::= `(` ⟨symbol⟩ ⟨selector_dec⟩∗ `)`.
-/
def ConstructorDec.tokens : ConstructorDec → List SyntaxToken
  | ⟨symbol, selectors⟩ => paren (.symbol symbol :: selectors.flatMap SelectorDec.tokens)

/--
The tokens of a datatype declaration: without `par` if it has no sort parameters.

Standard: 2.7 §3.11 Scripts; App. B ⟨datatype_dec⟩ ::= `(` ⟨constructor_dec⟩+ `)`
| `(` `par` `(` ⟨symbol⟩+ `)` `(` ⟨constructor_dec⟩+ `)` `)`.
-/
def DatatypeDec.tokens : DatatypeDec → List SyntaxToken
  | ⟨[], constructors⟩ => paren (constructors.flatMap ConstructorDec.tokens)
  | ⟨parameters, constructors⟩ =>
    paren (word "par" :: paren (parameters.map .symbol) ++
      paren (constructors.flatMap ConstructorDec.tokens))

/--
The tokens of a function declaration.

Standard: 2.7 §3.11 Scripts; App. B ⟨function_dec⟩ ::= `(` ⟨symbol⟩ `(` ⟨sorted_var⟩∗ `)` ⟨sort⟩
`)`.
-/
def FunctionDec.tokens : FunctionDec → List SyntaxToken
  | ⟨symbol, parameters, result⟩ =>
    paren (.symbol symbol :: paren (parameters.flatMap SortedVar.tokens) ++ result.tokens)

/--
The tokens of a function definition, which has no parentheses of its own.

Standard: 2.7 §3.11 Scripts; App. B ⟨function_def⟩ ::= ⟨symbol⟩ `(` ⟨sorted_var⟩∗ `)` ⟨sort⟩ ⟨term⟩.
-/
def FunctionDef.tokens : FunctionDef → List SyntaxToken
  | ⟨symbol, parameters, result, body⟩ =>
    .symbol symbol :: paren (parameters.flatMap SortedVar.tokens) ++ result.tokens ++ body.tokens

/--
The tokens of a propositional literal.

Standard: 2.5 and 2.6 §3.9 Scripts; App. B ⟨prop_literal⟩ ::= ⟨symbol⟩ | `(` `not` ⟨symbol⟩ `)`.
-/
def PropLiteral.tokens : PropLiteral → List SyntaxToken
  | .positive symbol => [.symbol symbol]
  | .negative negation symbol => paren [.symbol negation, .symbol symbol]

/--
The tokens of a command.

Standard: 2.7 §3.11 Scripts; App. B ⟨command⟩ of each version.
-/
def Command.tokens : Command → List SyntaxToken
  | .assert term => commandTokens "assert" term.tokens
  | .checkSat => commandTokens "check-sat" []
  | .checkSatAssuming terms => commandTokens "check-sat-assuming" (paren (Term.tokensAll terms))
  | .checkSatAssumingLiterals literals =>
    commandTokens "check-sat-assuming" (paren (literals.flatMap PropLiteral.tokens))
  | .declareConst symbol sort => commandTokens "declare-const" (.symbol symbol :: sort.tokens)
  | .declareDatatype symbol datatype =>
    commandTokens "declare-datatype" (.symbol symbol :: datatype.tokens)
  | .declareDatatypes sorts datatypes =>
    commandTokens "declare-datatypes"
      (paren (sorts.flatMap SortDec.tokens) ++ paren (datatypes.flatMap DatatypeDec.tokens))
  | .declareFun symbol parameters result =>
    commandTokens "declare-fun"
      (.symbol symbol :: paren (Sort.tokensAll parameters) ++ result.tokens)
  | .declareSort symbol arity => commandTokens "declare-sort" [.symbol symbol, .numeral arity]
  | .declareSortParameter symbol => commandTokens "declare-sort-parameter" [.symbol symbol]
  | .defineConst symbol sort term =>
    commandTokens "define-const" (.symbol symbol :: sort.tokens ++ term.tokens)
  | .defineFun definition => commandTokens "define-fun" definition.tokens
  | .defineFunRec definition => commandTokens "define-fun-rec" definition.tokens
  | .defineFunsRec declarations bodies =>
    commandTokens "define-funs-rec"
      (paren (declarations.flatMap FunctionDec.tokens) ++ paren (Term.tokensAll bodies))
  | .defineSort symbol parameters sort =>
    commandTokens "define-sort" (.symbol symbol :: paren (parameters.map .symbol) ++ sort.tokens)
  | .echo content => commandTokens "echo" [.string content]
  | .exit => commandTokens "exit" []
  | .getAssertions => commandTokens "get-assertions" []
  | .getAssignment => commandTokens "get-assignment" []
  | .getInfo flag => commandTokens "get-info" [.keyword flag]
  | .getModel => commandTokens "get-model" []
  | .getOption keyword => commandTokens "get-option" [.keyword keyword]
  | .getProof => commandTokens "get-proof" []
  | .getUnsatAssumptions => commandTokens "get-unsat-assumptions" []
  | .getUnsatCore => commandTokens "get-unsat-core" []
  | .getValue terms => commandTokens "get-value" (paren (Term.tokensAll terms))
  | .pop count => commandTokens "pop" [.numeral count]
  | .push count => commandTokens "push" [.numeral count]
  | .reset => commandTokens "reset" []
  | .resetAssertions => commandTokens "reset-assertions" []
  | .setInfo info => commandTokens "set-info" info.tokens
  | .setLogic symbol => commandTokens "set-logic" [.symbol symbol]
  | .setOption option => commandTokens "set-option" option.tokens

/-! ## Which trees each version has -/

mutual

/--
The s-expression is valid: a reserved word is an s-expression from 2.6 on, and only one that
the version reserves.

Standard: 2.7 §3.2 S-expressions; App. B ⟨s_expr⟩: a reserved word is an s-expression from
2.6 release 2021-04-02 on; ⟨reserved⟩ of each version. Reading G1: in 2.0 and 2.5, App. B
⟨s_expr⟩ without ⟨reserved⟩, against the prose of §3.2.
-/
def SExpr.Valid (version : Version) : SExpr → Prop
  | .reserved w =>
    versionAtLeast version .v2_6 ∧
      w ∈ (basicReservedWords version ++ commandNames version).map chars
  | .list items => SExpr.ValidAll version items
  | _ => True

/-- The s-expressions are each valid. -/
def SExpr.ValidAll (version : Version) : List SExpr → Prop
  | [] => True
  | first :: rest => first.Valid version ∧ SExpr.ValidAll version rest

end

/--
The index is valid: a symbol is an index from 2.5 on.

Standard: 2.7 §3.3 Identifiers; App. B ⟨index⟩ of each version.
-/
def Index.Valid (version : Version) : Index → Prop
  | .numeral _ => True
  | .symbol _ => versionAtLeast version .v2_5

/--
The identifier is valid: its indices are.

Standard: 2.7 §3.3 Identifiers; App. B ⟨identifier⟩.
-/
def Identifier.Valid (version : Version) (identifier : Identifier) : Prop :=
  ∀ index ∈ identifier.indices, index.Valid version

mutual

/--
The sort is valid: its identifier and its arguments are.

Standard: 2.7 §3.5 Sorts; App. B ⟨sort⟩.
-/
def Sort.Valid (version : Version) : «Sort» → Prop
  | .mk identifier arguments => identifier.Valid version ∧ Sort.ValidAll version arguments

/-- The sorts are each valid. -/
def Sort.ValidAll (version : Version) : List «Sort» → Prop
  | [] => True
  | first :: rest => first.Valid version ∧ Sort.ValidAll version rest

end

/--
The attribute value is valid: the items of a list value are.

Standard: 2.7 §3.4 Attributes; App. B ⟨attribute_value⟩.
-/
def AttributeValue.Valid (version : Version) : AttributeValue → Prop
  | .list items => SExpr.ValidAll version items
  | _ => True

/--
The attribute is valid: its value is, if it has one.

Standard: 2.7 §3.4 Attributes; App. B ⟨attribute⟩.
-/
def Attribute.Valid (version : Version) : Attribute → Prop
  | ⟨_, none⟩ => True
  | ⟨_, some value⟩ => value.Valid version

/--
The qualified identifier is valid: its identifier and sort are.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨qual_identifier⟩.
-/
def QualIdentifier.Valid (version : Version) : QualIdentifier → Prop
  | .plain identifier => identifier.Valid version
  | .as identifier sort => identifier.Valid version ∧ sort.Valid version

/--
The sorted variable is valid: its sort is.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨sorted_var⟩.
-/
def SortedVar.Valid (version : Version) (sortedVar : SortedVar) : Prop :=
  sortedVar.sort.Valid version

/--
The symbol or wildcard is valid: the wildcard is allowed from 2.7 on.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨pattern⟩ of each version.
-/
def SymbolOrWildcard.Valid (version : Version) : SymbolOrWildcard → Prop
  | .symbol _ => True
  | .wildcard => versionAtLeast version .v2_7

/--
The pattern is valid: a constructor has at least one argument, and its parts are valid.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨pattern⟩.
-/
def Pattern.Valid (version : Version) : Pattern → Prop
  | .single symbol => symbol.Valid version
  | .constructor _ arguments => arguments ≠ [] ∧ ∀ argument ∈ arguments, argument.Valid version

mutual

/--
The term is valid: its repetitions `+` are not empty, `match` is allowed from 2.6 on and
`lambda` from 2.7 on, and its parts are valid.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨term⟩ of each version.
-/
def Term.Valid (version : Version) : Term → Prop
  | .constant _ => True
  | .identifier qualified => qualified.Valid version
  | .application function arguments =>
    arguments ≠ [] ∧ function.Valid version ∧ Term.ValidAll version arguments
  | .«let» bindings body =>
    bindings ≠ [] ∧ Term.ValidBindings version bindings ∧ body.Valid version
  | .lambda variables body =>
    versionAtLeast version .v2_7 ∧ variables ≠ [] ∧
      (∀ sortedVar ∈ variables, sortedVar.Valid version) ∧ body.Valid version
  | .quantified _ variables body =>
    variables ≠ [] ∧ (∀ sortedVar ∈ variables, sortedVar.Valid version) ∧ body.Valid version
  | .«match» scrutinee cases =>
    versionAtLeast version .v2_6 ∧ cases ≠ [] ∧ scrutinee.Valid version ∧
      Term.ValidCases version cases
  | .annotated term attributes =>
    attributes ≠ [] ∧ term.Valid version ∧ ∀ annotation ∈ attributes, annotation.Valid version

/-- The terms are each valid. -/
def Term.ValidAll (version : Version) : List Term → Prop
  | [] => True
  | first :: rest => first.Valid version ∧ Term.ValidAll version rest

/-- The bound terms are each valid. -/
def Term.ValidBindings (version : Version) : List (Symbol × Term) → Prop
  | [] => True
  | (_, term) :: rest => term.Valid version ∧ Term.ValidBindings version rest

/-- The patterns and bodies of the cases are each valid. -/
def Term.ValidCases (version : Version) : List (Pattern × Term) → Prop
  | [] => True
  | (pattern, term) :: rest =>
    pattern.Valid version ∧ term.Valid version ∧ Term.ValidCases version rest

end

/--
The selector declaration is valid: its sort is.

Standard: 2.7 §3.11 Scripts; App. B ⟨selector_dec⟩.
-/
def SelectorDec.Valid (version : Version) (selector : SelectorDec) : Prop :=
  selector.sort.Valid version

/--
The constructor declaration is valid: its selectors are.

Standard: 2.7 §3.11 Scripts; App. B ⟨constructor_dec⟩.
-/
def ConstructorDec.Valid (version : Version) (constructor : ConstructorDec) : Prop :=
  ∀ selector ∈ constructor.selectors, selector.Valid version

/--
The datatype declaration is valid: it has at least one constructor, and its constructors are
valid.

Standard: 2.7 §3.11 Scripts; App. B ⟨datatype_dec⟩.
-/
def DatatypeDec.Valid (version : Version) (datatype : DatatypeDec) : Prop :=
  datatype.constructors ≠ [] ∧ ∀ constructor ∈ datatype.constructors, constructor.Valid version

/--
The function declaration is valid: its sorts are.

Standard: 2.7 §3.11 Scripts; App. B ⟨function_dec⟩.
-/
def FunctionDec.Valid (version : Version) (declaration : FunctionDec) : Prop :=
  (∀ parameter ∈ declaration.parameters, parameter.Valid version) ∧
    declaration.result.Valid version

/--
The function definition is valid: its sorts and its body are.

Standard: 2.7 §3.11 Scripts; App. B ⟨function_def⟩.
-/
def FunctionDef.Valid (version : Version) (definition : FunctionDef) : Prop :=
  (∀ parameter ∈ definition.parameters, parameter.Valid version) ∧
    definition.result.Valid version ∧ definition.body.Valid version

/--
The propositional literal is valid: a negation is written with the symbol `not`, quoted or not.

Standard: 2.5 and 2.6 §3.9 Scripts; App. B ⟨prop_literal⟩.
-/
def PropLiteral.Valid : PropLiteral → Prop
  | .positive _ => True
  | .negative negation _ => negation.name = chars "not"

/--
The command is valid: the version has the command, its repetitions `+` are not empty, the
lists that the standard pairs have the same length, and its parts are valid.

Standard: 2.7 §3.11 Scripts; App. B ⟨command⟩, ⟨option⟩ and ⟨info_flag⟩ of each version, the
standard commands only.
-/
def Command.Valid (version : Version) : Command → Prop
  | .assert term => term.Valid version
  | .checkSat => True
  | .checkSatAssuming terms => versionAtLeast version .v2_7 ∧ Term.ValidAll version terms
  | .checkSatAssumingLiterals literals =>
    versionAtLeast version .v2_5 ∧ ¬ versionAtLeast version .v2_7 ∧
      ∀ literal ∈ literals, literal.Valid
  | .declareConst _ sort => versionAtLeast version .v2_5 ∧ sort.Valid version
  | .declareDatatype _ datatype => versionAtLeast version .v2_6 ∧ datatype.Valid version
  | .declareDatatypes sorts datatypes =>
    versionAtLeast version .v2_6 ∧ sorts ≠ [] ∧ sorts.length = datatypes.length ∧
      ∀ datatype ∈ datatypes, datatype.Valid version
  | .declareFun _ parameters result => Sort.ValidAll version parameters ∧ result.Valid version
  | .declareSort _ _ => True
  | .declareSortParameter _ => versionAtLeast version .v2_7
  | .defineConst _ sort term =>
    versionAtLeast version .v2_7 ∧ sort.Valid version ∧ term.Valid version
  | .defineFun definition => definition.Valid version
  | .defineFunRec definition => versionAtLeast version .v2_5 ∧ definition.Valid version
  | .defineFunsRec declarations bodies =>
    versionAtLeast version .v2_5 ∧ declarations ≠ [] ∧ declarations.length = bodies.length ∧
      (∀ declaration ∈ declarations, declaration.Valid version) ∧ Term.ValidAll version bodies
  | .defineSort _ _ sort => sort.Valid version
  | .echo _ => versionAtLeast version .v2_5
  | .exit => True
  | .getAssertions => True
  | .getAssignment => True
  | .getInfo _ => True
  | .getModel => versionAtLeast version .v2_5
  | .getOption _ => True
  | .getProof => True
  | .getUnsatAssumptions => versionAtLeast version .v2_5
  | .getUnsatCore => True
  | .getValue terms => terms ≠ [] ∧ Term.ValidAll version terms
  | .pop _ => True
  | .push _ => True
  | .reset => versionAtLeast version .v2_5
  | .resetAssertions => versionAtLeast version .v2_5
  | .setInfo info => info.Valid version
  | .setLogic _ => True
  | .setOption option => option.Valid version

end Tree

namespace Syntax

/-! ## Sequences of tokens of a category -/

/--
`IsSExpr version tokens sExpr`: the tokens are the s-expression: they are how the s-expression
is written, and the s-expression is valid.

Standard: 2.7 §3.2 S-expressions; App. B ⟨s_expr⟩, as `Tree.SExpr.tokens` and
`Tree.SExpr.Valid`.
-/
def IsSExpr (version : Version) (tokens : List SyntaxToken) (sExpr : Tree.SExpr) : Prop :=
  sExpr.Valid version ∧ sExpr.tokens = tokens

/--
`IsAttribute version tokens attribute`: the tokens are the attribute: they are how the attribute
is written, and the attribute is valid.

Standard: 2.7 §3.4 Attributes; App. B ⟨attribute⟩, as `Tree.Attribute.tokens` and
`Tree.Attribute.Valid`.
-/
def IsAttribute (version : Version) (tokens : List SyntaxToken) («attribute» : Tree.Attribute) :
    Prop :=
  «attribute».Valid version ∧ «attribute».tokens = tokens

/--
`IsSort version tokens sort`: the tokens are the sort: they are how the sort is written, and the
sort is valid.

Standard: 2.7 §3.5 Sorts; App. B ⟨sort⟩, as `Tree.Sort.tokens` and `Tree.Sort.Valid`.
-/
def IsSort (version : Version) (tokens : List SyntaxToken) (sort : Tree.Sort) : Prop :=
  sort.Valid version ∧ sort.tokens = tokens

/--
`IsTerm version tokens term`: the tokens are the term: they are how the term is written, and the
term is valid.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨term⟩, as `Tree.Term.tokens` and
`Tree.Term.Valid`.
-/
def IsTerm (version : Version) (tokens : List SyntaxToken) (term : Tree.Term) : Prop :=
  term.Valid version ∧ term.tokens = tokens

/--
`IsCommand version tokens command`: the tokens are the command: they are how the command is
written, and the command is valid.

Standard: 2.7 §3.11 Scripts; App. B ⟨command⟩, as `Tree.Command.tokens` and
`Tree.Command.Valid`.
-/
def IsCommand (version : Version) (tokens : List SyntaxToken) (command : Tree.Command) : Prop :=
  command.Valid version ∧ command.tokens = tokens

end Syntax

end BSmtLibSpec.Grammar
