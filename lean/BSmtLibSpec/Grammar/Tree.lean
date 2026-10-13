import BSmtLibSpec.Lexicon

/-!
# Syntax trees

What the syntactic rules build: one type per syntactic category of SMT-LIB scripts. Names,
keywords and the contents of literals are characters, as the tokens give them; a symbol also
records whether it was written quoted. A propositional literal also has the term it is written as
(`PropLiteral.asTerm`).
-/

namespace BSmtLibSpec.Grammar

open BSmtLibSpec.Lexicon
open Regex (Chars)

namespace Tree

/--
A symbol: its name, which is the symbol, and whether it was written quoted. The form is
recorded for printing, not for identity: two symbols with the same name are the same symbol,
and wherever this specification compares symbols or matches a symbol, it compares names.

Standard: 2.7 §3.1 Symbols: a simple symbol and its quoted form are the same symbol.
-/
structure Symbol where
  name : Chars
  quoted : Bool

/--
⟨spec_constant⟩

Standard: 2.7 §3.2; App. B ⟨spec_constant⟩.
-/
inductive SpecConstant where
  | numeral (digits : Chars)
  | decimal (text : Chars)
  | hexadecimal (digits : Chars)
  | binary (digits : Chars)
  | string (content : Chars)

/--
⟨s_expr⟩

Standard: 2.7 §3.2 S-expressions; App. B ⟨s_expr⟩.
-/
inductive SExpr where
  | constant (constant : SpecConstant)
  | symbol (symbol : Symbol)
  | reserved (word : Chars)
  | keyword (name : Chars)
  | list (items : List SExpr)

/--
⟨index⟩

Standard: 2.7 §3.3 Identifiers; App. B ⟨index⟩.
-/
inductive Index where
  | numeral (digits : Chars)
  | symbol (symbol : Symbol)

/--
⟨identifier⟩: a symbol, with its indices if it is indexed.

Standard: 2.7 §3.3 Identifiers; App. B ⟨identifier⟩.
-/
structure Identifier where
  symbol : Symbol
  indices : List Index

/--
⟨sort⟩: an identifier, applied to the sorts if there are any.

Standard: 2.7 §3.5 Sorts; App. B ⟨sort⟩.
-/
inductive «Sort» where
  | mk (identifier : Identifier) (arguments : List «Sort»)

/--
⟨attribute_value⟩

Standard: 2.7 §3.4 Attributes; App. B ⟨attribute_value⟩.
-/
inductive AttributeValue where
  | constant (constant : SpecConstant)
  | symbol (symbol : Symbol)
  | list (items : List SExpr)

/--
⟨attribute⟩: a keyword, with its value if it has one.

Standard: 2.7 §3.4 Attributes; App. B ⟨attribute⟩.
-/
structure Attribute where
  keyword : Chars
  value : Option AttributeValue

/--
⟨qual_identifier⟩

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨qual_identifier⟩.
-/
inductive QualIdentifier where
  | plain (identifier : Identifier)
  | as (identifier : Identifier) (sort : «Sort»)

/--
⟨sorted_var⟩

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨sorted_var⟩.
-/
structure SortedVar where
  symbol : Symbol
  sort : «Sort»

/--
⟨symbol_⟩: a symbol, or the wildcard `_`.

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨pattern⟩.
-/
inductive SymbolOrWildcard where
  | symbol (symbol : Symbol)
  | wildcard

/--
⟨pattern⟩

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨pattern⟩.
-/
inductive Pattern where
  | single (symbol : SymbolOrWildcard)
  | constructor (constructor : Symbol) (arguments : List SymbolOrWildcard)

/--
The two quantifiers.

Standard: 2.7 §3.6 Terms and Formulas: the binders `forall` and `exists` of ⟨term⟩.
-/
inductive Quantifier where
  | «forall»
  | «exists»

/--
⟨term⟩

Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨term⟩.
-/
inductive Term where
  | constant (constant : SpecConstant)
  | identifier (identifier : QualIdentifier)
  | application (function : QualIdentifier) (arguments : List Term)
  | «let» (bindings : List (Symbol × Term)) (body : Term)
  | lambda (variables : List SortedVar) (body : Term)
  | quantified (quantifier : Quantifier) (variables : List SortedVar) (body : Term)
  | «match» (scrutinee : Term) (cases : List (Pattern × Term))
  | annotated (term : Term) (attributes : List Attribute)

/--
⟨sort_dec⟩

Standard: 2.7 §3.11 Scripts; App. B ⟨sort_dec⟩.
-/
structure SortDec where
  symbol : Symbol
  arity : Chars

/--
⟨selector_dec⟩

Standard: 2.7 §3.11 Scripts; App. B ⟨selector_dec⟩.
-/
structure SelectorDec where
  symbol : Symbol
  sort : «Sort»

/--
⟨constructor_dec⟩

Standard: 2.7 §3.11 Scripts; App. B ⟨constructor_dec⟩.
-/
structure ConstructorDec where
  symbol : Symbol
  selectors : List SelectorDec

/--
⟨datatype_dec⟩: the sort parameters, none unless it is parametric, and the constructors.

Standard: 2.7 §3.11 Scripts; App. B ⟨datatype_dec⟩.
-/
structure DatatypeDec where
  parameters : List Symbol
  constructors : List ConstructorDec

/--
⟨function_dec⟩

Standard: 2.7 §3.11 Scripts; App. B ⟨function_dec⟩.
-/
structure FunctionDec where
  symbol : Symbol
  parameters : List SortedVar
  result : «Sort»

/--
⟨function_def⟩

Standard: 2.7 §3.11 Scripts; App. B ⟨function_def⟩.
-/
structure FunctionDef where
  symbol : Symbol
  parameters : List SortedVar
  result : «Sort»
  body : Term

/--
⟨prop_literal⟩: a symbol, or its negation, which records the symbol `not` it was written with.

Standard: 2.5 and 2.6 §3.9 Scripts; App. B ⟨prop_literal⟩.
-/
inductive PropLiteral where
  | positive (symbol : Symbol)
  | negative (negation : Symbol) (symbol : Symbol)

/--
A propositional literal as the term it is written as: the symbol, or `not` applied to it.
-/
def PropLiteral.asTerm : Tree.PropLiteral → Tree.Term
  | .positive symbol => .identifier (.plain ⟨symbol, []⟩)
  | .negative negation symbol =>
    .application (.plain ⟨negation, []⟩) [.identifier (.plain ⟨symbol, []⟩)]

/--
⟨command⟩

Standard: 2.7 §3.11 Scripts; App. B ⟨command⟩, the standard commands only.
-/
inductive Command where
  | assert (term : Term)
  | checkSat
  | checkSatAssuming (assumptions : List Term)
  | checkSatAssumingLiterals (literals : List PropLiteral)
  | declareConst (symbol : Symbol) (sort : «Sort»)
  | declareDatatype (symbol : Symbol) (datatype : DatatypeDec)
  | declareDatatypes (sorts : List SortDec) (datatypes : List DatatypeDec)
  | declareFun (symbol : Symbol) (parameters : List «Sort») (result : «Sort»)
  | declareSort (symbol : Symbol) (arity : Chars)
  | declareSortParameter (symbol : Symbol)
  | defineConst (symbol : Symbol) (sort : «Sort») (term : Term)
  | defineFun (definition : FunctionDef)
  | defineFunRec (definition : FunctionDef)
  | defineFunsRec (declarations : List FunctionDec) (bodies : List Term)
  | defineSort (symbol : Symbol) (parameters : List Symbol) (sort : «Sort»)
  | echo (content : Chars)
  | exit
  | getAssertions
  | getAssignment
  | getInfo (flag : Chars)
  | getModel
  | getOption (keyword : Chars)
  | getProof
  | getUnsatAssumptions
  | getUnsatCore
  | getValue (terms : List Term)
  | pop (count : Chars)
  | push (count : Chars)
  | reset
  | resetAssertions
  | setInfo (info : Attribute)
  | setLogic (symbol : Symbol)
  | setOption (option : Attribute)

end Tree

end BSmtLibSpec.Grammar
