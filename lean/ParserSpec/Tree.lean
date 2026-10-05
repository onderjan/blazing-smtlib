import LexerSpec

/-!
# Syntax trees

What the syntactic rules build: one type per syntactic category of SMT-LIB scripts. Names,
keywords and the contents of literals are characters, as the tokens give them.
-/

namespace ParserSpec

open LexerSpec

namespace Tree

/-- ⟨spec_constant⟩ -/
inductive SpecConstant where
  | numeral (digits : Chars)
  | decimal (text : Chars)
  | hexadecimal (digits : Chars)
  | binary (digits : Chars)
  | string (content : Chars)

/-- ⟨s_expr⟩ -/
inductive SExpr where
  | constant (constant : SpecConstant)
  | symbol (name : Chars)
  | reserved (word : Chars)
  | keyword (name : Chars)
  | list (items : List SExpr)

/-- ⟨index⟩ -/
inductive Index where
  | numeral (digits : Chars)
  | symbol (name : Chars)

/-- ⟨identifier⟩: a symbol, with its indices if it is indexed. -/
structure Identifier where
  symbol : Chars
  indices : List Index

/-- ⟨sort⟩: an identifier, applied to the sorts if there are any. -/
inductive «Sort» where
  | mk (identifier : Identifier) (arguments : List «Sort»)

/-- ⟨attribute_value⟩ -/
inductive AttributeValue where
  | constant (constant : SpecConstant)
  | symbol (name : Chars)
  | list (items : List SExpr)

/-- ⟨attribute⟩: a keyword, with its value if it has one. -/
structure Attribute where
  keyword : Chars
  value : Option AttributeValue

/-- ⟨qual_identifier⟩ -/
inductive QualIdentifier where
  | plain (identifier : Identifier)
  | as (identifier : Identifier) (sort : «Sort»)

/-- ⟨sorted_var⟩ -/
structure SortedVar where
  symbol : Chars
  sort : «Sort»

/-- ⟨symbol_⟩: a symbol, or the wildcard `_`. -/
inductive SymbolOrWildcard where
  | symbol (name : Chars)
  | wildcard

/-- ⟨pattern⟩ -/
inductive Pattern where
  | single (symbol : SymbolOrWildcard)
  | constructor (constructor : Chars) (arguments : List SymbolOrWildcard)

/-- The two quantifiers. -/
inductive Quantifier where
  | «forall»
  | «exists»

/-- ⟨term⟩ -/
inductive Term where
  | constant (constant : SpecConstant)
  | identifier (identifier : QualIdentifier)
  | application (function : QualIdentifier) (arguments : List Term)
  | «let» (bindings : List (Chars × Term)) (body : Term)
  | lambda (variables : List SortedVar) (body : Term)
  | quantified (quantifier : Quantifier) (variables : List SortedVar) (body : Term)
  | «match» (scrutinee : Term) (cases : List (Pattern × Term))
  | annotated (term : Term) (attributes : List Attribute)

/-- ⟨sort_dec⟩ -/
structure SortDec where
  symbol : Chars
  arity : Chars

/-- ⟨selector_dec⟩ -/
structure SelectorDec where
  symbol : Chars
  sort : «Sort»

/-- ⟨constructor_dec⟩ -/
structure ConstructorDec where
  symbol : Chars
  selectors : List SelectorDec

/-- ⟨datatype_dec⟩: the sort parameters, none unless it is parametric, and the constructors. -/
structure DatatypeDec where
  parameters : List Chars
  constructors : List ConstructorDec

/-- ⟨function_dec⟩ -/
structure FunctionDec where
  symbol : Chars
  parameters : List SortedVar
  result : «Sort»

/-- ⟨function_def⟩ -/
structure FunctionDef where
  symbol : Chars
  parameters : List SortedVar
  result : «Sort»
  body : Term

/-- ⟨prop_literal⟩ -/
inductive PropLiteral where
  | positive (symbol : Chars)
  | negative (symbol : Chars)

/-- ⟨command⟩ -/
inductive Command where
  | assert (term : Term)
  | checkSat
  | checkSatAssuming (assumptions : List Term)
  | checkSatAssumingLiterals (literals : List PropLiteral)
  | declareConst (symbol : Chars) (sort : «Sort»)
  | declareDatatype (symbol : Chars) (datatype : DatatypeDec)
  | declareDatatypes (sorts : List SortDec) (datatypes : List DatatypeDec)
  | declareFun (symbol : Chars) (parameters : List «Sort») (result : «Sort»)
  | declareSort (symbol : Chars) (arity : Chars)
  | declareSortParameter (symbol : Chars)
  | defineConst (symbol : Chars) (sort : «Sort») (term : Term)
  | defineFun (definition : FunctionDef)
  | defineFunRec (definition : FunctionDef)
  | defineFunsRec (declarations : List FunctionDec) (bodies : List Term)
  | defineSort (symbol : Chars) (parameters : List Chars) (sort : «Sort»)
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
  | setLogic (symbol : Chars)
  | setOption (option : Attribute)

end Tree

end ParserSpec
