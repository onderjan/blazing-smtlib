import BSmtLib.Spec.Lexicon

/-!
# Syntax trees

What the syntactic rules build: one type per syntactic category of SMT-LIB scripts. Names,
keywords and the contents of literals are characters, as the tokens give them.
-/

namespace BSmtLib.Spec.Grammar

open BSmtLib.Spec.Lexicon

namespace Tree

/--
Standard: 2.7 §3.2; App. B ⟨spec_constant⟩.

⟨spec_constant⟩
-/
inductive SpecConstant where
  | numeral (digits : Chars)
  | decimal (text : Chars)
  | hexadecimal (digits : Chars)
  | binary (digits : Chars)
  | string (content : Chars)

/--
Standard: 2.7 §3.2 S-expressions; App. B ⟨s_expr⟩.

⟨s_expr⟩
-/
inductive SExpr where
  | constant (constant : SpecConstant)
  | symbol (name : Chars)
  | reserved (word : Chars)
  | keyword (name : Chars)
  | list (items : List SExpr)

/--
Standard: 2.7 §3.3 Identifiers; App. B ⟨index⟩.

⟨index⟩
-/
inductive Index where
  | numeral (digits : Chars)
  | symbol (name : Chars)

/--
Standard: 2.7 §3.3 Identifiers; App. B ⟨identifier⟩.

⟨identifier⟩: a symbol, with its indices if it is indexed.
-/
structure Identifier where
  symbol : Chars
  indices : List Index

/--
Standard: 2.7 §3.5 Sorts; App. B ⟨sort⟩.

⟨sort⟩: an identifier, applied to the sorts if there are any.
-/
inductive «Sort» where
  | mk (identifier : Identifier) (arguments : List «Sort»)

/--
Standard: 2.7 §3.4 Attributes; App. B ⟨attribute_value⟩.

⟨attribute_value⟩
-/
inductive AttributeValue where
  | constant (constant : SpecConstant)
  | symbol (name : Chars)
  | list (items : List SExpr)

/--
Standard: 2.7 §3.4 Attributes; App. B ⟨attribute⟩.

⟨attribute⟩: a keyword, with its value if it has one.
-/
structure Attribute where
  keyword : Chars
  value : Option AttributeValue

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨qual_identifier⟩.

⟨qual_identifier⟩
-/
inductive QualIdentifier where
  | plain (identifier : Identifier)
  | as (identifier : Identifier) (sort : «Sort»)

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨sorted_var⟩.

⟨sorted_var⟩
-/
structure SortedVar where
  symbol : Chars
  sort : «Sort»

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨pattern⟩.

⟨symbol_⟩: a symbol, or the wildcard `_`.
-/
inductive SymbolOrWildcard where
  | symbol (name : Chars)
  | wildcard

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨pattern⟩.

⟨pattern⟩
-/
inductive Pattern where
  | single (symbol : SymbolOrWildcard)
  | constructor (constructor : Chars) (arguments : List SymbolOrWildcard)

/--
Standard: 2.7 §3.6 Terms and Formulas: the binders `forall` and `exists` of ⟨term⟩.

The two quantifiers.
-/
inductive Quantifier where
  | «forall»
  | «exists»

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨term⟩.

⟨term⟩
-/
inductive Term where
  | constant (constant : SpecConstant)
  | identifier (identifier : QualIdentifier)
  | application (function : QualIdentifier) (arguments : List Term)
  | «let» (bindings : List (Chars × Term)) (body : Term)
  | lambda (variables : List SortedVar) (body : Term)
  | quantified (quantifier : Quantifier) (variables : List SortedVar) (body : Term)
  | «match» (scrutinee : Term) (cases : List (Pattern × Term))
  | annotated (term : Term) (attributes : List Attribute)

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨sort_dec⟩.

⟨sort_dec⟩
-/
structure SortDec where
  symbol : Chars
  arity : Chars

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨selector_dec⟩.

⟨selector_dec⟩
-/
structure SelectorDec where
  symbol : Chars
  sort : «Sort»

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨constructor_dec⟩.

⟨constructor_dec⟩
-/
structure ConstructorDec where
  symbol : Chars
  selectors : List SelectorDec

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨datatype_dec⟩.

⟨datatype_dec⟩: the sort parameters, none unless it is parametric, and the constructors.
-/
structure DatatypeDec where
  parameters : List Chars
  constructors : List ConstructorDec

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨function_dec⟩.

⟨function_dec⟩
-/
structure FunctionDec where
  symbol : Chars
  parameters : List SortedVar
  result : «Sort»

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨function_def⟩.

⟨function_def⟩
-/
structure FunctionDef where
  symbol : Chars
  parameters : List SortedVar
  result : «Sort»
  body : Term

/--
Standard: 2.5 and 2.6 §3.9 Scripts; App. B ⟨prop_literal⟩.

⟨prop_literal⟩
-/
inductive PropLiteral where
  | positive (symbol : Chars)
  | negative (symbol : Chars)

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨command⟩. Scope P6: the standard commands only.

⟨command⟩
-/
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

end BSmtLib.Spec.Grammar
