import BSmtLib.Spec.Lexicon

/-!
# Syntax trees

What the syntactic rules build: one type per syntactic category of SMT-LIB scripts. Names,
keywords and the contents of literals are characters, as the tokens give them; a symbol also
records whether it was written quoted.
-/

namespace BSmtLib.Spec.Grammar

open BSmtLib.Spec.Lexicon

namespace Tree

/--
Standard: 2.7 §3.1 Symbols: a simple symbol and its quoted form are the same symbol.
Extension: the form it was written in is recorded.

A symbol: its name, which is the symbol, and whether it was written quoted. The form is
recorded for printing, not for identity: two symbols with the same name are the same symbol,
and wherever this specification compares symbols or matches a symbol, it compares names.
-/
structure Symbol where
  name : Chars
  quoted : Bool

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
  | symbol (symbol : Symbol)
  | reserved (word : Chars)
  | keyword (name : Chars)
  | list (items : List SExpr)

/--
Standard: 2.7 §3.3 Identifiers; App. B ⟨index⟩.

⟨index⟩
-/
inductive Index where
  | numeral (digits : Chars)
  | symbol (symbol : Symbol)

/--
Standard: 2.7 §3.3 Identifiers; App. B ⟨identifier⟩.

⟨identifier⟩: a symbol, with its indices if it is indexed.
-/
structure Identifier where
  symbol : Symbol
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
  | symbol (symbol : Symbol)
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
  symbol : Symbol
  sort : «Sort»

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨pattern⟩.

⟨symbol_⟩: a symbol, or the wildcard `_`.
-/
inductive SymbolOrWildcard where
  | symbol (symbol : Symbol)
  | wildcard

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨pattern⟩.

⟨pattern⟩
-/
inductive Pattern where
  | single (symbol : SymbolOrWildcard)
  | constructor (constructor : Symbol) (arguments : List SymbolOrWildcard)

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
  | «let» (bindings : List (Symbol × Term)) (body : Term)
  | lambda (variables : List SortedVar) (body : Term)
  | quantified (quantifier : Quantifier) (variables : List SortedVar) (body : Term)
  | «match» (scrutinee : Term) (cases : List (Pattern × Term))
  | annotated (term : Term) (attributes : List Attribute)

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨sort_dec⟩.

⟨sort_dec⟩
-/
structure SortDec where
  symbol : Symbol
  arity : Chars

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨selector_dec⟩.

⟨selector_dec⟩
-/
structure SelectorDec where
  symbol : Symbol
  sort : «Sort»

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨constructor_dec⟩.

⟨constructor_dec⟩
-/
structure ConstructorDec where
  symbol : Symbol
  selectors : List SelectorDec

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨datatype_dec⟩.

⟨datatype_dec⟩: the sort parameters, none unless it is parametric, and the constructors.
-/
structure DatatypeDec where
  parameters : List Symbol
  constructors : List ConstructorDec

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨function_dec⟩.

⟨function_dec⟩
-/
structure FunctionDec where
  symbol : Symbol
  parameters : List SortedVar
  result : «Sort»

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨function_def⟩.

⟨function_def⟩
-/
structure FunctionDef where
  symbol : Symbol
  parameters : List SortedVar
  result : «Sort»
  body : Term

/--
Standard: 2.5 and 2.6 §3.9 Scripts; App. B ⟨prop_literal⟩.

⟨prop_literal⟩: a symbol, or its negation, which records the symbol `not` it was written with.
-/
inductive PropLiteral where
  | positive (symbol : Symbol)
  | negative (negation : Symbol) (symbol : Symbol)

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨command⟩. Scope P6: the standard commands only.

⟨command⟩
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

end BSmtLib.Spec.Grammar
