import BSmtLib.Spec.Grammar.Tree

/-!
# The syntactic rules

The production rules of the standard's scripts, over the tokens, in the versions 2.0, 2.5,
2.6 and 2.7. Each relation is named after its syntactic category and relates a sequence of
tokens to the syntax tree it derives. A rule that a version adds needs that version or a
later one.
-/

namespace BSmtLib.Spec.Grammar

open BSmtLib.Spec.Lexicon

/-- The version is `first` or a later one. -/
def versionAtLeast (version first : Version) : Prop :=
  first ∈ version.upTo

/-- The number of the version, as a decimal. -/
def versionNumber : Version → Chars
  | .v2_0 => chars "2.0"
  | .v2_5 => chars "2.5"
  | .v2_6 => chars "2.6"
  | .v2_7 => chars "2.7"

/--
Standard: 2.7 §3.1 Symbols: a simple symbol and its quoted form are the same symbol.

A token as the syntactic rules see it: what the lexical token stands for, and for a symbol
whether it was quoted.
-/
inductive SyntaxToken where
  | parenOpen
  | parenClose
  | numeral (digits : Chars)
  | decimal (text : Chars)
  | hexadecimal (digits : Chars)
  | binary (digits : Chars)
  | string (content : Chars)
  /--
  A simple or a quoted symbol: `abc` and `|abc|` are the same symbol. Whether it was quoted
  is recorded for printing, not for identity.
  -/
  | symbol (symbol : Tree.Symbol)
  | keyword (name : Chars)
  | reserved (word : Chars)

/--
Standard: 2.7 §3.1 Symbols, as `SyntaxToken`.

What a lexical token of the version stands for, and for a symbol whether it was quoted.
-/
def SyntaxToken.ofToken (version : Version) (token : Token) : SyntaxToken :=
  match token.category with
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral => .numeral token.text
  | .decimal => .decimal token.text
  | .hexadecimal => .hexadecimal (token.content version)
  | .binary => .binary (token.content version)
  | .string => .string (token.content version)
  | .simpleSymbol => .symbol ⟨token.content version, false⟩
  | .quotedSymbol => .symbol ⟨token.content version, true⟩
  | .keyword => .keyword (token.content version)
  | .reserved => .reserved token.text

/-- `(`, the tokens, `)`. -/
def paren (tokens : List SyntaxToken) : List SyntaxToken := .parenOpen :: tokens ++ [.parenClose]

/-- The reserved word `w`. -/
def word (w : String) : SyntaxToken := .reserved (chars w)

/-- `(`, the command name, the tokens, `)`. -/
def commandTokens (name : String) (tokens : List SyntaxToken) : List SyntaxToken :=
  paren (word name :: tokens)

/-- `Each rule tokens items`: the tokens derive the items, one after another, by the rule. -/
inductive Each {α : Type} (rule : List SyntaxToken → α → Prop) : List SyntaxToken → List α → Prop
  | nil : Each rule [] []
  | cons : rule first item → Each rule rest items → Each rule (first ++ rest) (item :: items)

/-! ## Tokens -/

/--
Standard: 2.7 §3.2; App. B ⟨spec_constant⟩.

⟨spec_constant⟩ ::= ⟨numeral⟩ | ⟨decimal⟩ | ⟨hexadecimal⟩ | ⟨binary⟩ | ⟨string⟩
-/
inductive SpecConstant : List SyntaxToken → Tree.SpecConstant → Prop
  | numeral : SpecConstant [.numeral digits] (.numeral digits)
  | decimal : SpecConstant [.decimal text] (.decimal text)
  | hexadecimal : SpecConstant [.hexadecimal digits] (.hexadecimal digits)
  | binary : SpecConstant [.binary digits] (.binary digits)
  | string : SpecConstant [.string content] (.string content)

/--
Standard: 2.7 §3.1 Symbols; App. B ⟨symbol⟩.

⟨symbol⟩
-/
inductive Symbol : List SyntaxToken → Tree.Symbol → Prop
  | mk : Symbol [.symbol name] name

/-! ## S-expressions, identifiers, sorts and attributes -/

/--
Standard: 2.7 §3.2 S-expressions; App. B ⟨s_expr⟩: a reserved word is an s-expression from
2.6 release 2021-04-02 on.

⟨s_expr⟩ ::= ⟨spec_constant⟩ | ⟨symbol⟩ | ⟨reserved⟩ | ⟨keyword⟩ | `(` ⟨s_expr⟩∗ `)`;
⟨reserved⟩ is an s-expression from 2.6 on.
-/
inductive SExpr (version : Version) : List SyntaxToken → Tree.SExpr → Prop
  | constant : SpecConstant tokens constant → SExpr version tokens (.constant constant)

  | symbol : SExpr version [.symbol name] (.symbol name)

  | reserved : versionAtLeast version .v2_6 → SExpr version [.reserved w] (.reserved w)

  | keyword : SExpr version [.keyword name] (.keyword name)

  | list : Each (SExpr version) tokens items →
      SExpr version (paren tokens) (.list items)

/--
Standard: 2.7 §3.3 Identifiers; App. B ⟨index⟩.

⟨index⟩ ::= ⟨numeral⟩ | ⟨symbol⟩; a symbol is an index from 2.5 on.
-/
inductive Index (version : Version) : List SyntaxToken → Tree.Index → Prop
  | numeral : Index version [.numeral digits] (.numeral digits)
  | symbol : versionAtLeast version .v2_5 → Index version [.symbol name] (.symbol name)

/--
Standard: 2.7 §3.3 Identifiers; App. B ⟨identifier⟩.

⟨identifier⟩ ::= ⟨symbol⟩ | `(` `_` ⟨symbol⟩ ⟨index⟩+ `)`
-/
inductive Identifier (version : Version) : List SyntaxToken → Tree.Identifier → Prop
  | symbol : Identifier version [.symbol name] ⟨name, []⟩

  | indexed : Each (Index version) tokens indices → indices ≠ [] →
      Identifier version (paren (word "_" :: .symbol name :: tokens)) ⟨name, indices⟩

/--
Standard: 2.7 §3.5 Sorts; App. B ⟨sort⟩.

⟨sort⟩ ::= ⟨identifier⟩ | `(` ⟨identifier⟩ ⟨sort⟩+ `)`
-/
inductive «Sort» (version : Version) : List SyntaxToken → Tree.Sort → Prop
  | identifier : Identifier version tokens identifier →
      «Sort» version tokens (.mk identifier [])

  | application : Identifier version head identifier →
      Each («Sort» version) tokens arguments → arguments ≠ [] →
      «Sort» version (paren (head ++ tokens)) (.mk identifier arguments)

/--
Standard: 2.7 §3.4 Attributes; App. B ⟨attribute_value⟩.

⟨attribute_value⟩ ::= ⟨spec_constant⟩ | ⟨symbol⟩ | `(` ⟨s_expr⟩∗ `)`
-/
inductive AttributeValue (version : Version) : List SyntaxToken → Tree.AttributeValue → Prop
  | constant : SpecConstant tokens constant →
      AttributeValue version tokens (.constant constant)

  | symbol : AttributeValue version [.symbol name] (.symbol name)

  | list : Each (SExpr version) tokens items →
      AttributeValue version (paren tokens) (.list items)

/--
Standard: 2.7 §3.4 Attributes; App. B ⟨attribute⟩.

⟨attribute⟩ ::= ⟨keyword⟩ | ⟨keyword⟩ ⟨attribute_value⟩
-/
inductive Attribute (version : Version) : List SyntaxToken → Tree.Attribute → Prop
  | keyword : Attribute version [.keyword name] ⟨name, none⟩

  | valued : AttributeValue version tokens value →
      Attribute version (.keyword name :: tokens) ⟨name, some value⟩

/-! ## Terms -/

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨qual_identifier⟩.

⟨qual_identifier⟩ ::= ⟨identifier⟩ | `(` `as` ⟨identifier⟩ ⟨sort⟩ `)`
-/
inductive QualIdentifier (version : Version) : List SyntaxToken → Tree.QualIdentifier → Prop
  | plain : Identifier version tokens identifier →
      QualIdentifier version tokens (.plain identifier)

  | as : Identifier version identifierTokens identifier →
      «Sort» version sortTokens sort →
      QualIdentifier version (paren (word "as" :: identifierTokens ++ sortTokens))
        (.as identifier sort)

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨sorted_var⟩.

⟨sorted_var⟩ ::= `(` ⟨symbol⟩ ⟨sort⟩ `)`
-/
inductive SortedVar (version : Version) : List SyntaxToken → Tree.SortedVar → Prop
  | mk : «Sort» version tokens sort →
      SortedVar version (paren (.symbol name :: tokens)) ⟨name, sort⟩

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨pattern⟩.

⟨symbol_⟩ ::= ⟨symbol⟩ | `_`; the wildcard `_` is one from 2.7 on.
-/
inductive SymbolOrWildcard (version : Version) : List SyntaxToken → Tree.SymbolOrWildcard → Prop
  | symbol : SymbolOrWildcard version [.symbol name] (.symbol name)
  | wildcard : versionAtLeast version .v2_7 → SymbolOrWildcard version [word "_"] .wildcard

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨pattern⟩.

⟨pattern⟩ ::= ⟨symbol_⟩ | `(` ⟨symbol⟩ ⟨symbol_⟩+ `)`, from 2.6 on.
-/
inductive Pattern (version : Version) : List SyntaxToken → Tree.Pattern → Prop
  | single : SymbolOrWildcard version tokens symbol →
      Pattern version tokens (.single symbol)

  | constructor : Each (SymbolOrWildcard version) tokens arguments → arguments ≠ [] →
      Pattern version (paren (.symbol name :: tokens)) (.constructor name arguments)

mutual

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨term⟩.

⟨term⟩
-/
inductive Term (version : Version) : List SyntaxToken → Tree.Term → Prop
  /-- ⟨spec_constant⟩ -/
  | constant : SpecConstant tokens constant → Term version tokens (.constant constant)

  /-- ⟨qual_identifier⟩ -/
  | identifier : QualIdentifier version tokens identifier →
      Term version tokens (.identifier identifier)

  /-- `(` ⟨qual_identifier⟩ ⟨term⟩+ `)` -/
  | application : QualIdentifier version head function →
      Each (Term version) tokens arguments → arguments ≠ [] →
      Term version (paren (head ++ tokens)) (.application function arguments)

  /-- `(` `let` `(` ⟨var_binding⟩+ `)` ⟨term⟩ `)` -/
  | «let» : Bindings version bindingTokens bindings → bindings ≠ [] →
      Term version bodyTokens body →
      Term version (paren (word "let" :: paren bindingTokens ++ bodyTokens))
        (.«let» bindings body)

  /-- `(` `lambda` `(` ⟨sorted_var⟩+ `)` ⟨term⟩ `)`, from 2.7 on -/
  | lambda : versionAtLeast version .v2_7 →
      Each (SortedVar version) variableTokens variables → variables ≠ [] →
      Term version bodyTokens body →
      Term version (paren (word "lambda" :: paren variableTokens ++ bodyTokens))
        (.lambda variables body)

  /-- `(` `forall` `(` ⟨sorted_var⟩+ `)` ⟨term⟩ `)` -/
  | «forall» : Each (SortedVar version) variableTokens variables → variables ≠ [] →
      Term version bodyTokens body →
      Term version (paren (word "forall" :: paren variableTokens ++ bodyTokens))
        (.quantified .«forall» variables body)

  /-- `(` `exists` `(` ⟨sorted_var⟩+ `)` ⟨term⟩ `)` -/
  | «exists» : Each (SortedVar version) variableTokens variables → variables ≠ [] →
      Term version bodyTokens body →
      Term version (paren (word "exists" :: paren variableTokens ++ bodyTokens))
        (.quantified .«exists» variables body)

  /-- `(` `match` ⟨term⟩ `(` ⟨match_case⟩+ `)` `)`, from 2.6 on -/
  | «match» : versionAtLeast version .v2_6 → Term version scrutineeTokens scrutinee →
      Cases version caseTokens cases → cases ≠ [] →
      Term version (paren (word "match" :: scrutineeTokens ++ paren caseTokens))
        (.«match» scrutinee cases)

  /-- `(` `!` ⟨term⟩ ⟨attribute⟩+ `)` -/
  | annotated : Term version termTokens term →
      Each (Attribute version) attributeTokens attributes → attributes ≠ [] →
      Term version (paren (word "!" :: termTokens ++ attributeTokens))
        (.annotated term attributes)

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨var_binding⟩.

⟨var_binding⟩∗, where ⟨var_binding⟩ ::= `(` ⟨symbol⟩ ⟨term⟩ `)`
-/
inductive Bindings (version : Version) :
    List SyntaxToken → List (Tree.Symbol × Tree.Term) → Prop
  | nil : Bindings version [] []

  | cons : Term version termTokens term → Bindings version rest bindings →
      Bindings version (paren (.symbol name :: termTokens) ++ rest) ((name, term) :: bindings)

/--
Standard: 2.7 §3.6 Terms and Formulas; App. B ⟨match_case⟩.

⟨match_case⟩∗, where ⟨match_case⟩ ::= `(` ⟨pattern⟩ ⟨term⟩ `)`
-/
inductive Cases (version : Version) :
    List SyntaxToken → List (Tree.Pattern × Tree.Term) → Prop
  | nil : Cases version [] []

  | cons : Pattern version patternTokens pattern → Term version termTokens term →
      Cases version rest cases →
      Cases version (paren (patternTokens ++ termTokens) ++ rest) ((pattern, term) :: cases)

end

/-! ## Commands -/

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨sort_dec⟩.

⟨sort_dec⟩ ::= `(` ⟨symbol⟩ ⟨numeral⟩ `)`
-/
inductive SortDec : List SyntaxToken → Tree.SortDec → Prop
  | mk : SortDec (paren [.symbol name, .numeral arity]) ⟨name, arity⟩

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨selector_dec⟩.

⟨selector_dec⟩ ::= `(` ⟨symbol⟩ ⟨sort⟩ `)`
-/
inductive SelectorDec (version : Version) : List SyntaxToken → Tree.SelectorDec → Prop
  | mk : «Sort» version tokens sort →
      SelectorDec version (paren (.symbol name :: tokens)) ⟨name, sort⟩

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨constructor_dec⟩.

⟨constructor_dec⟩ ::= `(` ⟨symbol⟩ ⟨selector_dec⟩∗ `)`
-/
inductive ConstructorDec (version : Version) : List SyntaxToken → Tree.ConstructorDec → Prop
  | mk : Each (SelectorDec version) tokens selectors →
      ConstructorDec version (paren (.symbol name :: tokens)) ⟨name, selectors⟩

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨datatype_dec⟩.

⟨datatype_dec⟩ ::= `(` ⟨constructor_dec⟩+ `)`
  | `(` `par` `(` ⟨symbol⟩+ `)` `(` ⟨constructor_dec⟩+ `)` `)`
-/
inductive DatatypeDec (version : Version) : List SyntaxToken → Tree.DatatypeDec → Prop
  | plain : Each (ConstructorDec version) tokens constructors → constructors ≠ [] →
      DatatypeDec version (paren tokens) ⟨[], constructors⟩

  | parametric : Each Symbol parameterTokens parameters → parameters ≠ [] →
      Each (ConstructorDec version) tokens constructors → constructors ≠ [] →
      DatatypeDec version (paren (word "par" :: paren parameterTokens ++ paren tokens))
        ⟨parameters, constructors⟩

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨function_dec⟩.

⟨function_dec⟩ ::= `(` ⟨symbol⟩ `(` ⟨sorted_var⟩∗ `)` ⟨sort⟩ `)`
-/
inductive FunctionDec (version : Version) : List SyntaxToken → Tree.FunctionDec → Prop
  | mk : Each (SortedVar version) parameterTokens parameters →
      «Sort» version resultTokens result →
      FunctionDec version (paren (.symbol name :: paren parameterTokens ++ resultTokens))
        ⟨name, parameters, result⟩

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨function_def⟩.

⟨function_def⟩ ::= ⟨symbol⟩ `(` ⟨sorted_var⟩∗ `)` ⟨sort⟩ ⟨term⟩
-/
inductive FunctionDef (version : Version) : List SyntaxToken → Tree.FunctionDef → Prop
  | mk : Each (SortedVar version) parameterTokens parameters →
      «Sort» version resultTokens result → Term version bodyTokens body →
      FunctionDef version
        (.symbol name :: paren parameterTokens ++ resultTokens ++ bodyTokens)
        ⟨name, parameters, result, body⟩

/--
Standard: 2.5 and 2.6 §3.9 Scripts; App. B ⟨prop_literal⟩.

⟨prop_literal⟩ ::= ⟨symbol⟩ | `(` `not` ⟨symbol⟩ `)`, where `not` is the symbol of that name,
quoted or not.
-/
inductive PropLiteral : List SyntaxToken → Tree.PropLiteral → Prop
  | positive : PropLiteral [.symbol name] (.positive name)
  | negative : negation.name = chars "not" →
      PropLiteral (paren [.symbol negation, .symbol name]) (.negative negation name)

/--
Standard: 2.7 §3.11 Scripts; App. B ⟨command⟩, ⟨option⟩ and ⟨info_flag⟩ of each version, the
standard commands only. Reading P4: each version accepts only a declaration of itself.

TODO: disagrees with P4 in `BSmtLib.Spec`, under which a declaration is parsed in the version
in force; each version is then to accept a declaration of any supported version.

⟨command⟩
-/
inductive Command (version : Version) : List SyntaxToken → Tree.Command → Prop
  /-- `(` `assert` ⟨term⟩ `)` -/
  | assert : Term version tokens term →
      Command version (commandTokens "assert" tokens) (.assert term)

  /-- `(` `check-sat` `)` -/
  | checkSat : Command version (commandTokens "check-sat" []) .checkSat

  /-- `(` `check-sat-assuming` `(` ⟨term⟩∗ `)` `)`, from 2.7 on -/
  | checkSatAssuming : versionAtLeast version .v2_7 → Each (Term version) tokens terms →
      Command version (commandTokens "check-sat-assuming" (paren tokens))
        (.checkSatAssuming terms)

  /-- `(` `check-sat-assuming` `(` ⟨prop_literal⟩∗ `)` `)`, in 2.5 and 2.6 -/
  | checkSatAssumingLiterals : versionAtLeast version .v2_5 → ¬ versionAtLeast version .v2_7 →
      Each PropLiteral tokens literals →
      Command version (commandTokens "check-sat-assuming" (paren tokens))
        (.checkSatAssumingLiterals literals)

  /-- `(` `declare-const` ⟨symbol⟩ ⟨sort⟩ `)`, from 2.5 on -/
  | declareConst : versionAtLeast version .v2_5 → «Sort» version tokens sort →
      Command version (commandTokens "declare-const" (.symbol name :: tokens))
        (.declareConst name sort)

  /-- `(` `declare-datatype` ⟨symbol⟩ ⟨datatype_dec⟩ `)`, from 2.6 on -/
  | declareDatatype : versionAtLeast version .v2_6 → DatatypeDec version tokens datatype →
      Command version (commandTokens "declare-datatype" (.symbol name :: tokens))
        (.declareDatatype name datatype)

  /-- `(` `declare-datatypes` `(` ⟨sort_dec⟩ⁿ⁺¹ `)` `(` ⟨datatype_dec⟩ⁿ⁺¹ `)` `)`, from 2.6 on -/
  | declareDatatypes : versionAtLeast version .v2_6 → Each SortDec sortTokens sorts →
      Each (DatatypeDec version) datatypeTokens datatypes → sorts ≠ [] →
      sorts.length = datatypes.length →
      Command version
        (commandTokens "declare-datatypes" (paren sortTokens ++ paren datatypeTokens))
        (.declareDatatypes sorts datatypes)

  /-- `(` `declare-fun` ⟨symbol⟩ `(` ⟨sort⟩∗ `)` ⟨sort⟩ `)` -/
  | declareFun : Each («Sort» version) parameterTokens parameters →
      «Sort» version resultTokens result →
      Command version
        (commandTokens "declare-fun" (.symbol name :: paren parameterTokens ++ resultTokens))
        (.declareFun name parameters result)

  /-- `(` `declare-sort` ⟨symbol⟩ ⟨numeral⟩ `)` -/
  | declareSort :
      Command version (commandTokens "declare-sort" [.symbol name, .numeral arity])
      (.declareSort name arity)

  /-- `(` `declare-sort-parameter` ⟨symbol⟩ `)`, from 2.7 on -/
  | declareSortParameter : versionAtLeast version .v2_7 →
      Command version (commandTokens "declare-sort-parameter" [.symbol name])
        (.declareSortParameter name)

  /-- `(` `define-const` ⟨symbol⟩ ⟨sort⟩ ⟨term⟩ `)`, from 2.7 on -/
  | defineConst : versionAtLeast version .v2_7 → «Sort» version sortTokens sort →
      Term version termTokens term →
      Command version
        (commandTokens "define-const" (.symbol name :: sortTokens ++ termTokens))
        (.defineConst name sort term)

  /-- `(` `define-fun` ⟨function_def⟩ `)` -/
  | defineFun : FunctionDef version tokens definition →
      Command version (commandTokens "define-fun" tokens) (.defineFun definition)

  /-- `(` `define-fun-rec` ⟨function_def⟩ `)`, from 2.5 on -/
  | defineFunRec : versionAtLeast version .v2_5 → FunctionDef version tokens definition →
      Command version (commandTokens "define-fun-rec" tokens) (.defineFunRec definition)

  /-- `(` `define-funs-rec` `(` ⟨function_dec⟩ⁿ⁺¹ `)` `(` ⟨term⟩ⁿ⁺¹ `)` `)`, from 2.5 on -/
  | defineFunsRec : versionAtLeast version .v2_5 →
      Each (FunctionDec version) declarationTokens declarations →
      Each (Term version) bodyTokens bodies → declarations ≠ [] →
      declarations.length = bodies.length →
      Command version
        (commandTokens "define-funs-rec" (paren declarationTokens ++ paren bodyTokens))
        (.defineFunsRec declarations bodies)

  /-- `(` `define-sort` ⟨symbol⟩ `(` ⟨symbol⟩∗ `)` ⟨sort⟩ `)` -/
  | defineSort : Each Symbol parameterTokens parameters → «Sort» version sortTokens sort →
      Command version
        (commandTokens "define-sort" (.symbol name :: paren parameterTokens ++ sortTokens))
        (.defineSort name parameters sort)

  /-- `(` `echo` ⟨string⟩ `)`, from 2.5 on -/
  | echo : versionAtLeast version .v2_5 →
      Command version (commandTokens "echo" [.string content]) (.echo content)

  /-- `(` `exit` `)` -/
  | exit : Command version (commandTokens "exit" []) .exit

  /-- `(` `get-assertions` `)` -/
  | getAssertions : Command version (commandTokens "get-assertions" []) .getAssertions

  /-- `(` `get-assignment` `)` -/
  | getAssignment : Command version (commandTokens "get-assignment" []) .getAssignment

  /-- `(` `get-info` ⟨info_flag⟩ `)`, where ⟨info_flag⟩ is any ⟨keyword⟩ -/
  | getInfo : Command version (commandTokens "get-info" [.keyword flag]) (.getInfo flag)

  /-- `(` `get-model` `)`, from 2.5 on -/
  | getModel : versionAtLeast version .v2_5 →
      Command version (commandTokens "get-model" []) .getModel

  /-- `(` `get-option` ⟨keyword⟩ `)` -/
  | getOption : Command version (commandTokens "get-option" [.keyword name]) (.getOption name)

  /-- `(` `get-proof` `)` -/
  | getProof : Command version (commandTokens "get-proof" []) .getProof

  /-- `(` `get-unsat-assumptions` `)`, from 2.5 on -/
  | getUnsatAssumptions : versionAtLeast version .v2_5 →
      Command version (commandTokens "get-unsat-assumptions" []) .getUnsatAssumptions

  /-- `(` `get-unsat-core` `)` -/
  | getUnsatCore : Command version (commandTokens "get-unsat-core" []) .getUnsatCore

  /-- `(` `get-value` `(` ⟨term⟩+ `)` `)` -/
  | getValue : Each (Term version) tokens terms → terms ≠ [] →
      Command version (commandTokens "get-value" (paren tokens)) (.getValue terms)

  /-- `(` `pop` ⟨numeral⟩ `)` -/
  | pop : Command version (commandTokens "pop" [.numeral count]) (.pop count)

  /-- `(` `push` ⟨numeral⟩ `)` -/
  | push : Command version (commandTokens "push" [.numeral count]) (.push count)

  /-- `(` `reset` `)`, from 2.5 on -/
  | reset : versionAtLeast version .v2_5 → Command version (commandTokens "reset" []) .reset

  /-- `(` `reset-assertions` `)`, from 2.5 on -/
  | resetAssertions : versionAtLeast version .v2_5 →
      Command version (commandTokens "reset-assertions" []) .resetAssertions

  /-- `(` `set-info` ⟨attribute⟩ `)`, for every attribute but `:smt-lib-version` -/
  | setInfo : Attribute version tokens info → info.keyword ≠ chars "smt-lib-version" →
      Command version (commandTokens "set-info" tokens) (.setInfo info)

  /--
  `(` `set-info` `:smt-lib-version` ⟨decimal⟩ `)`, where the decimal is the number of the
  version: a version declaration is parsed in the version it declares (see `ScriptParse`), and
  each version accepts only its own number. The standard does not say what a declaration of a
  version other than the one it is parsed in means; it is rejected, as a version number could
  not mean anything otherwise.
  -/
  | declareVersion :
      Command version
        (commandTokens "set-info"
          [.keyword (chars "smt-lib-version"), .decimal (versionNumber version)])
        (.setInfo ⟨chars "smt-lib-version", some (.constant (.decimal (versionNumber version)))⟩)

  /-- `(` `set-logic` ⟨symbol⟩ `)` -/
  | setLogic : Command version (commandTokens "set-logic" [.symbol name]) (.setLogic name)

  /--
  `(` `set-option` ⟨option⟩ `)`, where ⟨option⟩ is any ⟨attribute⟩: the standard defines the
  meaning of its predefined options, and every other option is an attribute too.
  -/
  | setOption : Attribute version tokens option →
      Command version (commandTokens "set-option" tokens) (.setOption option)

end BSmtLib.Spec.Grammar
