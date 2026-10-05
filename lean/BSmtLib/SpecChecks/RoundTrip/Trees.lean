import BSmtLib.Spec.Grammar

/-!
# Printing syntax trees

A printer from syntax trees to syntax tokens for every syntactic category the grammar has a rule
for, and the proof that the rules relate a tree only to its printed tokens: whatever tokens a
tree is read from are the tokens printed for it. Reading a tree back from its printed tokens
follows at once, and so does printing again what was read.

The printer follows the rules one to one. Where a rule leaves the choice of tokens to the
tree, the tree decides: an identifier without indices is a symbol, a sort without arguments an
identifier, an attribute without a value a keyword, and a datatype without parameters has no
`par`. No version is needed: the versions differ in which trees they accept, not in the tokens
of a tree.

The key lemmas, one per category, go by recursion over the derivation: each constructor of a
rule is matched by the printer's case for the tree it builds.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Grammar

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar

/-! ## The printer -/

/-- The tokens of a spec constant. -/
def printSpecConstant : Tree.SpecConstant → List SyntaxToken
  | .numeral digits => [.numeral digits]
  | .decimal text => [.decimal text]
  | .hexadecimal digits => [.hexadecimal digits]
  | .binary digits => [.binary digits]
  | .string content => [.string content]

/-- The tokens of a symbol. -/
def printSymbol (symbol : Tree.Symbol) : List SyntaxToken := [.symbol symbol]

mutual

/-- The tokens of an s-expression. -/
def printSExpr : Tree.SExpr → List SyntaxToken
  | .constant constant => printSpecConstant constant
  | .symbol symbol => [.symbol symbol]
  | .reserved w => [.reserved w]
  | .keyword name => [.keyword name]
  | .list items => paren (printSExprs items)

/-- The tokens of s-expressions, one after another. -/
def printSExprs : List Tree.SExpr → List SyntaxToken
  | [] => []
  | item :: items => printSExpr item ++ printSExprs items

end

/-- The tokens of an index. -/
def printIndex : Tree.Index → List SyntaxToken
  | .numeral digits => [.numeral digits]
  | .symbol symbol => [.symbol symbol]

/-- The tokens of an identifier: a symbol, or the indexed form if it has indices. -/
def printIdentifier : Tree.Identifier → List SyntaxToken
  | ⟨symbol, []⟩ => [.symbol symbol]
  | ⟨symbol, indices@(_ :: _)⟩ => paren (word "_" :: .symbol symbol :: indices.flatMap printIndex)

mutual

/-- The tokens of a sort: an identifier, or the application if it has arguments. -/
def printSort : Tree.Sort → List SyntaxToken
  | .mk identifier [] => printIdentifier identifier
  | .mk identifier (argument :: arguments) =>
    paren (printIdentifier identifier ++ (printSort argument ++ printSorts arguments))

/-- The tokens of sorts, one after another. -/
def printSorts : List Tree.Sort → List SyntaxToken
  | [] => []
  | sort :: sorts => printSort sort ++ printSorts sorts

end

/-- The tokens of an attribute value. -/
def printAttributeValue : Tree.AttributeValue → List SyntaxToken
  | .constant constant => printSpecConstant constant
  | .symbol symbol => [.symbol symbol]
  | .list items => paren (printSExprs items)

/-- The tokens of an attribute: its keyword, and its value if it has one. -/
def printAttribute : Tree.Attribute → List SyntaxToken
  | ⟨name, none⟩ => [.keyword name]
  | ⟨name, some value⟩ => .keyword name :: printAttributeValue value

/-- The tokens of a qualified identifier. -/
def printQualIdentifier : Tree.QualIdentifier → List SyntaxToken
  | .plain identifier => printIdentifier identifier
  | .as identifier sort => paren (word "as" :: printIdentifier identifier ++ printSort sort)

/-- The tokens of a sorted variable. -/
def printSortedVar : Tree.SortedVar → List SyntaxToken
  | ⟨symbol, sort⟩ => paren (.symbol symbol :: printSort sort)

/-- The tokens of a symbol or the wildcard. -/
def printSymbolOrWildcard : Tree.SymbolOrWildcard → List SyntaxToken
  | .symbol symbol => [.symbol symbol]
  | .wildcard => [word "_"]

/-- The tokens of a pattern. -/
def printPattern : Tree.Pattern → List SyntaxToken
  | .single symbol => printSymbolOrWildcard symbol
  | .constructor symbol arguments =>
    paren (.symbol symbol :: arguments.flatMap printSymbolOrWildcard)

mutual

/-- The tokens of a term. -/
def printTerm : Tree.Term → List SyntaxToken
  | .constant constant => printSpecConstant constant
  | .identifier identifier => printQualIdentifier identifier
  | .application function arguments => paren (printQualIdentifier function ++ printTerms arguments)
  | .«let» bindings body => paren (word "let" :: paren (printBindings bindings) ++ printTerm body)
  | .lambda variables body =>
    paren (word "lambda" :: paren (variables.flatMap printSortedVar) ++ printTerm body)
  | .quantified .«forall» variables body =>
    paren (word "forall" :: paren (variables.flatMap printSortedVar) ++ printTerm body)
  | .quantified .«exists» variables body =>
    paren (word "exists" :: paren (variables.flatMap printSortedVar) ++ printTerm body)
  | .«match» scrutinee cases =>
    paren (word "match" :: printTerm scrutinee ++ paren (printCases cases))
  | .annotated term attributes =>
    paren (word "!" :: printTerm term ++ attributes.flatMap printAttribute)

/-- The tokens of terms, one after another. -/
def printTerms : List Tree.Term → List SyntaxToken
  | [] => []
  | term :: terms => printTerm term ++ printTerms terms

/-- The tokens of variable bindings, one after another. -/
def printBindings : List (Tree.Symbol × Tree.Term) → List SyntaxToken
  | [] => []
  | (symbol, term) :: bindings => paren (.symbol symbol :: printTerm term) ++ printBindings bindings

/-- The tokens of match cases, one after another. -/
def printCases : List (Tree.Pattern × Tree.Term) → List SyntaxToken
  | [] => []
  | (pattern, term) :: cases => paren (printPattern pattern ++ printTerm term) ++ printCases cases

end

/-- The tokens of a sort declaration. -/
def printSortDec : Tree.SortDec → List SyntaxToken
  | ⟨symbol, arity⟩ => paren [.symbol symbol, .numeral arity]

/-- The tokens of a selector declaration. -/
def printSelectorDec : Tree.SelectorDec → List SyntaxToken
  | ⟨symbol, sort⟩ => paren (.symbol symbol :: printSort sort)

/-- The tokens of a constructor declaration. -/
def printConstructorDec : Tree.ConstructorDec → List SyntaxToken
  | ⟨symbol, selectors⟩ => paren (.symbol symbol :: selectors.flatMap printSelectorDec)

/-- The tokens of a datatype declaration: with `par` if it has parameters. -/
def printDatatypeDec : Tree.DatatypeDec → List SyntaxToken
  | ⟨[], constructors⟩ => paren (constructors.flatMap printConstructorDec)
  | ⟨parameters@(_ :: _), constructors⟩ =>
    paren (word "par" :: paren (parameters.flatMap printSymbol) ++
      paren (constructors.flatMap printConstructorDec))

/-- The tokens of a function declaration. -/
def printFunctionDec : Tree.FunctionDec → List SyntaxToken
  | ⟨symbol, parameters, result⟩ =>
    paren (.symbol symbol :: paren (parameters.flatMap printSortedVar) ++ printSort result)

/-- The tokens of a function definition. -/
def printFunctionDef : Tree.FunctionDef → List SyntaxToken
  | ⟨symbol, parameters, result, body⟩ =>
    .symbol symbol :: paren (parameters.flatMap printSortedVar) ++ printSort result ++
      printTerm body

/-- The tokens of a propositional literal. -/
def printPropLiteral : Tree.PropLiteral → List SyntaxToken
  | .positive symbol => [.symbol symbol]
  | .negative negation symbol => paren [.symbol negation, .symbol symbol]

/-- The tokens of a command. -/
def printCommand : Tree.Command → List SyntaxToken
  | .assert term => commandTokens "assert" (printTerm term)
  | .checkSat => commandTokens "check-sat" []
  | .checkSatAssuming terms => commandTokens "check-sat-assuming" (paren (printTerms terms))
  | .checkSatAssumingLiterals literals =>
    commandTokens "check-sat-assuming" (paren (literals.flatMap printPropLiteral))
  | .declareConst symbol sort => commandTokens "declare-const" (.symbol symbol :: printSort sort)
  | .declareDatatype symbol datatype =>
    commandTokens "declare-datatype" (.symbol symbol :: printDatatypeDec datatype)
  | .declareDatatypes sorts datatypes =>
    commandTokens "declare-datatypes"
      (paren (sorts.flatMap printSortDec) ++ paren (datatypes.flatMap printDatatypeDec))
  | .declareFun symbol parameters result =>
    commandTokens "declare-fun" (.symbol symbol :: paren (printSorts parameters) ++ printSort result)
  | .declareSort symbol arity => commandTokens "declare-sort" [.symbol symbol, .numeral arity]
  | .declareSortParameter symbol => commandTokens "declare-sort-parameter" [.symbol symbol]
  | .defineConst symbol sort term =>
    commandTokens "define-const" (.symbol symbol :: printSort sort ++ printTerm term)
  | .defineFun definition => commandTokens "define-fun" (printFunctionDef definition)
  | .defineFunRec definition => commandTokens "define-fun-rec" (printFunctionDef definition)
  | .defineFunsRec declarations bodies =>
    commandTokens "define-funs-rec"
      (paren (declarations.flatMap printFunctionDec) ++ paren (printTerms bodies))
  | .defineSort symbol parameters sort =>
    commandTokens "define-sort"
      (.symbol symbol :: paren (parameters.flatMap printSymbol) ++ printSort sort)
  | .echo content => commandTokens "echo" [.string content]
  | .exit => commandTokens "exit" []
  | .getAssertions => commandTokens "get-assertions" []
  | .getAssignment => commandTokens "get-assignment" []
  | .getInfo flag => commandTokens "get-info" [.keyword flag]
  | .getModel => commandTokens "get-model" []
  | .getOption name => commandTokens "get-option" [.keyword name]
  | .getProof => commandTokens "get-proof" []
  | .getUnsatAssumptions => commandTokens "get-unsat-assumptions" []
  | .getUnsatCore => commandTokens "get-unsat-core" []
  | .getValue terms => commandTokens "get-value" (paren (printTerms terms))
  | .pop count => commandTokens "pop" [.numeral count]
  | .push count => commandTokens "push" [.numeral count]
  | .reset => commandTokens "reset" []
  | .resetAssertions => commandTokens "reset-assertions" []
  | .setInfo info => commandTokens "set-info" (printAttribute info)
  | .setLogic symbol => commandTokens "set-logic" [.symbol symbol]
  | .setOption option => commandTokens "set-option" (printAttribute option)

/-! ## Tokens read are tokens printed -/

/-- Items derived one after another by a rule that relates every item only to its printed
tokens are derived only from their printed tokens, one after another. -/
theorem each_tokens {α : Type} {rule : List SyntaxToken → α → Prop}
    {print : α → List SyntaxToken} {tokens : List SyntaxToken} {items : List α}
    (he : Each rule tokens items) (h : ∀ tokens item, rule tokens item → tokens = print item) :
    tokens = items.flatMap print := by
  induction he with
  | nil => rfl
  | cons hfirst _ ih => rw [h _ _ hfirst, ih, List.flatMap_cons]

theorem specConstant_tokens {tokens : List SyntaxToken} {constant : Tree.SpecConstant}
    (h : SpecConstant tokens constant) : tokens = printSpecConstant constant := by
  cases h <;> rfl

theorem symbol_tokens {tokens : List SyntaxToken} {symbol : Tree.Symbol} (h : Symbol tokens symbol) :
    tokens = printSymbol symbol := by
  cases h
  rfl

mutual

theorem sExpr_tokens {version : Version} {tokens : List SyntaxToken} {item : Tree.SExpr} :
    SExpr version tokens item → tokens = printSExpr item
  | .constant h => specConstant_tokens h
  | .symbol => rfl
  | .reserved _ => rfl
  | .keyword => rfl
  | .list h => by rw [sExprs_tokens h]; rfl

theorem sExprs_tokens {version : Version} {tokens : List SyntaxToken} {items : List Tree.SExpr} :
    Each (SExpr version) tokens items → tokens = printSExprs items
  | .nil => rfl
  | .cons hfirst hrest => by rw [sExpr_tokens hfirst, sExprs_tokens hrest]; rfl

end

theorem index_tokens {version : Version} {tokens : List SyntaxToken} {index : Tree.Index}
    (h : Index version tokens index) : tokens = printIndex index := by
  cases h <;> rfl

theorem identifier_tokens {version : Version} {tokens : List SyntaxToken}
    {identifier : Tree.Identifier} (h : Identifier version tokens identifier) :
    tokens = printIdentifier identifier := by
  cases h with
  | symbol => rfl
  | indexed hindices hne =>
    rw [each_tokens hindices (fun _ _ => index_tokens)]
    obtain ⟨index, indices, rfl⟩ := List.exists_cons_of_ne_nil hne
    rfl

mutual

theorem sort_tokens {version : Version} {tokens : List SyntaxToken} {sort : Tree.Sort} :
    Grammar.Sort version tokens sort → tokens = printSort sort
  | .identifier h => identifier_tokens h
  | .application hidentifier harguments hne => by
    rw [identifier_tokens hidentifier, sorts_tokens harguments]
    obtain ⟨argument, arguments, rfl⟩ := List.exists_cons_of_ne_nil hne
    rfl

theorem sorts_tokens {version : Version} {tokens : List SyntaxToken} {sorts : List Tree.Sort} :
    Each (Grammar.Sort version) tokens sorts → tokens = printSorts sorts
  | .nil => rfl
  | .cons hfirst hrest => by rw [sort_tokens hfirst, sorts_tokens hrest]; rfl

end

theorem attributeValue_tokens {version : Version} {tokens : List SyntaxToken}
    {value : Tree.AttributeValue} (h : AttributeValue version tokens value) :
    tokens = printAttributeValue value := by
  cases h with
  | constant h => exact specConstant_tokens h
  | symbol => rfl
  | list h => rw [sExprs_tokens h]; rfl

theorem attribute_tokens {version : Version} {tokens : List SyntaxToken}
    {attr : Tree.Attribute} (h : Attribute version tokens attr) :
    tokens = printAttribute attr := by
  cases h with
  | keyword => rfl
  | valued h => rw [attributeValue_tokens h]; rfl

theorem qualIdentifier_tokens {version : Version} {tokens : List SyntaxToken}
    {identifier : Tree.QualIdentifier} (h : QualIdentifier version tokens identifier) :
    tokens = printQualIdentifier identifier := by
  cases h with
  | plain h => exact identifier_tokens h
  | as hidentifier hsort => rw [identifier_tokens hidentifier, sort_tokens hsort]; rfl

theorem sortedVar_tokens {version : Version} {tokens : List SyntaxToken}
    {var : Tree.SortedVar} (h : SortedVar version tokens var) :
    tokens = printSortedVar var := by
  cases h with
  | mk h => rw [sort_tokens h]; rfl

theorem symbolOrWildcard_tokens {version : Version} {tokens : List SyntaxToken}
    {symbol : Tree.SymbolOrWildcard} (h : SymbolOrWildcard version tokens symbol) :
    tokens = printSymbolOrWildcard symbol := by
  cases h <;> rfl

theorem pattern_tokens {version : Version} {tokens : List SyntaxToken}
    {pattern : Tree.Pattern} (h : Pattern version tokens pattern) :
    tokens = printPattern pattern := by
  cases h with
  | single h => exact symbolOrWildcard_tokens h
  | constructor h _ => rw [each_tokens h (fun _ _ => symbolOrWildcard_tokens)]; rfl

mutual

theorem term_tokens {version : Version} {tokens : List SyntaxToken} {term : Tree.Term} :
    Grammar.Term version tokens term → tokens = printTerm term
  | .constant h => specConstant_tokens h
  | .identifier h => qualIdentifier_tokens h
  | .application hfunction harguments _ => by
    rw [qualIdentifier_tokens hfunction, terms_tokens harguments]; rfl
  | .«let» hbindings _ hbody => by
    rw [bindings_tokens hbindings, term_tokens hbody]; rfl
  | .lambda _ hvariables _ hbody => by
    rw [each_tokens hvariables (fun _ _ => sortedVar_tokens), term_tokens hbody]; rfl
  | .«forall» hvariables _ hbody => by
    rw [each_tokens hvariables (fun _ _ => sortedVar_tokens), term_tokens hbody]; rfl
  | .«exists» hvariables _ hbody => by
    rw [each_tokens hvariables (fun _ _ => sortedVar_tokens), term_tokens hbody]; rfl
  | .«match» _ hscrutinee hcases _ => by
    rw [term_tokens hscrutinee, cases_tokens hcases]; rfl
  | .annotated hterm hattributes _ => by
    rw [term_tokens hterm, each_tokens hattributes (fun _ _ => attribute_tokens)]; rfl

theorem terms_tokens {version : Version} {tokens : List SyntaxToken} {terms : List Tree.Term} :
    Each (Grammar.Term version) tokens terms → tokens = printTerms terms
  | .nil => rfl
  | .cons hfirst hrest => by rw [term_tokens hfirst, terms_tokens hrest]; rfl

theorem bindings_tokens {version : Version} {tokens : List SyntaxToken}
    {bindings : List (Tree.Symbol × Tree.Term)} :
    Bindings version tokens bindings → tokens = printBindings bindings
  | .nil => rfl
  | .cons hterm hrest => by rw [term_tokens hterm, bindings_tokens hrest]; rfl

theorem cases_tokens {version : Version} {tokens : List SyntaxToken}
    {cases : List (Tree.Pattern × Tree.Term)} :
    Cases version tokens cases → tokens = printCases cases
  | .nil => rfl
  | .cons hpattern hterm hrest => by
    rw [pattern_tokens hpattern, term_tokens hterm, cases_tokens hrest]; rfl

end

theorem sortDec_tokens {tokens : List SyntaxToken} {sort : Tree.SortDec}
    (h : SortDec tokens sort) : tokens = printSortDec sort := by
  cases h
  rfl

theorem selectorDec_tokens {version : Version} {tokens : List SyntaxToken}
    {selector : Tree.SelectorDec} (h : SelectorDec version tokens selector) :
    tokens = printSelectorDec selector := by
  cases h with
  | mk h => rw [sort_tokens h]; rfl

theorem constructorDec_tokens {version : Version} {tokens : List SyntaxToken}
    {constructor : Tree.ConstructorDec} (h : ConstructorDec version tokens constructor) :
    tokens = printConstructorDec constructor := by
  cases h with
  | mk h => rw [each_tokens h (fun _ _ => selectorDec_tokens)]; rfl

theorem datatypeDec_tokens {version : Version} {tokens : List SyntaxToken}
    {datatype : Tree.DatatypeDec} (h : DatatypeDec version tokens datatype) :
    tokens = printDatatypeDec datatype := by
  cases h with
  | plain h _ => rw [each_tokens h (fun _ _ => constructorDec_tokens)]; rfl
  | parametric hparameters hne hconstructors _ =>
    rw [each_tokens hparameters (fun _ _ => symbol_tokens),
      each_tokens hconstructors (fun _ _ => constructorDec_tokens)]
    obtain ⟨parameter, parameters, rfl⟩ := List.exists_cons_of_ne_nil hne
    rfl

theorem functionDec_tokens {version : Version} {tokens : List SyntaxToken}
    {declaration : Tree.FunctionDec} (h : FunctionDec version tokens declaration) :
    tokens = printFunctionDec declaration := by
  cases h with
  | mk hparameters hresult =>
    rw [each_tokens hparameters (fun _ _ => sortedVar_tokens), sort_tokens hresult]; rfl

theorem functionDef_tokens {version : Version} {tokens : List SyntaxToken}
    {definition : Tree.FunctionDef} (h : FunctionDef version tokens definition) :
    tokens = printFunctionDef definition := by
  cases h with
  | mk hparameters hresult hbody =>
    rw [each_tokens hparameters (fun _ _ => sortedVar_tokens), sort_tokens hresult,
      term_tokens hbody]
    rfl

theorem propLiteral_tokens {tokens : List SyntaxToken} {literal : Tree.PropLiteral}
    (h : PropLiteral tokens literal) : tokens = printPropLiteral literal := by
  cases h <;> rfl

theorem command_tokens {version : Version} {tokens : List SyntaxToken}
    {command : Tree.Command} (h : Grammar.Command version tokens command) :
    tokens = printCommand command := by
  cases h with
  | assert h => rw [term_tokens h]; rfl
  | checkSatAssuming _ h => rw [terms_tokens h]; rfl
  | checkSatAssumingLiterals _ _ h => rw [each_tokens h (fun _ _ => propLiteral_tokens)]; rfl
  | declareConst _ h => rw [sort_tokens h]; rfl
  | declareDatatype _ h => rw [datatypeDec_tokens h]; rfl
  | declareDatatypes _ hsorts hdatatypes =>
    rw [each_tokens hsorts (fun _ _ => sortDec_tokens),
      each_tokens hdatatypes (fun _ _ => datatypeDec_tokens)]
    rfl
  | declareFun hparameters hresult => rw [sorts_tokens hparameters, sort_tokens hresult]; rfl
  | defineConst _ hsort hterm => rw [sort_tokens hsort, term_tokens hterm]; rfl
  | defineFun h => rw [functionDef_tokens h]; rfl
  | defineFunRec _ h => rw [functionDef_tokens h]; rfl
  | defineFunsRec _ hdeclarations hbodies =>
    rw [each_tokens hdeclarations (fun _ _ => functionDec_tokens), terms_tokens hbodies]
    rfl
  | defineSort hparameters hsort =>
    rw [each_tokens hparameters (fun _ _ => symbol_tokens), sort_tokens hsort]
    rfl
  | getValue h _ => rw [terms_tokens h]; rfl
  | setInfo h _ => rw [attribute_tokens h]; rfl
  | setOption h => rw [attribute_tokens h]; rfl
  | _ => rfl

end BSmtLib.SpecChecks.Grammar
