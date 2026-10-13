import BSmtLib.SpecChecks.Grammar.Read

/-!
# Trees are read back from their tokens

Each reader of `Grammar.Read` reads the tokens of a tree back as that tree, whatever follows
them: `readTerm_tokens` for terms and `readCommand_tokens` for the commands of a version, with
a lemma for each category below. Each goes by the shape of the tree, the readers of nested
categories by induction on their fuel.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Grammar

open BSmtLibSpec BSmtLibSpec.Lexicon BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLibSpec.Lexicon.Properties
open BSmtLibSpec.Regex (Chars chars)

theorem readIndices_tokens (indices : List Tree.Index) (rest : List SyntaxToken) :
    readIndices (indices.flatMap Tree.Index.tokens ++ .parenClose :: rest) =
      some (indices, rest) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
    cases index <;> simp [Tree.Index.tokens, readIndices, ih]

theorem readIdentifier_tokens (identifier : Tree.Identifier) (rest : List SyntaxToken) :
    readIdentifier (identifier.tokens ++ rest) = some (identifier, rest) := by
  obtain ⟨symbol, indices⟩ := identifier
  cases indices with
  | nil => rfl
  | cons index indices =>
    have h := readIndices_tokens (index :: indices) rest
    simp only [List.flatMap_cons, List.append_assoc] at h
    simp [Tree.Identifier.tokens, paren, word, readIdentifier, h]

theorem startsWord_identifier (w : String) (identifier : Tree.Identifier)
    (rest : List SyntaxToken) : startsWord w (identifier.tokens ++ rest) = false := by
  obtain ⟨symbol, indices⟩ := identifier
  cases indices <;> simp [Tree.Identifier.tokens, paren, word, startsWord]

theorem startsClose_identifier (identifier : Tree.Identifier) (rest : List SyntaxToken) :
    startsClose (identifier.tokens ++ rest) = false := by
  obtain ⟨symbol, indices⟩ := identifier
  cases indices <;> simp [Tree.Identifier.tokens, paren, startsClose]

theorem startsClose_sort (sort : Tree.Sort) (rest : List SyntaxToken) :
    startsClose (sort.tokens ++ rest) = false := by
  obtain ⟨identifier, arguments⟩ := sort
  cases arguments with
  | nil => simpa [Tree.Sort.tokens] using startsClose_identifier identifier rest
  | cons => simp [Tree.Sort.tokens, paren, startsClose]

theorem startsGroup_identifier_args (identifier : Tree.Identifier) (rest : List SyntaxToken) :
    startsGroup "_" (.parenOpen :: (identifier.tokens ++ rest)) = false := by
  simp [startsGroup, startsWord_identifier]

theorem readSort_tokens_aux : ∀ n,
    (∀ (sort : Tree.Sort) rest, sizeOf sort < n →
      readSort n (sort.tokens ++ rest) = some (sort, rest)) ∧
    (∀ (sorts : List Tree.Sort) rest, sizeOf sorts < n →
      readSorts n (Tree.Sort.tokensAll sorts ++ .parenClose :: rest) = some (sorts, rest))
  | 0 => ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨ih₁, ih₂⟩ := readSort_tokens_aux n
    refine ⟨fun sort rest h => ?_, fun sorts rest h => ?_⟩
    · obtain ⟨⟨symbol, indices⟩, arguments⟩ := sort
      cases arguments with
      | nil =>
        cases indices with
        | nil => simp [Tree.Sort.tokens, Tree.Identifier.tokens, readSort, startsGroup,
            readIdentifier]
        | cons index indices =>
          have h₁ := readIdentifier_tokens ⟨symbol, index :: indices⟩ rest
          have h₂ : startsGroup "_" (Tree.Identifier.tokens ⟨symbol, index :: indices⟩ ++ rest) =
            true := by simp [Tree.Identifier.tokens, paren, word, startsGroup, startsWord]
          simp only [Tree.Sort.tokens, readSort, h₂, ite_true, h₁]
          rfl
      | cons argument arguments =>
        simp only [Tree.Sort.mk.sizeOf_spec, List.cons.sizeOf_spec] at h
        have h₂ := ih₂ (argument :: arguments) rest (by simp; omega)
        simp [Tree.Sort.tokens, paren, readSort, startsGroup_identifier_args,
          readIdentifier_tokens, h₂]
    · cases sorts with
      | nil => simp [Tree.Sort.tokensAll, readSorts, startsClose]
      | cons sort sorts =>
        simp only [List.cons.sizeOf_spec] at h
        simp [Tree.Sort.tokensAll, readSorts, startsClose_sort, ih₁ sort _ (by omega),
          ih₂ sorts rest (by omega)]

theorem readSort_tokens (sort : Tree.Sort) (rest : List SyntaxToken) {n : Nat}
    (h : sizeOf sort < n) : readSort n (sort.tokens ++ rest) = some (sort, rest) :=
  (readSort_tokens_aux n).1 sort rest h

theorem readSorts_tokens (sorts : List Tree.Sort) (rest : List SyntaxToken) {n : Nat}
    (h : sizeOf sorts < n) :
    readSorts n (Tree.Sort.tokensAll sorts ++ .parenClose :: rest) = some (sorts, rest) :=
  (readSort_tokens_aux n).2 sorts rest h

theorem readConstant_token (constant : Tree.SpecConstant) :
    readConstant constant.token = some constant := by
  cases constant <;> rfl

theorem startsClose_sExpr (sExpr : Tree.SExpr) (rest : List SyntaxToken) :
    startsClose (sExpr.tokens ++ rest) = false := by
  cases sExpr with
  | constant constant => cases constant <;> rfl
  | list => simp [Tree.SExpr.tokens, paren, startsClose]
  | _ => rfl

theorem readSExpr_tokens_aux : ∀ n,
    (∀ (sExpr : Tree.SExpr) rest, sizeOf sExpr < n →
      readSExpr n (sExpr.tokens ++ rest) = some (sExpr, rest)) ∧
    (∀ (sExprs : List Tree.SExpr) rest, sizeOf sExprs < n →
      readSExprs n (Tree.SExpr.tokensAll sExprs ++ .parenClose :: rest) = some (sExprs, rest))
  | 0 => ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨ih₁, ih₂⟩ := readSExpr_tokens_aux n
    refine ⟨fun sExpr rest h => ?_, fun sExprs rest h => ?_⟩
    · cases sExpr with
      | constant constant => cases constant <;> rfl
      | list items =>
        simp only [Tree.SExpr.list.sizeOf_spec] at h
        simp [Tree.SExpr.tokens, paren, readSExpr, ih₂ items rest (by omega)]
      | _ => rfl
    · cases sExprs with
      | nil => simp [Tree.SExpr.tokensAll, readSExprs, startsClose]
      | cons sExpr sExprs =>
        simp only [List.cons.sizeOf_spec] at h
        simp [Tree.SExpr.tokensAll, readSExprs, startsClose_sExpr, ih₁ sExpr _ (by omega),
          ih₂ sExprs rest (by omega)]

theorem readSExprs_tokens (sExprs : List Tree.SExpr) (rest : List SyntaxToken) {n : Nat}
    (h : sizeOf sExprs < n) :
    readSExprs n (Tree.SExpr.tokensAll sExprs ++ .parenClose :: rest) = some (sExprs, rest) :=
  (readSExpr_tokens_aux n).2 sExprs rest h

theorem readAttributeValue_tokens (value : Tree.AttributeValue) (rest : List SyntaxToken)
    {n : Nat} (h : sizeOf value < n) :
    readAttributeValue n (value.tokens ++ rest) = some (value, rest) := by
  cases value with
  | constant constant => cases constant <;> rfl
  | symbol => rfl
  | list items =>
    simp only [Tree.AttributeValue.list.sizeOf_spec] at h
    simp [Tree.AttributeValue.tokens, paren, readAttributeValue,
      readSExprs_tokens items rest (n := n) (by omega)]

theorem startsValue_value (value : Tree.AttributeValue) (rest : List SyntaxToken) :
    startsValue (value.tokens ++ rest) = true := by
  cases value with
  | constant constant => cases constant <;> rfl
  | symbol => rfl
  | list => simp [Tree.AttributeValue.tokens, paren, startsValue]

/-- An attribute is read back from its tokens when no value follows one that has none. -/
theorem readAttribute_tokens (annotation : Tree.Attribute) (rest : List SyntaxToken) {n : Nat}
    (h : sizeOf annotation < n) (hrest : annotation.value = none → startsValue rest = false) :
    readAttribute n (annotation.tokens ++ rest) = some (annotation, rest) := by
  obtain ⟨keyword, value⟩ := annotation
  cases value with
  | none => simp [Tree.Attribute.tokens, readAttribute, hrest rfl]
  | some value =>
    simp only [Tree.Attribute.mk.sizeOf_spec, Option.some.sizeOf_spec] at h
    simp [Tree.Attribute.tokens, readAttribute, startsValue_value,
      readAttributeValue_tokens value rest (n := n) (by omega)]

theorem readAttributes_tokens : ∀ (attributes : List Tree.Attribute) (rest : List SyntaxToken)
    {n : Nat}, sizeOf attributes < n →
    readAttributes n (attributes.flatMap Tree.Attribute.tokens ++ .parenClose :: rest) =
      some (attributes, rest)
  | [], _, n + 1, _ => by simp [readAttributes, startsClose]
  | annotation :: attributes, rest, n + 1, h => by
    simp only [List.cons.sizeOf_spec] at h
    have hfirst : ∀ r, startsClose (annotation.tokens ++ r) = false := by
      intro r
      obtain ⟨keyword, value⟩ := annotation
      cases value <;> rfl
    have hnext : annotation.value = none →
        startsValue (attributes.flatMap Tree.Attribute.tokens ++ .parenClose :: rest) =
          false := by
      intro
      cases attributes with
      | nil => rfl
      | cons next _ =>
        obtain ⟨keyword, value⟩ := next
        cases value <;> rfl
    simp [readAttributes, List.append_assoc, readAttribute_tokens annotation _ (n := n)
      (by omega) hnext, readAttributes_tokens attributes rest (n := n) (by omega), hfirst]

theorem startsGroup_identifier (identifier : Tree.Identifier) (rest : List SyntaxToken) :
    startsGroup "as" (identifier.tokens ++ rest) = false := by
  obtain ⟨symbol, indices⟩ := identifier
  cases indices <;> simp +decide [Tree.Identifier.tokens, paren, word, startsGroup, startsWord]

theorem readQualIdentifier_tokens (qualified : Tree.QualIdentifier) (rest : List SyntaxToken)
    {n : Nat} (h : sizeOf qualified < n) :
    readQualIdentifier n (qualified.tokens ++ rest) = some (qualified, rest) := by
  cases qualified with
  | plain identifier =>
    simp [Tree.QualIdentifier.tokens, readQualIdentifier, startsGroup_identifier,
      readIdentifier_tokens]
  | as identifier sort =>
    simp only [Tree.QualIdentifier.as.sizeOf_spec] at h
    simp [Tree.QualIdentifier.tokens, paren, word, readQualIdentifier, startsGroup, startsWord,
      readIdentifier_tokens, readSort_tokens sort _ (n := n) (by omega), expectClose]

theorem startsWord_qualIdentifier (w : String) (qualified : Tree.QualIdentifier)
    (rest : List SyntaxToken) : startsWord w (qualified.tokens ++ rest) = false := by
  cases qualified with
  | plain identifier => exact startsWord_identifier w identifier rest
  | as => simp [Tree.QualIdentifier.tokens, paren, startsWord]

theorem readSortedVars_tokens : ∀ (variables : List Tree.SortedVar) (rest : List SyntaxToken)
    {n : Nat}, sizeOf variables < n →
    readSortedVars n (variables.flatMap Tree.SortedVar.tokens ++ .parenClose :: rest) =
      some (variables, rest)
  | [], _, n + 1, _ => by simp [readSortedVars]
  | ⟨symbol, sort⟩ :: variables, rest, n + 1, h => by
    simp only [List.cons.sizeOf_spec, Tree.SortedVar.mk.sizeOf_spec] at h
    simp [Tree.SortedVar.tokens, paren, readSortedVars, readSort_tokens sort _ (n := n)
      (by omega), expectClose, readSortedVars_tokens variables rest (n := n) (by omega)]

theorem readSymbolOrWildcard_token (symbol : Tree.SymbolOrWildcard) :
    readSymbolOrWildcard symbol.token = some symbol := by
  cases symbol <;> simp [Tree.SymbolOrWildcard.token, word, readSymbolOrWildcard]

theorem readSymbolOrWildcards_tokens (symbols : List Tree.SymbolOrWildcard)
    (rest : List SyntaxToken) :
    readSymbolOrWildcards (symbols.map Tree.SymbolOrWildcard.token ++ .parenClose :: rest) =
      some (symbols, rest) := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols ih =>
    cases symbol <;>
      simp [Tree.SymbolOrWildcard.token, word, readSymbolOrWildcards, readSymbolOrWildcard, ih]

theorem readPattern_tokens (pattern : Tree.Pattern) (rest : List SyntaxToken) :
    readPattern (pattern.tokens ++ rest) = some (pattern, rest) := by
  cases pattern with
  | single symbol =>
    cases symbol <;>
      simp [Tree.Pattern.tokens, Tree.SymbolOrWildcard.token, word, readPattern,
        readSymbolOrWildcard]
  | constructor head arguments =>
    simp [Tree.Pattern.tokens, paren, readPattern, readSymbolOrWildcards_tokens]

theorem startsClose_term (term : Tree.Term) (rest : List SyntaxToken) :
    startsClose (term.tokens ++ rest) = false := by
  cases term with
  | constant constant => cases constant <;> rfl
  | identifier qualified =>
    cases qualified with
    | plain identifier => simpa [Tree.Term.tokens, Tree.QualIdentifier.tokens] using
        startsClose_identifier identifier rest
    | as => simp [Tree.Term.tokens, Tree.QualIdentifier.tokens, paren, startsClose]
  | _ => simp [Tree.Term.tokens, paren, startsClose]

theorem quantifierOf_qualIdentifier (qualified : Tree.QualIdentifier) (rest : List SyntaxToken) :
    quantifierOf (qualified.tokens ++ rest) = none := by
  simp [quantifierOf, startsWord_qualIdentifier]

theorem readTerm_tokens_aux : ∀ n,
    (∀ (term : Tree.Term) rest, sizeOf term < n →
      readTerm n (term.tokens ++ rest) = some (term, rest)) ∧
    (∀ (terms : List Tree.Term) rest, sizeOf terms < n →
      readTerms n (Tree.Term.tokensAll terms ++ .parenClose :: rest) = some (terms, rest)) ∧
    (∀ (bindings : List (Tree.Symbol × Tree.Term)) rest, sizeOf bindings < n →
      readBindings n (Tree.Term.bindingTokens bindings ++ .parenClose :: rest) =
        some (bindings, rest)) ∧
    (∀ (cases : List (Tree.Pattern × Tree.Term)) rest, sizeOf cases < n →
      readCases n (Tree.Term.caseTokens cases ++ .parenClose :: rest) = some (cases, rest))
  | 0 => ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ := readTerm_tokens_aux n
    refine ⟨fun term rest h => ?_, fun terms rest h => ?_, fun bindings rest h => ?_,
      fun cases rest h => ?_⟩
    · cases term with
      | constant constant => cases constant <;> rfl
      | identifier qualified =>
        simp only [Tree.Term.identifier.sizeOf_spec] at h
        have hq := readQualIdentifier_tokens qualified rest (n := n) (by omega)
        cases qualified with
        | plain identifier =>
          obtain ⟨symbol, indices⟩ := identifier
          cases indices with
          | nil => rfl
          | cons =>
            simp [Tree.Term.tokens, Tree.QualIdentifier.tokens, Tree.Identifier.tokens, paren,
              word] at hq ⊢
            simp [readTerm, startsWord, hq]
        | as =>
          simp [Tree.Term.tokens, Tree.QualIdentifier.tokens, paren, word] at hq ⊢
          simp +decide [readTerm, startsWord, hq]
      | application function arguments =>
        simp only [Tree.Term.application.sizeOf_spec] at h
        simp [Tree.Term.tokens, paren, readTerm, startsWord_qualIdentifier,
          quantifierOf_qualIdentifier, readQualIdentifier_tokens function _ (n := n) (by omega),
          ih₂ arguments rest (by omega)]
      | «let» bindings body =>
        simp only [Tree.Term.let.sizeOf_spec] at h
        simp +decide [Tree.Term.tokens, paren, word, readTerm, startsWord,
          ih₃ bindings _ (by omega), ih₁ body _ (by omega), expectClose]
      | lambda variables body =>
        simp only [Tree.Term.lambda.sizeOf_spec] at h
        simp +decide [Tree.Term.tokens, paren, word, readTerm, startsWord,
          readSortedVars_tokens variables _ (n := n) (by omega), ih₁ body _ (by omega),
          expectClose]
      | quantified quantifier variables body =>
        simp only [Tree.Term.quantified.sizeOf_spec] at h
        cases quantifier <;>
        simp +decide [Tree.Term.tokens, Tree.Quantifier.word, paren, word, readTerm, startsWord,
          quantifierOf, readSortedVars_tokens variables _ (n := n) (by omega),
          ih₁ body _ (by omega), expectClose]
      | «match» scrutinee cases =>
        simp only [Tree.Term.match.sizeOf_spec] at h
        simp +decide [Tree.Term.tokens, paren, word, readTerm, startsWord, quantifierOf,
          ih₁ scrutinee _ (by omega), ih₄ cases _ (by omega), expectClose]
      | annotated term attributes =>
        simp only [Tree.Term.annotated.sizeOf_spec] at h
        simp +decide [Tree.Term.tokens, paren, word, readTerm, startsWord, quantifierOf,
          ih₁ term _ (by omega), readAttributes_tokens attributes rest (n := n) (by omega)]
    · cases terms with
      | nil => simp [Tree.Term.tokensAll, readTerms, startsClose]
      | cons term terms =>
        simp only [List.cons.sizeOf_spec] at h
        simp [Tree.Term.tokensAll, readTerms, startsClose_term, ih₁ term _ (by omega),
          ih₂ terms rest (by omega)]
    · cases bindings with
      | nil => simp [Tree.Term.bindingTokens, readBindings]
      | cons binding bindings =>
        obtain ⟨symbol, term⟩ := binding
        simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at h
        simp [Tree.Term.bindingTokens, paren, readBindings, ih₁ term _ (by omega), expectClose,
          ih₃ bindings rest (by omega)]
    · cases cases with
      | nil => simp [Tree.Term.caseTokens, readCases]
      | cons first cases =>
        obtain ⟨pattern, term⟩ := first
        simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at h
        simp [Tree.Term.caseTokens, paren, readCases, readPattern_tokens, ih₁ term _ (by omega),
          expectClose, ih₄ cases rest (by omega)]

theorem readTerm_tokens (term : Tree.Term) (rest : List SyntaxToken) {n : Nat}
    (h : sizeOf term < n) : readTerm n (term.tokens ++ rest) = some (term, rest) :=
  (readTerm_tokens_aux n).1 term rest h

theorem readTerms_tokens (terms : List Tree.Term) (rest : List SyntaxToken) {n : Nat}
    (h : sizeOf terms < n) :
    readTerms n (Tree.Term.tokensAll terms ++ .parenClose :: rest) = some (terms, rest) :=
  (readTerm_tokens_aux n).2.1 terms rest h

/-! ## The parts of commands -/

theorem readSymbols_tokens (symbols : List Tree.Symbol) (rest : List SyntaxToken) :
    readSymbols (symbols.map .symbol ++ .parenClose :: rest) = some (symbols, rest) := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols ih => simp [readSymbols, ih]

theorem readLiterals_tokens (literals : List Tree.PropLiteral) (rest : List SyntaxToken) :
    readLiterals (literals.flatMap Tree.PropLiteral.tokens ++ .parenClose :: rest) =
      some (literals, rest) := by
  induction literals with
  | nil => rfl
  | cons literal literals ih =>
    cases literal <;> simp [Tree.PropLiteral.tokens, paren, readLiterals, ih]

theorem readSortDecs_tokens (sorts : List Tree.SortDec) (rest : List SyntaxToken) :
    readSortDecs (sorts.flatMap Tree.SortDec.tokens ++ .parenClose :: rest) =
      some (sorts, rest) := by
  induction sorts with
  | nil => rfl
  | cons sort sorts ih => simp [Tree.SortDec.tokens, paren, readSortDecs, ih]

theorem readSelectors_tokens : ∀ (selectors : List Tree.SelectorDec) (rest : List SyntaxToken)
    {n : Nat}, sizeOf selectors < n →
    readSelectors n (selectors.flatMap Tree.SelectorDec.tokens ++ .parenClose :: rest) =
      some (selectors, rest)
  | [], _, n + 1, _ => by simp [readSelectors]
  | ⟨symbol, sort⟩ :: selectors, rest, n + 1, h => by
    simp only [List.cons.sizeOf_spec, Tree.SelectorDec.mk.sizeOf_spec] at h
    simp [Tree.SelectorDec.tokens, paren, readSelectors, readSort_tokens sort _ (n := n)
      (by omega), expectClose, readSelectors_tokens selectors rest (n := n) (by omega)]

theorem readConstructors_tokens : ∀ (constructors : List Tree.ConstructorDec)
    (rest : List SyntaxToken) {n : Nat}, sizeOf constructors < n →
    readConstructors n (constructors.flatMap Tree.ConstructorDec.tokens ++ .parenClose :: rest) =
      some (constructors, rest)
  | [], _, n + 1, _ => by simp [readConstructors]
  | ⟨symbol, selectors⟩ :: constructors, rest, n + 1, h => by
    simp only [List.cons.sizeOf_spec, Tree.ConstructorDec.mk.sizeOf_spec] at h
    simp [Tree.ConstructorDec.tokens, paren, readConstructors, readSelectors_tokens selectors _
      (n := n) (by omega), readConstructors_tokens constructors rest (n := n) (by omega)]

theorem readDatatype_tokens (datatype : Tree.DatatypeDec) (rest : List SyntaxToken) {n : Nat}
    (h : sizeOf datatype < n) :
    readDatatype n (datatype.tokens ++ rest) = some (datatype, rest) := by
  obtain ⟨parameters, constructors⟩ := datatype
  simp only [Tree.DatatypeDec.mk.sizeOf_spec] at h
  cases parameters with
  | nil =>
    have hc : startsWord "par" (constructors.flatMap Tree.ConstructorDec.tokens ++
        .parenClose :: rest) = false := by
      cases constructors <;> simp [Tree.ConstructorDec.tokens, paren, startsWord]
    simp [Tree.DatatypeDec.tokens, paren, readDatatype, hc,
      readConstructors_tokens constructors rest (n := n) (by omega)]
  | cons parameter parameters =>
    have hs := readSymbols_tokens (parameter :: parameters)
      (.parenOpen :: (constructors.flatMap Tree.ConstructorDec.tokens ++
        .parenClose :: .parenClose :: rest))
    simp only [List.map_cons, List.cons_append] at hs
    simp [Tree.DatatypeDec.tokens, paren, word, readDatatype, startsWord, hs,
      readConstructors_tokens constructors _ (n := n) (by omega), expectClose]

theorem readDatatypes_tokens : ∀ (datatypes : List Tree.DatatypeDec) (rest : List SyntaxToken)
    {n : Nat}, sizeOf datatypes < n →
    readDatatypes n (datatypes.flatMap Tree.DatatypeDec.tokens ++ .parenClose :: rest) =
      some (datatypes, rest)
  | [], _, n + 1, _ => by simp [readDatatypes, startsClose]
  | datatype :: datatypes, rest, n + 1, h => by
    simp only [List.cons.sizeOf_spec] at h
    have hc : ∀ r, startsClose (datatype.tokens ++ r) = false := by
      intro r
      obtain ⟨parameters, constructors⟩ := datatype
      cases parameters <;> simp [Tree.DatatypeDec.tokens, paren, startsClose]
    simp [readDatatypes, hc, readDatatype_tokens datatype _ (n := n) (by omega),
      readDatatypes_tokens datatypes rest (n := n) (by omega)]

theorem readSignature_tokens (parameters : List Tree.SortedVar) (result : Tree.Sort)
    (rest : List SyntaxToken) {n : Nat} (h : sizeOf parameters + sizeOf result < n) :
    readSignature n (paren (parameters.flatMap Tree.SortedVar.tokens) ++ result.tokens ++ rest) =
      some ((parameters, result), rest) := by
  simp [paren, readSignature, readSortedVars_tokens parameters _ (n := n) (by omega),
    readSort_tokens result rest (n := n) (by omega)]

theorem readFunctionDecs_tokens : ∀ (declarations : List Tree.FunctionDec)
    (rest : List SyntaxToken) {n : Nat}, sizeOf declarations < n →
    readFunctionDecs n (declarations.flatMap Tree.FunctionDec.tokens ++ .parenClose :: rest) =
      some (declarations, rest)
  | [], _, n + 1, _ => by simp [readFunctionDecs]
  | ⟨symbol, parameters, result⟩ :: declarations, rest, n + 1, h => by
    simp only [List.cons.sizeOf_spec, Tree.FunctionDec.mk.sizeOf_spec] at h
    have hs := readSignature_tokens parameters result
      (.parenClose :: (declarations.flatMap Tree.FunctionDec.tokens ++ .parenClose :: rest))
      (n := n) (by omega)
    simp only [paren, List.cons_append, List.append_assoc, List.nil_append] at hs
    simp [Tree.FunctionDec.tokens, paren, readFunctionDecs, hs, expectClose,
      readFunctionDecs_tokens declarations rest (n := n) (by omega)]

theorem readFunctionDef_tokens (definition : Tree.FunctionDef) (rest : List SyntaxToken)
    {n : Nat} (h : sizeOf definition < n) :
    readFunctionDef n (definition.tokens ++ rest) = some (definition, rest) := by
  obtain ⟨symbol, parameters, result, body⟩ := definition
  simp only [Tree.FunctionDef.mk.sizeOf_spec] at h
  have hs := readSignature_tokens parameters result (body.tokens ++ rest) (n := n) (by omega)
  simp only [paren, List.cons_append, List.append_assoc, List.nil_append] at hs
  simp [Tree.FunctionDef.tokens, paren, readFunctionDef, hs,
    readTerm_tokens body rest (n := n) (by omega)]

/-! ## Commands -/

theorem readAttribute_close (annotation : Tree.Attribute) (rest : List SyntaxToken) {n : Nat}
    (h : sizeOf annotation < n) :
    readAttribute n (annotation.tokens ++ .parenClose :: rest) =
      some (annotation, .parenClose :: rest) :=
  readAttribute_tokens annotation _ h fun _ => rfl

theorem readCommand_tokens (version : Version) (command : Tree.Command)
    (rest : List SyntaxToken) {n : Nat} (hv : command.Valid version)
    (h : sizeOf command < n) :
    readCommand version n (command.tokens ++ rest) = some (command, rest) := by
  cases command
  all_goals simp [Tree.Command.Valid, versionAtLeast] at h hv
  all_goals simp +decide (disch := omega) [Tree.Command.tokens, commandTokens, paren, word,
      readCommand, readCommandAfter, readBare, expectClose, readTerm_tokens, readTerms_tokens,
      readSort_tokens, readSorts_tokens, readDatatype_tokens, readDatatypes_tokens,
      readSortDecs_tokens, readFunctionDef_tokens, readFunctionDecs_tokens, readSymbols_tokens,
      readLiterals_tokens, readAttribute_close, hv]

/-! ## Lists written one after another -/

theorem tokensAll_eq_flatMap (sorts : List Tree.Sort) :
    Tree.Sort.tokensAll sorts = sorts.flatMap Tree.Sort.tokens := by
  induction sorts with
  | nil => rfl
  | cons s sorts ih => simp [Tree.Sort.tokensAll, ih]

theorem sExprsAll_eq_flatMap (items : List Tree.SExpr) :
    Tree.SExpr.tokensAll items = items.flatMap Tree.SExpr.tokens := by
  induction items with
  | nil => rfl
  | cons s items ih => simp [Tree.SExpr.tokensAll, ih]

theorem termsAll_eq_flatMap (terms : List Tree.Term) :
    Tree.Term.tokensAll terms = terms.flatMap Tree.Term.tokens := by
  induction terms with
  | nil => rfl
  | cons t terms ih => simp [Tree.Term.tokensAll, ih]

end BSmtLib.SpecChecks.Grammar
