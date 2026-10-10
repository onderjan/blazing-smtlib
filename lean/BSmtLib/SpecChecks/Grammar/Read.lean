import BSmtLib.Spec.Grammar

/-!
# Reading trees back from their tokens

A reader for each syntactic category: a function from tokens to a tree and the tokens after
it. Each reader reads the tokens of a tree back as that tree, whatever follows them
(`readTerm_tokens`, `readCommand_tokens`), so the tokens of a tree determine the tree. A
command needs its version for that: `check-sat-assuming` is written the same with terms and
with propositional literals, and the version tells which of the two it has.

A reader decides by the first one or two tokens what to read, and reads a list up to the `)`
after it. The readers of categories that nest take fuel, a bound on the steps they may take;
each step into a part, and each step to the next item of a list, takes one. Fuel larger than
the size of the tree is enough.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Grammar

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar

/-- A reader: from tokens to what they start with and the tokens after it, if they start with
one. -/
abbrev Reader (α : Type) := List SyntaxToken → Option (α × List SyntaxToken)

/-! ## Looking at the first tokens -/

/-- The tokens start with `)`. -/
def startsClose : List SyntaxToken → Bool
  | .parenClose :: _ => true
  | _ => false

/-- The tokens start with the reserved word `w`. -/
def startsWord (w : String) : List SyntaxToken → Bool
  | .reserved v :: _ => v = chars w
  | _ => false

/-- The tokens start with `(` and the reserved word `w`. -/
def startsGroup (w : String) : List SyntaxToken → Bool
  | .parenOpen :: rest => startsWord w rest
  | _ => false

/-- The tokens after the `)` they start with. -/
def expectClose : List SyntaxToken → Option (List SyntaxToken)
  | .parenClose :: rest => some rest
  | _ => none

/-- The tokens start with a token that can start an attribute value. -/
def startsValue : List SyntaxToken → Bool
  | .parenOpen :: _ | .symbol _ :: _ | .numeral _ :: _ | .decimal _ :: _
  | .hexadecimal _ :: _ | .binary _ :: _ | .string _ :: _ => true
  | _ => false

/-! ## The readers -/

/-- The constant a token is, if it is one. -/
def readConstant : SyntaxToken → Option Tree.SpecConstant
  | .numeral digits => some (.numeral digits)
  | .decimal text => some (.decimal text)
  | .hexadecimal digits => some (.hexadecimal digits)
  | .binary digits => some (.binary digits)
  | .string content => some (.string content)
  | _ => none

/-- Indices up to the `)` after them. -/
def readIndices : Reader (List Tree.Index)
  | .parenClose :: rest => some ([], rest)
  | .numeral digits :: rest => do
    let (others, rest) ← readIndices rest
    pure (.numeral digits :: others, rest)
  | .symbol name :: rest => do
    let (others, rest) ← readIndices rest
    pure (.symbol name :: others, rest)
  | _ => none

/-- An identifier: a symbol, or `(` `_` ⟨symbol⟩ ⟨index⟩+ `)`. -/
def readIdentifier : Reader Tree.Identifier
  | .symbol name :: rest => some (⟨name, []⟩, rest)
  | .parenOpen :: .reserved w :: .symbol name :: rest =>
    if w = chars "_" then do
      let (indices, rest) ← readIndices rest
      pure (⟨name, indices⟩, rest)
    else none
  | _ => none

mutual

/-- A sort. -/
def readSort : Nat → Reader Tree.Sort
  | 0, _ => none
  | n + 1, tokens =>
    if startsGroup "_" tokens then do
      let (identifier, rest) ← readIdentifier tokens
      pure (.mk identifier [], rest)
    else match tokens with
      | .parenOpen :: rest => do
        let (identifier, rest) ← readIdentifier rest
        let (arguments, rest) ← readSorts n rest
        pure (.mk identifier arguments, rest)
      | _ => do
        let (identifier, rest) ← readIdentifier tokens
        pure (.mk identifier [], rest)

/-- Sorts up to the `)` after them. -/
def readSorts : Nat → Reader (List Tree.Sort)
  | 0, _ => none
  | n + 1, tokens =>
    if startsClose tokens then some ([], tokens.drop 1) else do
      let (first, rest) ← readSort n tokens
      let (others, rest) ← readSorts n rest
      pure (first :: others, rest)

end

mutual

/-- An s-expression. -/
def readSExpr : Nat → Reader Tree.SExpr
  | 0, _ => none
  | n + 1, .parenOpen :: rest => do
    let (items, rest) ← readSExprs n rest
    pure (.list items, rest)
  | _ + 1, .symbol name :: rest => some (.symbol name, rest)
  | _ + 1, .reserved w :: rest => some (.reserved w, rest)
  | _ + 1, .keyword name :: rest => some (.keyword name, rest)
  | _ + 1, token :: rest => (readConstant token).map fun constant => (.constant constant, rest)
  | _ + 1, [] => none

/-- S-expressions up to the `)` after them. -/
def readSExprs : Nat → Reader (List Tree.SExpr)
  | 0, _ => none
  | n + 1, tokens =>
    if startsClose tokens then some ([], tokens.drop 1) else do
      let (first, rest) ← readSExpr n tokens
      let (others, rest) ← readSExprs n rest
      pure (first :: others, rest)

end

/-- An attribute value. -/
def readAttributeValue (n : Nat) : Reader Tree.AttributeValue
  | .parenOpen :: rest => do
    let (items, rest) ← readSExprs n rest
    pure (.list items, rest)
  | .symbol name :: rest => some (.symbol name, rest)
  | token :: rest => (readConstant token).map fun constant => (.constant constant, rest)
  | [] => none

/-- An attribute: a keyword, with the value after it if a value follows. -/
def readAttribute (n : Nat) : Reader Tree.Attribute
  | .keyword name :: rest =>
    if startsValue rest then do
      let (value, rest) ← readAttributeValue n rest
      pure (⟨name, some value⟩, rest)
    else some (⟨name, none⟩, rest)
  | _ => none

/-- Attributes up to the `)` after them. -/
def readAttributes : Nat → Reader (List Tree.Attribute)
  | 0, _ => none
  | n + 1, tokens =>
    if startsClose tokens then some ([], tokens.drop 1) else do
      let (first, rest) ← readAttribute n tokens
      let (others, rest) ← readAttributes n rest
      pure (first :: others, rest)

/-- A qualified identifier. -/
def readQualIdentifier (n : Nat) (tokens : List SyntaxToken) :
    Option (Tree.QualIdentifier × List SyntaxToken) :=
  if startsGroup "as" tokens then
    match tokens with
    | _ :: _ :: rest => do
      let (identifier, rest) ← readIdentifier rest
      let (sort, rest) ← readSort n rest
      let rest ← expectClose rest
      pure (.as identifier sort, rest)
    | _ => none
  else (readIdentifier tokens).map fun (identifier, rest) => (.plain identifier, rest)

/-- Sorted variables up to the `)` after them. -/
def readSortedVars : Nat → Reader (List Tree.SortedVar)
  | 0, _ => none
  | _ + 1, .parenClose :: rest => some ([], rest)
  | n + 1, .parenOpen :: .symbol name :: rest => do
    let (sort, rest) ← readSort n rest
    let rest ← expectClose rest
    let (others, rest) ← readSortedVars n rest
    pure (⟨name, sort⟩ :: others, rest)
  | _ + 1, _ => none

/-- A symbol or the wildcard. -/
def readSymbolOrWildcard : SyntaxToken → Option Tree.SymbolOrWildcard
  | .symbol name => some (.symbol name)
  | .reserved w => if w = chars "_" then some .wildcard else none
  | _ => none

/-- Symbols or wildcards up to the `)` after them. -/
def readSymbolOrWildcards : Reader (List Tree.SymbolOrWildcard)
  | .parenClose :: rest => some ([], rest)
  | token :: rest => do
    let first ← readSymbolOrWildcard token
    let (others, rest) ← readSymbolOrWildcards rest
    pure (first :: others, rest)
  | [] => none

/-- A pattern. -/
def readPattern : Reader Tree.Pattern
  | .parenOpen :: .symbol name :: rest => do
    let (arguments, rest) ← readSymbolOrWildcards rest
    pure (.constructor name arguments, rest)
  | token :: rest => (readSymbolOrWildcard token).map fun symbol => (.single symbol, rest)
  | [] => none

/-- The quantifier a reserved word names, if it names one. -/
def quantifierOf (tokens : List SyntaxToken) : Option Tree.Quantifier :=
  if startsWord "forall" tokens then some .«forall»
  else if startsWord "exists" tokens then some .«exists»
  else none

mutual

/-- A term. -/
def readTerm : Nat → Reader Tree.Term
  | 0, _ => none
  | n + 1, tokens =>
    match tokens with
    | .parenOpen :: rest =>
      if startsWord "_" rest || startsWord "as" rest then
        (readQualIdentifier n tokens).map fun (qualified, rest) => (.identifier qualified, rest)
      else if startsWord "let" rest then
        match rest with
        | _ :: .parenOpen :: rest => do
          let (bindings, rest) ← readBindings n rest
          let (body, rest) ← readTerm n rest
          let rest ← expectClose rest
          pure (.«let» bindings body, rest)
        | _ => none
      else if startsWord "lambda" rest then
        match rest with
        | _ :: .parenOpen :: rest => do
          let (variables, rest) ← readSortedVars n rest
          let (body, rest) ← readTerm n rest
          let rest ← expectClose rest
          pure (.lambda variables body, rest)
        | _ => none
      else if let some quantifier := quantifierOf rest then
        match rest with
        | _ :: .parenOpen :: rest => do
          let (variables, rest) ← readSortedVars n rest
          let (body, rest) ← readTerm n rest
          let rest ← expectClose rest
          pure (.quantified quantifier variables body, rest)
        | _ => none
      else if startsWord "match" rest then
        match rest with
        | _ :: rest => do
          let (scrutinee, rest) ← readTerm n rest
          match rest with
          | .parenOpen :: rest => do
            let (cases, rest) ← readCases n rest
            let rest ← expectClose rest
            pure (.«match» scrutinee cases, rest)
          | _ => none
        | _ => none
      else if startsWord "!" rest then
        match rest with
        | _ :: rest => do
          let (term, rest) ← readTerm n rest
          let (attributes, rest) ← readAttributes n rest
          pure (.annotated term attributes, rest)
        | _ => none
      else do
        let (function, rest) ← readQualIdentifier n rest
        let (arguments, rest) ← readTerms n rest
        pure (.application function arguments, rest)
    | .symbol name :: rest => some (.identifier (.plain ⟨name, []⟩), rest)
    | token :: rest => (readConstant token).map fun constant => (.constant constant, rest)
    | [] => none

/-- Terms up to the `)` after them. -/
def readTerms : Nat → Reader (List Tree.Term)
  | 0, _ => none
  | n + 1, tokens =>
    if startsClose tokens then some ([], tokens.drop 1) else do
      let (first, rest) ← readTerm n tokens
      let (others, rest) ← readTerms n rest
      pure (first :: others, rest)

/-- The bindings of a `let` up to the `)` after them. -/
def readBindings : Nat → Reader (List (Tree.Symbol × Tree.Term))
  | 0, _ => none
  | _ + 1, .parenClose :: rest => some ([], rest)
  | n + 1, .parenOpen :: .symbol name :: rest => do
    let (term, rest) ← readTerm n rest
    let rest ← expectClose rest
    let (others, rest) ← readBindings n rest
    pure ((name, term) :: others, rest)
  | _ + 1, _ => none

/-- The cases of a `match` up to the `)` after them. -/
def readCases : Nat → Reader (List (Tree.Pattern × Tree.Term))
  | 0, _ => none
  | _ + 1, .parenClose :: rest => some ([], rest)
  | n + 1, .parenOpen :: rest => do
    let (pattern, rest) ← readPattern rest
    let (term, rest) ← readTerm n rest
    let rest ← expectClose rest
    let (others, rest) ← readCases n rest
    pure ((pattern, term) :: others, rest)
  | _ + 1, _ => none

end

/-! ## The parts of commands -/

/-- Symbols up to the `)` after them. -/
def readSymbols : Reader (List Tree.Symbol)
  | .parenClose :: rest => some ([], rest)
  | .symbol name :: rest => do
    let (others, rest) ← readSymbols rest
    pure (name :: others, rest)
  | _ => none

/-- Propositional literals up to the `)` after them. -/
def readLiterals : Reader (List Tree.PropLiteral)
  | .parenClose :: rest => some ([], rest)
  | .symbol name :: rest => do
    let (others, rest) ← readLiterals rest
    pure (.positive name :: others, rest)
  | .parenOpen :: .symbol negation :: .symbol name :: .parenClose :: rest => do
    let (others, rest) ← readLiterals rest
    pure (.negative negation name :: others, rest)
  | _ => none

/-- Sort declarations up to the `)` after them. -/
def readSortDecs : Reader (List Tree.SortDec)
  | .parenClose :: rest => some ([], rest)
  | .parenOpen :: .symbol name :: .numeral arity :: .parenClose :: rest => do
    let (others, rest) ← readSortDecs rest
    pure (⟨name, arity⟩ :: others, rest)
  | _ => none

/-- Selector declarations up to the `)` after them. -/
def readSelectors : Nat → Reader (List Tree.SelectorDec)
  | 0, _ => none
  | _ + 1, .parenClose :: rest => some ([], rest)
  | n + 1, .parenOpen :: .symbol name :: rest => do
    let (sort, rest) ← readSort n rest
    let rest ← expectClose rest
    let (others, rest) ← readSelectors n rest
    pure (⟨name, sort⟩ :: others, rest)
  | _ + 1, _ => none

/-- Constructor declarations up to the `)` after them. -/
def readConstructors : Nat → Reader (List Tree.ConstructorDec)
  | 0, _ => none
  | _ + 1, .parenClose :: rest => some ([], rest)
  | n + 1, .parenOpen :: .symbol name :: rest => do
    let (selectors, rest) ← readSelectors n rest
    let (others, rest) ← readConstructors n rest
    pure (⟨name, selectors⟩ :: others, rest)
  | _ + 1, _ => none

/-- A datatype declaration. -/
def readDatatype (n : Nat) : Reader Tree.DatatypeDec
  | .parenOpen :: rest =>
    if startsWord "par" rest then
      match rest with
      | _ :: .parenOpen :: rest => do
        let (parameters, rest) ← readSymbols rest
        match rest with
        | .parenOpen :: rest => do
          let (constructors, rest) ← readConstructors n rest
          let rest ← expectClose rest
          pure (⟨parameters, constructors⟩, rest)
        | _ => none
      | _ => none
    else do
      let (constructors, rest) ← readConstructors n rest
      pure (⟨[], constructors⟩, rest)
  | _ => none

/-- Datatype declarations up to the `)` after them. -/
def readDatatypes : Nat → Reader (List Tree.DatatypeDec)
  | 0, _ => none
  | n + 1, tokens =>
    if startsClose tokens then some ([], tokens.drop 1) else do
      let (first, rest) ← readDatatype n tokens
      let (others, rest) ← readDatatypes n rest
      pure (first :: others, rest)

/-- The signature of a function after its symbol: `(` ⟨sorted_var⟩∗ `)` ⟨sort⟩. -/
def readSignature (n : Nat) : Reader (List Tree.SortedVar × Tree.Sort)
  | .parenOpen :: rest => do
    let (parameters, rest) ← readSortedVars n rest
    let (result, rest) ← readSort n rest
    pure ((parameters, result), rest)
  | _ => none

/-- Function declarations up to the `)` after them. -/
def readFunctionDecs : Nat → Reader (List Tree.FunctionDec)
  | 0, _ => none
  | _ + 1, .parenClose :: rest => some ([], rest)
  | n + 1, .parenOpen :: .symbol name :: rest => do
    let ((parameters, result), rest) ← readSignature n rest
    let rest ← expectClose rest
    let (others, rest) ← readFunctionDecs n rest
    pure (⟨name, parameters, result⟩ :: others, rest)
  | _ + 1, _ => none

/-- A function definition. -/
def readFunctionDef (n : Nat) : Reader Tree.FunctionDef
  | .symbol name :: rest => do
    let ((parameters, result), rest) ← readSignature n rest
    let (body, rest) ← readTerm n rest
    pure (⟨name, parameters, result, body⟩, rest)
  | _ => none

/-! ## Commands -/

/-- The tokens of a command that is only its name, from after its name on. -/
def readBare (command : Tree.Command) (tokens : List SyntaxToken) :
    Option (Tree.Command × List SyntaxToken) :=
  (expectClose tokens).map fun rest => (command, rest)

/-- The tokens of a command after its name, given the name. -/
def readCommandAfter (version : Version) (n : Nat) (w : Chars) (tokens : List SyntaxToken) :
    Option (Tree.Command × List SyntaxToken) :=
  if w = chars "assert" then do
    let (term, rest) ← readTerm n tokens
    let rest ← expectClose rest
    pure (.assert term, rest)
  else if w = chars "check-sat" then readBare .checkSat tokens
  else if w = chars "check-sat-assuming" then
    match tokens with
    | .parenOpen :: rest =>
      if Version.v2_7 ∈ version.upTo then do
        let (terms, rest) ← readTerms n rest
        let rest ← expectClose rest
        pure (.checkSatAssuming terms, rest)
      else do
        let (literals, rest) ← readLiterals rest
        let rest ← expectClose rest
        pure (.checkSatAssumingLiterals literals, rest)
    | _ => none
  else if w = chars "declare-const" then
    match tokens with
    | .symbol name :: rest => do
      let (sort, rest) ← readSort n rest
      let rest ← expectClose rest
      pure (.declareConst name sort, rest)
    | _ => none
  else if w = chars "declare-datatype" then
    match tokens with
    | .symbol name :: rest => do
      let (datatype, rest) ← readDatatype n rest
      let rest ← expectClose rest
      pure (.declareDatatype name datatype, rest)
    | _ => none
  else if w = chars "declare-datatypes" then
    match tokens with
    | .parenOpen :: rest => do
      let (sorts, rest) ← readSortDecs rest
      match rest with
      | .parenOpen :: rest => do
        let (datatypes, rest) ← readDatatypes n rest
        let rest ← expectClose rest
        pure (.declareDatatypes sorts datatypes, rest)
      | _ => none
    | _ => none
  else if w = chars "declare-fun" then
    match tokens with
    | .symbol name :: .parenOpen :: rest => do
      let (parameters, rest) ← readSorts n rest
      let (result, rest) ← readSort n rest
      let rest ← expectClose rest
      pure (.declareFun name parameters result, rest)
    | _ => none
  else if w = chars "declare-sort" then
    match tokens with
    | .symbol name :: .numeral arity :: rest => readBare (.declareSort name arity) rest
    | _ => none
  else if w = chars "declare-sort-parameter" then
    match tokens with
    | .symbol name :: rest => readBare (.declareSortParameter name) rest
    | _ => none
  else if w = chars "define-const" then
    match tokens with
    | .symbol name :: rest => do
      let (sort, rest) ← readSort n rest
      let (term, rest) ← readTerm n rest
      let rest ← expectClose rest
      pure (.defineConst name sort term, rest)
    | _ => none
  else if w = chars "define-fun" then do
    let (definition, rest) ← readFunctionDef n tokens
    let rest ← expectClose rest
    pure (.defineFun definition, rest)
  else if w = chars "define-fun-rec" then do
    let (definition, rest) ← readFunctionDef n tokens
    let rest ← expectClose rest
    pure (.defineFunRec definition, rest)
  else if w = chars "define-funs-rec" then
    match tokens with
    | .parenOpen :: rest => do
      let (declarations, rest) ← readFunctionDecs n rest
      match rest with
      | .parenOpen :: rest => do
        let (bodies, rest) ← readTerms n rest
        let rest ← expectClose rest
        pure (.defineFunsRec declarations bodies, rest)
      | _ => none
    | _ => none
  else if w = chars "define-sort" then
    match tokens with
    | .symbol name :: .parenOpen :: rest => do
      let (parameters, rest) ← readSymbols rest
      let (sort, rest) ← readSort n rest
      let rest ← expectClose rest
      pure (.defineSort name parameters sort, rest)
    | _ => none
  else if w = chars "echo" then
    match tokens with
    | .string content :: rest => readBare (.echo content) rest
    | _ => none
  else if w = chars "exit" then readBare .exit tokens
  else if w = chars "get-assertions" then readBare .getAssertions tokens
  else if w = chars "get-assignment" then readBare .getAssignment tokens
  else if w = chars "get-info" then
    match tokens with
    | .keyword flag :: rest => readBare (.getInfo flag) rest
    | _ => none
  else if w = chars "get-model" then readBare .getModel tokens
  else if w = chars "get-option" then
    match tokens with
    | .keyword name :: rest => readBare (.getOption name) rest
    | _ => none
  else if w = chars "get-proof" then readBare .getProof tokens
  else if w = chars "get-unsat-assumptions" then readBare .getUnsatAssumptions tokens
  else if w = chars "get-unsat-core" then readBare .getUnsatCore tokens
  else if w = chars "get-value" then
    match tokens with
    | .parenOpen :: rest => do
      let (terms, rest) ← readTerms n rest
      let rest ← expectClose rest
      pure (.getValue terms, rest)
    | _ => none
  else if w = chars "pop" then
    match tokens with
    | .numeral count :: rest => readBare (.pop count) rest
    | _ => none
  else if w = chars "push" then
    match tokens with
    | .numeral count :: rest => readBare (.push count) rest
    | _ => none
  else if w = chars "reset" then readBare .reset tokens
  else if w = chars "reset-assertions" then readBare .resetAssertions tokens
  else if w = chars "set-info" then do
    let (info, rest) ← readAttribute n tokens
    let rest ← expectClose rest
    pure (.setInfo info, rest)
  else if w = chars "set-logic" then
    match tokens with
    | .symbol name :: rest => readBare (.setLogic name) rest
    | _ => none
  else if w = chars "set-option" then do
    let (option, rest) ← readAttribute n tokens
    let rest ← expectClose rest
    pure (.setOption option, rest)
  else none

/-- A command of the version. -/
def readCommand (version : Version) (n : Nat) : Reader Tree.Command
  | .parenOpen :: .reserved w :: rest => readCommandAfter version n w rest
  | _ => none

end BSmtLib.SpecChecks.Grammar
