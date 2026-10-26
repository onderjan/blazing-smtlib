module

public import BSmtLib.Facts.Proofs.Parser.Rejection.Unique

@[expose] public section

/-!
# The reserved words of what a parser takes

Every reserved word among the tokens of a valid tree is reserved by the version the tree is valid
in: the words that start constructs and commands are reserved by every version that has the
construct, and a valid s-expression holds only words that the version reserves. So every item of
what a parser takes for a script, or for commands that a declaration of a version that is not supported ends, is one
that a lexer can hand over in the version in force (`takes_ofVersion`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Rejection.Lexical

open BSmtLibSpec.Regex (chars)
open BSmtLibSpec.Lexicon (basicReservedWords commandNames addedBasicReservedWords addedCommandNames)
open BSmtLib.Facts.Proofs.Parser.Rejection.Unique BSmtLib.Facts.Proofs.Parser.Script

open BSmtLibSpec.Grammar
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal

/-- The version reserves the word. -/
def ReservedIn (version : BSmtLibSpec.Lexicon.Version) (w : BSmtLibSpec.Regex.Chars) : Prop :=
  w ∈ (basicReservedWords version ++ commandNames version).map chars

/-- The version reserves every reserved word among the tokens. -/
def LexicalIn (version : BSmtLibSpec.Lexicon.Version)
    (tokens : List BSmtLibSpec.Grammar.SyntaxToken) : Prop :=
  ∀ w, BSmtLibSpec.Grammar.SyntaxToken.reserved w ∈ tokens → ReservedIn version w

variable {version : BSmtLibSpec.Lexicon.Version}

theorem reservedIn_word {first : BSmtLibSpec.Lexicon.Version} (h : versionAtLeast version first)
    {w : String}
    (hw : w ∈ addedBasicReservedWords first ∨ w ∈ addedCommandNames first) :
    ReservedIn version (chars w) := by
  unfold ReservedIn basicReservedWords commandNames
  apply List.mem_map_of_mem
  rcases hw with hw | hw
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨first, h, hw⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨first, h, hw⟩)

theorem atLeast_v2_0 (version : BSmtLibSpec.Lexicon.Version) : versionAtLeast version .v2_0 := by
  cases version <;> simp [versionAtLeast, BSmtLibSpec.Lexicon.Version.upTo]

theorem atLeast_v2_5_of_v2_7 (h : versionAtLeast version .v2_7) : versionAtLeast version .v2_5 := by
  cases version <;> simp_all [versionAtLeast, BSmtLibSpec.Lexicon.Version.upTo]

/-- A word that 2.0 reserves is reserved in every version. -/
theorem reservedIn_v2_0 {w : String}
    (hw : w ∈ addedBasicReservedWords .v2_0 ∨ w ∈ addedCommandNames .v2_0) :
    ReservedIn version (chars w) :=
  reservedIn_word (atLeast_v2_0 version) hw

@[simp]
theorem lexicalIn_nil : LexicalIn version [] := by
  simp [LexicalIn]

theorem lexicalIn_append {a b : List BSmtLibSpec.Grammar.SyntaxToken} :
    LexicalIn version (a ++ b) ↔ LexicalIn version a ∧ LexicalIn version b := by
  simp only [LexicalIn, List.mem_append]
  exact ⟨fun h => ⟨fun w hw => h w (.inl hw), fun w hw => h w (.inr hw)⟩,
    fun h w hw => hw.elim (h.1 w) (h.2 w)⟩

theorem lexicalIn_cons {t : BSmtLibSpec.Grammar.SyntaxToken}
    {ts : List BSmtLibSpec.Grammar.SyntaxToken} :
    LexicalIn version (t :: ts) ↔
      (∀ w, t = .reserved w → ReservedIn version w) ∧ LexicalIn version ts := by
  simp only [LexicalIn, List.mem_cons]
  constructor
  · intro h
    exact ⟨fun w hw => h w (.inl hw.symm), fun w hw => h w (.inr hw)⟩
  · intro h w hw
    rcases hw with hw | hw
    · exact h.1 w hw.symm
    · exact h.2 w hw

theorem lexicalIn_flatMap {α : Type} {l : List α} {f : α → List BSmtLibSpec.Grammar.SyntaxToken} :
    LexicalIn version (l.flatMap f) ↔ ∀ x ∈ l, LexicalIn version (f x) := by
  simp only [LexicalIn, List.mem_flatMap]
  constructor
  · intro h x hx w hw
    exact h w ⟨x, hx, hw⟩
  · intro h w ⟨x, hx, hw⟩
    exact h x hx w hw

theorem lexicalIn_map_symbol {l : List Tree.Symbol} :
    LexicalIn version (l.map .symbol) := by
  intro w hw
  simp at hw

theorem lexicalIn_paren {tokens : List BSmtLibSpec.Grammar.SyntaxToken} :
    LexicalIn version (paren tokens) ↔ LexicalIn version tokens := by
  simp [paren, lexicalIn_cons, lexicalIn_append]

theorem lexicalIn_word {w : String} {tokens : List BSmtLibSpec.Grammar.SyntaxToken}
    (hw : ReservedIn version (chars w)) (h : LexicalIn version tokens) :
    LexicalIn version (word w :: tokens) :=
  lexicalIn_cons.mpr ⟨fun _ e => by cases e; exact hw, h⟩

theorem lexicalIn_command {name : String} {tokens : List BSmtLibSpec.Grammar.SyntaxToken}
    (hw : ReservedIn version (chars name)) (h : LexicalIn version tokens) :
    LexicalIn version (commandTokens name tokens) :=
  lexicalIn_paren.mpr (lexicalIn_word hw h)

theorem lexicalIn_constant (c : Tree.SpecConstant) : LexicalIn version [c.token] := by
  cases c <;> simp [Tree.SpecConstant.token, lexicalIn_cons]

theorem lexicalIn_symbol (s : Tree.Symbol) : LexicalIn version [.symbol s] := by
  simp [lexicalIn_cons]

theorem lexicalIn_keyword (k : BSmtLibSpec.Regex.Chars) : LexicalIn version [.keyword k] := by
  simp [lexicalIn_cons]

attribute [local simp] lexicalIn_append lexicalIn_paren lexicalIn_flatMap lexicalIn_constant
  lexicalIn_symbol lexicalIn_keyword lexicalIn_map_symbol

/-! ## The trees -/

mutual

theorem sExpr_lexical : ∀ {s : Tree.SExpr}, s.Valid version → LexicalIn version s.tokens
  | .constant c, _ => by simp [Tree.SExpr.tokens]
  | .symbol _, _ => by simp [Tree.SExpr.tokens]
  | .reserved _, h => by
    simp only [Tree.SExpr.tokens, lexicalIn_cons]
    exact ⟨fun _ e => by cases e; exact h.2, lexicalIn_nil⟩
  | .keyword _, _ => by simp [Tree.SExpr.tokens]
  | .list _, h => by
    simp only [Tree.SExpr.tokens, lexicalIn_paren]
    exact sExprs_lexical h

theorem sExprs_lexical : ∀ {items : List Tree.SExpr}, Tree.SExpr.ValidAll version items →
    LexicalIn version (Tree.SExpr.tokensAll items)
  | [], _ => by simp [Tree.SExpr.tokensAll]
  | _ :: _, h => by
    simp only [Tree.SExpr.tokensAll, lexicalIn_append]
    exact ⟨sExpr_lexical h.1, sExprs_lexical h.2⟩

end

theorem index_lexical (index : Tree.Index) : LexicalIn version index.tokens := by
  cases index <;> simp [Tree.Index.tokens, lexicalIn_cons]

theorem identifier_lexical (identifier : Tree.Identifier) :
    LexicalIn version identifier.tokens := by
  obtain ⟨symbol, indices⟩ := identifier
  cases indices with
  | nil => simp [Tree.Identifier.tokens]
  | cons first rest =>
    simp only [Tree.Identifier.tokens, lexicalIn_paren]
    refine lexicalIn_word (reservedIn_v2_0 (by decide)) (lexicalIn_cons.mpr ⟨nofun, ?_⟩)
    exact lexicalIn_flatMap.mpr fun x _ => index_lexical x

mutual

theorem sort_lexical : ∀ (sort : Tree.«Sort»), LexicalIn version sort.tokens
  | .mk identifier [] => by
    simp only [Tree.«Sort».tokens]
    exact identifier_lexical identifier
  | .mk identifier (first :: rest) => by
    simp only [Tree.«Sort».tokens, lexicalIn_paren, lexicalIn_append]
    exact ⟨identifier_lexical identifier, sorts_lexical (first :: rest)⟩

theorem sorts_lexical : ∀ (sorts : List Tree.«Sort»), LexicalIn version
    (Tree.«Sort».tokensAll sorts)
  | [] => by simp [Tree.«Sort».tokensAll]
  | first :: rest => by
    simp only [Tree.«Sort».tokensAll, lexicalIn_append]
    exact ⟨sort_lexical first, sorts_lexical rest⟩

end

theorem attributeValue_lexical {value : Tree.AttributeValue} (h : value.Valid version) :
    LexicalIn version value.tokens := by
  cases value with
  | constant c => simp [Tree.AttributeValue.tokens]
  | symbol s => simp [Tree.AttributeValue.tokens]
  | list items =>
    simp only [Tree.AttributeValue.tokens, lexicalIn_paren]
    exact sExprs_lexical h

theorem attribute_lexical {annotation : Tree.Attribute} (h : annotation.Valid version) :
    LexicalIn version annotation.tokens := by
  obtain ⟨keyword, value⟩ := annotation
  cases value with
  | none => simp [Tree.Attribute.tokens]
  | some value =>
    simp only [Tree.Attribute.tokens]
    exact lexicalIn_cons.mpr ⟨nofun, attributeValue_lexical h⟩

theorem qualIdentifier_lexical (qualified : Tree.QualIdentifier) :
    LexicalIn version qualified.tokens := by
  cases qualified with
  | plain identifier => exact identifier_lexical identifier
  | as identifier sort =>
    simp only [Tree.QualIdentifier.tokens, lexicalIn_paren]
    exact lexicalIn_word (reservedIn_v2_0 (by decide))
      (lexicalIn_append.mpr ⟨identifier_lexical identifier, sort_lexical sort⟩)

theorem sortedVar_lexical (sortedVar : Tree.SortedVar) : LexicalIn version sortedVar.tokens := by
  obtain ⟨symbol, sort⟩ := sortedVar
  simp only [Tree.SortedVar.tokens, lexicalIn_paren]
  exact lexicalIn_cons.mpr ⟨nofun, sort_lexical sort⟩

theorem sortedVars_lexical (variables : List Tree.SortedVar) :
    LexicalIn version (variables.flatMap Tree.SortedVar.tokens) :=
  lexicalIn_flatMap.mpr fun x _ => sortedVar_lexical x

theorem symbolOrWildcard_lexical (symbol : Tree.SymbolOrWildcard) :
    LexicalIn version [symbol.token] := by
  cases symbol with
  | symbol s => simp [Tree.SymbolOrWildcard.token]
  | wildcard =>
    simp only [Tree.SymbolOrWildcard.token]
    exact lexicalIn_word (reservedIn_v2_0 (by decide)) lexicalIn_nil

theorem pattern_lexical (pattern : Tree.Pattern) : LexicalIn version pattern.tokens := by
  cases pattern with
  | single symbol => exact symbolOrWildcard_lexical symbol
  | constructor head arguments =>
    simp only [Tree.Pattern.tokens, lexicalIn_paren]
    refine lexicalIn_cons.mpr ⟨nofun, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨x, hx, e⟩ := hw
    exact symbolOrWildcard_lexical x w (by rw [e]; exact List.mem_singleton_self _)

theorem quantifier_lexical (quantifier : Tree.Quantifier)
    {tokens : List BSmtLibSpec.Grammar.SyntaxToken}
    (h : LexicalIn version tokens) : LexicalIn version (quantifier.word :: tokens) := by
  cases quantifier <;> exact lexicalIn_word (reservedIn_v2_0 (by decide)) h

mutual

theorem term_lexical : ∀ {term : Tree.Term}, term.Valid version → LexicalIn version term.tokens
  | .constant _, _ => by simp [Tree.Term.tokens]
  | .identifier qualified, _ => qualIdentifier_lexical qualified
  | .application function arguments, h => by
    simp only [Tree.Term.tokens, lexicalIn_paren, lexicalIn_append]
    exact ⟨qualIdentifier_lexical function, terms_lexical h.2.2⟩
  | .«let» bindings body, h => by
    simp only [Tree.Term.tokens, lexicalIn_paren]
    exact lexicalIn_word (reservedIn_v2_0 (by decide)) (lexicalIn_append.mpr
      ⟨lexicalIn_paren.mpr (bindings_lexical h.2.1), term_lexical h.2.2⟩)
  | .lambda variables body, h => by
    simp only [Tree.Term.tokens, lexicalIn_paren]
    exact lexicalIn_word (reservedIn_word h.1 (by decide)) (lexicalIn_append.mpr
      ⟨lexicalIn_paren.mpr (sortedVars_lexical variables), term_lexical h.2.2.2⟩)
  | .quantified quantifier variables body, h => by
    simp only [Tree.Term.tokens, lexicalIn_paren]
    exact quantifier_lexical quantifier (lexicalIn_append.mpr
      ⟨lexicalIn_paren.mpr (sortedVars_lexical variables), term_lexical h.2.2⟩)
  | .«match» scrutinee cases, h => by
    simp only [Tree.Term.tokens, lexicalIn_paren]
    exact lexicalIn_word (reservedIn_word h.1 (by decide)) (lexicalIn_append.mpr
      ⟨term_lexical h.2.2.1, lexicalIn_paren.mpr (cases_lexical h.2.2.2)⟩)
  | .annotated term attributes, h => by
    simp only [Tree.Term.tokens, lexicalIn_paren]
    exact lexicalIn_word (reservedIn_v2_0 (by decide)) (lexicalIn_append.mpr
      ⟨term_lexical h.2.1, lexicalIn_flatMap.mpr fun x hx => attribute_lexical (h.2.2 x hx)⟩)

theorem terms_lexical : ∀ {terms : List Tree.Term}, Tree.Term.ValidAll version terms →
    LexicalIn version (Tree.Term.tokensAll terms)
  | [], _ => by simp [Tree.Term.tokensAll]
  | _ :: _, h => by
    simp only [Tree.Term.tokensAll, lexicalIn_append]
    exact ⟨term_lexical h.1, terms_lexical h.2⟩

theorem bindings_lexical : ∀ {bindings : List (Tree.Symbol × Tree.Term)},
    Tree.Term.ValidBindings version bindings → LexicalIn version (Tree.Term.bindingTokens bindings)
  | [], _ => by simp [Tree.Term.bindingTokens]
  | (_, _) :: _, h => by
    simp only [Tree.Term.bindingTokens, lexicalIn_append, lexicalIn_paren]
    exact ⟨lexicalIn_cons.mpr ⟨nofun, term_lexical h.1⟩, bindings_lexical h.2⟩

theorem cases_lexical : ∀ {cases : List (Tree.Pattern × Tree.Term)},
    Tree.Term.ValidCases version cases → LexicalIn version (Tree.Term.caseTokens cases)
  | [], _ => by simp [Tree.Term.caseTokens]
  | (pattern, _) :: _, h => by
    simp only [Tree.Term.caseTokens, lexicalIn_append, lexicalIn_paren]
    exact ⟨⟨pattern_lexical pattern, term_lexical h.2.1⟩, cases_lexical h.2.2⟩

end

theorem sortDec_lexical (declaration : Tree.SortDec) : LexicalIn version declaration.tokens := by
  obtain ⟨symbol, arity⟩ := declaration
  simp [Tree.SortDec.tokens, lexicalIn_cons]

theorem selectorDec_lexical (selector : Tree.SelectorDec) : LexicalIn version selector.tokens := by
  obtain ⟨symbol, sort⟩ := selector
  simp only [Tree.SelectorDec.tokens, lexicalIn_paren]
  exact lexicalIn_cons.mpr ⟨nofun, sort_lexical sort⟩

theorem constructorDec_lexical (constructor : Tree.ConstructorDec) :
    LexicalIn version constructor.tokens := by
  obtain ⟨symbol, selectors⟩ := constructor
  simp only [Tree.ConstructorDec.tokens, lexicalIn_paren]
  exact lexicalIn_cons.mpr ⟨nofun, lexicalIn_flatMap.mpr fun x _ => selectorDec_lexical x⟩

theorem constructorDecs_lexical (constructors : List Tree.ConstructorDec) :
    LexicalIn version (constructors.flatMap Tree.ConstructorDec.tokens) :=
  lexicalIn_flatMap.mpr fun x _ => constructorDec_lexical x

theorem datatypeDec_lexical (datatype : Tree.DatatypeDec) : LexicalIn version datatype.tokens := by
  obtain ⟨parameters, constructors⟩ := datatype
  cases parameters with
  | nil =>
    simp only [Tree.DatatypeDec.tokens, lexicalIn_paren]
    exact constructorDecs_lexical constructors
  | cons first rest =>
    simp only [Tree.DatatypeDec.tokens, lexicalIn_paren]
    exact lexicalIn_word (reservedIn_v2_0 (by decide)) (lexicalIn_append.mpr
      ⟨lexicalIn_paren.mpr lexicalIn_map_symbol,
        lexicalIn_paren.mpr (constructorDecs_lexical constructors)⟩)

theorem functionDec_lexical (declaration : Tree.FunctionDec) :
    LexicalIn version declaration.tokens := by
  obtain ⟨symbol, parameters, result⟩ := declaration
  simp only [Tree.FunctionDec.tokens, lexicalIn_paren]
  exact lexicalIn_cons.mpr ⟨nofun, lexicalIn_append.mpr
    ⟨lexicalIn_paren.mpr (sortedVars_lexical parameters), sort_lexical result⟩⟩

theorem functionDef_lexical {definition : Tree.FunctionDef} (h : definition.Valid version) :
    LexicalIn version definition.tokens := by
  obtain ⟨symbol, parameters, result, body⟩ := definition
  simp only [Tree.FunctionDef.tokens]
  refine lexicalIn_cons.mpr ⟨nofun, lexicalIn_append.mpr ⟨lexicalIn_append.mpr
    ⟨lexicalIn_paren.mpr (sortedVars_lexical parameters), sort_lexical result⟩, ?_⟩⟩
  exact term_lexical h.2.2

theorem propLiteral_lexical (literal : Tree.PropLiteral) : LexicalIn version literal.tokens := by
  cases literal <;> simp [Tree.PropLiteral.tokens, lexicalIn_cons]

/-- The version reserves every reserved word among the tokens of a valid command. -/
theorem command_lexical {command : Tree.Command} (h : command.Valid version) :
    LexicalIn version command.tokens := by
  cases command <;> simp only [Tree.Command.tokens, Tree.Command.Valid] at h ⊢
  case assert term => exact lexicalIn_command (reservedIn_v2_0 (by decide)) (term_lexical h)
  case checkSat => exact lexicalIn_command (reservedIn_v2_0 (by decide)) lexicalIn_nil
  case checkSatAssuming terms =>
    exact lexicalIn_command (reservedIn_word (atLeast_v2_5_of_v2_7 h.1) (by decide))
      (lexicalIn_paren.mpr (terms_lexical h.2))
  case checkSatAssumingLiterals literals =>
    exact lexicalIn_command (reservedIn_word h.1 (by decide))
      (lexicalIn_paren.mpr (lexicalIn_flatMap.mpr fun x _ => propLiteral_lexical x))
  case declareConst symbol sort =>
    exact lexicalIn_command (reservedIn_word h.1 (by decide))
      (lexicalIn_cons.mpr ⟨nofun, sort_lexical sort⟩)
  case declareDatatype symbol datatype =>
    exact lexicalIn_command (reservedIn_word h.1 (by decide))
      (lexicalIn_cons.mpr ⟨nofun, datatypeDec_lexical datatype⟩)
  case declareDatatypes sorts datatypes =>
    exact lexicalIn_command (reservedIn_word h.1 (by decide)) (lexicalIn_append.mpr
      ⟨lexicalIn_paren.mpr (lexicalIn_flatMap.mpr fun x _ => sortDec_lexical x),
        lexicalIn_paren.mpr (lexicalIn_flatMap.mpr fun x _ => datatypeDec_lexical x)⟩)
  case declareFun symbol parameters result =>
    exact lexicalIn_command (reservedIn_v2_0 (by decide)) (lexicalIn_cons.mpr ⟨nofun,
      lexicalIn_append.mpr ⟨lexicalIn_paren.mpr (sorts_lexical parameters), sort_lexical result⟩⟩)
  case declareSort symbol arity =>
    exact lexicalIn_command (reservedIn_v2_0 (by decide)) (by simp [lexicalIn_cons])
  case declareSortParameter symbol =>
    exact lexicalIn_command (reservedIn_word h (by decide)) (by simp [lexicalIn_cons])
  case defineConst symbol sort term =>
    exact lexicalIn_command (reservedIn_word h.1 (by decide)) (lexicalIn_cons.mpr ⟨nofun,
      lexicalIn_append.mpr ⟨sort_lexical sort, term_lexical h.2.2⟩⟩)
  case defineFun definition =>
    exact lexicalIn_command (reservedIn_v2_0 (by decide)) (functionDef_lexical h)
  case defineFunRec definition =>
    exact lexicalIn_command (reservedIn_word h.1 (by decide)) (functionDef_lexical h.2)
  case defineFunsRec declarations bodies =>
    exact lexicalIn_command (reservedIn_word h.1 (by decide)) (lexicalIn_append.mpr
      ⟨lexicalIn_paren.mpr (lexicalIn_flatMap.mpr fun x _ => functionDec_lexical x),
        lexicalIn_paren.mpr (terms_lexical h.2.2.2.2)⟩)
  case defineSort symbol parameters sort =>
    exact lexicalIn_command (reservedIn_v2_0 (by decide)) (lexicalIn_cons.mpr ⟨nofun,
      lexicalIn_append.mpr ⟨lexicalIn_paren.mpr lexicalIn_map_symbol, sort_lexical sort⟩⟩)
  case echo content =>
    exact lexicalIn_command (reservedIn_word h (by decide)) (by simp [lexicalIn_cons])
  case exit => exact lexicalIn_command (reservedIn_v2_0 (by decide)) lexicalIn_nil
  case getAssertions => exact lexicalIn_command (reservedIn_v2_0 (by decide)) lexicalIn_nil
  case getAssignment => exact lexicalIn_command (reservedIn_v2_0 (by decide)) lexicalIn_nil
  case getInfo flag =>
    exact lexicalIn_command (reservedIn_v2_0 (by decide)) (by simp [lexicalIn_cons])
  case getModel => exact lexicalIn_command (reservedIn_word h (by decide)) lexicalIn_nil
  case getOption keyword =>
    exact lexicalIn_command (reservedIn_v2_0 (by decide)) (by simp [lexicalIn_cons])
  case getProof => exact lexicalIn_command (reservedIn_v2_0 (by decide)) lexicalIn_nil
  case getUnsatAssumptions =>
    exact lexicalIn_command (reservedIn_word h (by decide)) lexicalIn_nil
  case getUnsatCore => exact lexicalIn_command (reservedIn_v2_0 (by decide)) lexicalIn_nil
  case getValue terms =>
    exact lexicalIn_command (reservedIn_v2_0 (by decide))
      (lexicalIn_paren.mpr (terms_lexical h.2))
  case pop count =>
    exact lexicalIn_command (reservedIn_v2_0 (by decide)) (by simp [lexicalIn_cons])
  case push count =>
    exact lexicalIn_command (reservedIn_v2_0 (by decide)) (by simp [lexicalIn_cons])
  case reset => exact lexicalIn_command (reservedIn_word h (by decide)) lexicalIn_nil
  case resetAssertions => exact lexicalIn_command (reservedIn_word h (by decide)) lexicalIn_nil
  case setInfo info =>
    exact lexicalIn_command (reservedIn_v2_0 (by decide)) (attribute_lexical h)
  case setLogic symbol =>
    exact lexicalIn_command (reservedIn_v2_0 (by decide)) (by simp [lexicalIn_cons])
  case setOption option =>
    exact lexicalIn_command (reservedIn_v2_0 (by decide)) (attribute_lexical h)

/-- An item among a valid command's tokens is one of the command's version. -/
theorem ofVersion_command {command : Tree.Command} (h : command.Valid version) {position : Nat}
    {item : Received} (hitem : (command.tokens.map Received.token)[position]? = some item) :
    item.OfVersion version := by
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hitem
  obtain ⟨token, htoken, rfl⟩ := hitem
  cases token with
  | reserved w => exact command_lexical h w (List.mem_of_getElem? htoken)
  | _ => trivial

/-- Every item of what a parser takes for commands is one that a lexer can hand over in the
version in force there. -/
theorem takes_ofVersion {start : BSmtLibSpec.Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (h : Takes start commands taken ending) :
    ∀ position (item : Received), taken[position]? = some item →
      item.OfVersion (versionAt start commands position) := by
  induction h with
  | done =>
    intro position item hitem
    cases position with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hitem
      subst hitem
      trivial
    | succ n => simp at hitem
  | @command v next rest items ending c hc hm _ ih =>
    intro position item hitem
    by_cases hlt : position < c.tokens.length
    · rw [versionAt_head hlt]
      rw [List.getElem?_append_left (by simpa using hlt)] at hitem
      exact ofVersion_command hc hitem
    · have hlen : (c.tokens.map Received.token).length ≤ position := by simp; omega
      rw [List.getElem?_append_right hlen] at hitem
      simp only [versionAt, hlt, ↓reduceIte]
      obtain ⟨-, hnext⟩ := modeAfter_read hm
      rw [← hnext]
      simpa using ih _ item hitem
  | @stop v c hc hm =>
    intro position item hitem
    by_cases hlt : position < c.tokens.length
    · rw [versionAt_head hlt]
      rw [List.getElem?_append_left (by simpa using hlt)] at hitem
      exact ofVersion_command hc hitem
    · have hlen : (c.tokens.map Received.token).length ≤ position := by simp; omega
      rw [List.getElem?_append_right hlen] at hitem
      cases hk : position - (c.tokens.map Received.token).length with
      | zero =>
        rw [hk] at hitem
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hitem
        subst hitem
        trivial
      | succ n => rw [hk] at hitem; simp at hitem
  | @refused v c hc hm =>
    intro position item hitem
    have hlt : position < c.tokens.length := by
      have := (List.getElem?_eq_some_iff.mp hitem).1
      simpa using this
    rw [versionAt_head hlt]
    exact ofVersion_command hc hitem

end BSmtLib.Facts.Proofs.Parser.Rejection.Lexical
