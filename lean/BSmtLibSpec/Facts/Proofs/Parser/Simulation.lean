module

public import BSmtLibSpec.Facts.Proofs.Parser.Parse
public import BSmtLibSpec.Facts.Proofs.Parser.Equations
public import BSmtLibSpec.Facts.Proofs.Grammar.OneToOne

@[expose] public section

/-!
# The traversal and the parser make the same calls

For every monad, handler, points, producer and policy, `parseScript` run on what a
parser receives for a script does what the traversal of the script does (`run_script`), and
leaves whatever follows the script untouched. The proof goes category by category, from the
bottom up: run on the items of a tree followed by anything, the reader of the category makes the
calls of the traversal of the tree and leaves what follows (`run_sort`, `run_term`,
`run_command`, ...). A reader of a list goes through its elements up to the `)` after them
(`run_untilClose`), which no element starts with.

The traversal's own equations for each form of a tree are those of `Parser.Equations`.

Not trusted: everything here is proved.
-/

namespace BSmtLibSpec.Facts.Proofs.Parser.Simulation

open BSmtLibSpec.Lexicon BSmtLibSpec.Grammar BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Grammar.File
open BSmtLibSpec.Regex (Chars chars)
open BSmtLibSpec.Parser.Traversal Program
open BSmtLibSpec.Facts.Proofs.Parser.Equations BSmtLibSpec.Facts.Proofs.Parser.Parse

/-- The items of tokens. -/
abbrev items (tokens : List SyntaxToken) : List Received := tokens.map .token

theorem items_ne_close {tokens : List SyntaxToken}
    (h : Grammar.Read.startsClose (tokens ++ [.parenClose]) = false) (rest r : List Received) :
    items tokens ++ rest ≠ .token .parenClose :: r := by
  cases tokens with
  | nil => simp [Grammar.Read.startsClose] at h
  | cons token tokens =>
    cases token <;> simp_all [Grammar.Read.startsClose]



section

variable {m : Type → Type} [Monad m] [LawfulMonad m] {ε : Type} {values : Values}
variable {points : Points m} {handler : Handler m ε values}
variable {producer : Producer m} {policy : VersionPolicy}


local notation "runP" => Program.run points handler producer policy

theorem run_listStep {α : Type} (element : Received → Program values α)
    (others : Program values (List α)) (input : List Received)
    (h : ∀ rest, input ≠ .token .parenClose :: rest) :
    runP (listStep element others) input =
      runP (do let first ← parseWith element; let rest ← others; pure (first :: rest)) input := by
  cases input with
  | nil => simp [listStep, parseWith, next, run]
  | cons item input =>
    have hi : item ≠ .token .parenClose := fun e => h input (by rw [e])
    simp only [listStep, run_bind, run_next, run_parseWith, bind_assoc, pure_bind]

theorem run_listStep_close {α : Type} (element : Received → Program values α)
    (others : Program values (List α)) (rest : List Received) :
    runP (listStep element others) (.token .parenClose :: rest) =
      (Traversal.receive points (.token .parenClose) >>= fun _ => pure ([], rest)) := by
  simp [listStep, run_bind, run_next]

/-- A list read up to its `)` makes the calls of its elements, one after another, then takes
the `)`. -/
theorem run_untilClose {α β : Type} (element : Received → Program values α)
    (F : β → Run m ε α) (tokensOf : β → List SyntaxToken) :
    ∀ (list : List β) (rest : List Received) {k : Nat}, list.length < k →
    (∀ b ∈ list, Grammar.Read.startsClose (tokensOf b ++ [.parenClose]) = false) →
    (∀ b ∈ list, ∀ rest, runP (parseWith element) (items (tokensOf b) ++ rest) =
      (F b >>= fun a => pure (a, rest))) →
    runP (untilClose element k) (items (list.flatMap tokensOf) ++ .token .parenClose :: rest) =
      (do let handled ← list.mapM F; take points .parenClose; pure (handled, rest))
  | [], rest, k + 1, _, _, _ => by simp [untilClose, run_listStep_close, take]
  | b :: list, rest, k + 1, hk, hs, he => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
    simp only [untilClose, List.flatMap_cons, items, List.map_append, List.append_assoc]
    rw [run_listStep _ _ _ (items_ne_close (hs b (by simp)) _)]
    simp only [run_bind, he b (by simp), bind_assoc, pure_bind]
    simp [run_untilClose element F tokensOf list _ hk (fun b hb => hs b (by simp [hb]))
      (fun b hb => he b (by simp [hb]))]

/-- Taking the tokens of the elements of a list, element after element. -/
theorem takeAll_flatMap {β : Type} (f : β → List SyntaxToken) (list : List β) :
    (takeAll points (list.flatMap f) : Run m ε Unit) =
      list.forM fun b => takeAll points (f b) := by
  induction list with
  | nil => simp [takeAll]
  | cons b list ih => simp_all [takeAll]

/-- A run over a list whose results are given by the elements returns them. -/
theorem mapM_effects {β γ : Type} (x : β → Run m ε Unit) (g : β → γ) (list : List β) :
    list.mapM (fun b => (fun _ => g b) <$> x b) = (fun _ => list.map g) <$> forM list x := by
  induction list with
  | nil => simp
  | cons b list ih => simp [ih]

/-- A run over a list whose results are the elements themselves returns the list. -/
theorem mapM_const {β : Type} (x : β → Run m ε Unit) (list : List β) :
    list.mapM (fun b => (fun _ => b) <$> x b) = (fun _ => list) <$> list.forM x := by
  induction list with
  | nil => simp
  | cons b list ih => simp [ih]

theorem run_index (index : Tree.Index) (rest : List Received) :
    runP (parseWith indexAt) (items index.tokens ++ rest) =
      ((takeAll points index.tokens >>= fun _ => pure index) >>= fun a => pure (a, rest)) := by
  cases index <;> simp [Tree.Index.tokens, indexAt, run_parseWith, takeAll, take]

theorem startsClose_index (index : Tree.Index) :
    Grammar.Read.startsClose (index.tokens ++ [.parenClose]) = false := by
  cases index <;> rfl

theorem run_indexedAfterWord (symbol : Tree.Symbol) (list : List Tree.Index)
    (rest : List Received) {n : Nat} (h : list.length < n) :
    runP (indexedAfterWord n)
        (items (.symbol symbol :: list.flatMap Tree.Index.tokens) ++
          .token .parenClose :: rest) =
      (do take points (.symbol symbol); takeAll points (list.flatMap Tree.Index.tokens)
          take points .parenClose; pure (⟨symbol, list⟩, rest)) := by
  simp only [indexedAfterWord, expectSymbol, items, List.map_cons, List.cons_append, run_bind,
    run_next, bind_assoc, pure_bind]
  have hl := run_untilClose (points := points) (handler := handler)
    (producer := producer) (policy := policy) indexAt
    (fun i => takeAll points i.tokens >>= fun _ => pure i) Tree.Index.tokens list rest h
    (fun i _ => startsClose_index i) (fun i _ r => run_index i r)
  simp only [items] at hl
  simp [hl, takeAll_flatMap, take, mapM_const]

theorem run_identifier (identifier : Tree.Identifier) (rest : List Received) {n : Nat}
    (h : identifier.indices.length < n) :
    runP (parseWith (identifierAt n)) (items identifier.tokens ++ rest) =
      (do takeAll points identifier.tokens; pure (identifier, rest)) := by
  obtain ⟨symbol, indices⟩ := identifier
  cases indices with
  | nil => simp [Tree.Identifier.tokens, identifierAt, run_parseWith, takeAll, take]
  | cons index list =>
    have hw := run_indexedAfterWord (points := points) (handler := handler)
      (producer := producer) (policy := policy) symbol (index :: list) rest h
    simp [takeAll, take] at hw
    simp +decide [Tree.Identifier.tokens, paren, word, identifierAt, run_next, run_parseWith,
      run_bind, hw,
      takeAll, take]


theorem length_le_sizeOf {β : Type} [SizeOf β] (list : List β) : list.length ≤ sizeOf list := by
  induction list with
  | nil => simp
  | cons b list ih => simp; omega

theorem sizeOf_lt_of_mem {β : Type} [SizeOf β] {b : β} {list : List β} (h : b ∈ list) :
    sizeOf b < sizeOf list := List.sizeOf_lt_of_mem h

theorem sorts_eq (list : List Tree.«Sort») :
    sorts points handler list = list.mapM (sort points handler) := by
  induction list with
  | nil => simp [sorts]
  | cons s list ih => simp [sorts, ih]

theorem run_sort : ∀ n (s : Tree.«Sort») rest, sizeOf s < n →
    runP (parseSort n) (items s.tokens ++ rest) =
      (sort points handler s >>= fun a => pure (a, rest))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, ⟨⟨symbol, indices⟩, arguments⟩, rest, h => by
    simp only [Tree.«Sort».mk.sizeOf_spec, Tree.Identifier.mk.sizeOf_spec] at h
    have hlen := length_le_sizeOf indices
    have hlist : ∀ rest', runP (untilClose (sortAt n) n)
        (items (arguments.flatMap Tree.«Sort».tokens) ++ .token .parenClose :: rest') =
        (do let handled ← arguments.mapM (sort points handler); take points .parenClose
            pure (handled, rest')) := fun rest' =>
      run_untilClose _ _ _ arguments rest' (by have := length_le_sizeOf arguments; omega)
        (fun b _ => Grammar.OneToOne.startsClose_sort b _)
        (fun b hb r => run_sort n b r (by have := sizeOf_lt_of_mem hb; omega))
    cases arguments with
    | nil =>
      cases indices with
      | nil =>
        simp [parseSort, sortAt, sortStep.eq_def, Tree.«Sort».tokens, Tree.Identifier.tokens,
          sort_nil,
          run_parseWith, run_emitSort, takeAll, take]
      | cons index list =>
        have hw := run_indexedAfterWord (points := points) (handler := handler)
          (producer := producer) (policy := policy) symbol (index :: list)
          rest (n := n) (by omega)
        simp [takeAll, take] at hw
        simp +decide [parseSort, sortAt, sortStep.eq_def, Tree.«Sort».tokens,
            Tree.Identifier.tokens,
          paren, word, sort_nil, run_next, run_parseWith, run_bind, run_emitSort, hw, takeAll, take]
    | cons argument arguments =>
      have hl := hlist rest
      rw [← Grammar.OneToOne.tokensAll_eq_flatMap] at hl
      cases indices with
      | nil =>
        simp [take] at hl
        simp [parseSort, sortAt, sortStep.eq_def, Tree.«Sort».tokens, Tree.Identifier.tokens, paren,
          sort_cons, sorts_eq, identifierAt, run_next, run_parseWith, run_bind, run_emitSort, hl,
          takeAll, take]
      | cons index list =>
        have hw := run_indexedAfterWord (points := points) (handler := handler)
          (producer := producer) (policy := policy) symbol (index :: list)
          (items (Tree.«Sort».tokensAll (argument :: arguments)) ++ .token .parenClose :: rest)
          (n := n) (by omega)
        simp [takeAll, take] at hw hl
        simp +decide [parseSort, sortAt, sortStep.eq_def, Tree.«Sort».tokens,
          Tree.Identifier.tokens, paren, word, sort_cons, identifierAt, run_next, run_parseWith,
          run_bind,
          run_emitSort, sorts_eq, hw, hl, takeAll, take]

theorem sExprs_eq (list : List Tree.SExpr) :
    sExprs points handler list = list.mapM (sExpr points handler) := by
  induction list with
  | nil => simp [sExprs]
  | cons s list ih => simp only [sExprs, ih, List.mapM_cons]

theorem run_sExpr : ∀ n (s : Tree.SExpr) rest, sizeOf s < n →
    runP (parseWith (sExprAt n)) (items s.tokens ++ rest) =
      (sExpr points handler s >>= fun a => pure (a, rest))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, rest, h => by
    cases s with
    | constant constant =>
      cases constant <;> simp [sExprAt, sExprStep.eq_def, constantOf, Tree.SExpr.tokens,
        Tree.SpecConstant.token, sExpr_constant, run_parseWith, run_emitSExpr, take]
    | list list =>
      simp only [Tree.SExpr.list.sizeOf_spec] at h
      have hl := run_untilClose (points := points) (handler := handler)
        (producer := producer) (policy := policy) (sExprAt n) (sExpr points handler)
        Tree.SExpr.tokens list rest (k := n) (by have := length_le_sizeOf list; omega)
        (fun b _ => Grammar.OneToOne.startsClose_sExpr b _)
        (fun b hb r => run_sExpr n b r (by have := sizeOf_lt_of_mem hb; omega))
      rw [← Grammar.OneToOne.sExprsAll_eq_flatMap] at hl
      simp [take] at hl
      simp [sExprAt, sExprStep.eq_def, Tree.SExpr.tokens, paren, sExpr_list, sExprs_eq,
        run_parseWith, run_bind, run_emitSExpr, hl, take]
    | _ =>
      simp [sExprAt, sExprStep.eq_def, Tree.SExpr.tokens, sExpr_symbol, sExpr_reserved,
        sExpr_keyword, run_parseWith, run_emitSExpr, take]

theorem run_sExprs (list : List Tree.SExpr) (rest : List Received) {n : Nat}
    (h : sizeOf list < n) :
    runP (untilClose (sExprAt n) n)
        (items (Tree.SExpr.tokensAll list) ++ .token .parenClose :: rest) =
      (do let handled ← sExprs points handler list; take points .parenClose
          pure (handled, rest)) := by
  rw [Grammar.OneToOne.sExprsAll_eq_flatMap, sExprs_eq]
  exact run_untilClose _ _ _ list rest (by have := length_le_sizeOf list; omega)
    (fun b _ => Grammar.OneToOne.startsClose_sExpr b _)
    (fun b hb r => run_sExpr n b r (by have := sizeOf_lt_of_mem hb; omega))

/-- An attribute with a value: the value, its call, then the item after it. -/
theorem run_attributeAfter_some (keyword : Chars) (value : Tree.AttributeValue)
    (following : SyntaxToken) (rest : List Received) {n : Nat} (h : sizeOf value < n) :
    runP (attributeAfter n keyword) (items value.tokens ++ .token following :: rest) =
      (do let node ← attributeValue points handler value
          let handled ← callAttribute handler (.handleAttribute keyword (some node))
          take points following
          pure ((handled, some node, .token following), rest)) := by
  cases value with
  | constant constant =>
    cases constant <;> simp [attributeAfter, valueAt, constantOf, Tree.AttributeValue.tokens,
      Tree.SpecConstant.token, attributeValue, run_next, run_bind, run_emitAttribute, take]
  | symbol =>
    simp [attributeAfter, valueAt, Tree.AttributeValue.tokens, attributeValue, run_next,
      run_bind, run_emitAttribute, take]
  | list list =>
    simp only [Tree.AttributeValue.list.sizeOf_spec] at h
    have hl := run_sExprs (points := points) (handler := handler)
      (producer := producer) (policy := policy) list (.token following :: rest)
      (n := n) (by omega)
    simp [take] at hl
    simp [attributeAfter, valueAt, Tree.AttributeValue.tokens, paren, attributeValue, run_next,
      run_bind, run_emitAttribute, hl, take]

/-- An attribute without a value: the item after it, then its call. -/
theorem run_attributeAfter_none (keyword : Chars) (following : SyntaxToken)
    (hf : following = .parenClose ∨ ∃ name, following = .keyword name) (rest : List Received)
    (n : Nat) :
    runP (attributeAfter n keyword) (.token following :: rest) =
      (do take points following
          let handled ← callAttribute handler (.handleAttribute keyword none)
          pure ((handled, none, .token following), rest)) := by
  rcases hf with rfl | ⟨name, rfl⟩ <;>
    simp [attributeAfter, valueAt, constantOf, run_next, run_bind, run_emitAttribute, take]

/-- The tokens of an attribute's value, none if it has no value. -/
def valueTokens : Option Tree.AttributeValue → List SyntaxToken
  | some value => value.tokens
  | none => []

theorem attribute_tokens (keyword : Chars) (value : Option Tree.AttributeValue) :
    Tree.Attribute.tokens ⟨keyword, value⟩ = .keyword keyword :: valueTokens value := by
  cases value <;> rfl

theorem run_attributesFrom : ∀ (attributes : List Tree.Attribute) (keyword : Chars)
    (value : Option Tree.AttributeValue) (rest : List Received) {n : Nat},
    sizeOf value + sizeOf attributes < n →
    runP (attributesFrom n keyword)
        (items (valueTokens value ++ attributes.flatMap Tree.Attribute.tokens) ++
          .token .parenClose :: rest) =
      (attributesThen points handler keyword value attributes >>= fun a => pure (a, rest))
  | [], keyword, value, rest, n + 1, h => by
    cases value with
    | none =>
      simp [attributesFrom, attributesStep, valueTokens,
        run_attributeAfter_none keyword .parenClose (.inl rfl), run_bind, attributesThen,
        attributeThen_none, take]
    | some value =>
      simp only [Option.some.sizeOf_spec] at h
      simp [attributesFrom, attributesStep, valueTokens, run_attributeAfter_some keyword value
        .parenClose rest (n := n) (by omega), run_bind, attributesThen, attributeThen_some,
        take]
  | ⟨next, nextValue⟩ :: attributes, keyword, value, rest, n + 1, h => by
    simp only [List.cons.sizeOf_spec, Tree.Attribute.mk.sizeOf_spec] at h
    have ih := run_attributesFrom attributes next nextValue rest (n := n) (by omega)
    have hin : items (valueTokens value ++
          (⟨next, nextValue⟩ :: attributes).flatMap Tree.Attribute.tokens) ++
          .token .parenClose :: rest =
        items (valueTokens value) ++ .token (.keyword next) ::
          (items (valueTokens nextValue ++ attributes.flatMap Tree.Attribute.tokens) ++
            .token .parenClose :: rest) := by
      cases nextValue <;> simp [valueTokens, Tree.Attribute.tokens]
    rw [hin, attributesFrom, attributesStep, run_bind]
    cases value with
    | none =>
      simp only [valueTokens, items, List.map_nil, List.nil_append] at ih ⊢
      rw [run_attributeAfter_none keyword (.keyword next) (.inr ⟨next, rfl⟩)]
      simp only [List.map_append, List.append_assoc] at ih
      simp [ih, run_bind, attributesThen, attributeThen_none]
    | some value =>
      simp only [Option.some.sizeOf_spec] at h
      simp only [valueTokens, items] at ih ⊢
      rw [run_attributeAfter_some keyword value (.keyword next) _ (n := n) (by omega)]
      simp only [List.map_append, List.append_assoc] at ih
      simp [ih, run_bind, attributesThen, attributeThen_some]

/-! ## Sorted variables and patterns -/

/-- A sorted variable, as the traversal goes through it. -/
def sortedVarRun (variable' : Tree.SortedVar) : Run m ε (Tree.Symbol × values.sort) := do
  takeAll points [.parenOpen, .symbol variable'.symbol]
  let handled ← sort points handler variable'.sort
  take points .parenClose
  pure (variable'.symbol, handled)

theorem sortedVars_eq (list : List Tree.SortedVar) :
    sortedVars points handler list = list.mapM (sortedVarRun (points := points)
      (handler := handler)) := by
  induction list with
  | nil => simp [sortedVars]
  | cons v list ih =>
    obtain ⟨symbol, s⟩ := v
    simp only [sortedVars, ih, List.mapM_cons, sortedVarRun, bind_assoc, pure_bind]

theorem startsClose_sortedVar (variable' : Tree.SortedVar) :
    Grammar.Read.startsClose (variable'.tokens ++ [.parenClose]) = false := by
  obtain ⟨symbol, s⟩ := variable'
  rfl

theorem run_sortedVar (variable' : Tree.SortedVar) (rest : List Received) {n : Nat}
    (h : sizeOf variable' < n) :
    runP (parseWith (sortedVarAt n)) (items variable'.tokens ++ rest) =
      (sortedVarRun (points := points) (handler := handler) variable' >>= fun a =>
        pure (a, rest)) := by
  obtain ⟨symbol, s⟩ := variable'
  simp only [Tree.SortedVar.mk.sizeOf_spec] at h
  have hs := run_sort (points := points) (handler := handler)
    (producer := producer) (policy := policy) n s (.token .parenClose :: rest)
    (by omega)
  simp at hs
  simp [Tree.SortedVar.tokens, paren, sortedVarAt, expectSymbol, expectClose,
    sortedVarRun, run_next, run_parseWith, run_bind, hs, takeAll, take]

theorem run_sortedVars (list : List Tree.SortedVar) (rest : List Received) {n : Nat}
    (h : sizeOf list < n) :
    runP (untilClose (sortedVarAt n) n)
        (items (list.flatMap Tree.SortedVar.tokens) ++ .token .parenClose :: rest) =
      (do let handled ← sortedVars points handler list; take points .parenClose
          pure (handled, rest)) := by
  rw [sortedVars_eq]
  exact run_untilClose _ _ _ list rest (by have := length_le_sizeOf list; omega)
    (fun b _ => startsClose_sortedVar b)
    (fun b hb r => run_sortedVar b r (by have := sizeOf_lt_of_mem hb; omega))

theorem flatMap_singleton {β γ : Type} (f : β → γ) (list : List β) :
    list.flatMap (fun b => [f b]) = list.map f := by
  induction list with
  | nil => rfl
  | cons b list ih => simp [ih]

theorem run_symbolOrWildcard (symbol : Tree.SymbolOrWildcard) (rest : List Received) :
    runP (parseWith symbolOrWildcardAt) (items [symbol.token] ++ rest) =
      ((takeAll points [symbol.token] >>= fun _ => pure symbol) >>= fun a => pure (a, rest)) := by
  cases symbol <;> simp +decide [Tree.SymbolOrWildcard.token, word, symbolOrWildcardAt,
    symbolOrWildcardOf, run_parseWith, takeAll, take]

theorem run_pattern (pattern : Tree.Pattern) (rest : List Received) {n : Nat}
    (h : sizeOf pattern < n) :
    runP (parseWith (patternAt n)) (items pattern.tokens ++ rest) =
      (do takeAll points pattern.tokens; pure (pattern, rest)) := by
  cases pattern with
  | single symbol =>
    have hs := run_symbolOrWildcard (points := points) (handler := handler)
      (producer := producer) (policy := policy) symbol rest
    cases symbol <;> simp +decide [Tree.SymbolOrWildcard.token, word] at hs ⊢ <;>
      simp +decide [Tree.Pattern.tokens, Tree.SymbolOrWildcard.token, word, patternAt,
        symbolOrWildcardAt, symbolOrWildcardOf, run_parseWith, takeAll, take]
  | constructor head arguments =>
    simp only [Tree.Pattern.constructor.sizeOf_spec] at h
    have hl := run_untilClose (points := points) (handler := handler)
      (producer := producer) (policy := policy) symbolOrWildcardAt
      (fun s => takeAll points [s.token] >>= fun _ => pure s) (fun s => [s.token])
      arguments rest (k := n) (by have := length_le_sizeOf arguments; omega)
      (fun s _ => by cases s <;> rfl) (fun s _ r => run_symbolOrWildcard s r)
    simp [take, takeAll, flatMap_singleton, mapM_const] at hl
    simp [Tree.Pattern.tokens, paren, patternAt, expectSymbol, run_next, run_parseWith, run_bind,
      hl,
      takeAll, take]


/-! ## Terms -/

theorem terms_eq (list : List Tree.Term) :
    terms points handler list = list.mapM (term points handler) := by
  induction list with
  | nil => simp [terms]
  | cons t list ih => simp only [terms, ih, List.mapM_cons]

/-- A binding of a `let`, as the traversal goes through it. -/
def bindingRun (binding : Tree.Symbol × Tree.Term) : Run m ε (Tree.Symbol × values.term) := do
  takeAll points [.parenOpen, .symbol binding.1]
  let handled ← term points handler binding.2
  take points .parenClose
  pure (binding.1, handled)

theorem bindings_eq (list : List (Tree.Symbol × Tree.Term)) :
    bindings points handler list =
      list.mapM (bindingRun (points := points) (handler := handler)) := by
  induction list with
  | nil => simp [bindings]
  | cons b list ih =>
    obtain ⟨symbol, t⟩ := b
    simp only [bindings, ih, List.mapM_cons, bindingRun, bind_assoc, pure_bind]

/-- A case of a `match`, as the traversal goes through it. -/
def caseRun (scrutinee : values.term) (matchCase : Tree.Pattern × Tree.Term) :
    Run m ε (Tree.Pattern × values.term) := do
  take points .parenOpen
  takeAll points matchCase.1.tokens
  let scope ← callScope handler (.startMatchCase scrutinee matchCase.1)
  let result ← term points handler matchCase.2
  take points .parenClose
  let handled ← callTerm handler (.endMatchCase scope scrutinee result)
  pure (matchCase.1, handled)

theorem cases_eq (scrutinee : values.term) (list : List (Tree.Pattern × Tree.Term)) :
    cases points handler scrutinee list =
      list.mapM (caseRun (points := points) (handler := handler) scrutinee) := by
  induction list with
  | nil => simp [cases]
  | cons c list ih =>
    obtain ⟨pattern, body⟩ := c
    simp only [cases_cons, ih, List.mapM_cons, caseRun, bind_assoc, pure_bind]

theorem bindingTokens_eq (list : List (Tree.Symbol × Tree.Term)) :
    Tree.Term.bindingTokens list =
      list.flatMap fun b => paren (.symbol b.1 :: b.2.tokens) := by
  induction list with
  | nil => rfl
  | cons b list ih => simp [Tree.Term.bindingTokens, ih]

theorem caseTokens_eq (list : List (Tree.Pattern × Tree.Term)) :
    Tree.Term.caseTokens list = list.flatMap fun c => paren (c.1.tokens ++ c.2.tokens) := by
  induction list with
  | nil => rfl
  | cons c list ih => simp [Tree.Term.caseTokens, ih]

/-- What `run_term` proves for terms with less fuel. -/
def TermsRead (n : Nat) : Prop :=
  ∀ (t : Tree.Term) rest, sizeOf t < n →
    runP (parseWith (termAt n)) (items t.tokens ++ rest) =
      (term points handler t >>= fun a => pure (a, rest))

theorem run_terms_of {n : Nat} (ih : TermsRead (points := points) (handler := handler)
    (producer := producer) (policy := policy) n) (list : List Tree.Term)
    (rest : List Received) (h : sizeOf list < n) :
    runP (untilClose (termAt n) n)
        (items (Tree.Term.tokensAll list) ++ .token .parenClose :: rest) =
      (do let handled ← terms points handler list; take points .parenClose
          pure (handled, rest)) := by
  rw [Grammar.OneToOne.termsAll_eq_flatMap, terms_eq]
  exact run_untilClose _ _ _ list rest (by have := length_le_sizeOf list; omega)
    (fun b _ => Grammar.OneToOne.startsClose_term b _)
    (fun b hb r => ih b r (by have := sizeOf_lt_of_mem hb; omega))

theorem run_bindings_of {n : Nat} (ih : TermsRead (points := points) (handler := handler)
    (producer := producer) (policy := policy) n)
      (list : List (Tree.Symbol × Tree.Term)) (rest : List Received)
    (h : sizeOf list < n) :
    runP (untilClose (bindingAt (termAt n)) n)
        (items (Tree.Term.bindingTokens list) ++ .token .parenClose :: rest) =
      (do let handled ← bindings points handler list; take points .parenClose
          pure (handled, rest)) := by
  rw [bindingTokens_eq, bindings_eq]
  refine run_untilClose _ _ _ list rest (by have := length_le_sizeOf list; omega)
    (fun b _ => by simp [paren, Grammar.Read.startsClose]) (fun b hb r => ?_)
  obtain ⟨symbol, t⟩ := b
  have hb' := sizeOf_lt_of_mem hb
  simp only [Prod.mk.sizeOf_spec] at hb'
  have ht := ih t (.token .parenClose :: r) (by omega)
  simp at ht
  simp [paren, bindingAt, expectSymbol, expectClose, bindingRun, run_next, run_parseWith, run_bind,
    ht,
    takeAll, take]

theorem run_cases_of {n : Nat} (ih : TermsRead (points := points) (handler := handler)
    (producer := producer) (policy := policy) n) (scrutinee : values.term)
      (list : List (Tree.Pattern × Tree.Term))
    (rest : List Received) (h : sizeOf list < n) :
    runP (untilClose (caseAt (termAt n) n scrutinee) n)
        (items (Tree.Term.caseTokens list) ++ .token .parenClose :: rest) =
      (do let handled ← cases points handler scrutinee list; take points .parenClose
          pure (handled, rest)) := by
  rw [caseTokens_eq, cases_eq]
  refine run_untilClose _ _ _ list rest (by have := length_le_sizeOf list; omega)
    (fun b _ => by simp [paren, Grammar.Read.startsClose]) (fun b hb r => ?_)
  obtain ⟨pattern, t⟩ := b
  have hb' := sizeOf_lt_of_mem hb
  simp only [Prod.mk.sizeOf_spec] at hb'
  have ht := ih t (.token .parenClose :: r) (by omega)
  have hp := run_pattern (points := points) (handler := handler)
    (producer := producer) (policy := policy) pattern
    (items t.tokens ++ .token .parenClose :: r) (n := n) (by omega)
  simp at ht hp
  simp [paren, caseAt, expectClose, caseRun, run_next, run_parseWith, run_bind, ht, hp,
    run_emitScope,
    run_emitTerm, take]


set_option hygiene false in
/-- The simp set of the cases of `run_term`. -/
macro "term_simp" "[" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp +decide [termAt, termStep.eq_def, termAfterWord, applicationAt, Tree.Term.tokens,
    Tree.QualIdentifier.tokens, Tree.Quantifier.word, quantifierOf,
    paren, word, expectOpen, expectClose, qualIdentifier, run_next, run_parseWith, run_bind,
    run_emitTerm, run_emitScope, run_emitUnit, run_receive, takeAllArriving, takeAll, take,
    $extra,*])

/-- What `run_termArriving` proves for terms with less fuel: with a call due at the arrival
of the term's first item. -/
def TermsReadArriving (n : Nat) : Prop :=
  ∀ (atArrival : Option (Call values .nothing)) (t : Tree.Term) rest, sizeOf t < n →
    runP (Program.receive atArrival (termAt n)) (items t.tokens ++ rest) =
      (term points handler t (arrival handler atArrival) >>= fun a => pure (a, rest))

omit [LawfulMonad m] in
theorem termsRead_of {n : Nat} (h : TermsReadArriving (points := points) (handler := handler)
    (producer := producer) (policy := policy) n) :
    TermsRead (points := points) (handler := handler) (producer := producer) (policy := policy)
      n :=
  fun t rest ht => h none t rest ht

theorem run_termArriving : ∀ n, TermsReadArriving (points := points) (handler := handler)
    (producer := producer) (policy := policy) n
  | 0 => fun _ _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => by
    have ih := termsRead_of (run_termArriving n)
    intro atArrival t rest h
    cases t with
    | constant constant =>
      cases constant <;> term_simp [constantOf, Tree.SpecConstant.token, term_constant]
    | identifier qualified =>
      simp only [Tree.Term.identifier.sizeOf_spec] at h
      cases qualified with
      | plain identifier =>
        obtain ⟨symbol, indices⟩ := identifier
        cases indices with
        | nil => term_simp [term_identifier, Tree.Identifier.tokens]
        | cons index list =>
          simp only [Tree.QualIdentifier.plain.sizeOf_spec, Tree.Identifier.mk.sizeOf_spec,
            List.cons.sizeOf_spec] at h
          have hw := run_indexedAfterWord (points := points) (handler := handler)
            (producer := producer) (policy := policy) symbol (index :: list)
            rest (n := n) (by have := length_le_sizeOf (index :: list); simp at this ⊢; omega)
          simp [take] at hw
          term_simp [term_identifier, Tree.Identifier.tokens, hw]
      | as identifier s =>
        simp only [Tree.QualIdentifier.as.sizeOf_spec] at h
        have hs := run_sort (points := points) (handler := handler)
          (producer := producer) (policy := policy) n s
          (.token .parenClose :: rest) (by omega)
        have hi := run_identifier (points := points) (handler := handler)
          (producer := producer) (policy := policy) identifier
          (items s.tokens ++ .token .parenClose :: rest) (n := n)
          (by obtain ⟨_,
            indices⟩ := identifier; have := length_le_sizeOf indices; simp at h ⊢; omega)
        simp at hs hi
        term_simp [term_identifier, hs, hi]
    | application function arguments =>
      simp only [Tree.Term.application.sizeOf_spec] at h
      have ha := run_terms_of ih arguments rest (by omega)
      simp [take] at ha
      cases function with
      | plain identifier =>
        obtain ⟨symbol, indices⟩ := identifier
        cases indices with
        | nil => term_simp [term_application, Tree.Identifier.tokens, terms_eq, ha]
        | cons index list =>
          simp only [Tree.QualIdentifier.plain.sizeOf_spec, Tree.Identifier.mk.sizeOf_spec,
            List.cons.sizeOf_spec] at h
          have hw := run_indexedAfterWord (points := points) (handler := handler)
            (producer := producer) (policy := policy) symbol (index :: list)
            (items (Tree.Term.tokensAll arguments) ++ .token .parenClose :: rest) (n := n)
            (by have := length_le_sizeOf (index :: list); simp at this ⊢; omega)
          simp [take] at hw
          term_simp [term_application, Tree.Identifier.tokens, terms_eq, hw, ha]
      | as identifier s =>
        simp only [Tree.QualIdentifier.as.sizeOf_spec] at h
        have hs := run_sort (points := points) (handler := handler)
          (producer := producer) (policy := policy) n s
          (.token .parenClose :: (items (Tree.Term.tokensAll arguments) ++
            .token .parenClose :: rest)) (by omega)
        have hi := run_identifier (points := points) (handler := handler)
          (producer := producer) (policy := policy) identifier
          (items s.tokens ++ .token .parenClose :: (items (Tree.Term.tokensAll arguments) ++
            .token .parenClose :: rest)) (n := n)
          (by obtain ⟨_, indices⟩ := identifier; have := length_le_sizeOf indices; simp at h ⊢
              omega)
        simp at hs hi
        term_simp [term_application, terms_eq, hs, hi, ha]
    | «let» bindings body =>
      simp only [Tree.Term.«let».sizeOf_spec] at h
      have hb := ih body (.token .parenClose :: rest) (by omega)
      have hl := run_bindings_of ih bindings (items body.tokens ++ .token .parenClose :: rest)
        (by omega)
      simp [take] at hb hl
      term_simp [term_let, hb, hl]
    | lambda variables body =>
      simp only [Tree.Term.lambda.sizeOf_spec] at h
      have hb := ih body (.token .parenClose :: rest) (by omega)
      have hl := run_sortedVars (points := points) (handler := handler)
        (producer := producer) (policy := policy) variables
        (items body.tokens ++ .token .parenClose :: rest) (n := n) (by omega)
      simp [take] at hb hl
      term_simp [term_lambda, hb, hl]
    | quantified quantifier variables body =>
      simp only [Tree.Term.quantified.sizeOf_spec] at h
      have hb := ih body (.token .parenClose :: rest) (by omega)
      have hl := run_sortedVars (points := points) (handler := handler)
        (producer := producer) (policy := policy) variables
        (items body.tokens ++ .token .parenClose :: rest) (n := n) (by omega)
      simp [take] at hb hl
      cases quantifier <;> term_simp [term_quantified, hb, hl]
    | «match» scrutinee matchCases =>
      simp only [Tree.Term.«match».sizeOf_spec] at h
      have hs := ih scrutinee (.token .parenOpen :: (items (Tree.Term.caseTokens matchCases) ++
        .token .parenClose :: .token .parenClose :: rest)) (by omega)
      simp at hs
      have hc := fun scrutinee' => run_cases_of ih scrutinee' matchCases
        (.token .parenClose :: rest) (by omega)
      simp [take] at hc
      term_simp [term_match, hs, hc]
    | annotated annotated attributes =>
      simp only [Tree.Term.annotated.sizeOf_spec] at h
      cases attributes with
      | nil =>
        have ht := ih annotated (.token .parenClose :: rest) (by omega)
        simp at ht
        term_simp [term_annotated, ht]
      | cons first others =>
        obtain ⟨keyword, value⟩ := first
        simp only [List.cons.sizeOf_spec, Tree.Attribute.mk.sizeOf_spec] at h
        have hin : items (List.flatMap Tree.Attribute.tokens (⟨keyword, value⟩ :: others)) =
            .token (.keyword keyword) :: items (valueTokens value ++
              others.flatMap Tree.Attribute.tokens) := by
          cases value <;> simp [valueTokens, Tree.Attribute.tokens]
        have ha := run_attributesFrom (points := points) (handler := handler)
          (producer := producer) (policy := policy) others keyword value rest
          (n := n) (by omega)
        have ht := ih annotated (items (List.flatMap Tree.Attribute.tokens
          (⟨keyword, value⟩ :: others)) ++ .token .parenClose :: rest) (by omega)
        rw [hin] at ht
        simp at ht
        simp only [items, List.map_append, List.append_assoc] at ha
        term_simp [term_annotated, attribute_tokens, ht, ha]

theorem run_term (n : Nat) : TermsRead (points := points) (handler := handler)
    (producer := producer) (policy := policy) n :=
  termsRead_of (run_termArriving n)

/-! ## The parts of commands -/

/-- A selector as the sorted variable it is written as. -/
def selectorVar (selector : Tree.SelectorDec) : Tree.SortedVar := ⟨selector.symbol, selector.sort⟩

omit [LawfulMonad m] in
theorem selectors_eq (list : List Tree.SelectorDec) :
    selectors points handler list = sortedVars points handler (list.map selectorVar) := by
  induction list with
  | nil => simp [selectors, sortedVars]
  | cons s list ih =>
    obtain ⟨symbol, s⟩ := s
    simp only [selectors, sortedVars, ih, List.map_cons, selectorVar]

theorem selectorTokens_eq (list : List Tree.SelectorDec) :
    list.flatMap Tree.SelectorDec.tokens =
      (list.map selectorVar).flatMap Tree.SortedVar.tokens := by
  induction list with
  | nil => rfl
  | cons s list ih => simp [ih, selectorVar, Tree.SelectorDec.tokens, Tree.SortedVar.tokens]

theorem sizeOf_selectorVars (list : List Tree.SelectorDec) :
    sizeOf (list.map selectorVar) = sizeOf list := by
  induction list with
  | nil => rfl
  | cons s list ih => obtain ⟨symbol, s⟩ := s; simp [ih, selectorVar]

theorem run_constructorAfterOpen (constructor : Tree.ConstructorDec) (rest : List Received)
    {n : Nat} (h : sizeOf constructor < n) :
    runP (Parse.constructorAfterOpen n)
        (items (.symbol constructor.symbol :: constructor.selectors.flatMap Tree.SelectorDec.tokens)
          ++ .token .parenClose :: rest) =
      (Traversal.constructorAfterOpen points handler constructor >>= fun a => pure (a, rest)) := by
  obtain ⟨symbol, list⟩ := constructor
  simp only [Tree.ConstructorDec.mk.sizeOf_spec] at h
  have hl := run_sortedVars (points := points) (handler := handler)
    (producer := producer) (policy := policy) (list.map selectorVar) rest (n := n)
    (by rw [sizeOf_selectorVars]; omega)
  rw [← selectorTokens_eq, ← selectors_eq] at hl
  simp [take] at hl
  simp [Parse.constructorAfterOpen, expectSymbol, Traversal.constructorAfterOpen, run_next,
    run_bind, hl, take]

theorem run_constructors (list : List Tree.ConstructorDec) (rest : List Received) {n : Nat}
    (h : sizeOf list < n) :
    runP (untilClose (constructorAt n) n)
        (items (list.flatMap Tree.ConstructorDec.tokens) ++ .token .parenClose :: rest) =
      (do let handled ← constructors points handler list; take points .parenClose
          pure (handled, rest)) := by
  refine run_untilClose _ _ _ list rest (by have := length_le_sizeOf list; omega)
    (fun c _ => by simp [Tree.ConstructorDec.tokens, paren, Grammar.Read.startsClose])
    (fun c hc r => ?_)
  have hc' := sizeOf_lt_of_mem hc
  have ho := run_constructorAfterOpen (points := points) (handler := handler)
    (producer := producer) (policy := policy) c r (n := n) (by omega)
  obtain ⟨symbol, selectors⟩ := c
  simp at ho
  simp [Tree.ConstructorDec.tokens, paren, constructorAt, run_parseWith, ho, take]

theorem run_symbols (list : List Tree.Symbol) (rest : List Received) {n : Nat}
    (h : list.length < n) :
    runP (untilClose symbolAt n) (items (list.map .symbol) ++ .token .parenClose :: rest) =
      (do takeAll points (list.map .symbol); take points .parenClose; pure (list, rest)) := by
  have hl := run_untilClose (points := points) (handler := handler)
    (producer := producer) (policy := policy) symbolAt
    (fun s => takeAll points [.symbol s] >>= fun _ => pure s) (fun s => [.symbol s]) list rest h
    (fun _ _ => rfl) (fun s _ r => by simp [symbolAt, run_parseWith, takeAll, take])
  simp [take, takeAll, flatMap_singleton, mapM_const] at hl
  simp [hl, takeAll, take]

theorem run_datatype (start' : List Tree.Symbol → Program values Unit)
    (start : List Tree.Symbol → Run m ε Unit)
    (hstart : ∀ parameters rest, runP (start' parameters) rest =
      (start parameters >>= fun _ => pure ((), rest)))
    (declaration : Tree.DatatypeDec) (rest : List Received) {n : Nat}
    (h : sizeOf declaration < n) :
    runP (parseWith (datatypeAt n start')) (items declaration.tokens ++ rest) =
      (datatype points handler start declaration >>= fun a => pure (a, rest)) := by
  obtain ⟨parameters, list⟩ := declaration
  simp only [Tree.DatatypeDec.mk.sizeOf_spec] at h
  cases parameters with
  | nil =>
    cases list with
    | nil =>
      simp [Tree.DatatypeDec.tokens, paren, datatypeAt, datatype_empty, run_parseWith, run_next,
        run_bind, hstart, takeAll, take]
    | cons first others =>
      simp only [List.cons.sizeOf_spec] at h
      have ho := run_constructorAfterOpen (points := points) (handler := handler)
        (producer := producer) (policy := policy) first
        (items (others.flatMap Tree.ConstructorDec.tokens) ++ .token .parenClose :: rest)
        (n := n) (by omega)
      have hl := run_constructors (points := points) (handler := handler)
        (producer := producer) (policy := policy) others
        rest (n := n) (by omega)
      obtain ⟨symbol, selectors⟩ := first
      simp [take] at ho hl
      simp [Tree.DatatypeDec.tokens, Tree.ConstructorDec.tokens, paren, datatypeAt,
        datatype_plain, run_parseWith, run_next, run_bind, hstart, ho, hl, takeAll, take]
  | cons parameter parameters =>
    have hs := run_symbols (points := points) (handler := handler)
      (producer := producer) (policy := policy) (parameter :: parameters)
      (.token .parenOpen :: (items (list.flatMap Tree.ConstructorDec.tokens) ++
        .token .parenClose :: .token .parenClose :: rest)) (n := n)
      (by have := length_le_sizeOf (parameter :: parameters); omega)
    have hl := run_constructors (points := points) (handler := handler)
      (producer := producer) (policy := policy) list
      (.token .parenClose :: rest) (n := n) (by omega)
    simp [take, takeAll] at hs hl
    simp +decide [Tree.DatatypeDec.tokens, paren, word, datatypeAt, datatype_par, expectOpen,
      expectClose, run_parseWith, run_next, run_bind, hstart, hs, hl, takeAll, take]

theorem run_sorts (list : List Tree.«Sort») (rest : List Received) {n : Nat}
    (h : sizeOf list < n) :
    runP (untilClose (sortAt n) n)
        (items (Tree.«Sort».tokensAll list) ++ .token .parenClose :: rest) =
      (do let handled ← sorts points handler list; take points .parenClose
          pure (handled, rest)) := by
  rw [Grammar.OneToOne.tokensAll_eq_flatMap, sorts_eq]
  exact run_untilClose _ _ _ list rest (by have := length_le_sizeOf list; omega)
    (fun b _ => Grammar.OneToOne.startsClose_sort b _)
    (fun b hb r => run_sort n b r (by have := sizeOf_lt_of_mem hb; omega))

theorem run_sortDecs (list : List Tree.SortDec) (rest : List Received) {n : Nat}
    (h : list.length < n) :
    runP (untilClose sortDecAt n)
        (items (list.flatMap Tree.SortDec.tokens) ++ .token .parenClose :: rest) =
      (do takeAll points (list.flatMap Tree.SortDec.tokens); take points .parenClose
          pure (list.map fun s => (s.symbol, s.arity), rest)) := by
  have hl := run_untilClose (points := points) (handler := handler)
    (producer := producer) (policy := policy) sortDecAt
    (fun s => takeAll points s.tokens >>= fun _ => pure (s.symbol, s.arity))
    Tree.SortDec.tokens list rest h (fun _ _ => rfl)
    (fun s _ r => by
      obtain ⟨symbol, arity⟩ := s
      simp [Tree.SortDec.tokens, paren, sortDecAt, expectSymbol, expectClose, run_parseWith,
        run_next, run_bind, takeAll, take])
  simp [take] at hl
  simp [hl, takeAll_flatMap, mapM_effects, take]

/-- A run over a list for its effects alone, as one that collects its results. -/
theorem forM_eq_mapM {β : Type} (f : β → Run m ε Unit) (list : List β) :
    forM list f = (fun _ => ()) <$> list.mapM f := by
  induction list with
  | nil => simp
  | cons b list ih => simp [ih]

/-- The results of a run over a list are as many as its elements. -/
theorem mapM_length_bind {β γ δ : Type} (f : β → Run m ε γ) (list : List β)
    (g : List γ → Nat → Run m ε δ) :
    (list.mapM f >>= fun results => g results results.length) =
      (list.mapM f >>= fun results => g results list.length) := by
  induction list generalizing g with
  | nil => simp
  | cons b list ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind, List.length_cons]
    congr 1
    funext x
    exact ih fun results k => g (x :: results) (k + 1)

theorem run_signatureAfter (symbol : Tree.Symbol) (parameters : List Tree.SortedVar)
    (result : Tree.«Sort») (rest : List Received) {n : Nat}
    (h : sizeOf parameters + sizeOf result < n) :
    runP (signatureAfter n symbol)
        (items (paren (parameters.flatMap Tree.SortedVar.tokens) ++ result.tokens) ++ rest) =
      (do take points .parenOpen
          let handledParameters ← sortedVars points handler parameters
          take points .parenClose
          let handledResult ← sort points handler result
          pure (⟨symbol, handledParameters, handledResult⟩, rest)) := by
  have hs := run_sort (points := points) (handler := handler)
    (producer := producer) (policy := policy) n result rest (by omega)
  have hl := run_sortedVars (points := points) (handler := handler)
    (producer := producer) (policy := policy) parameters
    (items result.tokens ++ rest) (n := n) (by omega)
  simp [take] at hs hl
  simp [paren, signatureAfter, expectOpen, run_next, run_bind, hs, hl, take]

theorem run_functionDecs (list : List Tree.FunctionDec) (rest : List Received) {n : Nat}
    (h : sizeOf list < n) :
    runP (untilClose (functionDecAt n) n)
        (items (list.flatMap Tree.FunctionDec.tokens) ++ .token .parenClose :: rest) =
      (do
        let handled ← list.mapM fun declaration => do
          take points .parenOpen
          let handled ← signature points handler declaration.symbol declaration.parameters
            declaration.result
          take points .parenClose
          pure handled
        take points .parenClose
        pure (handled, rest)) := by
  refine run_untilClose _ _ _ list rest (by have := length_le_sizeOf list; omega)
    (fun d _ => by simp [Tree.FunctionDec.tokens, paren, Grammar.Read.startsClose])
    (fun d hd r => ?_)
  have hd' := sizeOf_lt_of_mem hd
  obtain ⟨symbol, parameters, result⟩ := d
  simp only [Tree.FunctionDec.mk.sizeOf_spec] at hd'
  have hs := run_signatureAfter (points := points) (handler := handler)
    (producer := producer) (policy := policy) symbol parameters result
    (.token .parenClose :: r) (n := n) (by omega)
  simp [paren, take] at hs
  simp [Tree.FunctionDec.tokens, paren, functionDecAt, expectSymbol, expectClose, signature,
    run_parseWith, run_next, run_bind, hs, takeAll, take]

theorem run_recursiveBodies : ∀ (signatures : List (Signature values)) (bodies : List Tree.Term)
    (rest : List Received) {n : Nat}, signatures.length = bodies.length → sizeOf bodies < n →
    runP (Parse.recursiveBodies n signatures) (items (Tree.Term.tokensAll bodies) ++ rest) =
      (Traversal.recursiveBodies points handler (signatures.zip bodies) >>=
        fun _ => pure ((), rest))
  | [], [], rest, _, _, _ => by
    simp [Parse.recursiveBodies, Traversal.recursiveBodies, Tree.Term.tokensAll]
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | signature :: signatures, body :: bodies, rest, n, hl, h => by
    simp only [List.cons.sizeOf_spec] at h
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hb := run_termArriving (points := points) (handler := handler)
      (producer := producer) (policy := policy) n (some (.startRecursiveBody signature)) body
      (items (Tree.Term.tokensAll bodies) ++ rest) (by omega)
    have ih := run_recursiveBodies signatures bodies rest (n := n) hl (by omega)
    have hp : (Parse.recursiveBodies n (signature :: signatures) : Program values Unit) =
        (Program.receive (some (.startRecursiveBody signature)) (termAt n) >>= fun handled =>
          emitUnit (.endRecursiveBody handled) >>= fun _ => Parse.recursiveBodies n signatures) :=
              rfl
    have hi : items (Tree.Term.tokensAll (body :: bodies)) ++ rest =
        items body.tokens ++ (items (Tree.Term.tokensAll bodies) ++ rest) := by
      simp [Tree.Term.tokensAll]
    have hb' : runP (Program.receive (some (Call.startRecursiveBody signature)) (termAt n))
        (items body.tokens ++ (items (Tree.Term.tokensAll bodies) ++ rest)) =
        (term points handler body (callUnit handler (.startRecursiveBody signature)) >>= fun a =>
          pure (a, items (Tree.Term.tokensAll bodies) ++ rest)) := hb
    rw [hp, run_bind, hi, hb', List.zip_cons_cons, recursiveBodies_cons]
    simp [run_bind, run_emitUnit, ih]

theorem literals_tokens (literals : List Tree.PropLiteral) :
    literals.flatMap Tree.PropLiteral.tokens =
      Tree.Term.tokensAll (literals.map Tree.PropLiteral.asTerm) := by
  induction literals with
  | nil => rfl
  | cons literal literals ih =>
    cases literal <;> simp [Tree.PropLiteral.tokens, Tree.PropLiteral.asTerm, Tree.Term.tokensAll,
      Tree.Term.tokens, Tree.QualIdentifier.tokens, Tree.Identifier.tokens, ih, paren]

theorem sizeOf_asTerms (literals : List Tree.PropLiteral) :
    sizeOf (literals.map Tree.PropLiteral.asTerm) ≤ 10 * sizeOf literals := by
  induction literals with
  | nil => simp
  | cons literal literals ih =>
    cases literal <;> simp [Tree.PropLiteral.asTerm] at ih ⊢ <;> omega

theorem parseWith_declarationAt (n : Nat) :
    parseWith (values := values) (declarationAt n) =
      (parseWith (datatypeAt n fun parameters => emitUnit (.startDatatypeDeclaration parameters))
        >>= fun handled => emitUnit (.endDatatypeDeclaration handled)) := by
  rw [parseWith, parseWith, bind_bind]
  rfl

theorem run_declarations (list : List Tree.DatatypeDec) (rest : List Received) {n : Nat}
    (h : sizeOf list < n) :
    runP (untilClose (declarationAt n) n)
        (items (list.flatMap Tree.DatatypeDec.tokens) ++ .token .parenClose :: rest) =
      (do
        let handled ← list.mapM fun declaration => do
          let handled ← datatype points handler
            (fun parameters => callUnit handler (.startDatatypeDeclaration parameters))
            declaration
          callUnit handler (.endDatatypeDeclaration handled)
        take points .parenClose
        pure (handled, rest)) := by
  refine run_untilClose _ _ _ list rest (by have := length_le_sizeOf list; omega)
    (fun d _ => by
      obtain ⟨parameters, constructors⟩ := d
      cases parameters <;> simp [Tree.DatatypeDec.tokens, paren, Grammar.Read.startsClose])
    (fun d hd r => ?_)
  have hd' := sizeOf_lt_of_mem hd
  rw [parseWith_declarationAt, run_bind,
    run_datatype _ (fun parameters => callUnit handler (.startDatatypeDeclaration parameters))
      (fun parameters r => run_emitUnit _ _ _ _ _ _) d r (n := n) (by omega)]
  simp [run_emitUnit]

/-- The continuation of a run over a list is told only results as many as the elements. -/
theorem mapM_bind_congr {β γ δ : Type} (f : β → Run m ε γ) (list : List β)
    (k k' : List γ → Run m ε δ) (hk : ∀ results,
      results.length = list.length → k results = k' results) :
    (list.mapM f >>= k) = (list.mapM f >>= k') := by
  induction list generalizing k k' with
  | nil => simpa using hk [] rfl
  | cons b list ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    congr 1
    funext x
    exact ih _ _ fun results h => hk (x :: results) (by simp [h])

/-! ## Commands -/

/-- How the reading goes on after the command. -/
def afterOf : Tree.Command → After
  | .exit => .exit
  | command => .continue command.declaredVersion

/-- A command, from its `(` on. -/
def commandFirst (n : Nat) : Program values After := do
  match ← Program.receive none .done with
  | .token .parenOpen => commandAfterOpen n
  | _ => .stuck

set_option hygiene false in
/-- The simp set of the cases of `run_command`. -/
macro "command_simp" "[" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp +decide [commandFirst, commandAfterOpen, commandAfter, bare, expectSymbol,
    expectOpen, expectClose, Tree.Command.tokens, commandTokens, paren, word, opening,
    afterOf, Tree.Command.declaredVersion, parseTerm, run_receive, run_next,
    run_parseWith, run_bind, run_emitUnit, takeAll, take, $extra,*])

set_option maxHeartbeats 4000000 in
theorem run_command (version : Version) (command : Tree.Command)
    (rest : List Received) {n : Nat} (hv : command.Valid version)
    (h : 10 * sizeOf command < n) :
    runP (commandFirst n) (items command.tokens ++ rest) =
      (Traversal.command points handler command >>=
        fun _ => pure (afterOf command, rest)) := by
  cases command with
  | assert t =>
    simp only [Tree.Command.assert.sizeOf_spec] at h
    have ht := run_term (points := points) (handler := handler)
      (producer := producer) (policy := policy) n t (.token .parenClose :: rest)
      (by omega)
    simp at ht
    command_simp [command_assert, ht]
  | checkSatAssuming terms =>
    simp only [Tree.Command.checkSatAssuming.sizeOf_spec] at h
    have hl := run_terms_of (run_term (points := points) (handler := handler)
      (producer := producer) (policy := policy) n) terms
      (.token .parenClose :: rest) (by omega)
    simp [take] at hl
    command_simp [command_checkSatAssuming, hl]
  | checkSatAssumingLiterals literals =>
    simp only [Tree.Command.checkSatAssumingLiterals.sizeOf_spec] at h
    have hl := run_terms_of (run_term (points := points) (handler := handler)
      (producer := producer) (policy := policy) n)
      (literals.map Tree.PropLiteral.asTerm) (.token .parenClose :: rest)
      (by have := sizeOf_asTerms literals; omega)
    simp [take] at hl
    command_simp [command_checkSatAssumingLiterals, literals_tokens, hl]
  | declareConst symbol s =>
    simp only [Tree.Command.declareConst.sizeOf_spec] at h
    have hs := run_sort (points := points) (handler := handler)
      (producer := producer) (policy := policy) n s (.token .parenClose :: rest)
      (by omega)
    simp at hs
    command_simp [command_declareConst, hs]
  | declareDatatype symbol declaration =>
    simp only [Tree.Command.declareDatatype.sizeOf_spec] at h
    have hd := run_datatype (points := points) (handler := handler)
      (producer := producer) (policy := policy)
      (fun parameters => emitUnit (.startDeclareDatatype symbol parameters))
      (fun parameters => callUnit handler (.startDeclareDatatype symbol parameters))
      (fun parameters r => run_emitUnit _ _ _ _ _ _) declaration
      (.token .parenClose :: rest) (n := n) (by omega)
    simp at hd
    command_simp [command_declareDatatype, hd]
  | checkSat => command_simp [command_checkSat]
  | declareSort symbol arity => command_simp [command_declareSort]
  | declareSortParameter symbol => command_simp [command_declareSortParameter]
  | echo content => command_simp [command_echo]
  | exit => command_simp [command_exit]
  | getAssertions => command_simp [command_getAssertions]
  | getAssignment => command_simp [command_getAssignment]
  | getInfo flag => command_simp [command_getInfo]
  | getModel => command_simp [command_getModel]
  | getOption keyword => command_simp [command_getOption]
  | getProof => command_simp [command_getProof]
  | getUnsatAssumptions => command_simp [command_getUnsatAssumptions]
  | getUnsatCore => command_simp [command_getUnsatCore]
  | pop count => command_simp [command_pop]
  | push count => command_simp [command_push]
  | reset => command_simp [command_reset]
  | resetAssertions => command_simp [command_resetAssertions]
  | setLogic symbol => command_simp [command_setLogic]
  | declareFun symbol parameters result =>
    simp only [Tree.Command.declareFun.sizeOf_spec] at h
    have hs := run_sort (points := points) (handler := handler)
      (producer := producer) (policy := policy) n result
      (.token .parenClose :: rest) (by omega)
    have hl := run_sorts (points := points) (handler := handler)
      (producer := producer) (policy := policy) parameters
      (items result.tokens ++ .token .parenClose :: rest) (n := n) (by omega)
    simp [take] at hs hl
    command_simp [command_declareFun, hs, hl]
  | defineConst symbol s body =>
    simp only [Tree.Command.defineConst.sizeOf_spec] at h
    have hb := run_term (points := points) (handler := handler)
      (producer := producer) (policy := policy) n body
      (.token .parenClose :: rest) (by omega)
    have hs := run_sort (points := points) (handler := handler)
      (producer := producer) (policy := policy) n s
      (items body.tokens ++ .token .parenClose :: rest) (by omega)
    simp at hs hb
    command_simp [command_defineConst, hs, hb]
  | defineFun definition =>
    obtain ⟨symbol, parameters, result, body⟩ := definition
    simp only [Tree.Command.defineFun.sizeOf_spec, Tree.FunctionDef.mk.sizeOf_spec] at h
    have hb := run_term (points := points) (handler := handler)
      (producer := producer) (policy := policy) n body
      (.token .parenClose :: rest) (by omega)
    have hs := run_signatureAfter (points := points) (handler := handler)
      (producer := producer) (policy := policy) symbol parameters result
      (items body.tokens ++ .token .parenClose :: rest) (n := n) (by omega)
    simp [paren, take] at hs hb
    command_simp [command_defineFun, Tree.FunctionDef.tokens, signature, hs, hb]
  | defineFunRec definition =>
    obtain ⟨symbol, parameters, result, body⟩ := definition
    simp only [Tree.Command.defineFunRec.sizeOf_spec, Tree.FunctionDef.mk.sizeOf_spec] at h
    have hb := run_term (points := points) (handler := handler)
      (producer := producer) (policy := policy) n body
      (.token .parenClose :: rest) (by omega)
    have hs := run_signatureAfter (points := points) (handler := handler)
      (producer := producer) (policy := policy) symbol parameters result
      (items body.tokens ++ .token .parenClose :: rest) (n := n) (by omega)
    simp [paren, take] at hs hb
    command_simp [command_defineFunRec, Tree.FunctionDef.tokens, signature, hs, hb]
  | defineSort symbol parameters s =>
    simp only [Tree.Command.defineSort.sizeOf_spec] at h
    have hs := run_sort (points := points) (handler := handler)
      (producer := producer) (policy := policy) n s
      (.token .parenClose :: rest) (by omega)
    have hl := run_symbols (points := points) (handler := handler)
      (producer := producer) (policy := policy) parameters
      (items s.tokens ++ .token .parenClose :: rest) (n := n)
      (by have := length_le_sizeOf parameters; omega)
    simp [take, takeAll] at hs hl
    command_simp [command_defineSort, hs, hl]
  | getValue terms =>
    simp only [Tree.Command.getValue.sizeOf_spec] at h
    have hl := run_terms_of (run_term (points := points) (handler := handler)
      (producer := producer) (policy := policy) n) terms
      (.token .parenClose :: rest) (by omega)
    simp [take] at hl
    command_simp [command_getValue, hl]
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    simp only [Tree.Command.setInfo.sizeOf_spec, Tree.Attribute.mk.sizeOf_spec] at h
    cases value with
    | none =>
      command_simp [command_setInfo, Tree.Attribute.tokens, attributeThen_none, declaredBy,
        run_attributeAfter_none keyword .parenClose (.inl rfl)]
    | some value =>
      simp only [Option.some.sizeOf_spec] at h
      have ha := run_attributeAfter_some (points := points) (handler := handler)
        (producer := producer) (policy := policy) keyword value .parenClose rest
        (n := n) (by omega)
      cases value with
      | constant constant =>
        cases constant <;>
          command_simp [command_setInfo, Tree.Attribute.tokens, attributeThen_some, declaredBy,
            attributeValue, ha]
      | _ =>
        command_simp [command_setInfo, Tree.Attribute.tokens, attributeThen_some, declaredBy,
          attributeValue, ha]
  | setOption option =>
    obtain ⟨keyword, value⟩ := option
    simp only [Tree.Command.setOption.sizeOf_spec, Tree.Attribute.mk.sizeOf_spec] at h
    cases value with
    | none =>
      command_simp [command_setOption, Tree.Attribute.tokens, attributeThen_none,
        run_attributeAfter_none keyword .parenClose (.inl rfl)]
    | some value =>
      simp only [Option.some.sizeOf_spec] at h
      have ha := run_attributeAfter_some (points := points) (handler := handler)
        (producer := producer) (policy := policy) keyword value .parenClose rest
        (n := n) (by omega)
      command_simp [command_setOption, Tree.Attribute.tokens, attributeThen_some, ha]
  | declareDatatypes sorts datatypes =>
    simp only [Tree.Command.declareDatatypes.sizeOf_spec] at h
    have hd := run_declarations (points := points) (handler := handler)
      (producer := producer) (policy := policy) datatypes
      (.token .parenClose :: rest) (n := n) (by omega)
    have hs := run_sortDecs (points := points) (handler := handler)
      (producer := producer) (policy := policy) sorts
      (.token .parenOpen :: (items (datatypes.flatMap Tree.DatatypeDec.tokens) ++
        .token .parenClose :: .token .parenClose :: rest)) (n := n)
      (by have := length_le_sizeOf sorts; omega)
    simp [take, takeAll] at hd hs
    command_simp [command_declareDatatypes, forM_eq_mapM, hd, hs]
  | defineFunsRec declarations bodies =>
    obtain ⟨-, -, hlen, -⟩ := hv
    simp only [Tree.Command.defineFunsRec.sizeOf_spec] at h
    have hd := run_functionDecs (points := points) (handler := handler)
      (producer := producer) (policy := policy) declarations
      (.token .parenOpen :: (items (Tree.Term.tokensAll bodies) ++
        .token .parenClose :: .token .parenClose :: rest)) (n := n) (by omega)
    have hb := fun signatures (hs : signatures.length = bodies.length) =>
      run_recursiveBodies (points := points) (handler := handler)
        (producer := producer) (policy := policy) signatures bodies
        (.token .parenClose :: .token .parenClose :: rest) (n := n) hs (by omega)
    simp [take] at hd
    command_simp [command_defineFunsRec, hd]
    congr 1; funext; congr 1; funext; congr 1; funext
    apply mapM_bind_congr
    intro results hr
    rw [hb results (by rw [hr, hlen])]
    simp [run_next]

/-! ## Scripts -/

theorem command_tokens_open (command : Tree.Command) :
    ∃ inner, command.tokens = .parenOpen :: inner := by
  cases command <;> exact ⟨_, rfl⟩

/-- What a parser receives for commands that do not start with `exit`. -/
theorem received_cons {command : Tree.Command} (h : command ≠ .exit)
    (commands : List Tree.Command) :
    received (command :: commands) = items command.tokens ++ received commands := by
  cases command <;> first | exact absurd rfl h | rfl

theorem modeAfter_unparsed {version : Version} {command : Tree.Command}
    (h : command.modeAfter version = some .unparsed) : command = .exit := by
  cases command with
  | exit => rfl
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    simp only [Tree.Command.modeAfter] at h
    split at h
    · split at h
      · rename_i decimal
        cases hv : versionOfNumber decimal <;> simp [hv] at h
      · simp at h
    · simp at h
  | _ => simp [Tree.Command.modeAfter] at h

/-- A command after which a script goes on, or stops, is no declaration of a version that is not
supported. -/
theorem namesNoVersion_eq_false {version : Version} {command : Tree.Command} {mode : Mode}
    (h : command.modeAfter version = some mode) : command.namesNoVersion = false := by
  cases command with
  | setInfo info =>
    obtain ⟨keyword, value⟩ := info
    simp only [Tree.Command.modeAfter] at h
    simp only [Tree.Command.namesNoVersion]
    by_cases hk : keyword = chars "smt-lib-version"
    · simp only [hk, ite_true] at h
      simp only [hk]
      rcases value with _ | ((_ | decimal | _ | _ | _) | _ | _) <;> simp_all
      cases hv : versionOfNumber decimal <;> simp_all
    · simp [hk]
  | _ => rfl

theorem run_commandsStep (rec : Nat → Program values Unit) (n : Nat) (declarations : Nat)
    (command : Tree.Command) (rest : List Received) :
    runP (commandsStep rec n declarations) (items command.tokens ++ rest) =
      runP (do
        match ← commandFirst n with
        | .exit => .discard endAfterExit
        | .continue none => rec declarations
        | .continue (some version) =>
          .switch declarations version (rec (declarations + 1)))
        (items command.tokens ++ rest) := by
  obtain ⟨inner, hc⟩ := command_tokens_open command
  rw [hc]
  simp [commandsStep, commandFirst, run_receive, run_bind]
  rfl

theorem run_commands : ∀ (commands : List Tree.Command) (version : Version)
    (declarations : Nat) (rest : List Received) {n : Nat}, Script version commands →
    10 * sizeOf commands < n →
    runP (commandsFrom n declarations) (received commands ++ rest) =
      (Traversal.commands points handler producer policy declarations commands >>= fun _ =>
          pure ((), rest))
  | [], _, declarations, rest, n + 1, _, _ => by
    simp [commandsFrom, commandsStep, received, Traversal.commands, run_receive, run]
  | command :: commands, version, declarations, rest, n + 1, hs, h => by
    simp only [List.cons.sizeOf_spec] at h
    cases hs with
    | stop hv hm =>
      obtain rfl := modeAfter_unparsed hm
      have hc := run_command (points := points) (handler := handler)
        (producer := producer) (policy := policy) version .exit (.endOfInput :: rest)
        (n := n) hv (by omega)
      simp only [commandsFrom, received]
      rw [List.append_assoc, List.singleton_append, run_commandsStep, run_bind, hc]
      simp [afterOf, Traversal.commands, run, endAfterExit]
    | command hv hm hrest =>
      rename_i next
      have hne : command ≠ .exit := by
        rintro rfl
        simp [Tree.Command.modeAfter] at hm
      have hc := run_command (points := points) (handler := handler)
        (producer := producer) (policy := policy) version command
        (received commands ++ rest) (n := n) hv (by omega)
      have ih := fun declarations => run_commands commands next declarations rest
        (n := n) hrest (by omega)
      rw [received_cons hne, List.append_assoc]
      simp only [commandsFrom]
      rw [run_commandsStep, run_bind, hc]
      have ha : afterOf command = .continue command.declaredVersion := by
        cases command <;> first | exact absurd rfl hne | rfl
      cases hd : command.declaredVersion with
      | none =>
        simp [ha, hd, ih, Traversal.commands, namesNoVersion_eq_false hm]
      | some v =>
        simp [ha, hd, ih, Traversal.commands, run]

/-- The script's traversal is `parseScript` run on what a parser receives for it. -/
theorem run_script (version : Version) (commands : List Tree.Command) (rest : List Received)
    {n : Nat} (h : Script version commands) (hn : 10 * sizeOf commands < n) :
    runP (parseScript n version) (received commands ++ rest) =
      (script points handler producer policy version commands >>= fun _ => pure ((), rest)) := by
  simp only [parseScript, Program.run, run_commands commands version 0 rest h hn,
    Traversal.script, bind_assoc]

end

end BSmtLibSpec.Facts.Proofs.Parser.Simulation
