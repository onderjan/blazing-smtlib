import BSmtLib.SpecChecks.Grammar.Unique.Balanced

/-!
# The parts of terms

For each syntactic category below terms: every acceptance is an item (`item`), or for an
attribute a keyword followed by at most one item (`balanced`), and the rule leaves at most one
tree for a sequence of tokens (`unique`). Uniqueness is stated for two sequences of tokens and
an equation between them, so that each derivation can be taken apart on its own.

Attributes in a row are not items, but they split in one way all the same: an attribute
starts with its keyword, and an attribute value never starts with a keyword
(`Attributes.unique`).

Where a rule has several alternatives, they differ in their first tokens: a single token
against a group, or a group that starts with a reserved word against one that starts with a
symbol or a group.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Grammar

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar

variable {version : Version}

/-- Closes a goal whose equation `h` between two token lists either fails at a token, or
determines the parts of the trees that are single tokens. -/
macro "tokens_eq " h:ident : tactic =>
  `(tactic| first
    | (simp [paren, word, chars] at $h:ident; done)
    | (simp [paren, word, chars] at $h:ident; simp [$h:ident]; done))

/-! ## Single tokens -/

theorem SpecConstant.item {tokens : List SyntaxToken} {c : Tree.SpecConstant}
    (h : SpecConstant tokens c) : Item tokens := by
  cases h <;> exact .atom ⟨nofun, nofun⟩

theorem SpecConstant.unique {a b : List SyntaxToken} {c c' : Tree.SpecConstant}
    (h : SpecConstant a c) (h' : SpecConstant b c') (hab : a = b) : c = c' := by
  cases h <;> cases h' <;> tokens_eq hab

theorem Symbol.item {tokens : List SyntaxToken} {s : Chars} (h : Symbol tokens s) :
    Item tokens := by
  cases h; exact .atom ⟨nofun, nofun⟩

theorem Symbol.unique {a b : List SyntaxToken} {s s' : Chars}
    (h : Symbol a s) (h' : Symbol b s') (hab : a = b) : s = s' := by
  cases h; cases h'; tokens_eq hab

theorem Index.item {tokens : List SyntaxToken} {i : Tree.Index} (h : Index version tokens i) :
    Item tokens := by
  cases h <;> exact .atom ⟨nofun, nofun⟩

theorem Index.unique {a b : List SyntaxToken} {i i' : Tree.Index}
    (h : Index version a i) (h' : Index version b i') (hab : a = b) : i = i' := by
  cases h <;> cases h' <;> tokens_eq hab

theorem SymbolOrWildcard.item {tokens : List SyntaxToken} {s : Tree.SymbolOrWildcard}
    (h : SymbolOrWildcard version tokens s) : Item tokens := by
  cases h <;> exact .atom ⟨nofun, nofun⟩

theorem SymbolOrWildcard.unique {a b : List SyntaxToken} {s s' : Tree.SymbolOrWildcard}
    (h : SymbolOrWildcard version a s) (h' : SymbolOrWildcard version b s') (hab : a = b) :
    s = s' := by
  cases h <;> cases h' <;> tokens_eq hab

/-! ## Identifiers and sorts -/

/-- An identifier is a symbol, or a group that starts with `_`. -/
theorem Identifier.head {tokens : List SyntaxToken} {i : Tree.Identifier}
    (h : Identifier version tokens i) :
    (∃ n, tokens = [.symbol n]) ∨ ∃ r, tokens = .parenOpen :: word "_" :: r := by
  cases h with
  | symbol => exact .inl ⟨_, rfl⟩
  | indexed => exact .inr ⟨_, rfl⟩

/-- An identifier starts with a symbol or a `(`. -/
theorem Identifier.first {tokens : List SyntaxToken} {i : Tree.Identifier}
    (h : Identifier version tokens i) :
    (∃ n r, tokens = .symbol n :: r) ∨ ∃ r, tokens = .parenOpen :: r := by
  rcases Identifier.head h with ⟨n, rfl⟩ | ⟨r, rfl⟩
  · exact .inl ⟨n, [], rfl⟩
  · exact .inr ⟨_, rfl⟩

theorem Identifier.item {tokens : List SyntaxToken} {i : Tree.Identifier}
    (h : Identifier version tokens i) : Item tokens := by
  cases h with
  | symbol => exact .atom ⟨nofun, nofun⟩
  | indexed hi =>
    exact .group (.atom ⟨nofun, nofun⟩ (.atom ⟨nofun, nofun⟩
      (Each.balanced' (fun _ _ h => Index.item h) hi)))

theorem Identifier.unique {a b : List SyntaxToken} {i i' : Tree.Identifier}
    (h : Identifier version a i) (h' : Identifier version b i') (hab : a = b) : i = i' := by
  cases h with
  | symbol => cases h' <;> tokens_eq hab
  | indexed hi =>
    cases h' with
    | symbol => tokens_eq hab
    | indexed hi' =>
      simp only [paren_inj, List.cons.injEq, SyntaxToken.symbol.injEq, true_and] at hab
      obtain ⟨rfl, rfl⟩ := hab
      rw [Each.unique' (fun _ _ h => Index.item h) (fun _ _ _ h h' => Index.unique h h' rfl)
        hi hi']

theorem Sort.item_lt : ∀ n (tokens : List SyntaxToken) (s : Tree.Sort), tokens.length < n →
    «Sort» version tokens s → Item tokens
  | 0, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, _, _, hn, h => by
    cases h with
    | identifier hi => exact (Identifier.item hi)
    | application hi he =>
      simp only [length_paren, List.length_append] at hn
      exact .group ((Identifier.item hi).balanced.append
        (Each.balanced (fun t x ht hx => Sort.item_lt n t x (by omega) hx) he (Nat.le_refl _)))

theorem Sort.item {tokens : List SyntaxToken} {s : Tree.Sort} (h : «Sort» version tokens s) :
    Item tokens :=
  Sort.item_lt _ _ _ (Nat.lt_succ_self _) h

theorem Sort.unique_lt : ∀ n (a b : List SyntaxToken) (s s' : Tree.Sort), a.length < n →
    «Sort» version a s → «Sort» version b s' → a = b → s = s'
  | 0, _, _, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, _, _, _, _, hn, h, h', hab => by
    cases h with
    | identifier hi =>
      cases h' with
      | identifier hi' => rw [Identifier.unique hi hi' hab]
      | application hi' =>
        rcases Identifier.head hi with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
          rcases Identifier.first hi' with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> tokens_eq hab
    | application hi he hne =>
      cases h' with
      | identifier hi' =>
        rcases Identifier.head hi' with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
          rcases Identifier.first hi with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> tokens_eq hab
      | application hi' he' =>
        simp only [length_paren, List.length_append] at hn
        rw [paren_inj] at hab
        obtain ⟨rfl, rfl⟩ := (Identifier.item hi).prefix_eq (Identifier.item hi') hab
        rw [Identifier.unique hi hi' rfl,
          Each.unique_lt (fun _ _ h => Sort.item h)
            (fun t ht x x' h h' => Sort.unique_lt n t t x x' (by omega) h h' rfl) he he'
            (by omega)]

theorem Sort.unique {a b : List SyntaxToken} {s s' : Tree.Sort} (h : «Sort» version a s)
    (h' : «Sort» version b s') (hab : a = b) : s = s' :=
  Sort.unique_lt _ _ _ _ _ (Nat.lt_succ_self _) h h' hab

/-! ## S-expressions and attributes -/

theorem SExpr.item_lt : ∀ n (tokens : List SyntaxToken) (s : Tree.SExpr), tokens.length < n →
    SExpr version tokens s → Item tokens
  | 0, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, _, _, hn, h => by
    cases h with
    | constant hc => exact (SpecConstant.item hc)
    | list he =>
      simp only [length_paren] at hn
      exact .group
        (Each.balanced (fun t x ht hx => SExpr.item_lt n t x (by omega) hx) he (Nat.le_refl _))
    | _ => exact .atom ⟨nofun, nofun⟩

theorem SExpr.item {tokens : List SyntaxToken} {s : Tree.SExpr} (h : SExpr version tokens s) :
    Item tokens :=
  SExpr.item_lt _ _ _ (Nat.lt_succ_self _) h

theorem SExpr.unique_lt : ∀ n (a b : List SyntaxToken) (s s' : Tree.SExpr), a.length < n →
    SExpr version a s → SExpr version b s' → a = b → s = s'
  | 0, _, _, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, _, _, _, _, hn, h, h', hab => by
    cases h with
    | list he =>
      cases h' with
      | list he' =>
        simp only [length_paren] at hn
        rw [paren_inj] at hab
        subst hab
        rw [Each.unique_lt (fun _ _ h => SExpr.item h)
          (fun t ht x x' h h' => SExpr.unique_lt n t t x x' (by omega) h h' rfl) he he'
          (by omega)]
      | constant hc' => cases hc' <;> tokens_eq hab
      | _ => tokens_eq hab
    | constant hc =>
      cases h' with
      | constant hc' => rw [SpecConstant.unique hc hc' hab]
      | _ => cases hc <;> tokens_eq hab
    | _ =>
      cases h' with
      | constant hc' => cases hc' <;> tokens_eq hab
      | _ => tokens_eq hab

theorem SExpr.unique {a b : List SyntaxToken} {s s' : Tree.SExpr} (h : SExpr version a s)
    (h' : SExpr version b s') (hab : a = b) : s = s' :=
  SExpr.unique_lt _ _ _ _ _ (Nat.lt_succ_self _) h h' hab

/-- An attribute value does not start with a keyword. -/
theorem AttributeValue.first {tokens : List SyntaxToken} {v : Tree.AttributeValue}
    (h : AttributeValue version tokens v) :
    ∃ x r, tokens = x :: r ∧ ∀ n, x ≠ .keyword n := by
  cases h with
  | constant hc => cases hc <;> exact ⟨_, _, rfl, nofun⟩
  | symbol => exact ⟨_, _, rfl, nofun⟩
  | list => exact ⟨_, _, rfl, nofun⟩

theorem AttributeValue.item {tokens : List SyntaxToken} {v : Tree.AttributeValue}
    (h : AttributeValue version tokens v) : Item tokens := by
  cases h with
  | constant hc => exact (SpecConstant.item hc)
  | symbol => exact .atom ⟨nofun, nofun⟩
  | list he => exact .group (Each.balanced' (fun _ _ h => SExpr.item h) he)

theorem AttributeValue.unique {a b : List SyntaxToken} {v v' : Tree.AttributeValue}
    (h : AttributeValue version a v) (h' : AttributeValue version b v') (hab : a = b) :
    v = v' := by
  cases h with
  | list he =>
    cases h' with
    | list he' =>
      rw [paren_inj] at hab
      subst hab
      rw [Each.unique' (fun _ _ h => SExpr.item h) (fun _ _ _ h h' => SExpr.unique h h' rfl)
        he he']
    | constant hc' => cases hc' <;> tokens_eq hab
    | symbol => tokens_eq hab
  | constant hc =>
    cases h' with
    | constant hc' => rw [SpecConstant.unique hc hc' hab]
    | _ => cases hc <;> tokens_eq hab
  | symbol =>
    cases h' with
    | constant hc' => cases hc' <;> tokens_eq hab
    | _ => tokens_eq hab

/-- An attribute is a keyword, followed by its value if it has one. -/
theorem Attribute.balanced {tokens : List SyntaxToken} {a : Tree.Attribute}
    (h : Attribute version tokens a) : Balanced tokens := by
  cases h with
  | keyword => exact .atom ⟨nofun, nofun⟩ .nil
  | valued hv => exact .atom ⟨nofun, nofun⟩ (AttributeValue.item hv).balanced

theorem Attribute.ne_nil {tokens : List SyntaxToken} {a : Tree.Attribute}
    (h : Attribute version tokens a) : tokens ≠ [] := by
  cases h <;> simp

theorem Attribute.unique {a b : List SyntaxToken} {x x' : Tree.Attribute}
    (h : Attribute version a x) (h' : Attribute version b x') (hab : a = b) : x = x' := by
  cases h with
  | keyword =>
    cases h' with
    | keyword => tokens_eq hab
    | valued hv' =>
      simp only [List.cons.injEq] at hab
      exact absurd hab.2.symm (AttributeValue.item hv').ne_nil
  | valued hv =>
    cases h' with
    | keyword =>
      simp only [List.cons.injEq] at hab
      exact absurd hab.2 (AttributeValue.item hv).ne_nil
    | valued hv' =>
      simp only [List.cons.injEq, SyntaxToken.keyword.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      rw [AttributeValue.unique hv hv' rfl]

/-- Attributes in a row start with a keyword, unless there are none. -/
theorem Attributes.first {tokens : List SyntaxToken} {xs : List Tree.Attribute}
    (h : Each (Attribute version) tokens xs) :
    tokens = [] ∨ ∃ n r, tokens = .keyword n :: r := by
  cases h with
  | nil => exact .inl rfl
  | cons h₁ _ =>
    cases h₁ with
    | keyword => exact .inr ⟨_, _, rfl⟩
    | valued => exact .inr ⟨_, _, rfl⟩

theorem Attributes.balanced {tokens : List SyntaxToken} {xs : List Tree.Attribute}
    (h : Each (Attribute version) tokens xs) : Balanced tokens := by
  induction h with
  | nil => exact .nil
  | cons h₁ _ ih => exact (Attribute.balanced h₁).append ih

/-- Attributes in a row split in one way: an attribute without a value is followed by the
next keyword or by nothing, and a value does not start with a keyword. -/
theorem Attributes.unique {tokens : List SyntaxToken} {xs xs' : List Tree.Attribute}
    (h : Each (Attribute version) tokens xs) (h' : Each (Attribute version) tokens xs') :
    xs = xs' := by
  induction h generalizing xs' with
  | nil =>
    rcases Each.inv h' with ⟨-, rfl⟩ | ⟨_, _, _, _, heq, -, h₁, -⟩
    · rfl
    · exact absurd (List.append_eq_nil_iff.mp heq.symm).1 (Attribute.ne_nil h₁)
  | cons h₁ hrest ih =>
    rcases Each.inv h' with ⟨heq, -⟩ | ⟨_, _, _, _, heq, rfl, h₁', hrest'⟩
    · exact absurd (List.append_eq_nil_iff.mp heq).1 (Attribute.ne_nil h₁)
    · cases h₁ with
      | keyword =>
        cases h₁' with
        | keyword =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq,
            SyntaxToken.keyword.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          rw [ih hrest']
        | valued hv' =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
          obtain ⟨x, r, hx, hxk⟩ := AttributeValue.first hv'
          rcases Attributes.first hrest with hr | ⟨n, r', hr⟩
          · rw [hr, hx] at heq
            simp at heq
          · rw [hr, hx] at heq
            simp only [List.cons_append, List.cons.injEq] at heq
            exact (hxk n heq.2.1.symm).elim
      | valued hv =>
        cases h₁' with
        | keyword =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
          obtain ⟨x, r, hx, hxk⟩ := AttributeValue.first hv
          rcases Attributes.first hrest' with hr | ⟨n, r', hr⟩
          · rw [hr, hx] at heq
            simp at heq
          · rw [hr, hx] at heq
            simp only [List.cons_append, List.cons.injEq] at heq
            exact (hxk n heq.2.1).elim
        | valued hv' =>
          simp only [List.cons_append, List.cons.injEq, SyntaxToken.keyword.injEq] at heq
          obtain ⟨rfl, heq⟩ := heq
          obtain ⟨rfl, rfl⟩ := (AttributeValue.item hv).prefix_eq (AttributeValue.item hv') heq
          rw [AttributeValue.unique hv hv' rfl, ih hrest']

/-! ## Qualified identifiers, sorted variables and patterns -/

/-- A qualified identifier is a symbol, or a group that starts with `_` or `as`. -/
theorem QualIdentifier.head {tokens : List SyntaxToken} {q : Tree.QualIdentifier}
    (h : QualIdentifier version tokens q) :
    (∃ n, tokens = [.symbol n]) ∨ (∃ r, tokens = .parenOpen :: word "_" :: r) ∨
      ∃ r, tokens = .parenOpen :: word "as" :: r := by
  cases h with
  | plain hi =>
    rcases Identifier.head hi with ⟨n, rfl⟩ | ⟨r, rfl⟩
    · exact .inl ⟨n, rfl⟩
    · exact .inr (.inl ⟨r, rfl⟩)
  | as => exact .inr (.inr ⟨_, rfl⟩)

/-- A qualified identifier starts with a symbol or a `(`. -/
theorem QualIdentifier.first {tokens : List SyntaxToken} {q : Tree.QualIdentifier}
    (h : QualIdentifier version tokens q) :
    (∃ n r, tokens = .symbol n :: r) ∨ ∃ r, tokens = .parenOpen :: r := by
  rcases QualIdentifier.head h with ⟨n, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · exact .inl ⟨n, [], rfl⟩
  · exact .inr ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩

theorem QualIdentifier.item {tokens : List SyntaxToken} {q : Tree.QualIdentifier}
    (h : QualIdentifier version tokens q) : Item tokens := by
  cases h with
  | plain hi => exact (Identifier.item hi)
  | as hi hs => exact .group (.atom ⟨nofun, nofun⟩ 
      ((Identifier.item hi).balanced.append (Sort.item hs).balanced))

theorem QualIdentifier.unique {a b : List SyntaxToken} {q q' : Tree.QualIdentifier}
    (h : QualIdentifier version a q) (h' : QualIdentifier version b q') (hab : a = b) :
    q = q' := by
  cases h with
  | plain hi =>
    cases h' with
    | plain hi' => rw [Identifier.unique hi hi' hab]
    | as => rcases Identifier.head hi with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> tokens_eq hab
  | as hi hs =>
    cases h' with
    | plain hi' => rcases Identifier.head hi' with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> tokens_eq hab
    | as hi' hs' =>
      simp only [paren_inj, List.cons_append, List.cons.injEq, true_and] at hab
      obtain ⟨rfl, rfl⟩ := (Identifier.item hi).prefix_eq (Identifier.item hi') hab
      rw [Identifier.unique hi hi' rfl, Sort.unique hs hs' rfl]

theorem SortedVar.item {tokens : List SyntaxToken} {s : Tree.SortedVar}
    (h : SortedVar version tokens s) : Item tokens := by
  cases h with
  | mk hs => exact .group (.atom ⟨nofun, nofun⟩ (Sort.item hs).balanced)

theorem SortedVar.unique {a b : List SyntaxToken} {s s' : Tree.SortedVar}
    (h : SortedVar version a s) (h' : SortedVar version b s') (hab : a = b) : s = s' := by
  cases h with
  | mk hs =>
    cases h' with
    | mk hs' =>
      simp only [paren_inj, List.cons.injEq, SyntaxToken.symbol.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      rw [Sort.unique hs hs' rfl]

theorem SortedVars.unique {tokens : List SyntaxToken} {xs xs' : List Tree.SortedVar}
    (h : Each (SortedVar version) tokens xs) (h' : Each (SortedVar version) tokens xs') :
    xs = xs' :=
  Each.unique' (fun _ _ h => SortedVar.item h) (fun _ _ _ h h' => SortedVar.unique h h' rfl)
    h h'

theorem Pattern.item {tokens : List SyntaxToken} {p : Tree.Pattern}
    (h : Pattern version tokens p) : Item tokens := by
  cases h with
  | single hs => exact SymbolOrWildcard.item hs
  | constructor he =>
    exact .group (.atom ⟨nofun, nofun⟩
      (Each.balanced' (fun _ _ h => SymbolOrWildcard.item h) he))

theorem Pattern.unique {a b : List SyntaxToken} {p p' : Tree.Pattern}
    (h : Pattern version a p) (h' : Pattern version b p') (hab : a = b) : p = p' := by
  cases h with
  | single hs =>
    cases h' with
    | single hs' => rw [SymbolOrWildcard.unique hs hs' hab]
    | constructor => cases hs <;> tokens_eq hab
  | constructor he =>
    cases h' with
    | single hs' => cases hs' <;> tokens_eq hab
    | constructor he' =>
      simp only [paren_inj, List.cons.injEq, SyntaxToken.symbol.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      rw [Each.unique' (fun _ _ h => SymbolOrWildcard.item h)
        (fun _ _ _ h h' => SymbolOrWildcard.unique h h' rfl) he he']

end BSmtLib.SpecChecks.Grammar
