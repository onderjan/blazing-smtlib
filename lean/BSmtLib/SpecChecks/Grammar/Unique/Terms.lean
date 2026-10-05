import BSmtLib.SpecChecks.Grammar.Unique.Parts

/-!
# Terms

Every acceptance of a term is an item, and the rules leave at most one tree for a sequence of
tokens of a term. Both go by induction on the number of tokens, since the parts of a term,
bindings and match cases are shorter than it.

The alternatives of ⟨term⟩ are told apart by their first two tokens (`termForm`): a single
token is a constant or a symbol, and a group starts with a reserved word that names its
alternative, with `_` or `as` for a qualified identifier, or else with the symbol or the `(`
of the function of an application. Within one alternative, the parts split in one way
because each is an item, or a run of attributes.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Grammar

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar

variable {version : Version}

/-! ## The alternative of a term -/

/-- The alternative of ⟨term⟩ that a sequence of tokens can be, by its first two tokens. -/
def termForm : List SyntaxToken → Nat
  | [.symbol _] => 1
  | [_] => 0
  | .parenOpen :: .reserved w :: _ =>
    if w = chars "_" ∨ w = chars "as" then 1
    else if w = chars "let" then 3
    else if w = chars "lambda" then 4
    else if w = chars "forall" then 5
    else if w = chars "exists" then 6
    else if w = chars "match" then 7
    else if w = chars "!" then 8
    else 9
  | .parenOpen :: _ => 2
  | _ => 9

/-- The alternative of ⟨term⟩ that a tree is, numbered as `termForm` numbers them. -/
def termTreeForm : Tree.Term → Nat
  | .constant _ => 0
  | .identifier _ => 1
  | .application _ _ => 2
  | .«let» _ _ => 3
  | .lambda _ _ => 4
  | .quantified .«forall» _ _ => 5
  | .quantified .«exists» _ _ => 6
  | .«match» _ _ => 7
  | .annotated _ _ => 8

/-- The first two tokens of a term tell which alternative its tree is. -/
theorem Term.form {tokens : List SyntaxToken} {t : Tree.Term} (h : Term version tokens t) :
    termForm tokens = termTreeForm t := by
  cases h with
  | constant hc => cases hc <;> rfl
  | identifier hq =>
    rcases QualIdentifier.head hq with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp [termForm, termTreeForm, word, chars]
  | application hq =>
    rcases QualIdentifier.first hq with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;>
      simp [termForm, termTreeForm, paren]
  | _ => simp [termForm, termTreeForm, paren, word, chars] <;> decide

/-! ## Terms are items -/

theorem items_lt : ∀ n (tokens : List SyntaxToken), tokens.length < n →
    (∀ t, Term version tokens t → Item tokens) ∧
      (∀ b, Bindings version tokens b → Balanced tokens) ∧
      (∀ c, Cases version tokens c → Balanced tokens)
  | 0, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, _, hn => by
    have ih := items_lt n
    refine ⟨fun t h => ?_, fun b h => ?_, fun c h => ?_⟩
    · cases h with
      | constant hc => exact SpecConstant.item hc
      | identifier hq => exact QualIdentifier.item hq
      | application hq he =>
        simp only [length_paren, List.length_append] at hn
        exact .group ((QualIdentifier.item hq).balanced.append
          (Each.balanced (fun t x ht hx => (ih t (by omega)).1 x hx) he (Nat.le_refl _)))
      | «let» hb _ hbody =>
        simp only [length_paren, List.length_append, List.length_cons] at hn
        exact .group (.atom ⟨nofun, nofun⟩
          ((Item.paren ((ih _ (by omega)).2.1 _ hb)).balanced.append
            ((ih _ (by omega)).1 _ hbody).balanced))
      | lambda _ hv _ hbody =>
        simp only [length_paren, List.length_append, List.length_cons] at hn
        exact .group (.atom ⟨nofun, nofun⟩
          ((Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hv)).balanced.append
            ((ih _ (by omega)).1 _ hbody).balanced))
      | «forall» hv _ hbody =>
        simp only [length_paren, List.length_append, List.length_cons] at hn
        exact .group (.atom ⟨nofun, nofun⟩
          ((Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hv)).balanced.append
            ((ih _ (by omega)).1 _ hbody).balanced))
      | «exists» hv _ hbody =>
        simp only [length_paren, List.length_append, List.length_cons] at hn
        exact .group (.atom ⟨nofun, nofun⟩
          ((Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hv)).balanced.append
            ((ih _ (by omega)).1 _ hbody).balanced))
      | «match» _ hs hc =>
        simp only [length_paren, List.length_append, List.length_cons] at hn
        exact .group (.atom ⟨nofun, nofun⟩
          (((ih _ (by omega)).1 _ hs).balanced.append
            (Item.paren ((ih _ (by omega)).2.2 _ hc)).balanced))
      | annotated ht ha =>
        simp only [length_paren, List.length_append, List.length_cons] at hn
        exact .group (.atom ⟨nofun, nofun⟩
          (((ih _ (by omega)).1 _ ht).balanced.append (Attributes.balanced ha)))
    · cases h with
      | nil => exact .nil
      | cons ht hb =>
        simp only [length_paren, List.length_append, List.length_cons] at hn
        exact .group (.atom ⟨nofun, nofun⟩ ((ih _ (by omega)).1 _ ht).balanced)
          ((ih _ (by omega)).2.1 _ hb)
    · cases h with
      | nil => exact .nil
      | cons hp ht hc =>
        simp only [length_paren, List.length_append] at hn
        exact .group ((Pattern.item hp).balanced.append ((ih _ (by omega)).1 _ ht).balanced)
          ((ih _ (by omega)).2.2 _ hc)

theorem Term.item {tokens : List SyntaxToken} {t : Tree.Term} (h : Term version tokens t) :
    Item tokens :=
  (items_lt _ _ (Nat.lt_succ_self _)).1 _ h

theorem Bindings.balanced {tokens : List SyntaxToken} {b : List (Chars × Tree.Term)}
    (h : Bindings version tokens b) : Balanced tokens :=
  (items_lt _ _ (Nat.lt_succ_self _)).2.1 _ h

theorem Cases.balanced {tokens : List SyntaxToken} {c : List (Tree.Pattern × Tree.Term)}
    (h : Cases version tokens c) : Balanced tokens :=
  (items_lt _ _ (Nat.lt_succ_self _)).2.2 _ h

/-! ## Terms are unique -/

/-- The rules for terms, bindings and match cases leave at most one tree for the tokens. -/
def TermsAt (version : Version) (tokens : List SyntaxToken) : Prop :=
  (∀ t t', Term version tokens t → Term version tokens t' → t = t') ∧
    (∀ b b', Bindings version tokens b → Bindings version tokens b' → b = b') ∧
    (∀ c c', Cases version tokens c → Cases version tokens c' → c = c')

theorem term_step {n : Nat} (ih : ∀ tokens : List SyntaxToken, tokens.length < n →
      TermsAt version tokens)
    {a b : List SyntaxToken} {t t' : Tree.Term} (h : Term version a t) (h' : Term version b t')
    (hab : a = b) (hn : a.length ≤ n) : t = t' := by
  have hform : termTreeForm t = termTreeForm t' := by
    rw [← Term.form h, ← Term.form h', hab]
  cases h with
  | constant hc =>
    cases h' with
    | constant hc' => rw [SpecConstant.unique hc hc' hab]
    | _ => simp [termTreeForm] at hform
  | identifier hq =>
    cases h' with
    | identifier hq' => rw [QualIdentifier.unique hq hq' hab]
    | _ => simp [termTreeForm] at hform
  | application hq he =>
    cases h' with
    | application hq' he' =>
      simp only [length_paren, List.length_append] at hn
      rw [paren_inj] at hab
      obtain ⟨rfl, rfl⟩ := (QualIdentifier.item hq).prefix_eq (QualIdentifier.item hq') hab
      rw [QualIdentifier.unique hq hq' rfl,
        Each.unique_lt (fun _ _ h => Term.item h) (fun t ht x x' h h' => (ih t ht).1 x x' h h')
          he he' (by omega)]
    | _ => simp [termTreeForm] at hform
  | «let» hb _ hbody =>
    cases h' with
    | «let» hb' _ hbody' =>
      simp only [length_paren, List.length_append, List.length_cons] at hn
      simp only [paren_inj, List.cons_append, List.cons.injEq, true_and] at hab
      obtain ⟨hp, rfl⟩ :=
        (Item.paren (Bindings.balanced hb)).prefix_eq (Item.paren (Bindings.balanced hb')) hab
      rw [paren_inj] at hp
      subst hp
      rw [(ih _ (by omega)).2.1 _ _ hb hb', (ih _ (by omega)).1 _ _ hbody hbody']
    | _ => simp [termTreeForm] at hform
  | lambda _ hv _ hbody =>
    cases h' with
    | lambda _ hv' _ hbody' =>
      simp only [length_paren, List.length_append, List.length_cons] at hn
      simp only [paren_inj, List.cons_append, List.cons.injEq, true_and] at hab
      obtain ⟨hp, rfl⟩ :=
        (Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hv)).prefix_eq
          (Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hv')) hab
      rw [paren_inj] at hp
      subst hp
      rw [SortedVars.unique hv hv', (ih _ (by omega)).1 _ _ hbody hbody']
    | _ => simp [termTreeForm] at hform
  | «forall» hv _ hbody =>
    cases h' with
    | «forall» hv' _ hbody' =>
      simp only [length_paren, List.length_append, List.length_cons] at hn
      simp only [paren_inj, List.cons_append, List.cons.injEq, true_and] at hab
      obtain ⟨hp, rfl⟩ :=
        (Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hv)).prefix_eq
          (Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hv')) hab
      rw [paren_inj] at hp
      subst hp
      rw [SortedVars.unique hv hv', (ih _ (by omega)).1 _ _ hbody hbody']
    | _ => simp [termTreeForm] at hform
  | «exists» hv _ hbody =>
    cases h' with
    | «exists» hv' _ hbody' =>
      simp only [length_paren, List.length_append, List.length_cons] at hn
      simp only [paren_inj, List.cons_append, List.cons.injEq, true_and] at hab
      obtain ⟨hp, rfl⟩ :=
        (Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hv)).prefix_eq
          (Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hv')) hab
      rw [paren_inj] at hp
      subst hp
      rw [SortedVars.unique hv hv', (ih _ (by omega)).1 _ _ hbody hbody']
    | _ => simp [termTreeForm] at hform
  | «match» _ hs hc =>
    cases h' with
    | «match» _ hs' hc' =>
      simp only [length_paren, List.length_append, List.length_cons] at hn
      simp only [paren_inj, List.cons_append, List.cons.injEq, true_and] at hab
      obtain ⟨rfl, hp⟩ := (Term.item hs).prefix_eq (Term.item hs') hab
      rw [paren_inj] at hp
      subst hp
      rw [(ih _ (by omega)).1 _ _ hs hs', (ih _ (by omega)).2.2 _ _ hc hc']
    | _ => simp [termTreeForm] at hform
  | annotated ht ha =>
    cases h' with
    | annotated ht' ha' =>
      simp only [length_paren, List.length_append, List.length_cons] at hn
      simp only [paren_inj, List.cons_append, List.cons.injEq, true_and] at hab
      obtain ⟨rfl, rfl⟩ := (Term.item ht).prefix_eq (Term.item ht') hab
      rw [(ih _ (by omega)).1 _ _ ht ht', Attributes.unique ha ha']
    | _ => simp [termTreeForm] at hform

theorem bindings_step {n : Nat} (ih : ∀ tokens : List SyntaxToken, tokens.length < n →
      TermsAt version tokens)
    {a b : List SyntaxToken} {bs bs' : List (Chars × Tree.Term)} (h : Bindings version a bs)
    (h' : Bindings version b bs') (hab : a = b) (hn : a.length ≤ n) : bs = bs' := by
  cases h with
  | nil =>
    cases h' with
    | nil => rfl
    | cons => simp [paren] at hab
  | cons ht hrest =>
    cases h' with
    | nil => simp [paren] at hab
    | cons ht' hrest' =>
      simp only [length_paren, List.length_append, List.length_cons] at hn
      obtain ⟨hp, rfl⟩ :=
        (Item.paren (.atom (t := .symbol _) ⟨nofun, nofun⟩ (Term.item ht).balanced)).prefix_eq
          (Item.paren (.atom (t := .symbol _) ⟨nofun, nofun⟩ (Term.item ht').balanced)) hab
      simp only [paren_inj, List.cons.injEq, SyntaxToken.symbol.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [(ih _ (by omega)).1 _ _ ht ht', (ih _ (by omega)).2.1 _ _ hrest hrest']

theorem cases_step {n : Nat} (ih : ∀ tokens : List SyntaxToken, tokens.length < n →
      TermsAt version tokens)
    {a b : List SyntaxToken} {cs cs' : List (Tree.Pattern × Tree.Term)}
    (h : Cases version a cs) (h' : Cases version b cs') (hab : a = b) (hn : a.length ≤ n) :
    cs = cs' := by
  cases h with
  | nil =>
    cases h' with
    | nil => rfl
    | cons => simp [paren] at hab
  | cons hp ht hrest =>
    cases h' with
    | nil => simp [paren] at hab
    | cons hp' ht' hrest' =>
      simp only [length_paren, List.length_append] at hn
      obtain ⟨hpt, rfl⟩ :=
        (Item.paren ((Pattern.item hp).balanced.append (Term.item ht).balanced)).prefix_eq
          (Item.paren ((Pattern.item hp').balanced.append (Term.item ht').balanced)) hab
      rw [paren_inj] at hpt
      obtain ⟨rfl, rfl⟩ := (Pattern.item hp).prefix_eq (Pattern.item hp') hpt
      rw [Pattern.unique hp hp' rfl, (ih _ (by omega)).1 _ _ ht ht',
        (ih _ (by omega)).2.2 _ _ hrest hrest']

theorem terms_lt : ∀ n (tokens : List SyntaxToken), tokens.length < n → TermsAt version tokens
  | 0, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, _, hn =>
    ⟨fun _ _ h h' => term_step (terms_lt n) h h' rfl (Nat.le_of_lt_succ hn),
      fun _ _ h h' => bindings_step (terms_lt n) h h' rfl (Nat.le_of_lt_succ hn),
      fun _ _ h h' => cases_step (terms_lt n) h h' rfl (Nat.le_of_lt_succ hn)⟩

theorem Term.unique {a b : List SyntaxToken} {t t' : Tree.Term} (h : Term version a t)
    (h' : Term version b t') (hab : a = b) : t = t' := by
  subst hab
  exact (terms_lt _ _ (Nat.lt_succ_self _)).1 _ _ h h'

theorem Terms.unique {tokens : List SyntaxToken} {ts ts' : List Tree.Term}
    (h : Each (Term version) tokens ts) (h' : Each (Term version) tokens ts') : ts = ts' :=
  Each.unique' (fun _ _ h => Term.item h) (fun _ _ _ h h' => Term.unique h h' rfl) h h'

end BSmtLib.SpecChecks.Grammar
