import BSmtLib.SpecChecks.Grammar.Unique.Terms

/-!
# Commands

The rules leave at most one tree for a sequence of tokens of a command. A command is a group
that starts with its name, a reserved word, so two derivations of one sequence are of commands
of the same name. Two alternatives share a name: `check-sat-assuming` takes terms from 2.7 on
and propositional literals before, and `set-info` takes a version declaration apart from
every other attribute. Within one alternative, the arguments split in one way because each is
an item.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Grammar

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar

variable {version : Version}

/-! ## The parts of commands -/

theorem SortDec.item {tokens : List SyntaxToken} {s : Tree.SortDec} (h : SortDec tokens s) :
    Item tokens := by
  cases h; exact .group (.atom ⟨nofun, nofun⟩ (.atom ⟨nofun, nofun⟩ .nil))

theorem SortDec.unique {a b : List SyntaxToken} {s s' : Tree.SortDec} (h : SortDec a s)
    (h' : SortDec b s') (hab : a = b) : s = s' := by
  cases h; cases h'; tokens_eq hab

theorem SelectorDec.item {tokens : List SyntaxToken} {s : Tree.SelectorDec}
    (h : SelectorDec version tokens s) : Item tokens := by
  cases h with
  | mk hs => exact .group (.atom ⟨nofun, nofun⟩ (Sort.item hs).balanced)

theorem SelectorDec.unique {a b : List SyntaxToken} {s s' : Tree.SelectorDec}
    (h : SelectorDec version a s) (h' : SelectorDec version b s') (hab : a = b) : s = s' := by
  cases h with
  | mk hs =>
    cases h' with
    | mk hs' =>
      simp only [paren_inj, List.cons.injEq, SyntaxToken.symbol.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      rw [Sort.unique hs hs' rfl]

theorem ConstructorDec.item {tokens : List SyntaxToken} {c : Tree.ConstructorDec}
    (h : ConstructorDec version tokens c) : Item tokens := by
  cases h with
  | mk he =>
    exact .group (.atom ⟨nofun, nofun⟩ (Each.balanced' (fun _ _ h => SelectorDec.item h) he))

theorem ConstructorDec.unique {a b : List SyntaxToken} {c c' : Tree.ConstructorDec}
    (h : ConstructorDec version a c) (h' : ConstructorDec version b c') (hab : a = b) :
    c = c' := by
  cases h with
  | mk he =>
    cases h' with
    | mk he' =>
      simp only [paren_inj, List.cons.injEq, SyntaxToken.symbol.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      rw [Each.unique' (fun _ _ h => SelectorDec.item h)
        (fun _ _ _ h h' => SelectorDec.unique h h' rfl) he he']

/-- Constructor declarations in a row start with `(`, unless there are none. -/
theorem ConstructorDecs.first {tokens : List SyntaxToken} {cs : List Tree.ConstructorDec}
    (h : Each (ConstructorDec version) tokens cs) (hne : cs ≠ []) :
    ∃ r, tokens = .parenOpen :: r := by
  cases h with
  | nil => exact absurd rfl hne
  | cons h₁ _ =>
    cases h₁
    exact ⟨_, rfl⟩

theorem DatatypeDec.item {tokens : List SyntaxToken} {d : Tree.DatatypeDec}
    (h : DatatypeDec version tokens d) : Item tokens := by
  cases h with
  | plain he => exact .group (Each.balanced' (fun _ _ h => ConstructorDec.item h) he)
  | parametric hp _ he =>
    exact .group (.atom ⟨nofun, nofun⟩
      ((Item.paren (Each.balanced' (fun _ _ h => Symbol.item h) hp)).balanced.append
        (Item.paren (Each.balanced' (fun _ _ h => ConstructorDec.item h) he)).balanced))

theorem DatatypeDec.unique {a b : List SyntaxToken} {d d' : Tree.DatatypeDec}
    (h : DatatypeDec version a d) (h' : DatatypeDec version b d') (hab : a = b) : d = d' := by
  cases h with
  | plain he hne =>
    cases h' with
    | plain he' =>
      rw [paren_inj] at hab
      subst hab
      rw [Each.unique' (fun _ _ h => ConstructorDec.item h)
        (fun _ _ _ h h' => ConstructorDec.unique h h' rfl) he he']
    | parametric =>
      obtain ⟨r, rfl⟩ := ConstructorDecs.first he hne
      tokens_eq hab
  | parametric hp _ he =>
    cases h' with
    | plain he' hne' =>
      obtain ⟨r, rfl⟩ := ConstructorDecs.first he' hne'
      tokens_eq hab
    | parametric hp' _ he' =>
      simp only [paren_inj, List.cons_append, List.cons.injEq, true_and] at hab
      obtain ⟨hpp, hpe⟩ :=
        (Item.paren (Each.balanced' (fun _ _ h => Symbol.item h) hp)).prefix_eq
          (Item.paren (Each.balanced' (fun _ _ h => Symbol.item h) hp')) hab
      rw [paren_inj] at hpp hpe
      subst hpp hpe
      rw [Each.unique' (fun _ _ h => Symbol.item h) (fun _ _ _ h h' => Symbol.unique h h' rfl)
          hp hp',
        Each.unique' (fun _ _ h => ConstructorDec.item h)
          (fun _ _ _ h h' => ConstructorDec.unique h h' rfl) he he']

theorem FunctionDec.item {tokens : List SyntaxToken} {f : Tree.FunctionDec}
    (h : FunctionDec version tokens f) : Item tokens := by
  cases h with
  | mk hp hr =>
    exact .group (.atom ⟨nofun, nofun⟩
      ((Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hp)).balanced.append
        (Sort.item hr).balanced))

theorem FunctionDec.unique {a b : List SyntaxToken} {f f' : Tree.FunctionDec}
    (h : FunctionDec version a f) (h' : FunctionDec version b f') (hab : a = b) : f = f' := by
  cases h with
  | mk hp hr =>
    cases h' with
    | mk hp' hr' =>
      simp only [paren_inj, List.cons_append, List.cons.injEq, SyntaxToken.symbol.injEq] at hab
      obtain ⟨rfl, hab⟩ := hab
      obtain ⟨hpp, rfl⟩ :=
        (Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hp)).prefix_eq
          (Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hp')) hab
      rw [paren_inj] at hpp
      subst hpp
      rw [SortedVars.unique hp hp', Sort.unique hr hr' rfl]

theorem FunctionDef.unique {a b : List SyntaxToken} {f f' : Tree.FunctionDef}
    (h : FunctionDef version a f) (h' : FunctionDef version b f') (hab : a = b) : f = f' := by
  cases h with
  | mk hp hr hb =>
    cases h' with
    | mk hp' hr' hb' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq,
        SyntaxToken.symbol.injEq] at hab
      obtain ⟨rfl, hrest⟩ := hab
      obtain ⟨hpp, hbody⟩ :=
        (Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hp)).prefix_eq
          (Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hp')) hrest
      rw [paren_inj] at hpp
      subst hpp
      obtain ⟨rfl, rfl⟩ := (Sort.item hr).prefix_eq (Sort.item hr') hbody
      rw [SortedVars.unique hp hp', Sort.unique hr hr' rfl, Term.unique hb hb' rfl]

theorem PropLiteral.item {tokens : List SyntaxToken} {p : Tree.PropLiteral}
    (h : PropLiteral tokens p) : Item tokens := by
  cases h with
  | positive => exact .atom ⟨nofun, nofun⟩
  | negative => exact .group (.atom ⟨nofun, nofun⟩ (.atom ⟨nofun, nofun⟩ .nil))

theorem PropLiteral.unique {a b : List SyntaxToken} {p p' : Tree.PropLiteral}
    (h : PropLiteral a p) (h' : PropLiteral b p') (hab : a = b) : p = p' := by
  cases h <;> cases h' <;> tokens_eq hab

/-! ## Commands -/

/-- Two commands of the same tokens have the same name and the same arguments. -/
theorem commandTokens_inj {n n' : String} {a a' : List SyntaxToken}
    (h : commandTokens n a = commandTokens n' a') : chars n = chars n' ∧ a = a' := by
  simpa [commandTokens, paren_inj, word] using h

/-- An attribute that starts with a keyword has that keyword. -/
theorem Attribute.keyword_eq {n : Chars} {r : List SyntaxToken} {x : Tree.Attribute}
    (h : Attribute version (.keyword n :: r) x) : x.keyword = n := by
  generalize ht : (SyntaxToken.keyword n :: r) = tokens at h
  cases h <;> simp_all

/-- Closes a goal whose equation `h` is between the tokens of commands of different names. -/
macro "names_differ " h:ident : tactic =>
  `(tactic| (obtain ⟨hn, -⟩ := commandTokens_inj $h:ident; exact absurd hn (by decide)))

/-- Closes a goal whose equation `h` is between the tokens of commands of one name, whose
arguments are single tokens. -/
macro "args_eq " h:ident : tactic =>
  `(tactic| (obtain ⟨-, ha⟩ := commandTokens_inj $h:ident; tokens_eq ha))

theorem Command.unique {a b : List SyntaxToken} {c c' : Tree.Command}
    (h : Command version a c) (h' : Command version b c') (hab : a = b) : c = c' := by
  cases h with
  | assert ht =>
    cases h' with
    | assert ht' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      rw [Term.unique ht ht' hab]
    | _ => names_differ hab
  | checkSat =>
    cases h' with
    | checkSat => rfl
    | _ => names_differ hab
  | checkSatAssuming h27 ht =>
    cases h' with
    | checkSatAssuming _ ht' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      rw [paren_inj] at hab
      subst hab
      rw [Terms.unique ht ht']
    | checkSatAssumingLiterals _ h27' => exact absurd h27 h27'
    | _ => names_differ hab
  | checkSatAssumingLiterals _ h27 hl =>
    cases h' with
    | checkSatAssuming h27' => exact absurd h27' h27
    | checkSatAssumingLiterals _ _ hl' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      rw [paren_inj] at hab
      subst hab
      rw [Each.unique' (fun _ _ h => PropLiteral.item h)
        (fun _ _ _ h h' => PropLiteral.unique h h' rfl) hl hl']
    | _ => names_differ hab
  | declareConst _ hs =>
    cases h' with
    | declareConst _ hs' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      simp only [List.cons.injEq, SyntaxToken.symbol.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      rw [Sort.unique hs hs' rfl]
    | _ => names_differ hab
  | declareDatatype _ hd =>
    cases h' with
    | declareDatatype _ hd' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      simp only [List.cons.injEq, SyntaxToken.symbol.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      rw [DatatypeDec.unique hd hd' rfl]
    | _ => names_differ hab
  | declareDatatypes _ hs hd =>
    cases h' with
    | declareDatatypes _ hs' hd' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      obtain ⟨hss, hdd⟩ :=
        (Item.paren (Each.balanced' (fun _ _ h => SortDec.item h) hs)).prefix_eq
          (Item.paren (Each.balanced' (fun _ _ h => SortDec.item h) hs')) hab
      rw [paren_inj] at hss hdd
      subst hss hdd
      rw [Each.unique' (fun _ _ h => SortDec.item h) (fun _ _ _ h h' => SortDec.unique h h' rfl)
          hs hs',
        Each.unique' (fun _ _ h => DatatypeDec.item h)
          (fun _ _ _ h h' => DatatypeDec.unique h h' rfl) hd hd']
    | _ => names_differ hab
  | declareFun hp hr =>
    cases h' with
    | declareFun hp' hr' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      simp only [List.cons_append, List.cons.injEq, SyntaxToken.symbol.injEq] at hab
      obtain ⟨rfl, hrest⟩ := hab
      obtain ⟨hpp, rfl⟩ :=
        (Item.paren (Each.balanced' (fun _ _ h => Sort.item h) hp)).prefix_eq
          (Item.paren (Each.balanced' (fun _ _ h => Sort.item h) hp')) hrest
      rw [paren_inj] at hpp
      subst hpp
      rw [Each.unique' (fun _ _ h => Sort.item h) (fun _ _ _ h h' => Sort.unique h h' rfl)
          hp hp',
        Sort.unique hr hr' rfl]
    | _ => names_differ hab
  | declareSort =>
    cases h' with
    | declareSort => args_eq hab
    | _ => names_differ hab
  | declareSortParameter =>
    cases h' with
    | declareSortParameter => args_eq hab
    | _ => names_differ hab
  | defineConst _ hs ht =>
    cases h' with
    | defineConst _ hs' ht' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      simp only [List.cons_append, List.cons.injEq, SyntaxToken.symbol.injEq] at hab
      obtain ⟨rfl, hrest⟩ := hab
      obtain ⟨rfl, rfl⟩ := (Sort.item hs).prefix_eq (Sort.item hs') hrest
      rw [Sort.unique hs hs' rfl, Term.unique ht ht' rfl]
    | _ => names_differ hab
  | defineFun hf =>
    cases h' with
    | defineFun hf' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      rw [FunctionDef.unique hf hf' hab]
    | _ => names_differ hab
  | defineFunRec _ hf =>
    cases h' with
    | defineFunRec _ hf' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      rw [FunctionDef.unique hf hf' hab]
    | _ => names_differ hab
  | defineFunsRec _ hd hb =>
    cases h' with
    | defineFunsRec _ hd' hb' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      obtain ⟨hdd, hbb⟩ :=
        (Item.paren (Each.balanced' (fun _ _ h => FunctionDec.item h) hd)).prefix_eq
          (Item.paren (Each.balanced' (fun _ _ h => FunctionDec.item h) hd')) hab
      rw [paren_inj] at hdd hbb
      subst hdd hbb
      rw [Each.unique' (fun _ _ h => FunctionDec.item h)
          (fun _ _ _ h h' => FunctionDec.unique h h' rfl) hd hd',
        Terms.unique hb hb']
    | _ => names_differ hab
  | defineSort hp hs =>
    cases h' with
    | defineSort hp' hs' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      simp only [List.cons_append, List.cons.injEq, SyntaxToken.symbol.injEq] at hab
      obtain ⟨rfl, hrest⟩ := hab
      obtain ⟨hpp, rfl⟩ :=
        (Item.paren (Each.balanced' (fun _ _ h => Symbol.item h) hp)).prefix_eq
          (Item.paren (Each.balanced' (fun _ _ h => Symbol.item h) hp')) hrest
      rw [paren_inj] at hpp
      subst hpp
      rw [Each.unique' (fun _ _ h => Symbol.item h) (fun _ _ _ h h' => Symbol.unique h h' rfl)
          hp hp',
        Sort.unique hs hs' rfl]
    | _ => names_differ hab
  | echo =>
    cases h' with
    | echo => args_eq hab
    | _ => names_differ hab
  | exit =>
    cases h' with
    | exit => rfl
    | _ => names_differ hab
  | getAssertions =>
    cases h' with
    | getAssertions => rfl
    | _ => names_differ hab
  | getAssignment =>
    cases h' with
    | getAssignment => rfl
    | _ => names_differ hab
  | getInfo =>
    cases h' with
    | getInfo => args_eq hab
    | _ => names_differ hab
  | getModel =>
    cases h' with
    | getModel => rfl
    | _ => names_differ hab
  | getOption =>
    cases h' with
    | getOption => args_eq hab
    | _ => names_differ hab
  | getProof =>
    cases h' with
    | getProof => rfl
    | _ => names_differ hab
  | getUnsatAssumptions =>
    cases h' with
    | getUnsatAssumptions => rfl
    | _ => names_differ hab
  | getUnsatCore =>
    cases h' with
    | getUnsatCore => rfl
    | _ => names_differ hab
  | getValue ht =>
    cases h' with
    | getValue ht' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      rw [paren_inj] at hab
      subst hab
      rw [Terms.unique ht ht']
    | _ => names_differ hab
  | pop =>
    cases h' with
    | pop => args_eq hab
    | _ => names_differ hab
  | push =>
    cases h' with
    | push => args_eq hab
    | _ => names_differ hab
  | reset =>
    cases h' with
    | reset => rfl
    | _ => names_differ hab
  | resetAssertions =>
    cases h' with
    | resetAssertions => rfl
    | _ => names_differ hab
  | setInfo ha hne =>
    cases h' with
    | setInfo ha' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      rw [Attribute.unique ha ha' hab]
    | declareVersion =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      subst hab
      exact absurd (Attribute.keyword_eq ha) hne
    | _ => names_differ hab
  | declareVersion =>
    cases h' with
    | setInfo ha' hne' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      subst hab
      exact absurd (Attribute.keyword_eq ha') hne'
    | declareVersion => rfl
    | _ => names_differ hab
  | setLogic =>
    cases h' with
    | setLogic => args_eq hab
    | _ => names_differ hab
  | setOption ha =>
    cases h' with
    | setOption ha' =>
      obtain ⟨-, hab⟩ := commandTokens_inj hab
      rw [Attribute.unique ha ha' hab]
    | _ => names_differ hab

end BSmtLib.SpecChecks.Grammar
