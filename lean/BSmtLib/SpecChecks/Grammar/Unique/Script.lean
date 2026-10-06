import BSmtLib.SpecChecks.Grammar.Unique.Commands
import BSmtLib.SpecChecks.Unique

/-!
# Scripts

Every script has at most one parse. The parse takes one command at a time, and the first
command of the input is determined, with the version it is parsed in:

- The tokens of a command are a group in parentheses, and its characters end with its `)`.
  Two tokenisations, in one version, of characters that one input starts with, each ending
  with a `)`, are one a prefix of the other (`tokenization_prefix`); since a group is an item,
  they are equal (`segment_eq`).
- A command parsed in another version than the one in force is a version declaration, whose
  tokens are a parenthesis, a reserved word, a keyword or a decimal: these have the same
  characters and the same meaning in every version (`Plain`). So the declaration is a
  tokenisation in the other version too, and there it does not parse as a command, since each
  version accepts only a declaration of itself (`declaration_version`).
- Input that is only whitespace contains no token, so the end of a script is determined as
  well.

Not trusted: everything here is proved.
-/

namespace BSmtLib.SpecChecks.Grammar

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar BSmtLib.SpecChecks.Lexicon

/-! ## A command is a group -/

theorem FunctionDef.balanced {version : Version} {tokens : List SyntaxToken}
    {f : Tree.FunctionDef} (h : FunctionDef version tokens f) : Balanced tokens := by
  cases h with
  | mk hp hr hb =>
    exact .atom ⟨nofun, nofun⟩
      (((Item.paren (Each.balanced' (fun _ _ h => SortedVar.item h) hp)).balanced.append
        (Sort.item hr).balanced).append (Term.item hb).balanced)

/-- The tokens of a command are a balanced sequence in parentheses. -/
theorem Command.group {version : Version} {tokens : List SyntaxToken} {c : Tree.Command}
    (h : Command version tokens c) : ∃ inner, tokens = paren inner ∧ Balanced inner := by
  cases h with
  | assert ht => exact ⟨_, rfl, .atom ⟨nofun, nofun⟩ (Term.item ht).balanced⟩
  | checkSatAssuming _ ht =>
    exact ⟨_, rfl, .atom ⟨nofun, nofun⟩
      (Item.paren (Each.balanced' (fun _ _ h => Term.item h) ht)).balanced⟩
  | checkSatAssumingLiterals _ _ hl =>
    exact ⟨_, rfl, .atom ⟨nofun, nofun⟩
      (Item.paren (Each.balanced' (fun _ _ h => PropLiteral.item h) hl)).balanced⟩
  | declareConst _ hs =>
    exact ⟨_, rfl, .atom ⟨nofun, nofun⟩ (.atom ⟨nofun, nofun⟩ (Sort.item hs).balanced)⟩
  | declareDatatype _ hd =>
    exact ⟨_, rfl, .atom ⟨nofun, nofun⟩ (.atom ⟨nofun, nofun⟩ (DatatypeDec.item hd).balanced)⟩
  | declareDatatypes _ hs hd =>
    exact ⟨_, rfl, .atom ⟨nofun, nofun⟩
      ((Item.paren (Each.balanced' (fun _ _ h => SortDec.item h) hs)).balanced.append
        (Item.paren (Each.balanced' (fun _ _ h => DatatypeDec.item h) hd)).balanced)⟩
  | declareFun hp hr =>
    exact ⟨_, rfl, .atom ⟨nofun, nofun⟩ (.atom ⟨nofun, nofun⟩
      ((Item.paren (Each.balanced' (fun _ _ h => Sort.item h) hp)).balanced.append
        (Sort.item hr).balanced))⟩
  | defineConst _ hs ht =>
    exact ⟨_, rfl, .atom ⟨nofun, nofun⟩ (.atom ⟨nofun, nofun⟩
      ((Sort.item hs).balanced.append (Term.item ht).balanced))⟩
  | defineFun hf => exact ⟨_, rfl, .atom ⟨nofun, nofun⟩ (FunctionDef.balanced hf)⟩
  | defineFunRec _ hf => exact ⟨_, rfl, .atom ⟨nofun, nofun⟩ (FunctionDef.balanced hf)⟩
  | defineFunsRec _ hd hb =>
    exact ⟨_, rfl, .atom ⟨nofun, nofun⟩
      ((Item.paren (Each.balanced' (fun _ _ h => FunctionDec.item h) hd)).balanced.append
        (Item.paren (Each.balanced' (fun _ _ h => Term.item h) hb)).balanced)⟩
  | defineSort hp hs =>
    exact ⟨_, rfl, .atom ⟨nofun, nofun⟩ (.atom ⟨nofun, nofun⟩
      ((Item.paren (Each.balanced' (fun _ _ h => Symbol.item h) hp)).balanced.append
        (Sort.item hs).balanced))⟩
  | getValue ht =>
    exact ⟨_, rfl, .atom ⟨nofun, nofun⟩
      (Item.paren (Each.balanced' (fun _ _ h => Term.item h) ht)).balanced⟩
  | setInfo ha => exact ⟨_, rfl, .atom ⟨nofun, nofun⟩ (Attribute.balanced ha)⟩
  | setOption ha => exact ⟨_, rfl, .atom ⟨nofun, nofun⟩ (Attribute.balanced ha)⟩
  | _ =>
    first
      | exact ⟨_, rfl, .atom ⟨nofun, nofun⟩ .nil⟩
      | exact ⟨_, rfl, .atom ⟨nofun, nofun⟩ (.atom ⟨nofun, nofun⟩ .nil)⟩
      | exact ⟨_, rfl, .atom ⟨nofun, nofun⟩ (.atom ⟨nofun, nofun⟩ (.atom ⟨nofun, nofun⟩ .nil))⟩

/-! ## What a token stands for -/

theorem ofToken_parenClose {version : Version} {t : Token}
    (h : SyntaxToken.ofToken version t = .parenClose) : t.category = .parenClose := by
  cases hc : t.category <;> simp [SyntaxToken.ofToken, hc] at h ⊢

theorem ofToken_parenOpen {version : Version} {t : Token}
    (h : SyntaxToken.ofToken version t = .parenOpen) : t.category = .parenOpen := by
  cases hc : t.category <;> simp [SyntaxToken.ofToken, hc] at h ⊢

theorem ofToken_reserved {version : Version} {t : Token} {w : Chars}
    (h : SyntaxToken.ofToken version t = .reserved w) : t.category = .reserved ∧ t.text = w := by
  cases hc : t.category <;> simp [SyntaxToken.ofToken, hc] at h ⊢
  exact h

theorem ofToken_keyword {version : Version} {t : Token} {n : Chars}
    (h : SyntaxToken.ofToken version t = .keyword n) : t.category = .keyword := by
  cases hc : t.category <;> simp [SyntaxToken.ofToken, hc] at h ⊢

theorem ofToken_decimal {version : Version} {t : Token} {d : Chars}
    (h : SyntaxToken.ofToken version t = .decimal d) : t.category = .decimal := by
  cases hc : t.category <;> simp [SyntaxToken.ofToken, hc] at h ⊢

/-- A token of a version declaration: a parenthesis, a keyword, a decimal, or the reserved
word `set-info`. -/
def Plain (t : Token) : Prop :=
  t.category = .parenOpen ∨ t.category = .parenClose ∨ t.category = .keyword ∨
    t.category = .decimal ∨ (t.category = .reserved ∧ t.text = chars "set-info")

/-- A plain token stands for the same in every version. -/
theorem Plain.ofToken {t : Token} (h : Plain t) (version version' : Version) :
    SyntaxToken.ofToken version t = SyntaxToken.ofToken version' t := by
  rcases h with h | h | h | h | ⟨h, -⟩ <;> simp [SyntaxToken.ofToken, Token.content, h]

/-- `set-info` is a reserved word in every version. -/
theorem reserved_setInfo (version : Version) : reserved version (chars "set-info") := by
  rw [reserved, litOneOf_iff]
  cases version <;> simp [basicReservedWords, commandNames, Version.upTo, addedCommandNames]

/-- A plain token is a token of every version. -/
theorem Plain.regex {t : Token} (h : Plain t) {version : Version}
    (ht : categoryRegex version t.category t.text) (version' : Version) :
    categoryRegex version' t.category t.text := by
  rcases h with h | h | h | h | ⟨h, ht'⟩ <;> rw [h] at ht ⊢
  · exact ht
  · exact ht
  · exact ht
  · exact ht
  · rw [ht']
    exact reserved_setInfo version'

/-- Every token of a tokenisation is a token of its category. -/
theorem tokenizationFrom_regex {version : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} (h : TokenizationFrom version offset input tokens) :
    ∀ t ∈ tokens, categoryRegex version t.category t.text := by
  induction h with
  | done => simp
  | token _ hs _ _ ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hs
    · exact ih t ht

/-- A tokenisation into tokens of another version is a tokenisation in that version. -/
theorem tokenizationFrom_transport {version version' : Version} {offset : Nat} {input : Chars}
    {tokens : List Token} (h : TokenizationFrom version offset input tokens)
    (hall : ∀ t ∈ tokens, categoryRegex version' t.category t.text) :
    TokenizationFrom version' offset input tokens := by
  induction h with
  | done hw => exact .done hw
  | token hw _ hd _ ih =>
    exact .token hw (hall _ (List.mem_cons.mpr (Or.inl rfl))) hd
      (ih fun t ht => hall t (List.mem_cons.mpr (Or.inr ht)))

/-! ## The characters of the first command -/

theorem delimited_append {category : Category} {r m : Chars} (h : Delimited category r)
    (hr : r ≠ []) : Delimited category (r ++ m) := by
  rcases h with h | h | h | ⟨c, more, rfl, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd h hr
  · exact Or.inr (Or.inr (Or.inr ⟨c, more ++ m, rfl, hc⟩))

/--
A tokenisation of characters that end with a `)` is the start of every tokenisation of an
input that starts with those characters: each of its tokens is followed by a delimiter or is
a parenthesis, so the input after the characters cannot change it.
-/
theorem tokenization_prefix {version : Version} {offset : Nat} {seg : Chars}
    {tokens : List Token} (h : TokenizationFrom version offset seg tokens) :
    ∀ {last : Token} {m : Chars} {tokens' : List Token}, tokens.getLast? = some last →
      last.offset + last.text.length = offset + seg.length → last.category = .parenClose →
      TokenizationFrom version offset (seg ++ m) tokens' →
      ∃ ts, tokens' = tokens ++ ts ∧ TokenizationFrom version (offset + seg.length) m ts := by
  induction h with
  | done _ => intro _ _ _ hlast; simp at hlast
  | @token w category s rest offset tokens hw hs hd hrest ih =>
    intro last m tokens' hlast hend hcat h'
    have hlen : offset + (w ++ s ++ rest).length = offset + w.length + s.length + rest.length := by
      simp only [List.length_append]
      omega
    cases tokens with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      have hrest0 : rest = [] := by
        simp only [List.length_append] at hend
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hrest0
      simp only at hcat
      simp only [List.append_nil] at h'
      obtain ⟨ts, -, hts, rfl⟩ := tokenizationFrom_head hw hs
        (headOf_delimited hs (by rw [hcat]; exact Or.inr (Or.inl rfl))) h'
      refine ⟨ts, rfl, ?_⟩
      rw [hlen, List.length_nil, Nat.add_zero]
      exact hts
    | cons t ts' =>
      have hne : rest ≠ [] := by
        rcases tokenizationFrom_inv hrest with ⟨h0, -⟩ | ⟨w', cat', s', r', _, hin, -, hs', -⟩
        · simp at h0
        · obtain ⟨c, u, rfl, -⟩ := token_shape hs'
          simp [hin]
      rw [List.append_assoc] at h'
      obtain ⟨ts2, -, hts2, rfl⟩ := tokenizationFrom_head hw hs
        (headOf_delimited hs (delimited_append hd hne)) h'
      obtain ⟨ts, rfl, hts⟩ := ih (by simpa using hlast) (by rw [hend, hlen]) hcat hts2
      refine ⟨ts, rfl, ?_⟩
      rw [hlen]
      exact hts

/-- The syntax tokens of a group end with `)`, so its last lexical token is a `)`. -/
theorem last_parenClose {version : Version} {tokens : List Token} {inner : List SyntaxToken}
    (h : tokens.map (SyntaxToken.ofToken version) = paren inner) :
    ∃ last, tokens.getLast? = some last ∧ last.category = .parenClose := by
  have hl := congrArg List.getLast? h
  rw [List.getLast?_map] at hl
  simp only [paren, List.cons_append, List.getLast?_cons, List.getLast?_append,
    Option.some_or, Option.getD_some] at hl
  cases hlast : tokens.getLast? with
  | none => simp [hlast] at hl
  | some last =>
    rw [hlast] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    exact ⟨last, rfl, ofToken_parenClose hl⟩

/--
In one version, two tokenisations of characters that one input starts with, each the tokens of
a group and each ending with its last token, are the same: one is the start of the other, and
a group is an item.
-/
theorem segment_eq_of_prefix {version : Version} {offset : Nat} {seg m : Chars}
    {tokens tokens' : List Token}
    (h : TokenizationExactly version offset seg tokens)
    (h' : TokenizationExactly version offset (seg ++ m) tokens')
    (hg : ∃ inner, tokens.map (SyntaxToken.ofToken version) = paren inner ∧ Balanced inner)
    (hg' : ∃ inner, tokens'.map (SyntaxToken.ofToken version) = paren inner ∧ Balanced inner) :
    m = [] ∧ tokens = tokens' := by
  obtain ⟨inner, hmap, hbal⟩ := hg
  obtain ⟨inner', hmap', hbal'⟩ := hg'
  obtain ⟨ht, last, hlast, hend⟩ := h
  obtain ⟨ht', last', hlast', hend'⟩ := h'
  obtain ⟨l, hl, hcat⟩ := last_parenClose hmap
  rw [hlast, Option.some.injEq] at hl
  subst hl
  obtain ⟨ts, rfl, -⟩ := tokenization_prefix ht hlast hend hcat ht'
  have hsplit : tokens.map (SyntaxToken.ofToken version) ++ ts.map (SyntaxToken.ofToken version) =
      (tokens ++ ts).map (SyntaxToken.ofToken version) ++ [] := by simp
  rw [hmap, hmap'] at hsplit
  obtain ⟨-, hts⟩ := (Item.paren hbal).prefix_eq (Item.paren hbal') hsplit
  have hts0 : ts = [] := List.map_eq_nil_iff.mp hts
  subst hts0
  rw [List.append_nil, hlast, Option.some.injEq] at hlast'
  subst hlast'
  rw [hend] at hend'
  simp only [List.length_append] at hend'
  exact ⟨List.eq_nil_of_length_eq_zero (by omega), (List.append_nil _).symm⟩

/-- `segment_eq_of_prefix`, for two tokenisations that one input starts with. -/
theorem segment_eq {version : Version} {offset : Nat} {seg seg' rest rest' : Chars}
    {tokens tokens' : List Token}
    (h : TokenizationExactly version offset seg tokens)
    (h' : TokenizationExactly version offset seg' tokens')
    (hg : ∃ inner, tokens.map (SyntaxToken.ofToken version) = paren inner ∧ Balanced inner)
    (hg' : ∃ inner, tokens'.map (SyntaxToken.ofToken version) = paren inner ∧ Balanced inner)
    (heq : seg ++ rest = seg' ++ rest') : seg = seg' ∧ tokens = tokens' := by
  rcases List.append_eq_append_iff.mp heq with ⟨m, rfl, -⟩ | ⟨m, rfl, -⟩
  · obtain ⟨rfl, rfl⟩ := segment_eq_of_prefix h h' hg hg'
    exact ⟨(List.append_nil _).symm, rfl⟩
  · obtain ⟨rfl, rfl⟩ := segment_eq_of_prefix h' h hg' hg
    exact ⟨List.append_nil _, rfl⟩

/-! ## Version declarations -/

/-- The tokens of a version declaration. -/
theorem Command.declaration {version : Version} {tokens : List SyntaxToken} {c : Tree.Command}
    (h : Command version tokens c) (hd : c.DeclaresVersion) :
    tokens = commandTokens "set-info"
      [.keyword (chars "smt-lib-version"), .decimal (versionNumber version)] := by
  obtain ⟨value, hv⟩ := hd
  cases h with
  | setInfo _ hne =>
    cases hv
    exact absurd rfl hne
  | declareVersion => rfl
  | _ => cases hv

/-- Each version accepts only a declaration of itself. -/
theorem declaration_version {version : Version} {d : Chars} {c : Tree.Command}
    (h : Command version
      (commandTokens "set-info" [.keyword (chars "smt-lib-version"), .decimal d]) c) :
    d = versionNumber version := by
  generalize ht : commandTokens "set-info" [.keyword (chars "smt-lib-version"), .decimal d] =
    tokens at h
  cases h with
  | setInfo ha hne =>
    obtain ⟨-, rfl⟩ := commandTokens_inj ht
    exact absurd (Attribute.keyword_eq ha) hne
  | declareVersion =>
    obtain ⟨-, ha⟩ := commandTokens_inj ht
    simp only [List.cons.injEq, SyntaxToken.decimal.injEq, and_true, true_and] at ha
    exact ha
  | _ => names_differ ht

theorem versionNumber_inj {version version' : Version}
    (h : versionNumber version = versionNumber version') : version = version' := by
  cases version <;> cases version' <;> first | rfl | exact absurd h (by decide)

/-- The tokens of a version declaration are plain. -/
theorem declaration_plain {version : Version} {tokens : List Token} {d : Chars}
    (h : tokens.map (SyntaxToken.ofToken version) =
      commandTokens "set-info" [.keyword (chars "smt-lib-version"), .decimal d]) :
    ∀ t ∈ tokens, Plain t := by
  rcases tokens with _ | ⟨t₀, _ | ⟨t₁, _ | ⟨t₂, _ | ⟨t₃, _ | ⟨t₄, _ | ⟨t₅, rest⟩⟩⟩⟩⟩⟩ <;>
    simp only [commandTokens, paren, word, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.cons.injEq, and_true, and_false, reduceCtorEq] at h
  obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := h
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (ofToken_parenOpen h₀)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (ofToken_reserved h₁))))
  · exact Or.inr (Or.inr (Or.inl (ofToken_keyword h₂)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (ofToken_decimal h₃))))
  · exact Or.inr (Or.inl (ofToken_parenClose h₄))

/--
A version declaration, in the version it declares, and a command of another version, both at
the start of one input: the declaration's tokens are a tokenisation in the other version too,
with the same meaning, and there they are a declaration of a version other than its own.
-/
theorem declaration_unique {version version' : Version} {offset : Nat}
    {seg seg' rest rest' : Chars} {tokens tokens' : List Token} {c c' : Tree.Command}
    (h : TokenizationExactly version offset seg tokens)
    (hc : Command version (tokens.map (SyntaxToken.ofToken version)) c) (hd : c.DeclaresVersion)
    (h' : TokenizationExactly version' offset seg' tokens')
    (hc' : Command version' (tokens'.map (SyntaxToken.ofToken version')) c')
    (heq : seg ++ rest = seg' ++ rest') : version = version' := by
  have hdecl := Command.declaration hc hd
  have hplain := declaration_plain hdecl
  have hmap : tokens.map (SyntaxToken.ofToken version') =
      tokens.map (SyntaxToken.ofToken version) :=
    List.map_congr_left fun t ht => (hplain t ht).ofToken version' version
  obtain ⟨ht, hlast⟩ := h
  have ht₂ : TokenizationExactly version' offset seg tokens :=
    ⟨tokenizationFrom_transport ht fun t htm => (hplain t htm).regex
      (tokenizationFrom_regex ht t htm) version', hlast⟩
  obtain ⟨-, rfl⟩ := segment_eq ht₂ h'
    (by rw [hmap]; exact Command.group hc) (Command.group hc') heq
  rw [hmap, hdecl] at hc'
  exact versionNumber_inj (declaration_version hc')

/-! ## The parse of a script -/

/--
The first command of an input is determined, with the version it is parsed in: the version in
force, or the version that the command, a declaration, declares.
-/
theorem first_command {version version₁ version₂ : Version} {offset : Nat}
    {seg₁ seg₂ rest₁ rest₂ : Chars} {tokens₁ tokens₂ : List Token} {c₁ c₂ : Tree.Command}
    (h₁ : TokenizationExactly version₁ offset seg₁ tokens₁)
    (hc₁ : Command version₁ (tokens₁.map (SyntaxToken.ofToken version₁)) c₁)
    (hv₁ : version₁ = version ∨ c₁.DeclaresVersion)
    (h₂ : TokenizationExactly version₂ offset seg₂ tokens₂)
    (hc₂ : Command version₂ (tokens₂.map (SyntaxToken.ofToken version₂)) c₂)
    (hv₂ : version₂ = version ∨ c₂.DeclaresVersion)
    (heq : seg₁ ++ rest₁ = seg₂ ++ rest₂) :
    version₁ = version₂ ∧ seg₁ = seg₂ ∧ c₁ = c₂ := by
  have hver : version₁ = version₂ := by
    rcases hv₁ with e₁ | hd₁
    · rcases hv₂ with e₂ | hd₂
      · exact e₁.trans e₂.symm
      · exact (declaration_unique h₂ hc₂ hd₂ h₁ hc₁ heq.symm).symm
    · exact declaration_unique h₁ hc₁ hd₁ h₂ hc₂ heq
  subst hver
  obtain ⟨rfl, rfl⟩ := segment_eq h₁ h₂ (Command.group hc₁) (Command.group hc₂) heq
  exact ⟨rfl, rfl, Command.unique hc₁ hc₂ rfl⟩

/-- Input that is only whitespace does not start with a command. -/
theorem not_done_and_command {version version' : Version} {offset : Nat} {seg rest : Chars}
    {tokens : List Token} (hdone : TokenizationFrom version offset (seg ++ rest) [])
    (h : TokenizationExactly version' offset seg tokens) : False := by
  obtain ⟨ht, last, hlast, -⟩ := h
  rcases tokenizationFrom_inv hdone with ⟨-, hend⟩ | ⟨_, _, _, _, _, -, -, -, -, -, hnil⟩
  · rcases tokenizationFrom_inv ht with ⟨rfl, -⟩ | ⟨w, cat, s, r, ts, hin, hw, hs, -⟩
    · simp at hlast
    · obtain ⟨c, u, rfl, hc, -⟩ := token_shape hs
      exact not_atEnd (x := u ++ (r ++ rest)) hw hend hc (by rw [hin]; simp)
  · simp at hnil

/-- What `ScriptParseFrom` holds of an input, taken apart. -/
theorem ScriptParseFrom.inv {version : Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} (h : ScriptParseFrom version offset input commands) :
    (commands = [] ∧ TokenizationFrom version offset input []) ∨
      (∃ version' seg rest tokens c cs, input = seg ++ rest ∧ commands = c :: cs ∧
        TokenizationExactly version' offset seg tokens ∧
        Command version' (tokens.map (SyntaxToken.ofToken version')) c ∧
        (version' = version ∨ c.DeclaresVersion) ∧ c ≠ .exit ∧
        ScriptParseFrom version' (offset + seg.length) rest cs) ∨
      (∃ seg rest tokens, input = seg ++ rest ∧ commands = [.exit] ∧
        TokenizationExactly version offset seg tokens ∧
        Command version (tokens.map (SyntaxToken.ofToken version)) .exit) := by
  cases h with
  | done ht => exact Or.inl ⟨rfl, ht⟩
  | command ht hc hv hne hrest =>
    exact Or.inr (Or.inl ⟨_, _, _, _, _, _, rfl, rfl, ht, hc, hv, hne, hrest⟩)
  | exit ht hc => exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl, ht, hc⟩)

/-- A parse of an input from any offset and version is unique. -/
theorem scriptParseFrom_unique {version : Version} {offset : Nat} {input : Chars}
    {commands commands' : List Tree.Command}
    (h : ScriptParseFrom version offset input commands)
    (h' : ScriptParseFrom version offset input commands') : commands = commands' := by
  induction h generalizing commands' with
  | done ht =>
    rcases ScriptParseFrom.inv h' with ⟨rfl, -⟩ | ⟨_, _, _, _, _, _, hin, -, ht', -⟩ |
      ⟨_, _, _, hin, -, ht', -⟩
    · rfl
    · exact (not_done_and_command (hin ▸ ht) ht').elim
    · exact (not_done_and_command (hin ▸ ht) ht').elim
  | command ht hc hv hne _ ih =>
    rcases ScriptParseFrom.inv h' with ⟨-, hdone⟩ |
      ⟨_, _, _, _, _, _, hin, rfl, ht', hc', hv', -, hrest'⟩ | ⟨_, _, _, hin, rfl, ht', hc'⟩
    · exact (not_done_and_command hdone ht).elim
    · obtain ⟨rfl, rfl, rfl⟩ := first_command ht hc hv ht' hc' hv' hin
      obtain rfl := List.append_cancel_left hin
      rw [ih hrest']
    · obtain ⟨-, -, rfl⟩ := first_command ht hc hv ht' hc' (Or.inl rfl) hin
      exact absurd rfl hne
  | exit ht hc =>
    rcases ScriptParseFrom.inv h' with ⟨-, hdone⟩ |
      ⟨_, _, _, _, _, _, hin, rfl, ht', hc', hv', hne', -⟩ | ⟨_, _, _, -, rfl, -, -⟩
    · exact (not_done_and_command hdone ht).elim
    · obtain ⟨-, -, he⟩ := first_command ht hc (Or.inl rfl) ht' hc' hv' hin
      exact absurd he.symm hne'
    · rfl

end BSmtLib.SpecChecks.Grammar
