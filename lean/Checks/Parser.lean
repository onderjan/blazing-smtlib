import ParserSpec

/-!
# The standard's examples of syntax

Examples the standard gives with its syntactic rules, checked against the parser spec. Not
trusted: these are proofs.
-/

namespace ParserSpec.Checks

open LexerSpec ParserSpec

/-- The symbol `s`. -/
abbrev sym (s : String) : SyntaxToken := .symbol (chars s)

/-- The numeral `s`. -/
abbrev num (s : String) : SyntaxToken := .numeral (chars s)

/-- The identifier `s`, not indexed. -/
abbrev ident (s : String) : Tree.Identifier := ⟨chars s, []⟩

/-- The sort `s`, not applied. -/
abbrev sort (s : String) : Tree.Sort := .mk (ident s) []

instance (version first : Version) : Decidable (version.atLeast first) :=
  inferInstanceAs (Decidable (first ∈ version.upTo))

/-- A single item. -/
theorem Each.single {α : Type} {rule : List SyntaxToken → α → Prop} {tokens : List SyntaxToken}
    {item : α} (h : rule tokens item) : Each rule tokens [item] := by
  simpa using Each.cons (rest := []) h .nil

/-! ## Identifiers and sorts -/

/-- `(_ BitVec 3)` -/
example : Grammar.Sort .v2_7 (paren [word "_", sym "BitVec", num "3"])
    (.mk ⟨chars "BitVec", [.numeral (chars "3")]⟩ []) :=
  .identifier (.indexed (tokens := [num "3"])
    (.cons (first := [num "3"]) (rest := []) .numeral .nil)
    (by simp))

/-- `(_ move up)`: a symbol index, from 2.5 on. -/
example : Grammar.Identifier .v2_5 (paren [word "_", sym "move", sym "up"])
    ⟨chars "move", [.symbol (chars "up")]⟩ :=
  .indexed (tokens := [sym "up"])
    (.cons (first := [sym "up"]) (rest := []) (.symbol (by decide)) .nil) (by simp)

/-- `(List (Array Int Real))` -/
example : Grammar.Sort .v2_7
    (paren [sym "List", .parenOpen, sym "Array", sym "Int", sym "Real", .parenClose])
    (.mk (ident "List") [.mk (ident "Array") [sort "Int", sort "Real"]]) := by
  apply Grammar.Sort.application (head := [sym "List"])
    (tokens := paren [sym "Array", sym "Int", sym "Real"]) .symbol _ (by simp)
  apply Each.cons (first := paren [sym "Array", sym "Int", sym "Real"]) (rest := []) _ .nil
  apply Grammar.Sort.application (head := [sym "Array"]) (tokens := [sym "Int", sym "Real"])
    .symbol _ (by simp)
  exact .cons (first := [sym "Int"]) (rest := [sym "Real"]) (.identifier .symbol)
    (.cons (first := [sym "Real"]) (rest := []) (.identifier .symbol) .nil)

/-- `(_ move up)` is not an identifier in 2.0, where indices are numerals. -/
example : ¬ Grammar.Identifier .v2_0 (paren [word "_", sym "move", sym "up"]) identifier := by
  generalize htokens : paren [word "_", sym "move", sym "up"] = tokens
  intro h
  cases h with
  | symbol => simp [paren] at htokens
  | @indexed indexTokens _ _ hindices _ =>
    simp only [paren, word, sym, List.cons_append, List.cons.injEq, true_and] at htokens
    have hsplit : [SyntaxToken.symbol (chars "up")] ++ [.parenClose] =
        indexTokens ++ [.parenClose] := by simpa using htokens.2
    have hup := List.append_cancel_right hsplit
    subst hup
    generalize hrest : [SyntaxToken.symbol (chars "up")] = rest at hindices
    cases hindices with
    | nil => simp at hrest
    | cons hfirst _ =>
      cases hfirst with
      | numeral => simp at hrest
      | symbol hversion => exact absurd hversion (by decide)

/-! ## Terms -/

/-- `(f x 1)` -/
example : Grammar.Term .v2_7 (paren [sym "f", sym "x", num "1"])
    (.application (.plain (ident "f"))
      [.identifier (.plain (ident "x")), .constant (.numeral (chars "1"))]) :=
  .application (head := [sym "f"]) (tokens := [sym "x", num "1"]) (.plain .symbol)
    (.cons (first := [sym "x"]) (rest := [num "1"]) (.identifier (.plain .symbol))
      (.cons (first := [num "1"]) (rest := []) (.constant .numeral) .nil))
    (by simp)

/-! ## Commands -/

/-- `(declare-fun f (Int) Int)` -/
example : Grammar.Command .v2_0
    (commandTokens "declare-fun" [sym "f", .parenOpen, sym "Int", .parenClose, sym "Int"])
    (.declareFun (chars "f") [sort "Int"] (sort "Int")) :=
  .declareFun (parameterTokens := [sym "Int"]) (resultTokens := [sym "Int"])
    (.cons (first := [sym "Int"]) (rest := []) (.identifier .symbol) .nil) (.identifier .symbol)

/-- The list datatype of the standard:
`(declare-datatypes ((List 1)) ((par (T) ((nil) (cons (head T) (tail (List T)))))))` -/
example : Grammar.Command .v2_6
    (commandTokens "declare-datatypes"
      (paren (paren [sym "List", num "1"]) ++
        paren (paren (word "par" :: paren [sym "T"] ++
          paren (paren [sym "nil"] ++
            paren (sym "cons" :: paren [sym "head", sym "T"] ++
              paren [sym "tail", .parenOpen, sym "List", sym "T", .parenClose]))))))
    (.declareDatatypes [⟨chars "List", chars "1"⟩]
      [⟨[chars "T"], [⟨chars "nil", []⟩,
        ⟨chars "cons",
          [⟨chars "head", sort "T"⟩, ⟨chars "tail", .mk (ident "List") [sort "T"]⟩]⟩]⟩]) := by
  apply Grammar.Command.declareDatatypes (by decide)
    (.cons (first := paren [sym "List", num "1"]) (rest := []) .mk .nil)
    _ (by simp) rfl
  apply Each.single
  apply Grammar.DatatypeDec.parametric (parameterTokens := [sym "T"])
    (.cons (first := [sym "T"]) (rest := []) .mk .nil) (by simp) _ (by simp)
  apply Each.cons (first := paren [sym "nil"]) (.mk .nil)
  apply Each.single
  apply Grammar.ConstructorDec.mk
  apply Each.cons (first := paren [sym "head", sym "T"]) (.mk (.identifier .symbol))
  apply Each.single
  apply Grammar.SelectorDec.mk
  exact .application (head := [sym "List"]) (tokens := [sym "T"]) .symbol
    (.cons (first := [sym "T"]) (rest := []) (.identifier .symbol) .nil) (by simp)

/-! ## Version declarations -/

/-- `(set-info :smt-lib-version 2.6)` is a command of 2.6. -/
example : Grammar.Command .v2_6
    (commandTokens "set-info" [.keyword (chars "smt-lib-version"), .decimal (chars "2.6")])
    (.setInfo ⟨chars "smt-lib-version", some (.constant (.decimal (chars "2.6")))⟩) :=
  .declareVersion

/-- It is not a command of 2.7: each version accepts only its own number. -/
example : ¬ Grammar.Command .v2_7
    (commandTokens "set-info" [.keyword (chars "smt-lib-version"), .decimal (chars "2.6")])
    command := by
  generalize htokens :
    commandTokens "set-info" [.keyword (chars "smt-lib-version"), .decimal (chars "2.6")] = tokens
  intro h
  cases h
  case setInfo attributeTokens info hattribute hkeyword =>
    have hsplit : [SyntaxToken.keyword (chars "smt-lib-version"), .decimal (chars "2.6")] ++
        [.parenClose] = attributeTokens ++ [.parenClose] := by
      simpa [commandTokens, paren, word] using htokens
    obtain rfl := List.append_cancel_right hsplit
    generalize hattributeTokens :
      [SyntaxToken.keyword (chars "smt-lib-version"), .decimal (chars "2.6")] = attributeTokens
      at hattribute
    cases hattribute with
    | keyword => simp at hattributeTokens
    | valued _ => simp_all
  all_goals simp_all (config := { decide := true }) [commandTokens, paren, word]

/-- The unrestricted policy restricts nothing. -/
theorem scriptReadsUnder_unrestricted (version : Version) (input : Chars)
    (commands : List Tree.Command) :
    ScriptReadsUnder .unrestricted version input commands ↔ ScriptReads version input commands := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun declared _ => ?_, by simp [VersionPolicy.unrestricted]⟩⟩
  cases declared <;> simp [VersionPolicy.unrestricted]

end ParserSpec.Checks
