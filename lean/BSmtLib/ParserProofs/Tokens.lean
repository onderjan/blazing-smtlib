import BSmtLib.ParserProofs.Lemmas

/-!
# Which tokens of the parser stand for which tokens of the spec

`Stands tokens syntaxTokens`: the parser's tokens stand for the spec's, one by one. The lemmas
split such a relation along the concatenations of `Tree.*.tokens` and invert it for each kind of
token, so that a proof by a tree finds the parser's tokens it steps over.
-/

namespace BSmtLib.ParserProofs

open BSmtLibSpec.Grammar
open BSmtLibSpec.Grammar.Syntax BSmtLibSpec.Grammar.File BSmtLibSpec.Grammar.Properties
open BSmtLibSpec.Parser.Traversal (Received)
open BSmtLib.Parser (Input)
open Bridge

namespace Input

theorem received_symbol {token : Input} {name : Tree.Symbol}
    (h : Bridge.received token = some (.token (.symbol name))) :
    ∃ symbol, token = .symbol symbol ∧ Bridge.symbol symbol = name := by
  cases token with
  | symbol symbol => exact ⟨symbol, rfl, by simpa [Bridge.received] using h⟩
  | constant constant => cases constant <;> simp [Bridge.received, Bridge.constant,
      Tree.SpecConstant.token] at h
  | _ => simp [Bridge.received] at h

theorem received_keyword {token : Input} {name : BSmtLibSpec.Regex.Chars}
    (h : Bridge.received token = some (.token (.keyword name))) :
    ∃ keyword, token = .keyword keyword ∧ Bridge.keyword keyword = name := by
  cases token with
  | keyword keyword => exact ⟨keyword, rfl, by simpa [Bridge.received] using h⟩
  | constant constant => cases constant <;> simp [Bridge.received, Bridge.constant,
      Tree.SpecConstant.token] at h
  | _ => simp [Bridge.received] at h

theorem received_reserved {token : Input} {word : BSmtLibSpec.Regex.Chars}
    (h : Bridge.received token = some (.token (.reserved word))) :
    ∃ reserved, token = .reserved reserved ∧ Bridge.reserved reserved = word := by
  cases token with
  | reserved reserved => exact ⟨reserved, rfl, by simpa [Bridge.received] using h⟩
  | constant constant => cases constant <;> simp [Bridge.received, Bridge.constant,
      Tree.SpecConstant.token] at h
  | _ => simp [Bridge.received] at h

theorem received_numeral {token : Input} {digits : BSmtLibSpec.Regex.Chars}
    (h : Bridge.received token = some (.token (.numeral digits))) :
    ∃ view, token = .constant (.numeral view) ∧ chars view.asSlice = digits := by
  cases token with
  | constant constant =>
    cases constant with
    | numeral view => exact ⟨view, rfl, by simpa [Bridge.received, Bridge.constant,
        Tree.SpecConstant.token] using h⟩
    | _ => simp [Bridge.received, Bridge.constant, Tree.SpecConstant.token] at h
  | _ => simp [Bridge.received] at h

theorem received_decimal {token : Input} {text : BSmtLibSpec.Regex.Chars}
    (h : Bridge.received token = some (.token (.decimal text))) :
    ∃ view, token = .constant (.decimal view) ∧ chars view.asSlice = text := by
  cases token with
  | constant constant =>
    cases constant with
    | decimal view => exact ⟨view, rfl, by simpa [Bridge.received, Bridge.constant,
        Tree.SpecConstant.token] using h⟩
    | _ => simp [Bridge.received, Bridge.constant, Tree.SpecConstant.token] at h
  | _ => simp [Bridge.received] at h

theorem received_string {token : Input} {content : BSmtLibSpec.Regex.Chars}
    (h : Bridge.received token = some (.token (.string content))) :
    ∃ view, token = .constant (.string view) ∧ chars view.asSlice = content := by
  cases token with
  | constant constant =>
    cases constant with
    | string view => exact ⟨view, rfl, by simpa [Bridge.received, Bridge.constant,
        Tree.SpecConstant.token] using h⟩
    | _ => simp [Bridge.received, Bridge.constant, Tree.SpecConstant.token] at h
  | _ => simp [Bridge.received] at h

theorem received_parenOpen {token : Input} (h : Bridge.received token = some (.token .parenOpen)) :
    token = .parenOpen := by
  cases token with
  | parenOpen => rfl
  | constant constant => cases constant <;> simp [Bridge.received, Bridge.constant,
      Tree.SpecConstant.token] at h
  | _ => simp [Bridge.received] at h

theorem received_parenClose {token : Input}
    (h : Bridge.received token = some (.token .parenClose)) : token = .parenClose := by
  cases token with
  | parenClose => rfl
  | constant constant => cases constant <;> simp [Bridge.received, Bridge.constant,
      Tree.SpecConstant.token] at h
  | _ => simp [Bridge.received] at h

theorem received_constant {token : Input} {constant : Tree.SpecConstant}
    (h : Bridge.received token = some (.token constant.token)) :
    ∃ constant', token = .constant constant' ∧ Bridge.constant constant' = constant := by
  cases token with
  | constant constant' =>
    refine ⟨constant', rfl, ?_⟩
    cases constant' <;> cases constant <;>
      simp_all [Bridge.received, Bridge.constant, Tree.SpecConstant.token]
  | _ => cases constant <;> simp [Bridge.received, Tree.SpecConstant.token] at h

theorem received_endOfInput {token : Input} (h : Bridge.received token = some .endOfInput) :
    token = .endOfInput := by
  cases token with
  | endOfInput => rfl
  | constant constant => cases constant <;> simp [Bridge.received] at h
  | _ => simp [Bridge.received] at h

end Input

namespace Stands

theorem nil : Stands [] [] := rfl

theorem cons {token : Input} {syntaxToken : BSmtLibSpec.Grammar.SyntaxToken} {tokens : List Input}
    {syntaxTokens : List BSmtLibSpec.Grammar.SyntaxToken}
    (h : Bridge.received token = some (.token syntaxToken))
    (hs : Stands tokens syntaxTokens) : Stands (token :: tokens) (syntaxToken :: syntaxTokens) := by
  simp only [Stands, List.map_cons, h] at hs ⊢
  rw [hs]

theorem append {tokens tokens' : List Input}
    {syntaxTokens syntaxTokens' : List BSmtLibSpec.Grammar.SyntaxToken}
    (h : Stands tokens syntaxTokens) (h' : Stands tokens' syntaxTokens') :
    Stands (tokens ++ tokens') (syntaxTokens ++ syntaxTokens') := by
  simp only [Stands, List.map_append] at h h' ⊢
  rw [h, h']

theorem eq_nil {tokens : List Input} (h : Stands tokens []) : tokens = [] :=
  List.map_eq_nil_iff.mp h

/-- Tokens that stand for a concatenation are a concatenation of tokens standing for its parts. -/
theorem split {tokens : List Input} {first second : List BSmtLibSpec.Grammar.SyntaxToken}
    (h : Stands tokens (first ++ second)) :
    ∃ tokens₁ tokens₂, tokens = tokens₁ ++ tokens₂ ∧ Stands tokens₁ first ∧
      Stands tokens₂ second := by
  simp only [Stands, List.map_append] at h
  obtain ⟨tokens₁, tokens₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp h
  exact ⟨tokens₁, tokens₂, rfl, h₁, h₂⟩

/-- Tokens that stand for a token and others are that token's and the others'. -/
theorem split_cons {tokens : List Input} {first : BSmtLibSpec.Grammar.SyntaxToken}
    {rest : List BSmtLibSpec.Grammar.SyntaxToken}
    (h : Stands tokens (first :: rest)) :
    ∃ token tokens', tokens = token :: tokens' ∧
      Bridge.received token = some (.token first) ∧ Stands tokens' rest := by
  cases tokens with
  | nil => simp [Stands] at h
  | cons token tokens' =>
    simp only [Stands, List.map_cons, List.cons.injEq] at h
    exact ⟨token, tokens', rfl, h.1, h.2⟩

/-- Tokens that stand for one token are one token. -/
theorem split_single {tokens : List Input} {only : BSmtLibSpec.Grammar.SyntaxToken}
    (h : Stands tokens [only]) :
    ∃ token, tokens = [token] ∧ Bridge.received token = some (.token only) := by
  obtain ⟨token, rest, rfl, htoken, hrest⟩ := split_cons h
  cases rest with
  | nil => exact ⟨token, rfl, htoken⟩
  | cons => simp [Stands] at hrest

/-- Tokens that stand for a parenthesised list are a `(`, tokens for the list, and a `)`. -/
theorem split_paren {tokens : List Input} {inner : List BSmtLibSpec.Grammar.SyntaxToken}
    (h : Stands tokens (paren inner)) :
    ∃ inner', tokens = .parenOpen :: (inner' ++ [.parenClose]) ∧ Stands inner' inner := by
  obtain ⟨token, rest, rfl, hopen, hrest⟩ := split_cons h
  obtain ⟨inner', closing, rfl, hinner, hclosing⟩ := split hrest
  obtain ⟨close, rfl, hclose⟩ := split_single hclosing
  rw [Input.received_parenOpen hopen, Input.received_parenClose hclose]
  exact ⟨inner', rfl, hinner⟩

/-- Tokens that stand for a spec constant are one constant token, standing for it. -/
theorem constant {tokens : List Input} {constant : Tree.SpecConstant}
    (h : Stands tokens [constant.token]) :
    ∃ constant', tokens = [.constant constant'] ∧ Bridge.constant constant' = constant := by
  obtain ⟨token, rfl, htoken⟩ := split_single h
  obtain ⟨constant', rfl, hc⟩ := Input.received_constant htoken
  exact ⟨constant', rfl, hc⟩

end Stands

end BSmtLib.ParserProofs
