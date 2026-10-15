module

public import BSmtLib.Facts.Proofs.Parser.Category.StepsSort
public import BSmtLib.Facts.Proofs.Parser.Sort
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Ident
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# The identifier parser on a cursor

The identifier parser steps as `IdentState.step`, whose lemmas against the traversal are those
of the sort proofs (`Facts.Proofs.Parser.Sort`); with the token points that mark nothing, they
give what the parser does on a cursor.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.Ident

open BSmtLibSpec.Grammar
open BSmtLib.Token (Produce)
open BSmtLib.Parser (Parse ParseState SyntaxErrorKind)
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.Ident
open BSmtLib.Parser.Category.Ident.Internal
open BSmtLib.Facts.Parser.Adapters.Bridge
open BSmtLib.Facts.Parser.Adapters.Cursor (Takes Reads noPoints)
open BSmtLib.Facts.Parser.Adapters.Outcome (Finishes Rejects)
open BSmtLib.Facts.Proofs.Parser.Category.Cursor (Simulates Moves)
open BSmtLib.Facts.Proofs.Parser.Category.Steps BSmtLib.Facts.Proofs.Parser.Category.CursorS
open BSmtLib.Facts.Proofs.Parser.Drive BSmtLib.Facts.Proofs.Parser.Tokens
open BSmtLib.Facts.Proofs.Parser.Tokens.Stands

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]

theorem ticks_noPoints (tokens : List Parser.Internal.Input) :
    ticks (noPoints : BSmtLibSpec.Parser.Traversal.Points (StateT H m)) tokens = pure () := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih => simp [ih]

private theorem ident_sim (version : Token.Version) :
    @Simulates H IdentParser Nodes.IdentBuf IdentState m _ _ (Internal.identByToken H)
      version IdentParser.mk (mapSteps Nodes.Ident.intoOwned (IdentState.step version))
      IdentParser.new := by
  letI := Internal.identByToken (m := m) H
  refine ⟨fun _ _ => rfl, fun state token => ?_, fun _ => rfl, fun _ _ => rfl⟩
  rw [mapSteps, Functor.map_map, map_eq_pure_bind]
  refine bind_congr fun step => ?_
  cases step <;> rfl

omit [LawfulMonad m] in
private theorem ident_hparse {Z : Type} [Produce Z] (parser : IdentParser)
    (state : ParseState H) (cursor : Z) :
    Parse.parse (m := m) parser state cursor =
      @Parser.Internal.parseByToken H IdentParser Nodes.IdentBuf _ m _
        (Internal.identByToken H) Z _ parser state cursor := rfl

/-- The identifier parser's steps from the start over the tokens of a valid identifier: no call,
and it ends with the identifier, through the bridge. -/
theorem ident_runs {version : Token.Version} (ident : Tree.Identifier)
    (hvalid : ident.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens ident.tokens) :
    ∃ result : Nodes.Ident, Bridge.identifier result = ident ∧
      RunsS noPoints (IdentState.step (H := H) version) .start tokens (pure ())
        (fun _ => pure (.done result)) := by
  match ident with
  | ⟨name, []⟩ =>
    obtain ⟨token, rfl, htoken⟩ := Stands.split_single hs
    obtain ⟨symbol, rfl, rfl⟩ := Parser.Internal.Input.received_symbol htoken
    refine ⟨⟨symbol, #[]⟩, by simp [Bridge.identifier], ?_⟩
    exact (RunsS.token (program := pure ()) (by simp [IdentState.step])).congr (by simp) rfl
  | ⟨name, index :: indices⟩ =>
    obtain ⟨symbolToken, rest, rfl, hsymbol, hrest⟩ :=
      BSmtLib.Facts.Proofs.Parser.«Sort».Stands.indexed (List.cons_ne_nil _ _) hs
    obtain ⟨head, hhead, hruns⟩ :=
      BSmtLib.Facts.Proofs.Parser.Category.StepsSort.indexed_runs (H := H)
      (points := noPoints) (version := version) hvalid (List.cons_ne_nil _ _) hsymbol hrest
    refine ⟨head, hhead, ?_⟩
    rw [show Parser.Internal.Input.parenOpen :: Parser.Internal.Input.reserved
        (.general .underscore) :: symbolToken :: (rest ++ [.parenClose]) =
      [.parenOpen] ++ ([.reserved (.general .underscore)] ++
        (symbolToken :: (rest ++ [.parenClose]))) by rfl]
    refine (RunsS.append (middle := fun _ => IdentState.opened)
      (RunsS.token_more (by simp [IdentState.step])) fun _ =>
        RunsS.append (middle := fun _ => IdentState.afterUnderscore)
          (RunsS.token_more (by simp [IdentState.step])) fun _ => hruns).congr ?_ rfl
    simp [ticks_noPoints]

/-- The identifier parser from its start on the tokens of a valid identifier: it gives the owned
identifier of a view that is the identifier through the bridge. -/
theorem ident_parses {version : Token.Version} (ident : Tree.Identifier)
    (hvalid : ident.Valid (Bridge.version version)) {tokens : List Parser.Internal.Input}
    (hs : Stands tokens ident.tokens) :
    ∃ result : Nodes.Ident, Bridge.identifier result = ident ∧
      Finishes version IdentParser.new tokens (pure result.intoOwned : PM H Nodes.IdentBuf)
        IdentParser.new := by
  letI := Internal.identByToken (m := m) H
  obtain ⟨result, hresult, hruns⟩ := ident_runs (H := H) ident hvalid hs
  have hruns' := (RunsS.mapSteps Nodes.Ident.intoOwned hruns).congr rfl
    (show (fun _ => mapDone Nodes.Ident.intoOwned <$> pure (.done result)) =
      fun _ => (pure (.done result.intoOwned) : PM H _) by funext; simp [mapDone])
  have := parses_of_runsS (H := H) (P := IdentParser) (R := Nodes.IdentBuf)
    (σ := IdentState) (m := m) (version := version) (mk := IdentParser.mk)
    (step := mapSteps Nodes.Ident.intoOwned (IdentState.step version))
    (state := .start) (program := pure result.intoOwned) (@ident_hparse H m _ _)
    (ident_sim version)
    (RunsS.map_program (f := fun _ => result.intoOwned) hruns' |>.congr (by simp) rfl)
  exact ⟨result, hresult, this⟩

private theorem ident_rejects {version : Token.Version} {state last : IdentState}
    {tokens : List Parser.Internal.Input} {token : Parser.Internal.Input} {kind : SyntaxErrorKind}
    (hmoves : Moves (IdentState.step (H := H) version) state tokens last)
    (hfail : IdentState.step (H := H) version last token = throw (.syntax kind)) :
    Rejects version (IdentParser.mk state) (tokens ++ [token]) (pure () : PM H Unit) kind := by
  letI := Internal.identByToken (m := m) H
  exact rejects_of_movesS (H := H) (P := IdentParser) (R := Nodes.IdentBuf)
    (σ := IdentState) (m := m) (version := version) (mk := IdentParser.mk)
    (step := mapSteps Nodes.Ident.intoOwned (IdentState.step version))
    (@ident_hparse H m _ _) (ident_sim version) (Moves.mapSteps _ hmoves)
    (by simp [mapSteps, hfail])

/-- The identifier parser on a first token that is neither a symbol nor `(`. -/
theorem ident_rejects_first {version : Token.Version} {token : Parser.Internal.Input}
    (hsymbol : ∀ symbol, token ≠ .symbol symbol) (hopen : token ≠ .parenOpen) :
    Rejects version IdentParser.new [token] (pure () : PM H Unit) .expectedIdent :=
  ident_rejects (tokens := []) (.nil _) (by
    cases token <;> first | exact absurd rfl (hsymbol _) | exact absurd rfl hopen | rfl)

/-- The identifier parser on `(` and a token that is not `_`. -/
theorem ident_rejects_underscore {version : Token.Version} {token : Parser.Internal.Input}
    (htoken : token ≠ .reserved (.general .underscore)) :
    Rejects version IdentParser.new [.parenOpen, token] (pure () : PM H Unit)
      .expectedUnderscore :=
  ident_rejects (tokens := [.parenOpen])
    (.cons (middle := .opened) (by simp [IdentState.step]) (.nil _)) (by
    have : token.isWord .underscore = false := by
      cases token with
      | reserved word =>
        cases word with
        | general w =>
          cases w <;> first | exact absurd rfl htoken | rfl
        | _ => rfl
      | _ => rfl
    simp [IdentState.step, this, Parser.Internal.syntaxError])

/-- The identifier parser on `(` `_` and a token that is not a symbol. -/
theorem ident_rejects_symbol {version : Token.Version} {token : Parser.Internal.Input}
    (htoken : ∀ symbol, token ≠ .symbol symbol) :
    Rejects version IdentParser.new [.parenOpen, .reserved (.general .underscore), token]
      (pure () : PM H Unit) .expectedSymbol :=
  ident_rejects (tokens := [.parenOpen, .reserved (.general .underscore)])
    (.cons (middle := .opened) (by simp [IdentState.step])
      (.cons (middle := .afterUnderscore) (by simp [IdentState.step]) (.nil _))) (by
      cases token <;> first | exact absurd rfl (htoken _) | rfl)

/-- The identifier parser on `(` `_`, a symbol and `)`, an identifier without indices. -/
theorem ident_rejects_empty {version : Token.Version} (symbol : Plain.Symbol) :
    Rejects version IdentParser.new
      [.parenOpen, .reserved (.general .underscore), .symbol symbol, .parenClose]
      (pure () : PM H Unit) .emptyIdentIndices :=
  ident_rejects (tokens := [.parenOpen, .reserved (.general .underscore), .symbol symbol])
    (.cons (middle := .opened) (by simp [IdentState.step])
      (.cons (middle := .afterUnderscore) (by simp [IdentState.step])
      (.cons (middle := .indices symbol #[]) (by simp [IdentState.step]) (.nil _)))) (by
        simp [IdentState.step, Parser.Internal.syntaxError])

/-- A token that is an index in the version. -/
def IsIndex (version : Token.Version) (token : Parser.Internal.Input) : Prop :=
  (∃ digits, token = .constant (.numeral digits)) ∨
    ((∃ symbol, token = .symbol symbol) ∧ version ≥ .v2_5)

omit [LawfulMonad m] in
private theorem indices_move {version : Token.Version} (symbol : Plain.Symbol) :
    (indices : List Parser.Internal.Input) → (∀ index ∈ indices, IsIndex version index) →
    (found : Array Nodes.Index) →
    ∃ found', Moves (IdentState.step (H := H) version) (.indices symbol found) indices
      (.indices symbol found')
  | [], _, found => ⟨found, .nil _⟩
  | index :: indices, hindices, found => by
    rcases hindices index (List.mem_cons_self ..) with ⟨digits, rfl⟩ | ⟨⟨name, rfl⟩, hversion⟩
    · obtain ⟨found', hmoves⟩ := indices_move symbol indices
        (fun i hi => hindices i (List.mem_cons_of_mem _ hi)) (found.push (.numeral digits))
      exact ⟨found', .cons (by simp [IdentState.step]) hmoves⟩
    · obtain ⟨found', hmoves⟩ := indices_move symbol indices
        (fun i hi => hindices i (List.mem_cons_of_mem _ hi)) (found.push (.symbol name))
      exact ⟨found', .cons (by simp [IdentState.step, hversion]) hmoves⟩

/-- The identifier parser on `(` `_`, a symbol, indices of the version and a token that is
neither an index of the version nor `)`. -/
theorem ident_rejects_index {version : Token.Version} (symbol : Plain.Symbol)
    {indices : List Parser.Internal.Input} (hindices : ∀ index ∈ indices, IsIndex version index)
    {token : Parser.Internal.Input} (htoken : ¬ IsIndex version token)
    (hclose : token ≠ .parenClose) :
    Rejects version IdentParser.new
      ([.parenOpen, .reserved (.general .underscore), .symbol symbol] ++ indices ++ [token])
      (pure () : PM H Unit) .expectedIndexOrCloseParen := by
  obtain ⟨found, hmoves⟩ := indices_move (H := H) (version := version) symbol indices hindices #[]
  refine ident_rejects (.cons (middle := .opened) (by simp [IdentState.step])
    (.cons (middle := .afterUnderscore) (by simp [IdentState.step])
      (.cons (middle := .indices symbol #[]) (by simp [IdentState.step]) hmoves))) ?_
  simp only [IsIndex, not_or, not_and, not_exists] at htoken
  cases token with
  | parenClose => exact absurd rfl hclose
  | constant c =>
    cases c with
    | numeral digits => exact absurd rfl (htoken.1 digits)
    | _ => rfl
  | symbol name =>
    have : ¬ version ≥ .v2_5 := htoken.2 ⟨name, rfl⟩
    simp [IdentState.step, this, Parser.Internal.syntaxError]
  | _ => rfl

end

end BSmtLib.Facts.Proofs.Parser.Category.Ident
