module

public import BSmtLib.Facts.Proofs.Parser.Category.CursorS
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Token

@[expose] public section

/-!
# The parsers of single tokens on a cursor

Each parser of a single token steps as `Category.Token.Internal.singleByToken` with what it
expects of the token: it finishes at its first token with what it takes of it, or fails there.
-/

namespace BSmtLib.Facts.Proofs.Parser.Category.Token

open BSmtLib.Token (Cursor)
open BSmtLib.Parser (Parse ParseState SyntaxErrorKind)
open BSmtLib.Parser.Internal (PM)
open BSmtLib.Parser.Category.Token
open BSmtLib.Parser.Category.Token.Internal
open BSmtLib.Facts.Parser.Adapters.Cursor (Takes Reads noPoints)
open BSmtLib.Facts.Parser.Adapters
open BSmtLib.Facts.Proofs.Parser.Category.Cursor BSmtLib.Facts.Proofs.Parser.Category.CursorS
open BSmtLib.Facts.Proofs.Parser.Category.Steps
open BSmtLib.Facts.Proofs.Parser.Drive

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {P ρ : Type}

/-- The steps of a parser of a single token, over no state. -/
def singleStep (expect : Parser.Internal.Input → PM H ρ) :
    Unit → Parser.Internal.Input → PM H (Parser.Internal.Step Unit ρ) :=
  fun _ token => (.done ·) <$> expect token

theorem single_sim (expect : Parser.Internal.Input → PM H ρ) (parser : P)
    (version : Token.Version) :
    @Simulates H P ρ Unit m _ _ (Internal.singleByToken (P := P) H expect) version
      (fun _ => parser) (singleStep expect) parser := by
  letI := Internal.singleByToken (P := P) H expect
  refine ⟨fun _ _ => rfl, fun _ token => ?_, fun _ => rfl, fun _ _ => rfl⟩
  simp only [singleStep, Functor.map_map]
  rw [map_eq_pure_bind]
  rfl

/-- A parser of a single token, on a token it takes. -/
theorem single_parses [Parse P H m (Traits.Handler.Error H) ρ]
    (expect : Parser.Internal.Input → PM H ρ) (parser : P)
    (hparse : ∀ {Z : Type} [Cursor Z] (parser : P) (state : ParseState H) (cursor : Z),
      Parse.parse parser state cursor =
        @Parser.Internal.parseByToken H P ρ _ m _ (Internal.singleByToken (P := P) H expect) Z _
          parser state cursor)
    (version : Token.Version) {token : Parser.Internal.Input} {result : ρ}
    (h : expect token = pure result) :
    Outcome.Finishes version parser [token] (pure result : PM H ρ) parser := by
  letI := Internal.singleByToken (P := P) H expect
  have hruns : RunsS noPoints (singleStep expect) () [token] (pure result : PM H ρ)
      fun r => pure (.done r) :=
    (RunsS.token (program := pure result) (by simp [singleStep, h])).congr (by simp) rfl
  have := parses_of_runsS (H := H) (P := P) (R := ρ) (σ := Unit) (m := m) (version := version)
    (mk := fun _ => parser) (step := singleStep expect) (state := ()) @hparse
    (single_sim expect parser version) hruns
  exact this

/-- A parser of a single token, on a token it does not take. -/
theorem single_rejects [Parse P H m (Traits.Handler.Error H) ρ]
    (expect : Parser.Internal.Input → PM H ρ) (parser : P)
    (hparse : ∀ {Z : Type} [Cursor Z] (parser : P) (state : ParseState H) (cursor : Z),
      Parse.parse parser state cursor =
        @Parser.Internal.parseByToken H P ρ _ m _ (Internal.singleByToken (P := P) H expect) Z _
          parser state cursor)
    (version : Token.Version) {token : Parser.Internal.Input} {kind : SyntaxErrorKind}
    (h : expect token = throw (.syntax kind)) :
    Outcome.Rejects version parser [token] (pure () : PM H Unit) kind := by
  letI := Internal.singleByToken (P := P) H expect
  have hruns : RunsS noPoints (singleStep expect) () [token] (pure () : PM H Unit)
      fun _ => throw (.syntax kind) :=
    (RunsS.token (program := pure ()) (next := fun _ => throw (.syntax kind))
      (by simp [singleStep, h])).congr (by simp) rfl
  have := rejects_of_runsS (H := H) (P := P) (R := ρ) (σ := Unit) (m := m) (version := version)
    (mk := fun _ => parser) (step := singleStep expect) (fresh := parser) (state := ()) @hparse
    (single_sim expect parser version) hruns
  simp only [map_pure] at this
  exact this

/-- A parser of a single token, on a cursor with no token: it wants more, as it was. -/
theorem single_waits [Parse P H m (Traits.Handler.Error H) ρ]
    (expect : Parser.Internal.Input → PM H ρ) (parser : P)
    (hparse : ∀ {Z : Type} [Cursor Z] (parser : P) (state : ParseState H) (cursor : Z),
      Parse.parse parser state cursor =
        @Parser.Internal.parseByToken H P ρ _ m _ (Internal.singleByToken (P := P) H expect) Z _
          parser state cursor)
    (version : Token.Version) :
    Outcome.Waits version parser [] (pure () : PM H Unit) fun _ => parser := by
  letI := Internal.singleByToken (P := P) H expect
  have hruns : RunsS noPoints (singleStep expect) () [] (pure () : PM H Unit)
      fun _ => pure (.more ()) := RunsS.nil () rfl
  exact waits_of_runsS (H := H) (P := P) (R := ρ) (σ := Unit) (m := m) (version := version)
    (mk := fun _ => parser) (step := singleStep expect) (fresh := parser) (state := ()) @hparse
    (single_sim expect parser version) hruns

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable (version : Token.Version)

open BSmtLib.Plain (Numeral Keyword StringContent)

theorem symbol_parses (symbol : Plain.Symbol) :
    Outcome.Finishes version SymbolParser.new [.symbol symbol]
      (pure symbol.intoOwned : PM H Plain.SymbolBuf) SymbolParser.new :=
  single_parses (fun token => Plain.Symbol.intoOwned <$> expectSymbol token)
    SymbolParser.new (fun _ _ _ => rfl) version (by simp [expectSymbol])

theorem symbol_rejects {token : Parser.Internal.Input} (h : ∀ symbol, token ≠ .symbol symbol) :
    Outcome.Rejects version SymbolParser.new [token] (pure () : PM H Unit) (.expected #[.symbol]) :=
  single_rejects (fun token => Plain.Symbol.intoOwned <$> expectSymbol token)
    SymbolParser.new (fun _ _ _ => rfl) version
    (by
      cases token <;> first
        | exact absurd rfl (h _)
        | simp [expectSymbol, Parser.Internal.syntaxError])

theorem openParen_parses :
    Outcome.Finishes version OpenParenParser.new [.parenOpen] (pure () : PM H Unit)
      OpenParenParser.new :=
  single_parses expectOpen OpenParenParser.new (fun _ _ _ => rfl) version rfl

theorem openParen_rejects {token : Parser.Internal.Input} (h : token ≠ .parenOpen) :
    Outcome.Rejects version OpenParenParser.new [token] (pure () : PM H Unit)
      (.expected #[.token .parenOpen]) :=
  single_rejects expectOpen OpenParenParser.new (fun _ _ _ => rfl) version
    (by cases token <;> first | exact absurd rfl h | rfl)

theorem closeParen_parses :
    Outcome.Finishes version CloseParenParser.new [.parenClose] (pure () : PM H Unit)
      CloseParenParser.new :=
  single_parses expectClose CloseParenParser.new (fun _ _ _ => rfl) version rfl

theorem closeParen_rejects {token : Parser.Internal.Input} (h : token ≠ .parenClose) :
    Outcome.Rejects version CloseParenParser.new [token] (pure () : PM H Unit)
      (.expected #[.token .parenClose]) :=
  single_rejects expectClose CloseParenParser.new (fun _ _ _ => rfl) version
    (by cases token <;> first | exact absurd rfl h | rfl)

theorem numeral_parses (digits : Numeral) :
    Outcome.Finishes version NumeralParser.new [.constant (.numeral digits)]
      (pure digits.intoOwned : PM H Plain.NumeralBuf) NumeralParser.new :=
  single_parses (fun token => Numeral.intoOwned <$> expectNumeral token)
    NumeralParser.new (fun _ _ _ => rfl) version (by simp [expectNumeral])

theorem numeral_rejects {token : Parser.Internal.Input}
    (h : ∀ digits, token ≠ .constant (.numeral digits)) :
    Outcome.Rejects version NumeralParser.new [token] (pure () : PM H Unit)
      (.expected #[.token .numeral]) :=
  single_rejects (fun token => Numeral.intoOwned <$> expectNumeral token)
    NumeralParser.new (fun _ _ _ => rfl) version
    (by
      cases token with
      | constant c =>
        cases c <;> first
          | exact absurd rfl (h _)
          | simp [expectNumeral, Parser.Internal.syntaxError]
      | _ => simp [expectNumeral, Parser.Internal.syntaxError])

theorem keyword_parses (name : Keyword) :
    Outcome.Finishes version KeywordParser.new [.keyword name]
      (pure name.intoOwned : PM H Plain.KeywordBuf) KeywordParser.new :=
  single_parses (fun token => Keyword.intoOwned <$> expectKeyword token)
    KeywordParser.new (fun _ _ _ => rfl) version (by simp [expectKeyword])

theorem keyword_rejects {token : Parser.Internal.Input} (h : ∀ name, token ≠ .keyword name) :
    Outcome.Rejects version KeywordParser.new [token] (pure () : PM H Unit)
      (.expected #[.token .keyword]) :=
  single_rejects (fun token => Keyword.intoOwned <$> expectKeyword token)
    KeywordParser.new (fun _ _ _ => rfl) version
    (by
      cases token <;> first
        | exact absurd rfl (h _)
        | simp [expectKeyword, Parser.Internal.syntaxError])

theorem string_parses (content : StringContent) :
    Outcome.Finishes version StringParser.new [.constant (.string content)]
      (pure content.intoOwned : PM H Plain.StringContentBuf) StringParser.new :=
  single_parses (fun token => StringContent.intoOwned <$> expectString token)
    StringParser.new (fun _ _ _ => rfl) version (by simp [expectString])

theorem string_rejects {token : Parser.Internal.Input}
    (h : ∀ content, token ≠ .constant (.string content)) :
    Outcome.Rejects version StringParser.new [token] (pure () : PM H Unit)
      (.expected #[.token .string]) :=
  single_rejects (fun token => StringContent.intoOwned <$> expectString token)
    StringParser.new (fun _ _ _ => rfl) version
    (by
      cases token with
      | constant c =>
        cases c <;> first
          | exact absurd rfl (h _)
          | simp [expectString, Parser.Internal.syntaxError]
      | _ => simp [expectString, Parser.Internal.syntaxError])


theorem symbol_waits :
    Outcome.Waits version SymbolParser.new [] (pure () : PM H Unit) fun _ => SymbolParser.new :=
  single_waits (fun token => Plain.Symbol.intoOwned <$> expectSymbol token)
    SymbolParser.new (fun _ _ _ => rfl) version

theorem openParen_waits :
    Outcome.Waits version OpenParenParser.new [] (pure () : PM H Unit)
      fun _ => OpenParenParser.new :=
  single_waits expectOpen OpenParenParser.new (fun _ _ _ => rfl) version

theorem closeParen_waits :
    Outcome.Waits version CloseParenParser.new [] (pure () : PM H Unit)
      fun _ => CloseParenParser.new :=
  single_waits expectClose CloseParenParser.new (fun _ _ _ => rfl) version

theorem numeral_waits :
    Outcome.Waits version NumeralParser.new [] (pure () : PM H Unit) fun _ => NumeralParser.new :=
  single_waits (fun token => Numeral.intoOwned <$> expectNumeral token)
    NumeralParser.new (fun _ _ _ => rfl) version

theorem keyword_waits :
    Outcome.Waits version KeywordParser.new [] (pure () : PM H Unit) fun _ => KeywordParser.new :=
  single_waits (fun token => Keyword.intoOwned <$> expectKeyword token)
    KeywordParser.new (fun _ _ _ => rfl) version

theorem string_waits :
    Outcome.Waits version StringParser.new [] (pure () : PM H Unit) fun _ => StringParser.new :=
  single_waits (fun token => StringContent.intoOwned <$> expectString token)
    StringParser.new (fun _ _ _ => rfl) version

end

end BSmtLib.Facts.Proofs.Parser.Category.Token
