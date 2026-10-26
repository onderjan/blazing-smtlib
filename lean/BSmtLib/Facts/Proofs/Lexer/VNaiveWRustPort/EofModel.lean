module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
import all BSmtLib.Lexer.Error
import all BSmtLib.Span

@[expose] public section

/-!
# What the consumer does at the end of the input

At the end of the input a lexer finishes the token in progress (`finishLs`) and hands it over,
and then the end-of-file token, unless a result is held. A relex or a request to discard at the
finished token does not stop the end of the input: the end-of-file token is handed over after it,
and a request to discard makes the lexer discard from the token on (`eofHand`). `eofOut` is what
the consumer does there, from the tokens it has taken and the version in force, and `EofRes`
states the result of the end of the input it gives: the result returned, the tokens taken, and on
an error, the version in force and where the lexer discards from.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Lexer.Error BSmtLib.Lexer.Internal.VNaive

/-- The lexemes the end of the input finishes before the end-of-file one, or none on an
error. -/
def finishLs (ws : Bool) (st : St) (location : Span.Location) : Option (List Lexeme) :=
  match st with
  | .idle => some []
  | .token p =>
    match Lexer.Internal.VNaive.finish ws p location with
    | .none => some []
    | .token l => some [l]
    | .error _ => none

/-- The failure of finishing the token in progress at the end of the input, where it fails. -/
def finishFail (ws : Bool) (st : St) (location : Span.Location) : LexFailure :=
  match st with
  | .idle => failAtEnd .unexpectedByte location location
  | .token p =>
    match Lexer.Internal.VNaive.finish ws p location with
    | .error f => f
    | _ => failAtEnd .unexpectedByte location location

section

variable (C : BSmtLibSpec.Lexer.Consumer)

/-- What the consumer does with the end-of-file token, after it has done `h` with the lexemes
the end of the input finishes, while the lexer holds a result if `hd`: also where the lexer
discards from after a request at a finished lexeme. -/
def eofHand (hd : Bool) (eof : Lexeme) : HandOut C → HandOut C × Option Span.Location
  | .cont p => (if hd then .cont p else hand1 C false (.cont p) eof, none)
  | .stop (.relex _) p => (if hd then .cont p else hand1 C false (.cont p) eof, none)
  | .stop (.discard none l) p => (if hd then .cont p else hand1 C false (.cont p) eof, some l.end)
  | h => (h, none)

/-- What the consumer does at the end of the input in the state `st` at `location`, from the
tokens `coll` it has taken under the version `ver`; none if finishing the token in progress
fails. -/
def eofOut (hd ws : Bool) (ver : Version) (coll : List Handed) (st : St)
    (location : Span.Location) :
    Option (HandOut C × Option Span.Location) :=
  (finishLs ws st location).map fun ls => eofHand C hd (eofLexeme location)
                                         (pending C hd ver coll ls)

end

/-- The formalism's failure for the cause of an error and its span. -/
def causeFailure {ε : Type} (cause : LexerErrorCause (Option ε)) (span : Span) :
    BSmtLibSpec.Lexer.Failure ε :=
  failureOf (LexerError.Internal.new cause span none)

theorem failureOf_eq {ε : Type} (e : LexerError (Option ε)) :
    failureOf e = causeFailure e.cause e.span :=
  (rfl)

theorem causeFailure_lexical {ε : Type} {k : LexicalErrorKind} {span : Span}
    (h : k ≠ .unexpectedTrailingToken) :
    causeFailure (ε := ε) (.lexical k) span = .lexical := by
  simp only [causeFailure, failureOf, LexerError.Internal.cause_new]
  have : (k == .unexpectedTrailingToken) = false := by
    cases k <;> first | rfl | exact absurd rfl h
  rw [this]
  rfl

/-- A failure as precisely as the lexers agree on it: the formalism's failure and, for a lexical
error other than trailing input, its kind and span. -/
abbrev PFailure (ε : Type) := BSmtLibSpec.Lexer.Failure ε × Option (LexicalErrorKind × Span)

/-- The kind and span of a lexical error other than trailing input; none for another error. -/
def lexicalKey {ε : Type} (cause : LexerErrorCause (Option ε)) (span : Span) :
    Option (LexicalErrorKind × Span) :=
  match cause with
  | .lexical kind => if kind == .unexpectedTrailingToken then none else some (kind, span)
  | .consumer _ => none

/-- The precise failure for the cause of an error and its span. -/
def preciseFailure {ε : Type} (cause : LexerErrorCause (Option ε)) (span : Span) : PFailure ε :=
  (causeFailure cause span, lexicalKey cause span)

/-- The precise failure of an error. -/
def preciseOf {ε : Type} (e : LexerError (Option ε)) : PFailure ε :=
  preciseFailure e.cause e.span

theorem preciseFailure_lexical {ε : Type} {k : LexicalErrorKind} {span : Span}
    (h : k ≠ .unexpectedTrailingToken) :
    preciseFailure (ε := ε) (.lexical k) span = (.lexical, some (k, span)) := by
  have : (k == .unexpectedTrailingToken) = false := by
    cases k <;> first | rfl | exact absurd rfl h
  simp only [preciseFailure, causeFailure_lexical h, lexicalKey, this]
  rfl

theorem preciseFailure_trailing {ε : Type} {span : Span} :
    preciseFailure (ε := ε) (.lexical .unexpectedTrailingToken) span =
      (.trailing (toLocation span.start), none) := (rfl)

theorem preciseFailure_consumer {ε : Type} {o : Option ε} {span : Span} :
    preciseFailure (.consumer o) span = (causeFailure (.consumer o) span, none) := (rfl)

/-- The precise failure gives the formalism's failure. -/
theorem preciseOf_fst {ε : Type} (e : LexerError (Option ε)) : (preciseOf e).1 = failureOf e :=
  (rfl)

/-- The formalism's failure at a stop of the consumer that fails the lexer. -/
def stopFailure {C : BSmtLibSpec.Lexer.Consumer} : Stop C → BSmtLibSpec.Lexer.Failure C.Error
  | .trailing l => .trailing (toLocation l.start)
  | .fail e _ _ => .consumer e
  | _ => .lexical

/-- What the end of the input at `location` gives, as what the consumer did there says: the result
`res`, the version `ver'` in force after it, where the lexer discards from after it (`d'`), and
the tokens taken (`coll'`). The consumer has done `h` with the lexemes the end of the input
finishes and the end-of-file token; a request to discard at a finished lexeme made the lexer
discard from `d`; and the lexer discarded from `d0` before. -/
def EofTail (C : BSmtLibSpec.Lexer.Consumer) (h : HandOut C) (d d0 : Option Span.Location)
    (location : Span.Location)
    (res : Except (PFailure C.Error) (ControlFlow (Span.Located C.Result)))
    (ver' : Version)
    (d' : Option Span.Location) (coll' : List Handed) : Prop :=
  match h with
  | .cont p => res = .ok .continue ∧ coll' = p.taken
  | .wait r _ p => res = .ok (.break (Span.Located.Internal.new r location)) ∧ coll' = p.taken
  | .stop s p =>
    match s with
    | .brkX r _ => res = .ok (.break (Span.Located.Internal.new r location)) ∧ coll' = p.taken
    | .discard (some r) _ =>
      res = .ok (.break (Span.Located.Internal.new r location)) ∧ coll' = p.taken
    | .discard none _ => res = .ok .continue ∧ coll' = p.taken
    | .relex _ => res = .ok .continue ∧ coll' = p.taken
    | .brk _ _ _ => False
    | s => res = .error (stopFailure s, none) ∧ ver' = p.ver ∧
        d' = discardsAfter (d.or d0) s.discards ∧ coll' = p.taken

/-- What the end of the input at `location` gives, as `o`, what the consumer does there, says: the
result `res`, the version `ver'` in force after it, where the lexer discards from after it (`d'`),
and the tokens taken (`coll'`). Before it, the tokens `coll` were taken under the version `ver`,
and the lexer discarded from `d0`. `fl` is the failure of finishing the token in progress, if it
fails. -/
def EofRes (C : BSmtLibSpec.Lexer.Consumer) (o : Option (HandOut C × Option Span.Location))
    (d0 : Option Span.Location) (ver : Version) (coll : List Handed)
    (location : Span.Location) (fl : LexFailure)
    (res : Except (PFailure C.Error) (ControlFlow (Span.Located C.Result)))
    (ver' : Version)
    (d' : Option Span.Location) (coll' : List Handed) : Prop :=
  match o with
  | none => res = .error (.lexical, some (fl.kind, fl.span)) ∧ ver' = ver ∧ d' = d0 ∧ coll' = coll
  | some (h, d) => EofTail C h d d0 location res ver' d' coll'

/-- What two ends of the input that satisfy `EofRes` for the same `o` give alike: the same
result, the same tokens taken, and after an error, the same version and discarding. -/
theorem eofRes_unique {C : BSmtLibSpec.Lexer.Consumer}
    {o : Option (HandOut C × Option Span.Location)}
    {d0 : Option Span.Location} {ver : Version} {coll : List Handed}
    {location : Span.Location} {fl : LexFailure}
    {res₁ res₂ : Except (PFailure C.Error) (ControlFlow (Span.Located C.Result))}
    {ver₁ ver₂ : Version} {d₁ d₂ : Option Span.Location} {coll₁ coll₂ : List Handed}
    (h₁ : EofRes C o d0 ver coll location fl res₁ ver₁ d₁ coll₁)
    (h₂ : EofRes C o d0 ver coll location fl res₂ ver₂ d₂ coll₂) :
    res₁ = res₂ ∧ coll₁ = coll₂ ∧ (res₁.isOk = false → ver₁ = ver₂ ∧ d₁ = d₂) := by
  unfold EofRes EofTail at h₁ h₂
  rcases o with _ | ⟨h, d⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h₁
    obtain ⟨b1, b2, b3, b4⟩ := h₂
    exact ⟨a1.trans b1.symm, a4.trans b4.symm, fun _ => ⟨a2.trans b2.symm, a3.trans b3.symm⟩⟩
  · rcases h with p | ⟨r, l, p⟩ | ⟨s, p⟩
    · exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm, fun hn => by rw [h₁.1] at hn; cases hn⟩
    · exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm, fun hn => by rw [h₁.1] at hn; cases hn⟩
    · cases s with
      | brkX r l =>
        exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm, fun hn => by rw [h₁.1] at hn; cases hn⟩
      | discard r l =>
        cases r with
        | some r =>
          exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm,
            fun hn => by rw [h₁.1] at hn; cases hn⟩
        | none =>
          exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm,
            fun hn => by rw [h₁.1] at hn; cases hn⟩
      | relex l =>
        exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm, fun hn => by rw [h₁.1] at hn; cases hn⟩
      | brk r l nx => exact h₁.elim
      | trailing l =>
        obtain ⟨a1, a2, a3, a4⟩ := h₁
        obtain ⟨b1, b2, b3, b4⟩ := h₂
        exact ⟨a1.trans b1.symm, a4.trans b4.symm, fun _ => ⟨a2.trans b2.symm, a3.trans b3.symm⟩⟩
      | fail e dd l =>
        obtain ⟨a1, a2, a3, a4⟩ := h₁
        obtain ⟨b1, b2, b3, b4⟩ := h₂
        exact ⟨a1.trans b1.symm, a4.trans b4.symm, fun _ => ⟨a2.trans b2.symm, a3.trans b3.symm⟩⟩
      | layout l =>
        obtain ⟨a1, a2, a3, a4⟩ := h₁
        obtain ⟨b1, b2, b3, b4⟩ := h₂
        exact ⟨a1.trans b1.symm, a4.trans b4.symm, fun _ => ⟨a2.trans b2.symm, a3.trans b3.symm⟩⟩

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel
