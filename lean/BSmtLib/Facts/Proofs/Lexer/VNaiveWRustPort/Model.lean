module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.WP
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes

@[expose] public section

/-!
# What the adapter's consumer does with the lexemes handed over

The adapter's consumer `Answering C` takes the lexemes handed over one at a time, and answers
as the spec's consumer `C` does. `hand1` states what becomes of one lexeme, from what the
consumer has done so far (`HandOut`): it goes on (`cont`), with the tokens it has taken and the
version in force (`Prog`); it has broken at a lexeme and waits for the next one, which is
trailing input (`wait`); or it has stopped (`stop`), and the rest of the lexemes do not matter.
While the lexer holds a result (`hd`), the next lexeme is trailing input. A switch of the version
that changes the lexical rules (between 2.0 and the later versions) stops the hand-over: the
lexemes after it are lexed again; another switch only changes the version the tokens are reported
in.

`pending` hands lexemes over from where the consumer is, and `outcome` hands over those of the
naive lexer's run over the rest of a slice (`feedFrom`) after them: what the consumer has done at
the end of the slice, or when the run fails, or where it stopped.
-/

open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Lexer.Internal.VNaive

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)

/-- What the consumer has done while it goes on: the tokens it has taken and the version in
force. -/
structure Prog where
  taken : List Handed
  ver : Token.Version

section

variable (C : BSmtLibSpec.Lexer.Consumer)

/-- Where a hand-over stops, at the lexeme `l`. -/
inductive Stop where
  /-- The lexer holds a result: the lexeme is trailing input. -/
  | trailing (l : Lexeme)
  /-- The consumer fails at the entry, having the rest discarded if `d`. -/
  | fail (e : C.Error) (d : Bool) (l : Lexeme)
  /-- A consumer that does not take whitespace and comments is handed one. -/
  | layout (l : Lexeme)
  /-- The consumer breaks at the token; `next` is the lexeme handed over after it, if any,
  which is trailing input. -/
  | brk (r : C.Result) (l : Lexeme) (next : Option Lexeme)
  /-- The consumer breaks at the token and switches to a version with other lexical rules. -/
  | brkX (r : C.Result) (l : Lexeme)
  /-- The consumer has the rest discarded after the token, breaking if `r` is a result. -/
  | discard (r : Option C.Result) (l : Lexeme)
  /-- The consumer goes on after the token and switches to a version with other lexical
  rules. -/
  | relex (l : Lexeme)

/-- What the consumer has done with the lexemes handed over so far. -/
inductive HandOut where
  | cont (p : Prog)
  | wait (r : C.Result) (l : Lexeme) (p : Prog)
  | stop (s : Stop C) (p : Prog)

/-- What the consumer has done with the lexemes of a run over the rest of a slice. -/
inductive Out where
  /-- It went on to the end of the slice, where the run is in the state at the location. -/
  | endOk (st : St) (location : Span.Location) (p : Prog)
  /-- It went on to where the run fails. -/
  | endErr (p : Prog)
  /-- It stopped. -/
  | stopped (s : Stop C) (p : Prog)

end

/-- Whether the switch from one version to the other changes the lexical rules. -/
def crosses (a b : Token.Version) : Bool := (a == .v2_0) != (b == .v2_0)

/-- The version in force after the consumer asked for `o`, if it did. -/
def switchedTo (ver : Token.Version) : Option BSmtLibSpec.Lexicon.Version → Token.Version
  | some v => toVersion v
  | none => ver

section

variable (C : BSmtLibSpec.Lexer.Consumer) (hd : Bool)

/-- What the consumer does with the lexeme, from where it is. -/
def hand1 : HandOut C → Lexeme → HandOut C
  | .stop s p, _ => .stop s p
  | .wait r l0 p, l => .stop (.brk r l0 (some l)) p
  | .cont p, l =>
    if hd then .stop (.trailing l) p else
    match lexemeEntry C.concrete p.ver l with
    | none => .stop (.layout l) p
    | some x =>
      match C.answer (p.taken ++ [x]) with
      | .fail e =>
        .stop (.fail e (C.discards (p.taken ++ [x])) l)
          ⟨p.taken ++ [x], switchedTo p.ver (C.switchTo (p.taken ++ [x]))⟩
      | .break r =>
        if C.discards (p.taken ++ [x]) then
          .stop (.discard (some r) l)
            ⟨p.taken ++ [x], switchedTo p.ver (C.switchTo (p.taken ++ [x]))⟩
        else if crosses p.ver (switchedTo p.ver (C.switchTo (p.taken ++ [x]))) then
          .stop (.brkX r l) ⟨p.taken ++ [x], switchedTo p.ver (C.switchTo (p.taken ++ [x]))⟩
        else .wait r l ⟨p.taken ++ [x], switchedTo p.ver (C.switchTo (p.taken ++ [x]))⟩
      | .continue =>
        if C.discards (p.taken ++ [x]) then
          .stop (.discard none l)
            ⟨p.taken ++ [x], switchedTo p.ver (C.switchTo (p.taken ++ [x]))⟩
        else if crosses p.ver (switchedTo p.ver (C.switchTo (p.taken ++ [x]))) then
          .stop (.relex l) ⟨p.taken ++ [x], switchedTo p.ver (C.switchTo (p.taken ++ [x]))⟩
        else .cont ⟨p.taken ++ [x], switchedTo p.ver (C.switchTo (p.taken ++ [x]))⟩

/-- What the consumer does with the lexemes, one after another, from where it is. -/
def handAll (h : HandOut C) (ls : List Lexeme) : HandOut C := ls.foldl (hand1 C hd) h

/-- What the consumer does with the lexemes, from the tokens `coll` it has taken under the
version `ver`. -/
def pending (ver : Token.Version) (coll : List Handed) (ls : List Lexeme) : HandOut C :=
  handAll C hd (.cont ⟨coll, ver⟩) ls

/-- What the consumer has done at the end of a run, from where it was. -/
def finish : HandOut C → (Prog → Out C) → Out C
  | .cont p, k => k p
  | .wait r l p, _ => .stopped (.brk r l none) p
  | .stop s p, _ => .stopped s p

/-- What the consumer does with the lexemes of the run over the rest of a slice, from where it
is: what it has done at the end of the slice, or where the run fails, or where it stopped. -/
def outcome (h : HandOut C) : Except (List Lexeme) (St × Span.Location × List Lexeme) → Out C
  | .ok (st, location, ls) => finish C (handAll C hd h ls) (.endOk st location)
  | .error ls => finish C (handAll C hd h ls) .endErr

theorem handAll_nil (h : HandOut C) : handAll C hd h [] = h := rfl

theorem handAll_append (h : HandOut C) (xs ys : List Lexeme) :
    handAll C hd h (xs ++ ys) = handAll C hd (handAll C hd h xs) ys := by
  simp [handAll, List.foldl_append]

theorem handAll_cons (h : HandOut C) (l : Lexeme) (ls : List Lexeme) :
    handAll C hd h (l :: ls) = handAll C hd (hand1 C hd h l) ls := rfl

theorem handAll_stop (s : Stop C) (p : Prog) : ∀ ls, handAll C hd (.stop s p) ls = .stop s p
  | [] => rfl
  | _ :: ls => handAll_stop s p ls

theorem pending_nil (ver : Token.Version) (coll : List Handed) :
    pending C hd ver coll [] = .cont ⟨coll, ver⟩ := rfl

theorem pending_append (ver : Token.Version) (coll : List Handed) (xs ys : List Lexeme) :
    pending C hd ver coll (xs ++ ys) = handAll C hd (pending C hd ver coll xs) ys :=
  handAll_append C hd _ xs ys

/-- What the consumer does after lexemes depends only on where it is after them. -/
theorem pending_congr_append {ver ver' : Token.Version} {c₁ c₂ : List Handed} {xs ys : List Lexeme}
    (h : pending C hd ver c₁ xs = pending C hd ver' c₂ ys) (zs : List Lexeme) :
    pending C hd ver c₁ (xs ++ zs) = pending C hd ver' c₂ (ys ++ zs) := by
  rw [pending_append, pending_append, h]

theorem pending_stop_append {ver : Token.Version} {coll : List Handed} {xs : List Lexeme}
    {s : Stop C}
    {p : Prog} (h : pending C hd ver coll xs = .stop s p) (ys : List Lexeme) :
    pending C hd ver coll (xs ++ ys) = .stop s p := by
  rw [pending_append, h, handAll_stop]

/-- Lexemes moved from the run to those handed over before it. -/
theorem outcome_prep (h : HandOut C) (held ls : List Lexeme)
    (e : Except (List Lexeme) (St × Span.Location × List Lexeme)) :
    outcome C hd (handAll C hd h held) (Prep ls e) =
      outcome C hd (handAll C hd h (held ++ ls)) e := by
  cases e with
  | ok e =>
    obtain ⟨st, location, ls'⟩ := e
    simp only [outcome, Prep, withBefore, handAll_append]
  | error ls' =>
    simp only [outcome, Prep, withBefore, handAll_append]

theorem outcome_pending_prep (ver : Token.Version) (coll : List Handed) (held ls : List Lexeme)
    (e : Except (List Lexeme) (St × Span.Location × List Lexeme)) :
    outcome C hd (pending C hd ver coll held) (Prep ls e) =
      outcome C hd (pending C hd ver coll (held ++ ls)) e :=
  outcome_prep C hd _ held ls e

/-- A run that stopped stays stopped. -/
theorem outcome_stop (s : Stop C) (p : Prog)
    (e : Except (List Lexeme) (St × Span.Location × List Lexeme)) :
    outcome C hd (.stop s p) e = .stopped s p := by
  cases e with
  | ok e => obtain ⟨st, location, ls⟩ := e; simp only [outcome, handAll_stop, finish]
  | error ls => simp only [outcome, handAll_stop, finish]

/-- A run that fails at once leaves the consumer where it is. -/
theorem outcome_error_nil (h : HandOut C) :
    outcome C hd h (.error []) = finish C h .endErr := rfl

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model

open BSmtLib.Facts.Lexer.Adapters

/-- The lexeme a hand-over stopped at. -/
def Stop.lex {C : BSmtLibSpec.Lexer.Consumer} : Stop C → Lexeme
  | .trailing l | .fail _ _ l | .layout l | .brk _ l _ | .brkX _ l | .discard _ l | .relex l => l

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model

/-- Where the lexer discards from after the stop, if the stop makes it discard though it does
not go on: a failure of the consumer at an entry where it had the rest discarded. -/
def Stop.discards {C : BSmtLibSpec.Lexer.Consumer} : Stop C → Option Span.Location
  | .fail _ true l => some l.end
  | _ => none

/-- Where the lexer discards from, after it discarded from `x`, if it did, and the consumer
stopped making it discard from `d`, if it did: from where it began. -/
def discardsAfter (x d : Option Span.Location) : Option Span.Location :=
  match d with
  | none => x
  | some location => x.or (some location)

theorem discardsAfter_none (d : Option Span.Location) : discardsAfter none d = d := by
  cases d <;> rfl

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
