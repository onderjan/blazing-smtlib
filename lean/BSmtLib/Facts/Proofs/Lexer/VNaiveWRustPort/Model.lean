module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.WP
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes

@[expose] public section

/-!
# What the adapter's consumer does with the lexemes handed over

The adapter's consumer `Answering C` takes the lexemes handed over one at a time, and answers as the
consumer `C` of the specification formalism (`BSmtLibSpec`) does. `hand1` states what becomes of one
lexeme, from what the consumer has done so far (`HandOut`): it goes on (`cont`), with the tokens it
has taken and the version in force (`Prog`); it has broken at a lexeme and waits for the next one,
which is trailing input (`wait`); or it has stopped (`stop`), and the rest of the lexemes do not
matter. While the lexer holds a result (`hd`), the next lexeme is trailing input. A version switch
that changes the lexical rules (between 2.0 and the later versions) stops the hand-over: the lexemes
after it are lexed again; another switch only changes the version the tokens are reported in.

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
  ver : Version

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
  /-- It went on to where the run fails, with the failure. -/
  | endErr (f : LexFailure) (p : Prog)
  /-- It stopped. -/
  | stopped (s : Stop C) (p : Prog)

end

/-- Whether the switch from one version to the other changes the lexical rules. -/
def crosses (a b : Version) : Bool := (a == .v2_0) != (b == .v2_0)

/-- The version in force after the consumer asked for `o`, if it did. -/
def switchedTo (ver : Version) : Option BSmtLibSpec.Lexicon.Version → Version
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
def pending (ver : Version) (coll : List Handed) (ls : List Lexeme) : HandOut C :=
  handAll C hd (.cont ⟨coll, ver⟩) ls

/-- What the consumer has done at the end of a run, from where it was. -/
def finish : HandOut C → (Prog → Out C) → Out C
  | .cont p, k => k p
  | .wait r l p, _ => .stopped (.brk r l none) p
  | .stop s p, _ => .stopped s p

/-- What the consumer does with the lexemes of the run over the rest of a slice, from where it
is: what it has done at the end of the slice, or where the run fails, or where it stopped. -/
def outcome (h : HandOut C) : Consumers.Pure.RunF → Out C
  | .ok (st, location, ls) => finish C (handAll C hd h ls) (.endOk st location)
  | .error (ls, f) => finish C (handAll C hd h ls) (.endErr f)

theorem handAll_nil (h : HandOut C) : handAll C hd h [] = h := rfl

theorem handAll_append (h : HandOut C) (xs ys : List Lexeme) :
    handAll C hd h (xs ++ ys) = handAll C hd (handAll C hd h xs) ys := by
  simp [handAll, List.foldl_append]

theorem handAll_cons (h : HandOut C) (l : Lexeme) (ls : List Lexeme) :
    handAll C hd h (l :: ls) = handAll C hd (hand1 C hd h l) ls := rfl

theorem handAll_stop (s : Stop C) (p : Prog) : ∀ ls, handAll C hd (.stop s p) ls = .stop s p
  | [] => rfl
  | _ :: ls => handAll_stop s p ls

theorem pending_nil (ver : Version) (coll : List Handed) :
    pending C hd ver coll [] = .cont ⟨coll, ver⟩ := rfl

theorem pending_append (ver : Version) (coll : List Handed) (xs ys : List Lexeme) :
    pending C hd ver coll (xs ++ ys) = handAll C hd (pending C hd ver coll xs) ys :=
  handAll_append C hd _ xs ys

/-- What the consumer does after lexemes depends only on where it is after them. -/
theorem pending_congr_append {ver ver' : Version} {c₁ c₂ : List Handed} {xs ys : List Lexeme}
    (h : pending C hd ver c₁ xs = pending C hd ver' c₂ ys) (zs : List Lexeme) :
    pending C hd ver c₁ (xs ++ zs) = pending C hd ver' c₂ (ys ++ zs) := by
  rw [pending_append, pending_append, h]

theorem pending_stop_append {ver : Version} {coll : List Handed} {xs : List Lexeme}
    {s : Stop C}
    {p : Prog} (h : pending C hd ver coll xs = .stop s p) (ys : List Lexeme) :
    pending C hd ver coll (xs ++ ys) = .stop s p := by
  rw [pending_append, h, handAll_stop]

/-- Lexemes moved from the run to those handed over before it. -/
theorem outcome_prep (h : HandOut C) (held ls : List Lexeme)
    (e : Consumers.Pure.RunF) :
    outcome C hd (handAll C hd h held) (Prep ls e) =
      outcome C hd (handAll C hd h (held ++ ls)) e := by
  cases e with
  | ok e =>
    obtain ⟨st, location, ls'⟩ := e
    simp only [outcome, Prep, Consumers.Pure.withBeforeF, handAll_append]
  | error r =>
    obtain ⟨ls', f⟩ := r
    simp only [outcome, Prep, Consumers.Pure.withBeforeF, handAll_append]

theorem outcome_pending_prep (ver : Version) (coll : List Handed) (held ls : List Lexeme)
    (e : Consumers.Pure.RunF) :
    outcome C hd (pending C hd ver coll held) (Prep ls e) =
      outcome C hd (pending C hd ver coll (held ++ ls)) e :=
  outcome_prep C hd _ held ls e

/-- A run that stopped stays stopped. -/
theorem outcome_stop (s : Stop C) (p : Prog)
    (e : Consumers.Pure.RunF) :
    outcome C hd (.stop s p) e = .stopped s p := by
  cases e with
  | ok e => obtain ⟨st, location, ls⟩ := e; simp only [outcome, handAll_stop, finish]
  | error r => obtain ⟨ls, f⟩ := r; simp only [outcome, handAll_stop, finish]

/-- A run that fails at once leaves the consumer where it is. -/
theorem outcome_error_nil (h : HandOut C) (f : LexFailure) :
    outcome C hd h (.error ([], f)) = finish C h (.endErr f) := rfl

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

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model

open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run

/-! ## The token a consumer fails at is the last it took -/

section

variable (C : BSmtLibSpec.Lexer.Consumer) (hd : Bool)

/-- Where the consumer has stopped by failing at a lexeme, the last token it took is that
lexeme's. -/
def FailTaken (h : HandOut C) : Prop :=
  ∀ e d l p, h = .stop (.fail e d l) p →
    ∃ x, p.taken.getLast? = some x ∧ x.start = toLocation l.start ∧ x.end = toLocation l.end

/-- Where the consumer has stopped by failing at a lexeme, the last token it took is that
lexeme's. -/
def OutFailTaken (o : Out C) : Prop :=
  ∀ e d l p, o = .stopped (.fail e d l) p →
    ∃ x, p.taken.getLast? = some x ∧ x.start = toLocation l.start ∧ x.end = toLocation l.end

theorem lexemeEntry_locs {concrete : Bool} {version : Version} {l : Lexeme}
    {x : BSmtLibSpec.Lexer.Handed} (h : lexemeEntry concrete version l = some x) :
    x.start = toLocation l.start ∧ x.end = toLocation l.end := by
  unfold lexemeEntry lexemeHanded at h
  cases ht : toTokenType l.category with
  | some t =>
    simp only [ht, Option.map_some] at h
    cases h
    exact ⟨rfl, rfl⟩
  | none =>
    simp only [ht, Option.map_none] at h
    cases hc : concrete
    · simp only [hc, Bool.false_eq_true, ite_false] at h
      cases h
    · simp only [hc, ite_true, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩

theorem failTaken_cont (p : Prog) : FailTaken C (.cont p) := fun _ _ _ _ h => by cases h

theorem hand1_failTaken {h : HandOut C} (hf : FailTaken C h) (l : Lexeme) :
    FailTaken C (hand1 C hd h l) := by
  intro e d l' p hs
  cases h with
  | stop s p₀ => exact hf e d l' p hs
  | wait r l0 p₀ => cases hs
  | cont p₀ =>
    cases hhd : hd
    · cases hx : lexemeEntry C.concrete p₀.ver l with
      | none => simp [hand1, hhd, hx] at hs
      | some x =>
        cases ha : C.answer (p₀.taken ++ [x]) with
        | fail e' =>
          simp only [hand1, hhd, hx, ha, Bool.false_eq_true, ite_false, HandOut.stop.injEq,
            Stop.fail.injEq] at hs
          obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hs
          exact ⟨x, by simp, lexemeEntry_locs hx⟩
        | «break» r =>
          simp only [hand1, hhd, hx, ha, Bool.false_eq_true, ite_false] at hs
          repeat' split at hs
          all_goals cases hs
        | «continue» =>
          simp only [hand1, hhd, hx, ha, Bool.false_eq_true, ite_false] at hs
          repeat' split at hs
          all_goals cases hs
    · simp [hand1, hhd] at hs

theorem handAll_failTaken : ∀ (ls : List Lexeme) {h : HandOut C}, FailTaken C h →
    FailTaken C (handAll C hd h ls)
  | [], _, hf => hf
  | l :: ls, _, hf => handAll_failTaken ls (hand1_failTaken C hd hf l)

theorem outcome_failTaken {h : HandOut C} (hf : FailTaken C h) (r : Consumers.Pure.RunF) :
    OutFailTaken C (outcome C hd h r) := by
  intro e d l p ho
  have key : ∀ (ls : List Lexeme) (k : Prog → Out C),
      finish C (handAll C hd h ls) k = .stopped (.fail e d l) p →
      (∀ p', k p' ≠ .stopped (.fail e d l) p) →
      ∃ x, p.taken.getLast? = some x ∧ x.start = toLocation l.start ∧ x.end = toLocation l.end := by
    intro ls k hfin hk
    have hall := handAll_failTaken C hd ls hf
    generalize handAll C hd h ls = H at hall hfin
    cases H with
    | cont p' => exact absurd hfin (hk p')
    | wait r l0 p' => cases hfin
    | stop s p' =>
      cases hfin
      exact hall e d l p rfl
  cases r with
  | ok v =>
    obtain ⟨st, location, ls⟩ := v
    exact key ls _ ho (fun _ h' => by cases h')
  | error v =>
    obtain ⟨ls, f⟩ := v
    exact key ls _ ho (fun _ h' => by cases h')

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
