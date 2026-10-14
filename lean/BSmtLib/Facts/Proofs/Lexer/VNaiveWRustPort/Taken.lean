import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel
import BSmtLib.Facts.Proofs.Lexer.Consumers.Pure

/-!
# No whitespace or comment for a consumer that does not take them

For a consumer that does not take whitespace and comments, the naive lexer's pure run finishes
only lexemes the consumer takes (`VNaive.lexBytes_taken`, `VNaive.endStep_taken`), from a state
that the Rust port's state agrees with (`st_taken`). So the consumer, handed those lexemes, never
stops at whitespace or a comment (`outcome_ne_layout`, `eofOut_ne_layout`), and the Rust port
never raises the adapter's error `none` there (`matches_none`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Taken

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix
open BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix.Lexeme BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model BSmtLib.Lexer.Internal.VNaive

variable {C : BSmtLibSpec.Lexer.Consumer}

/-- The naive lexer's pure state that the Rust port's state agrees with, for a consumer that does
not take whitespace, has no whitespace in progress. -/
theorem st_taken {v : Token.Version} {st : St} {c : WP.WCore}
    (h : StAgrees v false st c) : st.Taken := by
  cases st with
  | idle => trivial
  | token p =>
    obtain ⟨ht, -⟩ := h
    show p.mode ≠ .whitespace
    intro hm
    unfold TokenAgrees at ht
    cases hs : c.state <;> rw [hs] at ht <;>
      simp only [TokenAgreesNoWs, hm] at ht <;>
      first
        | (exact absurd ht.2.1 Bool.false_ne_true; done)
        | (obtain ⟨-, h1, -⟩ := ht; cases h1; done)
        | (obtain ⟨-, h1⟩ := ht; cases h1; done)
        | (obtain ⟨-, h1, -⟩ := ht; split at h1 <;> cases h1; done)
        | (obtain ⟨h1, -⟩ := ht; split at h1 <;> cases h1; done)
        | (obtain ⟨-, -, h1, -⟩ := ht; cases h1; done)
        | (obtain ⟨-, h1, -⟩ := ht; cases h1; done)
        | (exact ht.2; done)
        | (simp at ht; done)
        | (simp_all; done)

/-- A consumer takes every lexeme that is not whitespace or a comment. -/
theorem lexemeEntry_taken (concrete : Bool) (v : Token.Version) {l : Lexeme} (h : (Taken l)) :
    lexemeEntry concrete v l ≠ none := by
  unfold Lexeme.Taken at h
  unfold lexemeEntry lexemeHanded
  cases ht : toTokenType l.category with
  | none => rw [ht] at h; cases h
  | some type => simp

/-- A consumer that does not take whitespace and comments, handed lexemes it takes, does not
stop at whitespace or a comment. -/
theorem handAll_ne_layout (hd : Bool) :
    ∀ (ls : List Lexeme), (∀ l ∈ ls, (Taken l)) → ∀ (h : HandOut C),
      (∀ l p, h ≠ .stop (.layout l) p) → ∀ l p, handAll C hd h ls ≠ .stop (.layout l) p
  | [], _, h, hh => by simpa [handAll] using hh
  | x :: xs, hls, h, hh => by
    rw [handAll_cons]
    refine handAll_ne_layout hd xs (fun l hl => hls l (by simp [hl])) _ ?_
    intro l p heq
    have hx : (Taken x) := hls x (by simp)
    cases h with
    | stop s q =>
      simp only [hand1] at heq
      exact hh l p heq
    | wait r l0 q =>
      simp only [hand1] at heq
      cases heq
    | cont q =>
      simp only [hand1] at heq
      split at heq
      · cases heq
      · split at heq
        · rename_i hn
          exact lexemeEntry_taken C.concrete q.ver hx hn
        · repeat' split at heq
          all_goals cases heq

theorem lexBytesW_taken {v : Token.Version} {st : St} {location : Span.Location}
    {bytes : List UInt8}
    (hst : st.Taken) :
    match lexBytesW v false st location bytes with
    | .ok (_, _, ls) => ∀ l ∈ ls, (Taken l)
    | .error ls => ∀ l ∈ ls, (Taken l) := by
  have h := lexBytes_taken (version := v) bytes (location := location) hst
  rw [lexBytesW_false]
  revert h
  rcases lexBytes v st location bytes with ls | ⟨st', loc', ls⟩
  · exact id
  · exact fun h => h.2

/-- A consumer that does not take whitespace and comments, handed what the naive lexer's pure run
finishes from a state with no whitespace in progress, does not stop at whitespace or a
comment. -/
theorem outcome_ne_layout (hc : C.concrete = false) {hd : Bool} {q : Prog} {v : Token.Version}
    {st : St} (hst : st.Taken) {location : Span.Location} {bytes : List UInt8} (l : Lexeme)
    (p : Prog) :
    outcome C hd (.cont q) (lexBytesW v C.concrete st location bytes) ≠ .stopped (.layout l) p := by
  rw [hc]
  have ht := lexBytesW_taken (v := v) (location := location) (bytes := bytes) hst
  revert ht
  rcases lexBytesW v false st location bytes with ls | ⟨st', loc', ls⟩
  all_goals
    intro ht heq
    simp only [outcome] at heq
    have hne := handAll_ne_layout (C := C) hd ls ht (.cont q) (fun _ _ => nofun) l p
    generalize handAll C hd (.cont q) ls = h at heq hne
    cases h with
    | cont _ => simp [Model.finish] at heq
    | wait _ _ _ => simp [Model.finish] at heq
    | stop s q' =>
      simp only [Model.finish, Out.stopped.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact hne rfl

/-- What the end of the input finishes from a state with no whitespace in progress, for a
consumer that does not take whitespace, the consumer takes. -/
theorem finishLs_taken {st : St} {location : Span.Location} {ls : List Lexeme} (hst : st.Taken)
    (h : finishLs false st location = some ls) : ∀ l ∈ ls, (Taken l) := by
  have he : endStep st location = some (ls ++ [eofLexeme location]) := by
    cases st with
    | idle =>
      simp only [finishLs, Option.some.injEq] at h
      subst h
      rfl
    | token p =>
      simp only [finishLs] at h
      simp only [endStep]
      split at h
      · rename_i hf
        simp only [Option.some.injEq] at h
        subst h
        rw [hf]
        rfl
      · rename_i l hf
        simp only [Option.some.injEq] at h
        subst h
        rw [hf]
        rfl
      · cases h
  intro l hl
  exact endStep_taken he hst l (List.mem_append_left _ hl)

/-- A consumer that does not take whitespace and comments does not stop at whitespace or a
comment at the end of the input, from a state with no whitespace in progress. -/
theorem eofOut_ne_layout {hd : Bool} {ver : Token.Version} {coll : List Handed} {st : St}
    {location : Span.Location} (hst : st.Taken) {h : HandOut C} {d : Option Span.Location}
    (heq : eofOut C hd false ver coll st location = some (h, d)) :
    ∀ l p, h ≠ .stop (.layout l) p := by
  unfold eofOut at heq
  cases hf : finishLs false st location with
  | none => rw [hf] at heq; cases heq
  | some ls =>
    rw [hf] at heq
    simp only [Option.map_some, Option.some.injEq] at heq
    have hls := finishLs_taken hst hf
    have hp := handAll_ne_layout (C := C) hd ls hls (.cont ⟨coll, ver⟩) (fun _ _ => nofun)
    have heof : (Taken (eofLexeme location)) := rfl
    have hone : ∀ q, ∀ l p, hand1 C false (.cont q) (eofLexeme location) ≠ .stop (.layout l) p :=
      fun q => handAll_ne_layout (C := C) false [eofLexeme location] (by simpa using heof)
        (.cont q) (fun _ _ => nofun)
    unfold pending at heq
    generalize handAll C hd (.cont ⟨coll, ver⟩) ls = h0 at heq hp
    intro l p habs
    have h1 := congrArg Prod.fst heq
    simp only at h1
    rw [← h1] at habs
    unfold eofHand at habs
    split at habs
    · split at habs
      · cases habs
      · exact hone _ l p habs
    · split at habs
      · cases habs
      · exact hone _ l p habs
    · split at habs
      · cases habs
      · exact hone _ l p habs
    · simp only at habs
      rename_i h0' _ _ _
      exact hp l p habs

/-- The Rust port raises the adapter's error `none` only at a stop at whitespace or a comment. -/
theorem matches_none {floor : Option Nat} {s : Stop C} {e : WP.Intr C floor} (hm : Matches s e)
    (he : e.result = .error (.consumer none)) : ∃ l, s = .layout l := by
  cases s with
  | trailing l =>
    obtain ⟨h, -⟩ := hm
    rw [he] at h
    cases h
  | fail err d l =>
    simp only [Matches] at hm
    rw [he] at hm
    cases hm
  | layout l => exact ⟨l, rfl⟩
  | brk r l next =>
    rcases hm with ⟨h, -⟩ | ⟨l2, -, h, -⟩ <;> rw [he] at h <;> cases h
  | brkX r l =>
    obtain ⟨h, -⟩ := hm
    rw [he] at h
    cases h
  | discard r l =>
    obtain ⟨h, -⟩ := hm
    rw [he] at h
    cases h
  | relex l =>
    obtain ⟨h, -⟩ := hm
    rw [he] at h
    cases h

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Taken
