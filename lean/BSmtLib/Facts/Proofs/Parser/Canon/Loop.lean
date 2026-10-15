module

public import BSmtLib.Facts.Proofs.Parser.Canon.Commands
public import BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
public import BSmtLib.Facts.Proofs.Reader.Param.Adapter
public import BSmtLib.Facts.Proofs.Parser.HandOver
import all BSmtLib.Parser
import all BSmtLib.Plain
import all BSmtLib.Token
import all BSmtLib.Token.SyntaxToken
import all BSmtLib.Token.Produce
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# The script parser's loop over cursors that agree

Two cursors that agree (`Batch.CursorAgree`) hold the same tokens, with contents in different
storage. The script parser views the tokens of each as inputs whose canonicalisations are the
same (`canon_syntax`), and its steps on canonically equal states and inputs give canonically
equal results (`Commands`), so its loop over the two cursors from canonically equal parsers gives
the same answer and log, canonically equal parsers, and cursors that agree again
(`parseByToken_agree`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Canon.Loop

open BSmtLib.Parser BSmtLib.Nodes
open BSmtLib.Plain (SymbolView NumeralView DecimalView HexDigitsView BinDigitsView
  StringContentView KeywordView)
open Basic States Simp
open BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
open BSmtLib.Token.BatchCursor.Internal (remaining)

/-! ## The inputs a cursor views -/

theorem canonSlice_canonSlice (s : ByteSlice) : canonSlice (canonSlice s) = canonSlice s := by
  show (canonSlice s).toByteArray.toByteSlice = _
  rw [toByteArray_canonSlice]
  rfl

/-- What a token's category and content stand for, canonicalised, reads its content only as
bytes. -/
theorem canonInput_fromParts (category : Token.TokenCategory) (content : ByteSlice)
    (version : Token.Version) :
    canonInput (Internal.Input.ofSyntax
        (Token.SyntaxToken.Internal.fromParts category content version)) =
      canonInput (Internal.Input.ofSyntax
        (Token.SyntaxToken.Internal.fromParts category (canonSlice content) version)) := by
  have hr : Token.Reserved.fromBytes? (canonSlice content) version =
      Token.Reserved.fromBytes? content version :=
    BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes.fromBytes_toByteArray content version
  cases category <;>
    simp only [Token.SyntaxToken.Internal.fromParts, Internal.Input.ofSyntax, canonInput,
      Canon.canon, canonConstant, canonSymbol, canon_simps, canonSlice_canonSlice]
  all_goals first
    | rfl
    | (rw [hr]
       cases Token.Reserved.fromBytes? content version <;>
         simp only [canon_simps, canonSlice_canonSlice])

variable {g g' : Token.BatchTag}

/-- Two cursors that agree view tokens at the same index as inputs with the same
canonicalisation. -/
theorem canon_syntax {c : Token.BatchCursor g} {d : Token.BatchCursor g'} (h : CursorAgree c d)
    {t : BSmtLib.Token g} {t' : BSmtLib.Token g'} (et : tokenIndex t = tokenIndex t')
    (ht : tokenIndex t < (BSmtLib.Lexer.Internal.intoBatch c).len) :
    canonInput (Internal.Input.ofSyntax (c.syntax t)) =
      canonInput (Internal.Input.ofSyntax (d.syntax t')) := by
  unfold Token.BatchCursor.syntax Token.SyntaxToken.fromToken
  rw [canonInput_fromParts, canonInput_fromParts (d.category t'), h.category et ht, h.version]
  have hc : canonSlice (c.content t) = canonSlice (d.content t') := by
    show (c.content t).toByteArray.toByteSlice = (d.content t').toByteArray.toByteSlice
    rw [h.content et ht]
  rw [hc]

/-! ## The actions on agreeing cursors -/

theorem CursorAgree.setVersion {c : Token.BatchCursor g} {d : Token.BatchCursor g'}
    (h : CursorAgree c d) (v : Token.Version) {c' : Token.BatchCursor g}
    {d' : Token.BatchCursor g'} (hc : c.setVersion v = .ok c') (hd : d.setVersion v = .ok d') :
    CursorAgree c' d' := by
  have hv := h.version
  unfold Token.BatchCursor.setVersion at hc hd
  injection hc with hc
  injection hd with hd
  subst hc hd
  rw [hv]
  by_cases hrx : ((d.version == Token.Version.v2_0) != (v == .v2_0)) = true
  · simp only [hrx, ite_true]
    refine ⟨rfl, ?_, h.first, h.next, h.next, rfl, h.discard, ?_⟩
    · rw [intoBatch_eq _ c, intoBatch_eq _ d]; exact h.batch
    · rw [intoBatch_eq _ c]
      exact Nat.le_trans (cNext_le_cStop c) h.bounded
  · simp only [hrx, Bool.false_eq_true, ite_false]
    refine ⟨rfl, ?_, h.first, h.stop, h.next, h.relex, h.discard, ?_⟩
    · rw [intoBatch_eq _ c, intoBatch_eq _ d]; exact h.batch
    · rw [intoBatch_eq _ c]; exact h.bounded

theorem CursorAgree.discardRest {c : Token.BatchCursor g} {d : Token.BatchCursor g'}
    (h : CursorAgree c d) : CursorAgree c.discardRest d.discardRest := by
  refine ⟨h.version, ?_, h.first, h.next, h.next, h.relex, rfl, ?_⟩
  · rw [intoBatch_eq _ c, intoBatch_eq _ d]; exact h.batch
  · rw [intoBatch_eq _ c]
    exact Nat.le_trans (cNext_le_cStop c) h.bounded

/-! ## The steps of the script parser on canonically equal arguments -/

open BSmtLib.Parser.Script
open BSmtLibSpec.Parser.Properties (Event)
open BSmtLib.Facts.Proofs.Parser.Quiet (RPM)
open BSmtLib.Facts.Proofs.Parser.Canon.Commands
open BSmtLib.Facts.Proofs.Reader.Param.Adapter (id_bind_eq)
open BSmtLib.Facts.Proofs.Parser.HandOver (recording_noHandOver rest_of_none
  parseByToken_of_none)

/-- Two runs related to the same run by `CSim` give canonically equal results and the same
log. -/
theorem CSim.agree {α : Type} [Canon α] {x x' y : RPM α} (h : CSim x y) (h' : CSim x' y)
    (log : List Event) :
    (x.run.run log).1.map canon = (x'.run.run log).1.map canon ∧
      (x.run.run log).2 = (x'.run.run log).2 := by
  have e := h.run log
  have e' := h'.run log
  rw [e] at e'
  exact ⟨congrArg Prod.fst e', congrArg (fun p => p.2) e'⟩

/-- A token's arrival at the script parser and its step, canonicalised. -/
theorem block_canon (version : Token.Version) (parser : ScriptParser (List Event))
    (input : Internal.Input) :
    CSim (do Internal.ParseByToken.arrive parser input
             Internal.ParseByToken.step version parser input)
      (do Internal.ParseByToken.arrive (canon parser) (canon input)
          Internal.ParseByToken.step version (canon parser) (canon input)) :=
  CSim.bind (ScriptParser_arrive_canon rfl rfl) fun _ => ScriptParser_step_canon rfl rfl

/-- The arrival of a token at the script parser, then its step. -/
abbrev block (version : Token.Version) (parser : ScriptParser (List Event))
    (input : Internal.Input) :
    RPM (Internal.Flow RPM (ScriptParser (List Event)) Unit) :=
  Internal.ParseByToken.arrive parser input >>= fun _ =>
    Internal.ParseByToken.step version parser input

/-- The arrival and step of canonically equal parsers at canonically equal inputs give
canonically equal results and the same log. -/
theorem block_agree (version : Token.Version) {p₁ p₂ : ScriptParser (List Event)}
    (hp : canon p₁ = canon p₂) {i₁ i₂ : Internal.Input} (hi : canonInput i₁ = canonInput i₂)
    (log : List Event) :
    ((block version p₁ i₁).run.run log).1.map canon =
        ((block version p₂ i₂).run.run log).1.map canon ∧
      ((block version p₁ i₁).run.run log).2 = ((block version p₂ i₂).run.run log).2 := by
  have h₂ := block_canon version p₂ i₂
  rw [← hp, show (canon i₂ : Internal.Input) = canon i₁ from hi.symm] at h₂
  exact CSim.agree (block_canon version p₁ i₁) h₂ log

/-- A run of an action mapped by a function. -/
theorem run_map {α β : Type} (f : α → β) (x : RPM α) (log : List Event) :
    ((f <$> x).run.run log) = ((x.run.run log).1.map f, (x.run.run log).2) := by
  simp only [ExceptT.run_map, StateT.run_map]
  rcases x.run.run log with ⟨_ | _, _⟩ <;> rfl

/-- What the parser did with the token, on the two sides: going on with canonically equal
parsers, or stopping with the same answer and parser. -/
def AfterRel : Internal.After (ScriptParser (List Event)) Unit Unit →
    Internal.After (ScriptParser (List Event)) Unit Unit → Prop
  | .goOn p₁, .goOn p₂ => canon p₁ = canon p₂
  | .stop a₁ p₁, .stop a₂ p₂ => a₁ = a₂ ∧ p₁ = p₂
  | _, _ => False

theorem reset_eq {p₁ p₂ : ScriptParser (List Event)} (hp : canon p₁ = canon p₂) :
    Internal.ParseByToken.reset p₁ = Internal.ParseByToken.reset p₂ := by
  have h : ScriptParser.Internal.posture (canon p₁) = ScriptParser.Internal.posture (canon p₂) :=
    congrArg ScriptParser.Internal.posture hp
  show (ScriptParser.new (ScriptParser.Internal.posture p₁) : type_of% p₁) =
    ScriptParser.new (ScriptParser.Internal.posture p₂)
  rw [show ScriptParser.Internal.posture p₁ = ScriptParser.Internal.posture p₂ from h]

theorem resumed_rel {p₁ p₂ : ScriptParser (List Event)} (hp : canon p₁ = canon p₂)
    {s₁ s₂ : Internal.Step (ScriptParser (List Event)) Unit} (hs : canon s₁ = canon s₂) :
    AfterRel (Internal.resumed (E := Unit) (Internal.ParseByToken.reset p₁) s₁)
      (Internal.resumed (Internal.ParseByToken.reset p₂) s₂) := by
  cases s₁ <;> cases s₂ <;>
    simp only [Canon.canon, canonStep, Internal.Step.more.injEq, reduceCtorEq] at hs
  · exact hs
  · exact ⟨rfl, reset_eq hp⟩

/-! ## Relations between cursors -/

/-- A relation between cursors that the script parser cannot tell apart: related cursors have
the same version and whether a token remains, view their next tokens as canonically equal
inputs and leave related cursors after them, and stay related through the actions of a step. -/
structure CursorRel (Rel : Token.BatchCursor g → Token.BatchCursor g' → Prop) : Prop where
  version : ∀ {c d}, Rel c d → c.version = d.version
  hasNext : ∀ {c d}, Rel c d → (c.HasNext ↔ d.HasNext)
  next : ∀ {c d}, Rel c d → ∀ (hc : c.HasNext) (hd : d.HasNext),
    Rel (c.next hc).2.1 (d.next hd).2.1 ∧
      canonInput (Internal.Input.ofSyntax ((c.next hc).2.1.syntax (c.next hc).1)) =
        canonInput (Internal.Input.ofSyntax ((d.next hd).2.1.syntax (d.next hd).1))
  setVersion : ∀ {c d}, Rel c d → ∀ (v : Token.Version) {c' d'}, c.setVersion v = .ok c' →
    d.setVersion v = .ok d' → Rel c' d'
  discardRest : ∀ {c d}, Rel c d → Rel c.discardRest d.discardRest

/-- The token a cursor yields next lies below the length of its batch. -/
theorem index_lt_len {c : Token.BatchCursor g} {c' : Token.BatchCursor g'} (h : CursorAgree c c')
    (hc : c.HasNext) :
    tokenIndex (c.next hc).1 < (BSmtLib.Lexer.Internal.intoBatch (c.next hc).2.1).len := by
  rw [tokenIndex_next, intoBatch_eq _ c]
  exact Nat.lt_of_lt_of_le ((hasNext_iff c).mp hc) h.bounded

/-- Cursors that agree. -/
theorem cursorRel_agree : CursorRel (CursorAgree (g := g) (g' := g')) where
  version h := h.version
  hasNext h := h.hasNext_iff
  next h hc hd := by
    obtain ⟨et, hn⟩ := h.takeNext hc hd
    exact ⟨hn, canon_syntax hn et (index_lt_len h hc)⟩
  setVersion h v _ _ hc hd := CursorAgree.setVersion h v hc hd
  discardRest h := CursorAgree.discardRest h

/-- The same cursor. -/
theorem cursorRel_eq : CursorRel (fun (c d : Token.BatchCursor g) => c = d) where
  version h := by rw [h]
  hasNext h := by rw [h]
  next h hc hd := by subst h; exact ⟨rfl, rfl⟩
  setVersion h v _ _ hc hd := by subst h; rw [hc] at hd; cases hd; rfl
  discardRest h := by rw [h]

/-! ## A token taken by the script parser from cursors that agree -/

variable {Rel : Token.BatchCursor g → Token.BatchCursor g' → Prop}

theorem takeOne_agree {p₁ p₂ : ScriptParser (List Event)} (hp : canon p₁ = canon p₂)
    {c₁ n₁ : Token.BatchCursor g} {c₂ n₂ : Token.BatchCursor g'} {t₁ : BSmtLib.Token g}
    {t₂ : BSmtLib.Token g'} (k₁ : Token.Produce.Consumed n₁ c₁)
    (k₂ : Token.Produce.Consumed n₂ c₂) (hR : CursorRel Rel) (hn : Rel n₁ n₂)
    (hi : canonInput (Internal.Input.ofSyntax (n₁.syntax t₁)) =
      canonInput (Internal.Input.ofSyntax (n₂.syntax t₂)))
    (log : List Event) :
    AfterRel ((Internal.takeOne p₁ c₁ t₁ n₁ k₁).run log).1.1
        ((Internal.takeOne p₂ c₂ t₂ n₂ k₂).run log).1.1 ∧
      Rel ((Internal.takeOne p₁ c₁ t₁ n₁ k₁).run log).1.2.val
        ((Internal.takeOne p₂ c₂ t₂ n₂ k₂).run log).1.2.val ∧
      ((Internal.takeOne p₁ c₁ t₁ n₁ k₁).run log).2 =
        ((Internal.takeOne p₂ c₂ t₂ n₂ k₂).run log).2 := by
  have hv : Token.Produce.version n₁ = Token.Produce.version n₂ := hR.version hn
  obtain ⟨hb1, hb2⟩ := block_agree (Token.Produce.version n₂) hp hi log
  unfold Internal.takeOne
  simp only [StateT.run_bind, id_bind_eq]
  rw [hv]
  generalize ((block (Token.Produce.version n₂) p₁
    (Internal.Input.ofSyntax (n₁.syntax t₁))).run.run log) = R₁ at hb1 hb2 ⊢
  generalize ((block (Token.Produce.version n₂) p₂
    (Internal.Input.ofSyntax (n₂.syntax t₂))).run.run log) = R₂ at hb1 hb2 ⊢
  obtain ⟨r₁, l₁⟩ := R₁
  obtain ⟨r₂, l₂⟩ := R₂
  dsimp only at hb1 hb2 ⊢
  subst hb2
  rcases r₁ with e₁ | f₁ <;> rcases r₂ with e₂ | f₂ <;>
    simp only [Except.map, reduceCtorEq, Except.error.injEq, Except.ok.injEq] at hb1
  · subst hb1
    exact ⟨⟨rfl, reset_eq hp⟩, hn, rfl⟩
  · cases f₁ <;> cases f₂ <;>
      simp only [Canon.canon, canonFlow, reduceCtorEq, Internal.Flow.more.injEq,
        Internal.Flow.switchVersion.injEq,
        Internal.Flow.discardRest.injEq] at hb1
    · exact ⟨hb1, hn, rfl⟩
    · exact ⟨⟨rfl, reset_eq hp⟩, hn, rfl⟩
    · obtain ⟨rfl, hres⟩ := hb1
      rename_i v resume₁ resume₂
      have hm := run_map canonStep resume₁ l₁
      rw [hres, run_map] at hm
      dsimp only
      split
      · rename_i heq
        simp [Token.Produce.setVersion, Token.BatchCursor.setVersion] at heq
      · rename_i s₁ hs₁
        split
        · rename_i heq
          simp [Token.Produce.setVersion, Token.BatchCursor.setVersion] at heq
        · rename_i s₂ hs₂
          have hag := hR.setVersion hn v hs₁ hs₂
          simp only [StateT.run_bind, id_bind_eq]
          generalize resume₁.run.run l₁ = S₁ at hm ⊢
          generalize resume₂.run.run l₁ = S₂ at hm ⊢
          obtain ⟨u₁, m₁⟩ := S₁
          obtain ⟨u₂, m₂⟩ := S₂
          have hu := (congrArg Prod.fst hm).symm
          have hl : m₁ = m₂ := (congrArg Prod.snd hm).symm
          dsimp only at hu
          subst hl
          rcases u₁ with e₁ | w₁ <;> rcases u₂ with e₂ | w₂ <;>
            simp only [Except.map, reduceCtorEq, Except.error.injEq, Except.ok.injEq] at hu
          · subst hu
            exact ⟨⟨rfl, reset_eq hp⟩, hag, rfl⟩
          · exact ⟨resumed_rel hp hu, hag, rfl⟩
    · rename_i resume₁ resume₂
      have hres := hb1
      have hm := run_map canonStep resume₁ l₁
      rw [hres, run_map] at hm
      dsimp only
      simp only [StateT.run_bind, id_bind_eq]
      have hag := hR.discardRest hn
      generalize resume₁.run.run l₁ = S₁ at hm ⊢
      generalize resume₂.run.run l₁ = S₂ at hm ⊢
      obtain ⟨u₁, m₁⟩ := S₁
      obtain ⟨u₂, m₂⟩ := S₂
      have hu := (congrArg Prod.fst hm).symm
      have hl : m₁ = m₂ := (congrArg Prod.snd hm).symm
      dsimp only at hu
      subst hl
      rcases u₁ with e₁ | w₁ <;> rcases u₂ with e₂ | w₂ <;>
        simp only [Except.map, reduceCtorEq, Except.error.injEq, Except.ok.injEq] at hu
      · subst hu
        exact ⟨⟨rfl, reset_eq hp⟩, hag, rfl⟩
      · exact ⟨resumed_rel hp hu, hag, rfl⟩

/-! ## The loop over the tokens of cursors that agree -/


/-- The parser's answer, its parser, the cursor it leaves and its log, on the two sides: the same
answer and log, canonically equal parsers and cursors that agree. -/
def LoopRel (Rel : Token.BatchCursor g → Token.BatchCursor g' → Prop)
    {o₁ : Token.BatchCursor g} {o₂ : Token.BatchCursor g'}
    (r₁ : (Except (ParseError Unit) (ControlFlow Unit) × ScriptParser (List Event) ×
      { z : Token.BatchCursor g // Token.Produce.Consumed z o₁ }) × List Event)
    (r₂ : (Except (ParseError Unit) (ControlFlow Unit) × ScriptParser (List Event) ×
      { z : Token.BatchCursor g' // Token.Produce.Consumed z o₂ }) × List Event) : Prop :=
  r₁.1.1 = r₂.1.1 ∧ canon r₁.1.2.1 = canon r₂.1.2.1 ∧ Rel r₁.1.2.2.val r₂.1.2.2.val ∧
    r₁.2 = r₂.2

theorem rest_agree (hR : CursorRel Rel) (n : Nat) :
    ∀ {p₁ p₂ : ScriptParser (List Event)}, canon p₁ = canon p₂ →
    ∀ {o₁ c₁ : Token.BatchCursor g} {o₂ c₂ : Token.BatchCursor g'}
      (k₁ : Token.Produce.Consumed c₁ o₁) (k₂ : Token.Produce.Consumed c₂ o₂),
      Rel c₁ c₂ → remaining c₁ < n → ∀ log : List Event,
      LoopRel Rel ((Internal.rest o₁ p₁ c₁ k₁).run log)
        ((Internal.rest o₂ p₂ c₂ k₂).run log) := by
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ hr; omega
  | succ n ih =>
  intro p₁ p₂ hp o₁ c₁ o₂ c₂ k₁ k₂ hc hr log
  rw [rest_of_none k₁ (recording_noHandOver _ _), rest_of_none k₂ (recording_noHandOver _ _)]
  by_cases h₁ : c₁.HasNext
  · have h₂ : c₂.HasNext := (hR.hasNext hc).mp h₁
    have e₁ : Token.Produce.next? c₁ = some (c₁.next h₁) := by
      show Token.BatchCursor.next? c₁ = _
      simp [Token.BatchCursor.next?, h₁]
    have e₂ : Token.Produce.next? c₂ = some (c₂.next h₂) := by
      show Token.BatchCursor.next? c₂ = _
      simp [Token.BatchCursor.next?, h₂]
    simp only [e₁, e₂]
    obtain ⟨hn, hi⟩ := hR.next hc h₁ h₂
    obtain ⟨ha, hag, hl⟩ := takeOne_agree hp (c₁.next h₁).2.2 (c₂.next h₂).2.2 hR hn hi log
    simp only [StateT.run_bind, id_bind_eq]
    generalize (Internal.takeOne p₁ c₁ (c₁.next h₁).1 (c₁.next h₁).2.1 (c₁.next h₁).2.2).run log
      = T₁ at ha hag hl ⊢
    generalize (Internal.takeOne p₂ c₂ (c₂.next h₂).1 (c₂.next h₂).2.1 (c₂.next h₂).2.2).run log
      = T₂ at ha hag hl ⊢
    obtain ⟨⟨a₁, later₁, taken₁⟩, l₁⟩ := T₁
    obtain ⟨⟨a₂, later₂, taken₂⟩, l₂⟩ := T₂
    dsimp only at ha hag hl ⊢
    subst hl
    cases a₁ <;> cases a₂ <;> simp only [AfterRel] at ha
    · exact ih ha _ _ hag (Nat.lt_of_lt_of_le taken₁.remaining_lt (Nat.le_of_lt_succ hr)) l₁
    · obtain ⟨rfl, rfl⟩ := ha
      exact ⟨rfl, rfl, hag, rfl⟩
  · have h₂ : ¬ c₂.HasNext := fun h => h₁ ((hR.hasNext hc).mpr h)
    have e₁ : Token.Produce.next? c₁ = none := by
      show Token.BatchCursor.next? c₁ = _
      simp [Token.BatchCursor.next?, h₁]
    have e₂ : Token.Produce.next? c₂ = none := by
      show Token.BatchCursor.next? c₂ = _
      simp [Token.BatchCursor.next?, h₂]
    simp only [e₁, e₂]
    exact ⟨rfl, hp, hc, rfl⟩

/-- The script parser's parse of cursors that agree, from canonically equal parsers: the same
answer, state and log, canonically equal parsers, and cursors that agree. -/
theorem parseByToken_agree {p₁ p₂ : ScriptParser (List Event)} (hp : canon p₁ = canon p₂)
    (st : ParseState (List Event)) {c₁ : Token.BatchCursor g} {c₂ : Token.BatchCursor g'}
    (hR : CursorRel Rel) (hc : Rel c₁ c₂) (log : List Event) :
    ((Internal.parseByToken p₁ st c₁).run log).1.1 =
        ((Internal.parseByToken p₂ st c₂).run log).1.1 ∧
      canon ((Internal.parseByToken p₁ st c₁).run log).1.2.1 =
        canon ((Internal.parseByToken p₂ st c₂).run log).1.2.1 ∧
      ((Internal.parseByToken p₁ st c₁).run log).1.2.2.1 =
        ((Internal.parseByToken p₂ st c₂).run log).1.2.2.1 ∧
      Rel ((Internal.parseByToken p₁ st c₁).run log).1.2.2.2.val
        ((Internal.parseByToken p₂ st c₂).run log).1.2.2.2.val ∧
      ((Internal.parseByToken p₁ st c₁).run log).2 =
        ((Internal.parseByToken p₂ st c₂).run log).2 := by
  rw [parseByToken_of_none st (recording_noHandOver _ _),
    parseByToken_of_none st (recording_noHandOver _ _)]
  by_cases h₁ : c₁.HasNext
  · have h₂ : c₂.HasNext := (hR.hasNext hc).mp h₁
    have e₁ : Token.Produce.next? c₁ = some (c₁.next h₁) := by
      show Token.BatchCursor.next? c₁ = _
      simp [Token.BatchCursor.next?, h₁]
    have e₂ : Token.Produce.next? c₂ = some (c₂.next h₂) := by
      show Token.BatchCursor.next? c₂ = _
      simp [Token.BatchCursor.next?, h₂]
    split
    · rename_i heq; rw [e₁] at heq; cases heq
    · rename_i token₁ next₁ consumed₁ heq₁
      rw [e₁] at heq₁
      split
      · rename_i heq; rw [e₂] at heq; cases heq
      · rename_i token₂ next₂ consumed₂ heq₂
        rw [e₂] at heq₂
        injection heq₁ with heq₁
        injection heq₂ with heq₂
        have ht₁ : token₁ = (c₁.next h₁).1 := by rw [heq₁]
        have hn₁ : next₁ = (c₁.next h₁).2.1 := by rw [heq₁]
        have ht₂ : token₂ = (c₂.next h₂).1 := by rw [heq₂]
        have hn₂ : next₂ = (c₂.next h₂).2.1 := by rw [heq₂]
        obtain ⟨hn, hi⟩ := hR.next hc h₁ h₂
        rw [← ht₁, ← ht₂, ← hn₁, ← hn₂] at hi
        rw [← hn₁, ← hn₂] at hn
        obtain ⟨ha, hag, hl⟩ := takeOne_agree hp consumed₁ consumed₂ hR hn hi log
        simp only [StateT.run_bind, id_bind_eq]
        generalize (Internal.takeOne p₁ c₁ token₁ next₁ consumed₁).run log = T₁ at ha hag hl ⊢
        generalize (Internal.takeOne p₂ c₂ token₂ next₂ consumed₂).run log = T₂ at ha hag hl ⊢
        obtain ⟨⟨a₁, later₁, taken₁⟩, l₁⟩ := T₁
        obtain ⟨⟨a₂, later₂, taken₂⟩, l₂⟩ := T₂
        dsimp only at ha hag hl ⊢
        subst hl
        cases a₁ <;> cases a₂ <;> simp only [AfterRel] at ha
        · obtain ⟨r1, r2, r3, r4⟩ := rest_agree hR (remaining later₁ + 1) ha taken₁ taken₂ hag
            (Nat.lt_succ_self _) l₁
          simp only [StateT.run_bind, id_bind_eq]
          rename_i q₁ q₂
          generalize (Internal.rest c₁ q₁ later₁ taken₁).run l₁ = U₁ at r1 r2 r3 r4 ⊢
          generalize (Internal.rest c₂ q₂ later₂ taken₂).run l₁ = U₂ at r1 r2 r3 r4 ⊢
          obtain ⟨⟨u₁, q₁, d₁⟩, m₁⟩ := U₁
          obtain ⟨⟨u₂, q₂, d₂⟩, m₂⟩ := U₂
          refine ⟨r1, r2, ?_, r3, r4⟩ <;> first | rfl | trivial
        · obtain ⟨rfl, rfl⟩ := ha
          refine ⟨?_, ?_, ?_, hag, ?_⟩ <;> first | rfl | trivial
  · have h₂ : ¬ c₂.HasNext := fun h => h₁ ((hR.hasNext hc).mpr h)
    have e₁ : Token.Produce.next? c₁ = none := by
      show Token.BatchCursor.next? c₁ = _
      simp [Token.BatchCursor.next?, h₁]
    have e₂ : Token.Produce.next? c₂ = none := by
      show Token.BatchCursor.next? c₂ = _
      simp [Token.BatchCursor.next?, h₂]
    split
    · split
      · exact ⟨rfl, hp, rfl, hc, rfl⟩
      · rename_i heq; rw [e₂] at heq; cases heq
    · rename_i heq; rw [e₁] at heq; cases heq

end BSmtLib.Facts.Proofs.Parser.Canon.Loop
