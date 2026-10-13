import BSmtLib.Proofs.Consumers.VEvent

/-!
# The naive lexer with a consumer of the spec, as `Runs` states

`walk`: what the naive lexer has done with the consumer from a state that is the pure run's
state, holding no result, is what `Spec.Lexer.Runs` states, from the tokens of the run from that
state. It is by induction on the bytes left, with a token in progress counted as half a byte, so
that a token ended before a byte is handed over before the byte is lexed again. A token handed
over at a boundary is `event` (`eventA` for a token that is a byte by itself, `eventB` for one
that a byte ends before it, `eventC` for one that the end of the input ends); the end-of-file
token handed over at the end is `walk_eof`.
-/

namespace BSmtLib.Proofs.Lexer.VNaive

open BSmtLib.Proofs.Adapter
open Spec.Lexer (Handed)

section
variable (consumer : Spec.Lexer.Consumer) (sv : Spec.Lexicon.Version) (input : List UInt8)
  (ended : Bool)

theorem vSession_congr_step {X Y : Core} {b : UInt8} {t t' : List Handed}
    (held : Option (Located consumer.Result)) (bs : List UInt8)
    (h : vByte consumer X b t = vByte consumer Y b t') :
    vSession consumer X held (b :: bs) ended t = vSession consumer Y held (b :: bs) ended t' := by
  unfold vSession
  simp only [vBytes, h]

theorem vSession_nil (core : Core) (taken : List Handed) :
    vSession consumer core none [] ended taken =
      if ended then
        match vEnd consumer core taken with
        | ((.ok flow, core''), taken'') =>
          sessionOf consumer taken''
            (match eofResult none flow with
              | some result => .finished result.value (toLocation result.location)
              | none => .running) core''
        | ((.error e, core''), taken'') => sessionOf consumer taken'' (.failed (failureOf e)) core''
      else sessionOf consumer taken .running core := rfl

/-- With a result held, a byte with nothing in progress gives no result. -/
theorem lexStart_holding (core : Core) (b : UInt8) (taken : List Handed)
    (hh : core.holding = true) (y : Located consumer.Result) :
    (vRun consumer (lexStart (H := Answering consumer) core b) taken).1.1 ≠ .ok (some y) := by
  cases hs : start core.version consumer.concrete core.location b with
  | idle =>
    obtain ⟨core', h, -⟩ := lexStart_none consumer core b taken (st := .idle)
      (by simp [startStepW, hs])
    rw [h]; nofun
  | pending p =>
    obtain ⟨core', h, -⟩ := lexStart_none consumer core b taken (st := .token p)
      (by simp [startStepW, hs])
    rw [h]; nofun
  | token l =>
    obtain ⟨hl, h⟩ := lexStart_token consumer core b taken hs
    rw [h, handOverAt_holding consumer (idleAfter core b) l hl (by simpa [idleAfter] using hh)]
    nofun
  | error f =>
    rw [lexStart_error' consumer core b taken hs]
    nofun

/-- The session after the consumer failed at a lexeme handed over from a lexer with nothing in
progress: the version it left, and discarding from the end of the lexeme if it asked for it. -/
theorem sessionOf_coreAfterError (taken : List Handed)
    (outcome : Spec.Lexer.Outcome consumer.Result consumer.Error) (X : Core) (l : Lexeme)
    (version : Version) (discards : Bool) (ha : X.activity = .idle) :
    sessionOf consumer taken outcome (coreAfterError X l version discards) =
      ⟨taken, outcome, fromVersion version,
        if discards then some (toLocation l.end) else none⟩ := by
  unfold sessionOf coreAfterError
  cases discards <;> simp [discardedOf, ha, Activity.discardStart]

/-- At the end of the input with nothing in progress and no result held: the end-of-file token
is handed over. -/
theorem walk_eof (hb : consumer.BreaksAtEnd) (j : Nat) (v : Version) (core : Core)
    (taken : List Handed) (hj : input.drop j = []) (hv : core.version = v)
    (ha : core.activity = .idle) (hl : core.location = locAfter (input.take j))
    (hh : core.holding = false) (hi : core.initialVersion = toVersion sv) :
    Spec.Lexer.Runs fedRun consumer sv input true (fromVersion v)
      [Spec.Lexer.endOfFile input] false taken
      (vSession consumer core none [] true taken) := by
  have hl' : core.location = locAfter input := by rw [hl, drop_length_eq_nil hj]
  rw [vSession_nil]
  simp only [ite_true]
  have hr := handOverAt_reply consumer core (eofAt core.location) (eofAt_valid _) hh taken
  have heof : lexemeEntry consumer.concrete core.version (eofAt core.location) =
      some (Spec.Lexer.endOfFile input) := by
    rw [hl']; exact lexemeEntry_of_handed (lexemeHanded_eofAt _ input)
  simp only [reply, heof] at hr
  cases hans : consumer.answer (taken ++ [Spec.Lexer.endOfFile input]) with
  | fail e =>
    simp only [hans] at hr
    rw [vEnd_eof consumer core taken (.inl ha) hh hr]
    have := Spec.Lexer.Runs.fails (feed := fedRun) (consumer := consumer)
      (start := sv) (input := input) (ended := true) (version := fromVersion v)
      (ready := []) (failed := false) (taken := taken) (token := Spec.Lexer.endOfFile input) hans
    rw [settle_not_finished _ _ _ rfl, ← fromVersion_getD] at this
    have hend : toLocation (eofAt core.location).end = (Spec.Lexer.endOfFile input).«end» := by
      simp [hl', toLocation_locAfter, Spec.Lexer.endOfFile]
    simp only [failureOf]
    rw [sessionOf_coreAfterError consumer _ _ _ _ _ _ ha, hend, hv]
    exact this
  | «break» r =>
    simp only [hans] at hr
    rw [vEnd_eof consumer core taken (.inl ha) hh hr]
    have := Spec.Lexer.Runs.ends (feed := fedRun) (consumer := consumer)
      (start := sv) (input := input) (ended := true) (version := fromVersion v)
      (ready := []) (failed := false) (taken := taken) (token := Spec.Lexer.endOfFile input) rfl
      hans
    rw [settle_finished] at this
    simp only [eofResult, sessionOf, discardedOf_reset, Option.map_none]
    rw [reset_version _ sv (by simp only [coreAfter]; split <;> exact hi)]
    have hend : toLocation (eofAt core.location).end = (Spec.Lexer.endOfFile input).«end» := by
      simp [hl', toLocation_locAfter, Spec.Lexer.endOfFile]
    rw [hend]
    exact this
  | «continue» =>
    exact absurd hans (hb taken (Spec.Lexer.endOfFile input) rfl)


/-- The session after a byte at which the lexer hands a lexeme over and goes on with the bytes
after it. -/
theorem session_handOver {core X : Core} {b : UInt8} {bs : List UInt8} {l : Lexeme}
    {hl : l.Valid} (taken : List Handed) (held : Option (Located consumer.Result))
    (hX : X.holding = false)
    (hbyte : vByte consumer core b taken =
      vRun consumer (handOverAt (H := Answering consumer) X l hl) taken) :
    vSession consumer core held (b :: bs) ended taken =
      match reply consumer X.version taken l with
      | (.ok .continue, version, discards, taken') =>
        vSession consumer (coreAfter X l version discards) held bs ended taken'
      | (.ok (.break value), version, discards, taken') =>
        vSession consumer { coreAfter X l version discards with holding := true }
          (some ⟨value, l.end⟩) bs ended taken'
      | (.error err, version, discards, taken') =>
        sessionOf consumer taken'
            (.failed (failureOf ⟨.consumer err, Span.newUnchecked l.end l.end, none⟩))
          (coreAfterError X l version discards) := by
  have hr := handOverAt_reply consumer X l hl hX taken
  rw [hr] at hbyte
  generalize reply consumer X.version taken l = R at hbyte ⊢
  obtain ⟨answer, version, discards, taken'⟩ := R
  cases answer with
  | error e => exact vSession_step_error consumer held bs ended hbyte
  | ok flow =>
    cases flow with
    | «continue» => exact vSession_step_none consumer held bs ended hbyte
    | «break» value => exact vSession_step_some consumer held bs ended hbyte


theorem coreAfter_fields (X : Core) (l : Lexeme) (version : Version) (discards : Bool) :
    (coreAfter X l version discards).version = version ∧
      (coreAfter X l version discards).activity =
        (if discards then .discarding l.end else X.activity) ∧
      (coreAfter X l version discards).location = X.location ∧
      (coreAfter X l version discards).holding = X.holding ∧
      (coreAfter X l version discards).initialVersion = X.initialVersion := by
  unfold coreAfter
  cases discards <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An entry that a byte ends with it, handed over with nothing in progress after it, at the
boundary `j + 1`: a token that is the byte by itself, or a comment that the byte ends. -/
theorem eventA (hb : consumer.BreaksAtEnd) {j : Nat} {v : Version} {core : Core}
    {taken : List Handed} {b : UInt8} {bs : List UInt8} {l : Lexeme} {hd : Handed}
    (hj : input.drop j = b :: bs) (hv : core.version = v)
    (hl : core.location = locAfter (input.take j)) (hh : core.holding = false)
    (hi : core.initialVersion = toVersion sv) (hlv : l.Valid)
    (hbyte : vByte consumer core b taken =
      vRun consumer (handOverAt (H := Answering consumer) (idleAfter core b) l hlv) taken)
    (hend : l.end = locAfter (input.take (j + 1))) (hne : (l.category == .endOfFile) = false)
    (hhd : lexemeEntry consumer.concrete v l = some hd)
    (IH : BoundaryRuns consumer sv input ended (j + 1)) :
    Spec.Lexer.Runs fedRun consumer sv input ended (fromVersion v)
      (hd :: (Spec.Lexer.readyFrom fedRun consumer.concrete (fromVersion v) input ended
        (j + 1)).handed)
      (Spec.Lexer.readyFrom fedRun consumer.concrete (fromVersion v) input ended (j + 1)).failed
      taken (vSession consumer core none (b :: bs) ended taken) := by
  obtain ⟨hj', hl'⟩ := drop_succ_of hj
  have hjle : j + 1 ≤ input.length := by
    have := congrArg List.length hj
    simp at this
    omega
  have hX : (idleAfter core b).holding = false := by simpa [idleAfter] using hh
  rw [session_handOver consumer ended taken none hX hbyte]
  have hver : (idleAfter core b).version = v := by simp [idleAfter, hv]
  rw [hver]
  simp only [reply, hhd]
  have hloc : (idleAfter core b).location = locAfter (input.take (j + 1)) := by
    simp [idleAfter, hl, hl']
  refine event consumer sv input ended hb hhd hne hend hjle IH _
    ?_ ?_ ?_ ?_ ?_
  · intro e hans
    simp only [hans, failureOf]
    exact sessionOf_coreAfterError consumer _ _ _ _ _ _ rfl
  · intro hans hdi
    simp only [hans, hdi]
    obtain ⟨f1, f2, f3, f4, f5⟩ := coreAfter_fields (idleAfter core b) l
      (((consumer.switchTo (taken ++ [hd])).map toVersion).getD v) false
    refine ⟨_, f1, by rw [f2]; rfl, by rw [f3, hloc], by rw [f4, hX], by rw [f5]; exact hi, ?_⟩
    rw [hj']
  · intro hans hdi
    simp only [hans, hdi]
    obtain ⟨f1, f2, f3, f4, f5⟩ := coreAfter_fields (idleAfter core b) l
      (((consumer.switchTo (taken ++ [hd])).map toVersion).getD v) true
    rw [← hj']
    exact discard_session consumer sv ended _ _ none _ (by rw [f2]; rfl) f1
      (by rw [f3, hloc, hend]) (by rw [f4, hX]) (by rw [f5]; exact hi) (fun _ => rfl)
  · intro r hans hdi
    simp only [hans, hdi]
    obtain ⟨f1, f2, f3, f4, f5⟩ := coreAfter_fields (idleAfter core b) l
      (((consumer.switchTo (taken ++ [hd])).map toVersion).getD v) false
    rw [← hj']
    exact hold consumer sv input ended _ _ _ (input.drop (j + 1)) .idle (Nat.le_refl _) (j + 1)
      _ _ rfl f1 (by rw [f2]; rfl) (by rw [f3, hloc]) rfl (by rw [f5]; exact hi)
  · intro r hans hdi
    simp only [hans, hdi]
    obtain ⟨f1, f2, f3, f4, f5⟩ := coreAfter_fields (idleAfter core b) l
      (((consumer.switchTo (taken ++ [hd])).map toVersion).getD v) true
    rw [← hj']
    exact discard_session consumer sv ended _ _ _ _ (by rw [f2]; rfl) f1
      (by rw [f3, hloc, hend]) rfl (by rw [f5]; exact hi) nofun

/-- An entry that a byte ends before it, handed over at the boundary `j`, after which the byte is
lexed again with nothing in progress. -/
theorem eventB (hb : consumer.BreaksAtEnd) {j : Nat} {v : Version} {core : Core}
    {taken : List Handed} {b : UInt8} {bs : List UInt8} {p : Pending} {l : Lexeme}
    {hd : Handed}
    (hj : input.drop j = b :: bs) (hv : core.version = v) (ha : core.activity = .token p)
    (hl : core.location = locAfter (input.take j)) (hh : core.holding = false)
    (hi : core.initialVersion = toVersion sv)
    (hadv : advance consumer.concrete p core.location b = .tokenBefore l)
    (hhd : lexemeEntry consumer.concrete v l = some hd)
    (IH : BoundaryRuns consumer sv input ended j) :
    Spec.Lexer.Runs fedRun consumer sv input ended (fromVersion v)
      (hd :: (Spec.Lexer.readyFrom fedRun consumer.concrete (fromVersion v) input ended j).handed)
      (Spec.Lexer.readyFrom fedRun consumer.concrete (fromVersion v) input ended j).failed
      taken (vSession consumer core none (b :: bs) ended taken) := by
  obtain ⟨hj', hl'⟩ := drop_succ_of hj
  have hjle : j ≤ input.length := by
    have := congrArg List.length hj
    simp at this
    omega
  have hspan := advance_tokenBefore hadv
  obtain ⟨hlv, hbyte⟩ := lexByte_tokenBefore consumer core b taken ha hadv
  have hX : (idleAt core).holding = false := by simpa [idleAt] using hh
  have hr := handOverAt_reply consumer (idleAt core) l hlv hX taken
  have hver : (idleAt core).version = v := by simp [idleAt, hv]
  rw [hver] at hr
  simp only [reply, hhd] at hr
  have hend : l.end = locAfter (input.take j) := by rw [hspan.2, hl]
  have hloc : (idleAt core).location = locAfter (input.take j) := by simp [idleAt, hl]
  refine event consumer sv input ended hb hhd (advance_lexeme_ne_eof (.inr hadv)) hend hjle IH
    _ ?_ ?_ ?_ ?_ ?_
  · intro e hans
    simp only [hans] at hr
    rw [vSession_step_error consumer none bs ended (hbyte hr)]
    simp only [failureOf]
    exact sessionOf_coreAfterError consumer _ _ _ _ _ _ rfl
  · intro hans hdi
    simp only [hans, hdi] at hr
    obtain ⟨f1, f2, f3, f4, f5⟩ := coreAfter_fields (idleAt core) l
      (((consumer.switchTo (taken ++ [hd])).map toVersion).getD v) false
    have ha2 : (coreAfter (idleAt core) l
        (((consumer.switchTo (taken ++ [hd])).map toVersion).getD v) false).activity = .idle := by
      rw [f2]; rfl
    have h2 := hbyte hr
    simp only [ha2] at h2
    rw [← lexByte_idle consumer _ b _ ha2] at h2
    refine ⟨_, f1, ha2, by rw [f3, hloc], by rw [f4, hX], by rw [f5]; exact hi, ?_⟩
    rw [hj]
    exact vSession_congr_step consumer ended none bs h2
  · intro hans hdi
    simp only [hans, hdi] at hr
    obtain ⟨f1, f2, f3, f4, f5⟩ := coreAfter_fields (idleAt core) l
      (((consumer.switchTo (taken ++ [hd])).map toVersion).getD v) true
    have h2 := hbyte hr
    simp only [f2, ite_true] at h2
    rw [vSession_step_none consumer none bs ended h2, ← hj']
    exact discard_session consumer sv ended _ _ none _ rfl
      (by simp [discardingAfter, f1])
      (by simp [discardingAfter, f3, hloc, hend]) (by simp [discardingAfter, f4, hX])
      (by simp only [discardingAfter]; rw [f5]; exact hi) (fun _ => rfl)
  · intro r hans hdi
    simp only [hans, hdi] at hr
    obtain ⟨f1, f2, f3, f4, f5⟩ := coreAfter_fields (idleAt core) l
      (((consumer.switchTo (taken ++ [hd])).map toVersion).getD v) false
    generalize hH : ({ coreAfter (idleAt core) l
      (((consumer.switchTo (taken ++ [hd])).map toVersion).getD v) false with holding := true } :
      Core) = H at hr
    have haH : H.activity = .idle := by rw [← hH]; simp only; rw [f2]; rfl
    have hvH : H.version = ((consumer.switchTo (taken ++ [hd])).map toVersion).getD v := by
      rw [← hH]; exact f1
    have hlH : H.location = locAfter (input.take j) := by rw [← hH]; simp only; rw [f3, hloc]
    have hhH : H.holding = true := by rw [← hH]
    have hiH : H.initialVersion = toVersion sv := by rw [← hH]; simp only; rw [f5]; exact hi
    have h2 := hbyte hr
    simp only [haH] at h2
    have hsame : vSession consumer core none (b :: bs) ended taken =
        vSession consumer H (some ⟨r, l.end⟩) (b :: bs) ended (taken ++ [hd]) := by
      unfold vSession
      simp only [vBytes]
      rw [h2, lexByte_idle consumer H b _ haH]
      have hns := lexStart_holding consumer H b (taken ++ [hd]) hhH
      generalize vRun consumer (lexStart (H := Answering consumer) H b) (taken ++ [hd]) = R3
        at hns ⊢
      obtain ⟨⟨r3, c3⟩, t3⟩ := R3
      cases r3 with
      | error f => rfl
      | ok y =>
        cases y with
        | none => rfl
        | some y => exact absurd rfl (hns y)
    rw [hsame, ← hj]
    exact hold consumer sv input ended _ _ _ (input.drop j) .idle (Nat.le_refl _) j _ _ rfl
      hvH haH hlH hhH hiH
  · intro r hans hdi
    simp only [hans, hdi] at hr
    obtain ⟨f1, f2, f3, f4, f5⟩ := coreAfter_fields (idleAt core) l
      (((consumer.switchTo (taken ++ [hd])).map toVersion).getD v) true
    have h2 := hbyte hr
    simp only [f2, ite_true] at h2
    rw [vSession_step_some consumer none bs ended h2, ← hj']
    exact discard_session consumer sv ended _ _ _ _ rfl (by simp [discardingAfter, f1])
      (by simp [discardingAfter, f3, hloc, hend]) rfl
      (by simp only [discardingAfter]; rw [f5]; exact hi) nofun


theorem stream_at_end (version : Version) (ws : Bool) {j : Nat} (hj : input.drop j = []) :
    stream version ws input true j = ([eofLexeme (locAfter (input.take j))], false) := by
  simp [stream, streamFrom, hj, lexBytesW, endStepW]

/-- An entry that the end of the input ends, handed over at the end. -/
theorem eventC (hb : consumer.BreaksAtEnd) {j : Nat} {v : Version} {core : Core}
    {taken : List Handed} {p : Pending} {l : Lexeme} {hd : Handed}
    (hj : input.drop j = []) (hjle : j ≤ input.length) (hv : core.version = v)
    (ha : core.activity = .token p)
    (hl : core.location = locAfter (input.take j)) (hh : core.holding = false)
    (hi : core.initialVersion = toVersion sv)
    (hf : finish consumer.concrete p core.location = .token l)
    (hhd : lexemeEntry consumer.concrete v l = some hd)
    (IH : BoundaryRuns consumer sv input true j) :
    Spec.Lexer.Runs fedRun consumer sv input true (fromVersion v)
      (hd :: (Spec.Lexer.readyFrom fedRun consumer.concrete (fromVersion v) input true j).handed)
      (Spec.Lexer.readyFrom fedRun consumer.concrete (fromVersion v) input true j).failed
      taken (vSession consumer core none [] true taken) := by
  have hspan := finish_token hf
  obtain ⟨hlv, hend1, hend2, hend3⟩ := vEnd_finish_token consumer core taken ha hf
  have hX : (idleAt core).holding = false := by simpa [idleAt] using hh
  have hr := handOverAt_reply consumer (idleAt core) l hlv hX taken
  have hver : (idleAt core).version = v := by simp [idleAt, hv]
  rw [hver] at hr
  simp only [reply, hhd] at hr
  have hend : l.end = locAfter (input.take j) := by rw [hspan.2, hl]
  have hloc : (idleAt core).location = locAfter (input.take j) := by simp [idleAt, hl]
  -- after the token, the end-of-file token is handed over as at the end with nothing else
  have heof : ∀ {core2 taken2}, core2.holding = false → core2.location = core.location →
      (core2.activity = .idle ∨ ∃ s, core2.activity = .discarding s) →
      vRun consumer (handOverAt (H := Answering consumer) (idleAt core) l hlv) taken =
        ((.ok none, core2), taken2) →
      vSession consumer core none [] true taken = vSession consumer core2 none [] true taken2 := by
    intro core2 taken2 hh2 hl2 ha2 hr2
    rw [vSession_nil, vSession_nil]
    simp only [ite_true]
    generalize hR3 : vRun consumer (handOverAt (H := Answering consumer) core2
      (eofAt core.location) (eofAt_valid _)) taken2 = R3
    obtain ⟨⟨r3, core3⟩, taken3⟩ := R3
    rw [hend3 hh2 hr2 hR3, vEnd_eof consumer core2 taken2 ha2 hh2 (r := r3) (core2 := core3)
      (taken2 := taken3) (by rw [hl2]; exact hR3)]
  refine event consumer sv input true hb hhd (finish_token_ne_eof hf) hend hjle IH _
    ?_ ?_ ?_ ?_ ?_
  · intro e hans
    simp only [hans] at hr
    rw [vSession_nil]
    simp only [ite_true, hend1 hr]
    simp only [failureOf]
    exact sessionOf_coreAfterError consumer _ _ _ _ _ _ rfl
  · intro hans hdi
    simp only [hans, hdi] at hr
    obtain ⟨f1, f2, f3, f4, f5⟩ := coreAfter_fields (idleAt core) l
      (((consumer.switchTo (taken ++ [hd])).map toVersion).getD v) false
    refine ⟨_, f1, by rw [f2]; rfl, by rw [f3, hloc], by rw [f4, hX], by rw [f5]; exact hi, ?_⟩
    rw [hj]
    exact heof (by rw [f4, hX]) (by rw [f3]; rfl) (.inl (by rw [f2]; rfl)) hr
  · intro hans hdi
    simp only [hans, hdi] at hr
    obtain ⟨f1, f2, f3, f4, f5⟩ := coreAfter_fields (idleAt core) l
      (((consumer.switchTo (taken ++ [hd])).map toVersion).getD v) true
    rw [heof (by rw [f4, hX]) (by rw [f3]; rfl) (.inr ⟨_, by rw [f2]; rfl⟩) hr, ← hj]
    exact discard_session consumer sv true _ _ none _ (by rw [f2]; rfl) f1
      (by rw [f3, hloc, hend]) (by rw [f4, hX]) (by rw [f5]; exact hi) (fun _ => rfl)
  · intro r hans hdi
    simp only [hans, hdi] at hr
    rw [vSession_nil]
    simp only [ite_true, hend2 hr, stream_at_end input _ _ hj]
    simp only [eofResult, sessionOf, holdSession, eofLexeme, discardedOf_reset, Option.map_none]
    rw [reset_version _ sv (by simp only [coreAfter]; split <;> exact hi)]
    rfl
  · intro r hans hdi
    simp only [hans, hdi] at hr
    rw [vSession_nil]
    simp only [ite_true, hend2 hr]
    simp only [eofResult, sessionOf, discardSession, ite_true, discardedOf_reset, Option.map_none]
    rw [reset_version _ sv (by simp only [coreAfter]; split <;> exact hi)]


/-- After the token that the end of the input ends, if the consumer continues, the end-of-file
token is handed over as at the end with nothing else in progress. -/
theorem session_end_after {core core2 : Core} {taken taken2 : List Handed} {p : Pending}
    {l : Lexeme} (ha : core.activity = .token p)
    (hf : finish consumer.concrete p core.location = .token l) (hlv : l.Valid)
    (hh2 : core2.holding = false) (hl2 : core2.location = core.location)
    (ha2 : core2.activity = .idle ∨ ∃ s, core2.activity = .discarding s)
    (hr2 : vRun consumer (handOverAt (H := Answering consumer) (idleAt core) l hlv) taken =
      ((.ok none, core2), taken2)) :
    vSession consumer core none [] true taken = vSession consumer core2 none [] true taken2 := by
  obtain ⟨hlv', -, -, hend3⟩ := vEnd_finish_token consumer core taken ha hf
  rw [vSession_nil, vSession_nil]
  simp only [ite_true]
  generalize hR3 : vRun consumer (handOverAt (H := Answering consumer) core2
    (eofAt core.location) (eofAt_valid _)) taken2 = R3
  obtain ⟨⟨r3, core3⟩, taken3⟩ := R3
  rw [hend3 hh2 hr2 hR3, vEnd_eof consumer core2 taken2 ha2 hh2 (r := r3) (core2 := core3)
    (taken2 := taken3) (by rw [hl2]; exact hR3)]

theorem start_token_taken {version : Version} {ws : Bool} {location : Location} {c : UInt8}
    {l : Lexeme} (h : start version ws location c = .token l) : l.Taken := by
  simp only [start] at h
  repeat' split at h
  all_goals cases h
  all_goals rfl

/-- A lexeme the lexer hands over is an entry the consumer takes: any lexeme for a concrete
consumer, a token for one that is not. -/
theorem entry_of (version : Version) {l : Lexeme} (h : consumer.concrete = false → l.Taken) :
    ∃ hd, lexemeEntry consumer.concrete version l = some hd := by
  cases hc : consumer.concrete with
  | true => unfold lexemeEntry; cases lexemeHanded version l <;> simp
  | false =>
    obtain ⟨hd, hhd⟩ := lexemeHanded_of_taken (version := version) (h hc)
    exact ⟨hd, lexemeEntry_of_handed hhd⟩

/-- At the end of the bytes with nothing in progress. -/
theorem walk_nil_idle (hb : consumer.BreaksAtEnd) (j : Nat) (v : Version) (core : Core)
    (taken : List Handed) (hj : input.drop j = []) (hv : core.version = v)
    (ha : core.activity = .idle) (hl : core.location = locAfter (input.take j))
    (hh : core.holding = false) (hi : core.initialVersion = toVersion sv) :
    Spec.Lexer.Runs fedRun consumer sv input ended (fromVersion v)
      (entriesOf consumer.concrete v
        (streamFromSt v consumer.concrete ended .idle (locAfter (input.take j)) []).1)
      (streamFromSt v consumer.concrete ended .idle (locAfter (input.take j)) []).2
      taken (vSession consumer core none [] ended taken) := by
  rw [streamFromSt_nil]
  cases ended with
  | false =>
    have := Spec.Lexer.Runs.waiting (feed := fedRun) (consumer := consumer)
      (start := sv) (input := input) (ended := false) (version := fromVersion v) (taken := taken)
    rw [settle_not_finished _ _ _ rfl] at this
    rw [vSession_nil]
    simp only [Bool.false_eq_true, ite_false, sessionOf, hv, discardedOf, ha, Option.map_none]
    exact this
  | true =>
    simp only [ite_true, endStepW]
    have he : entriesOf consumer.concrete v [eofLexeme (locAfter (input.take j))] =
        [Spec.Lexer.endOfFile input] := by
      rw [drop_length_eq_nil hj]
      simp [entriesOf, lexemeEntry_of_handed (lexemeHanded_eof v input)]
    rw [he]
    exact walk_eof consumer sv input hb j v core taken hj hv ha hl hh hi

/-- What the naive lexer has done from the state that is the pure run's state, holding no
result, is what `Runs` states, from the entries of the run from that state. -/
theorem walk (hb : consumer.BreaksAtEnd) : ∀ (n : Nat) (bytes : List UInt8) (st : St),
    2 * bytes.length + st.weight ≤ n →
    ∀ (j : Nat) (v : Version) (core : Core) (taken : List Handed),
    input.drop j = bytes → j ≤ input.length → core.version = v →
    core.activity = st.activity → core.location = locAfter (input.take j) →
    core.holding = false → core.initialVersion = toVersion sv →
    (consumer.concrete = false → st.Taken) →
    Spec.Lexer.Runs fedRun consumer sv input ended (fromVersion v)
      (entriesOf consumer.concrete v
        (streamFromSt v consumer.concrete ended st (locAfter (input.take j)) bytes).1)
      (streamFromSt v consumer.concrete ended st (locAfter (input.take j)) bytes).2
      taken (vSession consumer core none bytes ended taken) := by
  intro n
  induction n with
  | zero =>
    intro bytes st hn j v core taken hj hjle hv ha hl hh hi htk
    have hb0 : bytes = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hst : st = .idle := by cases st <;> simp_all [St.weight]
    subst hb0 hst
    exact walk_nil_idle consumer sv input ended hb j v core taken hj hv ha hl hh hi
  | succ n ih =>
    intro bytes st hn j v core taken hj hjle hv ha hl hh hi htk
    -- the lexer at a boundary further on, by the induction
    have bnd : ∀ o, o ≤ input.length → 2 * (input.drop o).length ≤ n →
        BoundaryRuns consumer sv input ended o := by
      intro o ho hm version B taken' hBv hBa hBl hBh hBi
      have := ih (input.drop o) .idle (by simp only [St.weight]; omega) o version B taken' rfl ho
        hBv (by rw [hBa]; rfl) hBl hBh hBi (fun _ => trivial)
      rw [ready_stream consumer.concrete version input ended o ho]
      exact this
    have hvs : core.version = v := hv
    rw [← hl]
    cases bytes with
    | nil =>
      cases st with
      | idle =>
        rw [hl]; exact walk_nil_idle consumer sv input ended hb j v core taken hj hv ha hl hh hi
      | token p =>
        rw [streamFromSt_nil]
        cases ended with
        | false =>
          have := Spec.Lexer.Runs.waiting (feed := fedRun) (consumer := consumer)
            (start := sv) (input := input) (ended := false) (version := fromVersion v)
            (taken := taken)
          rw [settle_not_finished _ _ _ rfl] at this
          rw [vSession_nil]
          simp only [Bool.false_eq_true, ite_false, sessionOf, hv, discardedOf, ha,
            St.activity, Option.map_none]
          exact this
        | true =>
          simp only [ite_true, endStepW]
          have hloc : core.location = locAfter input := by rw [hl, drop_length_eq_nil hj]
          have hX : (idleAt core).holding = false := by simpa [idleAt] using hh
          rw [← hvs]
          cases hf : finish consumer.concrete p core.location with
          | none =>
            have he : entriesOf consumer.concrete core.version [eofLexeme core.location] =
                [Spec.Lexer.endOfFile input] := by
              rw [hloc]; simp [entriesOf, lexemeEntry_of_handed (lexemeHanded_eof _ input)]
            simp only [he]
            have hsame : vSession consumer core none [] true taken =
                vSession consumer (idleAt core) none [] true taken := by
              rw [vSession_nil, vSession_nil]
              simp only [ite_true]
              generalize hR : vRun consumer (handOverAt (H := Answering consumer) (idleAt core)
                (eofAt core.location) (eofAt_valid _)) taken = R
              obtain ⟨⟨r, core2⟩, taken2⟩ := R
              rw [(vEnd_finish_none consumer core taken ha hf).2 hh hR,
                vEnd_eof consumer (idleAt core) taken (.inl rfl) hX (r := r) (core2 := core2)
                  (taken2 := taken2) hR]
            rw [hsame]
            exact walk_eof consumer sv input hb j core.version (idleAt core) taken hj rfl rfl
              (by simp [idleAt, hl]) hX (by simpa [idleAt] using hi)
          | token l =>
            obtain ⟨hd, hhd⟩ := entry_of consumer core.version (l := l) (fun hc => by
              have hst := htk hc
              rw [hc] at hf
              exact endStep_taken (st := .token p) (location := core.location)
                (ls := [l, eofLexeme core.location]) (by simp [endStep, hf]) hst l (by simp))
            have hseg := ready_stream consumer.concrete core.version input true j hjle
            rw [stream_at_end input _ _ hj] at hseg
            have he : entriesOf consumer.concrete core.version [l, eofLexeme core.location] =
                hd :: (Spec.Lexer.readyFrom fedRun consumer.concrete (fromVersion core.version)
                  input true j).handed := by
              rw [hseg, hloc, drop_length_eq_nil hj]
              simp [entriesOf, hhd, lexemeEntry_of_handed (lexemeHanded_eof _ input)]
            have hf' : (Spec.Lexer.readyFrom fedRun consumer.concrete (fromVersion core.version)
                input true j).failed = false := by rw [hseg]
            simp only [he, ← hf']
            exact eventC consumer sv input hb hj hjle rfl ha hl hh hi hf hhd (bnd j hjle (by
              rw [hj]; simp))
          | error f =>
            have := Spec.Lexer.Runs.lexical (feed := fedRun) (consumer := consumer)
              (start := sv) (input := input) (ended := true) (version := fromVersion core.version)
              (taken := taken)
            rw [settle_not_finished _ _ _ rfl] at this
            rw [vSession_nil]
            simp only [ite_true, vEnd_finish_error consumer core taken ha hf, sessionOf,
              failureOf_lexical (finish_error_kind hf), discardedOf, ha, St.activity,
              Option.map_none]
            exact this
    | cons b bs =>
      obtain ⟨hj', hl'⟩ := drop_succ_of hj
      have hjl : j < input.length := by
        have := congrArg List.length hj
        simp at this
        omega
      rw [← hvs]
      -- a quiet step and the rest, by the induction
      have quiet : ∀ {core' : Core} {st' : St}, vByte consumer core b taken =
          ((.ok none, core'), taken) → core'.version = core.version →
          core'.activity = st'.activity → core'.location = core.location.afterByte b →
          core'.holding = core.holding → core'.initialVersion = core.initialVersion →
          st'.weight ≤ 1 → (consumer.concrete = false → st'.Taken) →
          byteStepW core.version consumer.concrete st core.location b = some (st', []) →
          Spec.Lexer.Runs fedRun consumer sv input ended (fromVersion core.version)
            (entriesOf consumer.concrete core.version
              (streamFromSt core.version consumer.concrete ended st core.location (b :: bs)).1)
            (streamFromSt core.version consumer.concrete ended st core.location (b :: bs)).2
            taken (vSession consumer core none (b :: bs) ended taken) := by
        intro core' st' h hv' ha' hl'' hh' hi' hw htk' hs
        rw [vSession_step_none consumer _ bs ended h, streamFromSt_cons_some hs]
        have := ih bs st' (by simp at hn; omega) (j + 1) core.version core' taken hj' hjl hv' ha'
          (by rw [hl'', hl, hl']) (hh'.trans hh) (hi'.trans hi) htk'
        rw [hl', ← hl] at this
        exact this
      have lexical : ∀ {core' : Core} (k : LexicalErrorKind) (span : Span) (loc : Location),
          vByte consumer core b taken = ((.error ⟨.lexical k, span, loc⟩, core'), taken) →
          (k == .unexpectedTrailingToken) = false →
          core'.version = core.version → discardedOf core' = none →
          streamFromSt core.version consumer.concrete ended st core.location (b :: bs) =
            ([], true) →
          Spec.Lexer.Runs fedRun consumer sv input ended (fromVersion core.version)
            (entriesOf consumer.concrete core.version
              (streamFromSt core.version consumer.concrete ended st core.location (b :: bs)).1)
            (streamFromSt core.version consumer.concrete ended st core.location (b :: bs)).2
            taken (vSession consumer core none (b :: bs) ended taken) := by
        intro core' k span loc h hk hv' hd hs
        rw [vSession_step_error consumer _ bs ended h, hs]
        have := Spec.Lexer.Runs.lexical (feed := fedRun) (consumer := consumer)
          (start := sv) (input := input) (ended := ended) (version := fromVersion core.version)
          (taken := taken)
        rw [settle_not_finished _ _ _ rfl] at this
        simp only [sessionOf, hv', hd, Option.map_none, failureOf_lexical hk]
        exact this
      -- an entry that the byte ends with it, at the boundary after the byte
      have withByte : ∀ {l : Lexeme} (hlv : l.Valid), vByte consumer core b taken =
            vRun consumer (handOverAt (H := Answering consumer) (idleAfter core b) l hlv) taken →
          l.end = core.location.afterByte b → (l.category == .endOfFile) = false →
          (consumer.concrete = false → l.Taken) →
          byteStepW core.version consumer.concrete st core.location b = some (.idle, [l]) →
          Spec.Lexer.Runs fedRun consumer sv input ended (fromVersion core.version)
            (entriesOf consumer.concrete core.version
              (streamFromSt core.version consumer.concrete ended st core.location (b :: bs)).1)
            (streamFromSt core.version consumer.concrete ended st core.location (b :: bs)).2
            taken (vSession consumer core none (b :: bs) ended taken) := by
        intro l hlv hbyte hend hne htl hs
        obtain ⟨hd, hhd⟩ := entry_of consumer core.version htl
        rw [streamFromSt_cons_some hs]
        have hseg := ready_stream consumer.concrete core.version input ended (j + 1) hjl
        have he : entriesOf consumer.concrete core.version ([l] ++ (streamFromSt core.version
            consumer.concrete ended .idle (core.location.afterByte b) bs).1) =
            hd :: (Spec.Lexer.readyFrom fedRun consumer.concrete (fromVersion core.version) input
              ended (j + 1)).handed := by
          rw [hseg]
          simp [entriesOf, hhd, stream, streamFrom_eq, hj', hl', ← hl]
        have hf' : (streamFromSt core.version consumer.concrete ended .idle
            (core.location.afterByte b) bs).2 = (Spec.Lexer.readyFrom fedRun consumer.concrete
              (fromVersion core.version) input ended (j + 1)).failed := by
          rw [hseg]
          simp [stream, streamFrom_eq, hj', hl', ← hl]
        rw [he, hf']
        exact eventA consumer sv input ended hb hj rfl hl hh hi hlv hbyte
          (by rw [hend, hl, hl']) hne hhd (bnd (j + 1) hjl (by rw [hj']; simp at hn; omega))
      cases st with
      | idle =>
        cases hs : start core.version consumer.concrete core.location b with
        | idle =>
          obtain ⟨core', h, hv', ha', hl'', hh', hi'⟩ :=
            lexStart_none consumer core b taken (st := .idle) (by simp [startStepW, hs])
          rw [← lexByte_idle consumer core b taken ha] at h
          exact quiet h hv' ha' hl'' hh' hi' (by simp [St.weight]) (fun _ => trivial)
            (by simp [byteStepW, startStepW, hs])
        | pending p =>
          obtain ⟨core', h, hv', ha', hl'', hh', hi'⟩ :=
            lexStart_none consumer core b taken (st := .token p) (by simp [startStepW, hs])
          rw [← lexByte_idle consumer core b taken ha] at h
          refine quiet h hv' ha' hl'' hh' hi' (by simp [St.weight]) (fun hc => ?_)
            (by simp [byteStepW, startStepW, hs])
          rw [hc] at hs
          exact start_taken hs
        | token l =>
          obtain ⟨hlv, hlex⟩ := lexStart_token consumer core b taken hs
          exact withByte hlv (by rw [lexByte_idle consumer core b taken ha, hlex])
            (start_token_span hs).2 (start_token_ne_eof hs) (fun _ => start_token_taken hs)
            (by simp [byteStepW, startStepW, hs])
        | error f =>
          have h := lexStart_error' consumer core b taken hs
          rw [← lexByte_idle consumer core b taken ha] at h
          exact lexical f.kind f.span f.location h (start_error_kind hs) rfl
            (discardedOf_of_activity (st := .idle) ha)
            (by rw [streamFromSt_cons_none (by simp [byteStepW, startStepW, hs])]; rfl)
      | token p =>
        cases hadv : advance consumer.concrete p core.location b with
        | pending p' =>
          obtain ⟨core', h, hv', ha', hl'', hh', hi'⟩ :=
            lexByte_pending consumer core b taken ha hadv
          refine quiet (st' := .token p') h hv' ha' hl'' hh' hi' (by simp [St.weight])
            (fun hc => ?_) (by simp [byteStepW, hadv])
          rw [hc] at hadv
          exact advance_taken hadv (htk hc)
        | idle =>
          obtain ⟨core', h, hv', ha', hl'', hh', hi'⟩ :=
            lexByte_advance_idle consumer core b taken ha hadv
          exact quiet (st' := .idle) h hv' ha' hl'' hh' hi' (by simp [St.weight])
            (fun _ => trivial) (by simp [byteStepW, hadv])
        | tokenWith l =>
          -- a comment, which only a consumer that takes comments is handed
          obtain ⟨hlv, h⟩ := lexByte_tokenWith consumer core b taken ha hadv
          exact withByte hlv h (advance_tokenWith hadv).2 (advance_lexeme_ne_eof (.inl hadv))
            (fun hc => by rw [hc] at hadv; exact (advance_not_tokenWith hadv).elim)
            (by simp [byteStepW, hadv])
        | tokenBefore l =>
          obtain ⟨hd, hhd⟩ := entry_of consumer core.version (l := l) (fun hc => by
            rw [hc] at hadv
            exact (advance_tokenBefore_taken hadv (htk hc)).2)
          rw [streamFromSt_tokenBefore hadv]
          have hseg := ready_stream consumer.concrete core.version input ended j hjle
          have he : entriesOf consumer.concrete core.version (l :: (streamFromSt core.version
              consumer.concrete ended .idle core.location (b :: bs)).1) =
              hd :: (Spec.Lexer.readyFrom fedRun consumer.concrete (fromVersion core.version)
                input ended j).handed := by
            rw [hseg]
            simp [entriesOf, hhd, stream, streamFrom_eq, hj, ← hl]
          have hf' : (streamFromSt core.version consumer.concrete ended .idle core.location
              (b :: bs)).2 = (Spec.Lexer.readyFrom fedRun consumer.concrete
                (fromVersion core.version) input ended j).failed := by
            rw [hseg]
            simp [stream, streamFrom_eq, hj, ← hl]
          rw [he, hf']
          exact eventB consumer sv input ended hb hj rfl ha hl hh hi hadv hhd
            (bnd j hjle (by rw [hj]; simp [St.weight] at hn ⊢; omega))
        | error f =>
          have h := lexByte_advance_error consumer core b taken ha hadv
          exact lexical f.kind f.span f.location h (advance_error_kind hadv) rfl
            (discardedOf_of_activity (st := .token p) ha)
            (by rw [streamFromSt_cons_none (by simp [byteStepW, hadv])]; simp [failedBeforeW, hadv])

end

end BSmtLib.Proofs.Lexer.VNaive
