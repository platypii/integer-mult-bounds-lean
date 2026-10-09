import IntegerMultBounds.Schoenhage.Wp

/-! Word-list fragments on arbitrary tapes: copy the current word, skip it,
append every remaining word of one tape to another, and copy as many words as
a tick tape holds. Each has an exact effect and a step bound linear in the
words moved. -/

namespace IntegerMultBounds.Schoenhage

open Machine Strm

variable {a t : ℕ}

/-- Copy the current word of `s` to the end of `d`. -/
noncomputable def cpy (s d : Fin t) (h : s ≠ d) : Cmd a t := op0 Rules.copy false s d h

/-- Step past the current word of `s` (the junk tape `j` stays unchanged). -/
noncomputable def skp (s j : Fin t) (h : s ≠ j) : Cmd a t := op0 Rules.skip false s j h

theorem time_copy (w : List Bool) (ws : Fin 0 → List Bool) : time Rules.copy w ws = w.length + 6 := by
  have h := (Rules.go_copy w ws).2
  simp [time, rest, h]

theorem time_skip (w : List Bool) (ws : Fin 0 → List Bool) : time Rules.skip w ws = w.length + 5 := by
  simp [time, rest]

theorem runs_cpy {s d : Fin t} (h : s ≠ d) (σ : Fin t → WTape) (hs : (σ s).right ≠ [])
    (hd : (σ d).right = []) :
    Runs (a := a) (cpy s d h) σ
      (· = Function.update (Function.update σ s (σ s).next) d ((σ d).put false [(σ s).cur]))
      ((σ s).cur.length + 6) := by
  apply Runs.of_wp
  simp only [cpy, wp_op0, Rules.output_copy, parse_syms]
  refine ⟨⟨hs, hd, ?_, ?_⟩, ?_, ?_⟩ <;> simp [time_copy]

theorem put_nil (T : WTape) (h : T.right = []) : T.put false [] = T := by
  cases T; simp_all [WTape.put]

theorem runs_skp {s j : Fin t} (h : s ≠ j) (σ : Fin t → WTape) (hs : (σ s).right ≠ [])
    (hj : (σ j).right = []) :
    Runs (a := a) (skp s j h) σ (· = Function.update σ s (σ s).next) ((σ s).cur.length + 5) := by
  apply Runs.of_wp
  simp only [skp, wp_op0, Rules.output_skip, parse_syms]
  refine ⟨⟨hs, hj, ?_, ?_⟩, ?_, ?_⟩
  · simp
  · simp
  rotate_left
  · simp [time_skip]
  funext x
  by_cases hx : x = j
  · subst hx; simp [h.symm]
    exact put_nil _ hj
  · simp [Function.update_apply, hx]

/-- Append every remaining word of `s` to `d`. -/
noncomputable def appendAll (s d : Fin t) (h : s ≠ d) : Cmd a t := .loop s (cpy s d h)

theorem runs_appendAll {s d : Fin t} (h : s ≠ d) (W : ℕ) :
    ∀ (R : List (List Bool)) (σ : Fin t → WTape) (L M : List (List Bool)),
      σ s = ⟨L, R⟩ → σ d = ⟨M, []⟩ → (∀ w ∈ R, w.length ≤ W) →
      Runs (a := a) (appendAll s d h) σ
        (· = Function.update (Function.update σ s ⟨R.reverse ++ L, []⟩) d ⟨R.reverse ++ M, []⟩)
        (R.length * (W + 8))
  | [], σ, L, M, hs, hd, _ => by
    show Runs (Cmd.loop s (cpy s d h)) _ _ _
    refine (Runs.loop_done (by simp [hs]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext x
    by_cases hxd : x = d
    · subst hxd; simp [hd]
    · by_cases hxs : x = s
      · subst hxs; simp [hxd, hs]
      · simp [hxd, hxs]
  | w :: R, σ, L, M, hs, hd, hW => by
    show Runs (Cmd.loop s (cpy s d h)) _ _ _
    have h1 := runs_cpy (a := a) h σ (by simp [hs]) (by simp [hd])
    have hw : w.length ≤ W := hW w (by simp)
    set σ₁ := Function.update (Function.update σ s (σ s).next) d ((σ d).put false [(σ s).cur])
    have hs₁ : σ₁ s = ⟨w :: L, R⟩ := by simp [σ₁, h, hs, WTape.next, WTape.cur]
    have hd₁ : σ₁ d = ⟨w :: M, []⟩ := by
      simp [σ₁, hs, hd, WTape.cur]
    have ih := runs_appendAll h W R σ₁ (w :: L) (w :: M) hs₁ hd₁ (fun v hv => hW v (by simp [hv]))
    unfold appendAll at ih
    refine (Runs.loop_step (by simp [hs]) (h1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      funext x
      by_cases hxd : x = d
      · subst hxd; simp
      · by_cases hxs : x = s
        · subst hxs; simp [hxd]
        · simp [σ₁, hxd, hxs]
    · simp only [hs, WTape.cur, List.headD_cons, List.length_cons]; nlinarith

/-- Copy one word of `s` to `d` per word of the tick tape `k` (junk tape `j`). -/
noncomputable def moveN (k s d j : Fin t) (h1 : s ≠ d) (h2 : k ≠ j) : Cmd a t :=
  .loop k (.seq (cpy s d h1) (skp k j h2))

theorem runs_moveN {k s d j : Fin t} (h1 : s ≠ d) (h2 : k ≠ j) (hks : k ≠ s) (hkd : k ≠ d)
    (hsj : s ≠ j) (hdj : d ≠ j) (W : ℕ) :
    ∀ (Tk : List (List Bool)) (σ : Fin t → WTape) (TL L R1 R2 M : List (List Bool)),
      σ k = ⟨TL, Tk⟩ → σ s = ⟨L, R1 ++ R2⟩ → R1.length = Tk.length → σ d = ⟨M, []⟩ →
      (σ j).right = [] → (∀ w ∈ R1, w.length ≤ W) → (∀ w ∈ Tk, w.length ≤ W) →
      Runs (a := a) (moveN k s d j h1 h2) σ
        (· = Function.update (Function.update (Function.update σ k ⟨Tk.reverse ++ TL, []⟩) s
          ⟨R1.reverse ++ L, R2⟩) d ⟨R1.reverse ++ M, []⟩)
        (Tk.length * (2 * W + 15))
  | [], σ, TL, L, R1, R2, M, hk, hs, hl, hd, hj, _, _ => by
    show Runs (Cmd.loop k _) _ _ _
    have hR1 : R1 = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst hR1
    refine (Runs.loop_done (by simp [hk]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext x
    by_cases hxd : x = d
    · subst hxd; simp [hd]
    · by_cases hxs : x = s
      · subst hxs; simp [hxd, hs]
      · by_cases hxk : x = k
        · subst hxk; simp [hxd, hxs, hk]
        · simp [hxd, hxs, hxk]
  | tk :: Tk, σ, TL, L, R1, R2, M, hk, hs, hl, hd, hj, hW, hT => by
    show Runs (Cmd.loop k _) _ _ _
    obtain ⟨w, R1', rfl⟩ : ∃ w R1', R1 = w :: R1' := by
      cases R1 with
      | nil => simp at hl
      | cons w R1' => exact ⟨w, R1', rfl⟩
    have hw : w.length ≤ W := hW w (by simp)
    have htk : tk.length ≤ W := hT tk (by simp)
    have c1 := runs_cpy (a := a) h1 σ (by simp [hs]) (by simp [hd])
    set σ₁ := Function.update (Function.update σ s (σ s).next) d ((σ d).put false [(σ s).cur])
    have hk₁ : σ₁ k = ⟨TL, tk :: Tk⟩ := by simp [σ₁, hks, hkd, hk]
    have hj₁ : (σ₁ j).right = [] := by simp [σ₁, hsj.symm, hdj.symm, hj]
    have c2 := runs_skp (a := a) h2 σ₁ (by simp [hk₁]) hj₁
    set σ₂ := Function.update σ₁ k (σ₁ k).next
    have hk₂ : σ₂ k = ⟨tk :: TL, Tk⟩ := by simp [σ₂, hk₁, WTape.next, WTape.cur]
    have hs₂ : σ₂ s = ⟨w :: L, R1' ++ R2⟩ := by
      simp [σ₂, σ₁, hks.symm, h1, hs, WTape.next, WTape.cur]
    have hd₂ : σ₂ d = ⟨w :: M, []⟩ := by
      simp [σ₂, σ₁, hkd.symm, hs, hd, WTape.cur]
    have hj₂ : (σ₂ j).right = [] := by simp [σ₂, h2.symm, hj₁]
    have ih := runs_moveN h1 h2 hks hkd hsj hdj W Tk σ₂ (tk :: TL) (w :: L) R1' R2 (w :: M) hk₂ hs₂
      (by simpa using hl) hd₂ hj₂ (fun v hv => hW v (by simp [hv])) (fun v hv => hT v (by simp [hv]))
    unfold moveN at ih
    refine (Runs.loop_step (by simp [hk])
      (Runs.then c1 (c2.mono (fun σ' h' => by rw [h']; exact ih) le_rfl))).mono (fun σ' h' => ?_) ?_
    · rw [h']
      funext x
      by_cases hxd : x = d
      · subst hxd; simp
      · by_cases hxs : x = s
        · subst hxs; simp [hxd]
        · by_cases hxk : x = k
          · subst hxk; simp [hxd, hxs]
          · simp [σ₂, σ₁, hxd, hxs, hxk]
    · simp only [hs, hk₁, WTape.cur, List.headD_cons, List.length_cons, List.cons_append]
      nlinarith

end IntegerMultBounds.Schoenhage

namespace IntegerMultBounds.Schoenhage

open Machine Strm

variable {a t : ℕ}

/-! ### Register moves -/

/-- Load the current word of `s` into the empty register `r`. -/
noncomputable def regIn (s r : Fin t) (h : s ≠ r) : Cmd a t := .seq (cpy s r h) (rewind r)

theorem runs_regIn {s r : Fin t} (h : s ≠ r) (σ : Fin t → WTape) {L R : List (List Bool)} {w : List Bool}
    (hs : σ s = ⟨L, w :: R⟩) (hr : σ r = emp) :
    Runs (a := a) (regIn s r h) σ (· = Function.update (Function.update σ s ⟨w :: L, R⟩) r (reg w))
      (2 * w.length + 12) := by
  apply Runs.of_wp
  simp only [regIn, WP, cpy, wp_op0, wp_rewind, Rules.output_copy, parse_syms]
  refine ⟨⟨by simp [hs], by simp [hr, emp], by simp, by simp⟩, ?_, ?_⟩
  · funext x
    by_cases hx : x = r
    · subst hx; simp [hs, hr, emp, reg, WTape.put]
    · by_cases hxs : x = s
      · subst hxs; simp [hx, hs, WTape.next]
      · simp [hx, hxs]
  · simp [hs, hr, h.symm, time_copy, emp, clen]; omega

/-- Append the register `r` to `d` and empty `r`. -/
noncomputable def regOut (r d : Fin t) (h : r ≠ d) : Cmd a t := .seq (cpy r d h) (clear r)

theorem runs_regOut {r d : Fin t} (h : r ≠ d) (σ : Fin t → WTape) {M : List (List Bool)} {w : List Bool}
    (hr : σ r = reg w) (hd : σ d = ⟨M, []⟩) :
    Runs (a := a) (regOut r d h) σ (· = Function.update (Function.update σ r emp) d ⟨w :: M, []⟩)
      (3 * w.length + 12) := by
  apply Runs.of_wp
  simp only [regOut, WP, cpy, wp_op0, wp_clear, Rules.output_copy, parse_syms]
  refine ⟨⟨by simp [hr, reg], by simp [hd], by simp, by simp⟩, ?_, ?_⟩
  · funext x
    by_cases hx : x = d
    · subst hx; simp [h.symm, hd, hr, reg]
    · by_cases hxr : x = r
      · subst hxr; simp [hx, emp]
      · simp [hx, hxr]
  · simp [hr, hd, h, time_copy, reg, clen, WTape.words]; omega

/-- Move register `r` into the empty register `r'`. -/
noncomputable def regMove (r r' : Fin t) (h : r ≠ r') : Cmd a t := .seq (regIn r r' h) (clear r)

theorem runs_regMove {r r' : Fin t} (h : r ≠ r') (σ : Fin t → WTape) {w : List Bool}
    (hr : σ r = reg w) (hr' : σ r' = emp) :
    Runs (a := a) (regMove r r' h) σ (· = Function.update (Function.update σ r emp) r' (reg w))
      (4 * w.length + 20) := by
  refine (Runs.then (runs_regIn h σ (L := []) (R := []) (w := w) (by simpa [reg] using hr) hr')
    (runs_clear r _)).mono (fun σ' h' => ?_) ?_
  · rw [h']; funext x
    by_cases hx : x = r'
    · subst hx; simp [h.symm]
    · by_cases hxr : x = r
      · subst hxr; simp [hx, emp]
      · simp [hx, hxr]
  · simp [h, clen, WTape.words]; omega

/-- Copy register `r` into the empty register `r'`, keeping `r`. -/
noncomputable def regDup (r r' : Fin t) (h : r ≠ r') : Cmd a t := .seq (regIn r r' h) (rewind r)

theorem runs_regDup {r r' : Fin t} (h : r ≠ r') (σ : Fin t → WTape) {w : List Bool}
    (hr : σ r = reg w) (hr' : σ r' = emp) :
    Runs (a := a) (regDup r r' h) σ (· = Function.update σ r' (reg w)) (3 * w.length + 20) := by
  refine (Runs.then (runs_regIn h σ (L := []) (R := []) (w := w) (by simpa [reg] using hr) hr')
    (runs_rewind r _)).mono (fun σ' h' => ?_) ?_
  · rw [h']; funext x
    by_cases hx : x = r'
    · subst hx; simp [h.symm]
    · by_cases hxr : x = r
      · subst hxr; simp [hx, hr, reg]
      · simp [hx, hxr]
  · simp [h, clen]; omega

end IntegerMultBounds.Schoenhage
