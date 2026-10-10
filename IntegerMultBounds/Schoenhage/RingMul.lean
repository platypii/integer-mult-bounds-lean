import IntegerMultBounds.Schoenhage.RingBank

/-! One product modulo `2^N + 1` inside the ring product's bank: the operand
registers `s₁`, `s₂` (tapes of the ring product's own) are loaded onto the
multiplier's input, the size `kN` onto its size tape, the cleaned multiplier
runs on the first 64 tapes, and the product moves to the register `d`
(`runs_mulStep`). Before and after, the multiplier's tapes are all empty. -/

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-- The multiplier's tapes are all empty. -/
def Clean (τ : Fin 𝕌 → WTape) : Prop := τ ∘ ι = fun _ => emp

/-- A tape of the ring product's own. -/
def Own (s : Fin 𝕌) : Prop := 64 ≤ s.val

theorem Own.ne {s : Fin 𝕌} (h : Own s) (i : Fin 𝕋) : s ≠ ι i :=
  fun e => by have := i.isLt; subst e; unfold Own at h; rw [ι_val] at h; omega

theorem Own.ne' {s : Fin 𝕌} (h : Own s) (i : Fin 𝕋) : ι i ≠ s := (h.ne i).symm

theorem SSDone.eq {N v : ℕ} {σ : Fin 𝕋 → WTape} (h : SSDone N v σ) :
    σ = Function.update (fun _ => emp) tIn ⟨[], [rwd N v]⟩ := by
  funext i
  by_cases hi : i = tIn
  · subst hi; simp [h.1]
  · rw [Function.update_of_ne hi, h.2 i hi]

theorem ext_update_ι (τ : Fin 𝕌 → WTape) (σ : Fin 𝕋 → WTape) (i : Fin 𝕋) (v : WTape) :
    ext (Function.update τ (ι i) v) σ = ext τ σ := by
  funext x
  unfold ext
  split_ifs with h
  · rfl
  · rw [Function.update_of_ne]
    intro e; apply h; rw [e]; exact i.isLt

theorem ext_clean {τ : Fin 𝕌 → WTape} (h : Clean τ) : ext τ (fun _ => emp) = τ := by
  rw [← h]; exact ext_self τ

/-- Load the operands and the size. -/
noncomputable def loadSS (s₁ s₂ : Fin 𝕌) (h₁ : s₁ ≠ ι tIn) (h₂ : s₂ ≠ ι tIn) : Cmd 0 𝕌 :=
  .seq (cpy s₁ (ι tIn) h₁) <| .seq (cpy s₂ (ι tIn) h₂) <| .seq (rewind (ι tIn)) <|
  .seq (rewind s₁) <| .seq (rewind s₂) <| .seq (cpy kN (ι pN) (by decide)) <|
  .seq (rewind (ι pN)) (rewind kN)

theorem runs_loadSS {s₁ s₂ : Fin 𝕌} (o₁ : Own s₁) (o₂ : Own s₂) (h12 : s₁ ≠ s₂) (hk1 : s₁ ≠ kN)
    (hk2 : s₂ ≠ kN) {N : ℕ} {x y : List Bool} (τ : Fin 𝕌 → WTape) (hc : Clean τ)
    (hx : τ s₁ = reg x) (hy : τ s₂ = reg y) (hK : τ kN = reg (ones N)) :
    Runs (loadSS s₁ s₂ (o₁.ne tIn) (o₂.ne tIn)) τ
      (· = Function.update (Function.update τ (ι tIn) ⟨[], [x, y]⟩) (ι pN) (reg (ones N)))
      (3 * x.length + 3 * y.length + 3 * N + 60) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  have a1 := o₁.ne' tIn; have a2 := o₂.ne' tIn; have a3 := o₁.ne' pN; have a4 := o₂.ne' pN
  have b1 := o₁.ne tIn; have b2 := o₂.ne tIn; have b3 := o₁.ne pN; have b4 := o₂.ne pN
  have hT := hz tIn; have hP := hz pN
  apply Runs.of_wp
  simp only [loadSS, cpy, WP, wp_op0, wp_rewind]
  tsimp [hx, hy, hK, hT, hP, emp, reg, Rules.output_copy, a1, a2, a3, a4, b1, b2, b3, b4, h12, h12.symm,
    hk1, hk2, hk1.symm, hk2.symm]
  have t1 := time_le Rules.copy x (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.copy y (fun j => j.elim0) 0 (fun j => j.elim0)
  have t3 := time_le Rules.copy (ones N) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i
    by_cases e1 : i = ι tIn
    · subst e1; tsimp [a1, a2, b1, b2, hT]
    by_cases e2 : i = ι pN
    · subst e2; tsimp [a3, a4, b3, b4, hP, reg]
    by_cases e3 : i = s₁
    · subst e3; tsimp [e1, e2, h12, hk1, hx, reg]
    by_cases e4 : i = s₂
    · subst e4; tsimp [e1, e2, h12.symm, hk2, hy, reg]
    by_cases e5 : i = kN
    · subst e5; tsimp [e1, e2, hk1.symm, hk2.symm, hK, reg]
    · tsimp [e1, e2, e3, e4, e5]
  · simp at t1 t2 t3 ⊢; omega

/-- One product: load, multiply, move the product to `d`. -/
noncomputable def mulStep (s₁ s₂ d : Fin 𝕌) (o₁ : Own s₁) (o₂ : Own s₂) (od : Own d) : Cmd 0 𝕌 :=
  .seq (loadSS s₁ s₂ (o₁.ne tIn) (o₂.ne tIn)) <| .seq (up ssClean) (regMove (ι tIn) d (od.ne' tIn))

theorem runs_mulStep {s₁ s₂ d : Fin 𝕌} (o₁ : Own s₁) (o₂ : Own s₂) (od : Own d) (h12 : s₁ ≠ s₂)
    (hk1 : s₁ ≠ kN) (hk2 : s₂ ≠ kN) {N x y : ℕ} (hN : 0 < N) (hk : 2 ^ kOf N ∣ N) (hxF : x < Fm N)
    (hyF : y < Fm N) (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hx : τ s₁ = reg (rwd N x))
    (hy : τ s₂ = reg (rwd N y)) (hK : τ kN = reg (ones N)) (hd : τ d = emp) :
    Runs (mulStep s₁ s₂ d o₁ o₂ od) τ (· = Function.update τ d (reg (rwd N (x * y % Fm N))))
      (ssCost N [x, y] + 40 * N + 6000) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  have s1 := runs_loadSS o₁ o₂ h12 hk1 hk2 τ hc hx hy hK
  set τ₁ := Function.update (Function.update τ (ι tIn) ⟨[], [rwd N x, rwd N y]⟩) (ι pN) (reg (ones N))
  have hS : SSStart N x y (τ₁ ∘ ι) := by
    have e : τ₁ ∘ ι = Function.update (Function.update (fun _ => emp) tIn ⟨[], [rwd N x, rwd N y]⟩)
        pN (reg (ones N)) := by
      simp only [τ₁, comp_ι_update]; rw [hc]
    rw [e]
    refine ⟨by tsimp, by tsimp, fun i h1 h2 => ?_⟩
    rw [Function.update_of_ne h2, Function.update_of_ne h1]
  set v := x * y % Fm N
  have s2 : Runs (up ssClean) τ₁ (· = Function.update τ (ι tIn) (reg (rwd N v)))
      (ssCost N [x, y] + 1 + (20 * N + 5000)) := by
    refine runs_up' ((runs_ssClean hN hk hxF hyF (τ₁ ∘ ι) hS).mono (fun σ' h => h.eq) le_rfl) ?_
    rw [ext_update]
    simp only [τ₁, ext_update_ι, ext_clean hc]
    rfl
  have s3 := runs_regMove (a := 0) (od.ne' tIn) (Function.update τ (ι tIn) (reg (rwd N v)))
    (w := rwd N v) (by simp) (by rw [Function.update_of_ne (od.ne tIn), hd])
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ' h => ?_) ?_
  · have e : Function.update τ (ι tIn) emp = τ := by rw [← hz tIn]; exact Function.update_eq_self _ _
    rw [h, Function.update_idem, e]
  · simp only [rwd_length]; omega

end IntegerMultBounds.Schoenhage
