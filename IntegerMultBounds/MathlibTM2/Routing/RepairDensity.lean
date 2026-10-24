module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCore

/-! Price the executed exceptional-sort term using R1's physical bad-set density. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {K : ℕ}

noncomputable def repairDensityScanCost (p : Par) (X rb R B : ℕ) (scale : ℝ) : ℝ :=
  let k := fieldsLen (selectiveKeyLen p X rb)
  let M := R * 2 ^ fieldsLen (selectiveLen p X)
  ((M * (2 * idxStepCost (badClassifierCost p.wy) (k + B) (selectiveLen p X) +
    6 * (k + B) + 15)) : ℕ) +
    (k : ℝ) * (5 / (128 * scale ^ 3) * (M : ℝ) * ((12 * k + 6 * B + 13) : ℕ)) +
    ((10 * k + 8 * fieldsLen (selectiveLen p X) + 8 * 5 + 18) : ℕ)

/-- Uniform scan/sort ledger retaining the physical exceptional-density factor. -/
noncomputable def repairUniformDensityScanCost (n rb R B : ℕ) (scale : ℝ) : ℝ :=
  (R * 2 ^ n * (76 * n + 14 * (n + rb + B) + 195) : ℕ) +
    ((n + rb : ℕ) : ℝ) * (5 / (128 * scale ^ 3) * (R * 2 ^ n : ℕ) *
      (12 * (n + rb) + 6 * B + 13 : ℕ)) + (10 * (n + rb) + 8 * n + 58 : ℕ)

theorem repairUniformDensityScanCost_amortized (n rb R B : ℕ) (scale : ℝ)
    (hscale : 0 < scale) (hR : 1 ≤ R) (hB : (n + rb + 1) ^ 2 ≤ B) :
    repairUniformDensityScanCost n rb R B scale ≤
      (389 * (R * 2 ^ n * B) : ℕ) +
        ((n + rb : ℕ) : ℝ) * (155 / (128 * scale ^ 3)) * (R * 2 ^ n * B : ℕ) := by
  let M := R * 2 ^ n
  have hM : 1 ≤ M := by
    have hp := Nat.two_pow_pos n
    dsimp only [M]
    nlinarith
  have hlinear : n + rb + 1 ≤ B := by nlinarith
  have hi : 76 * n + 14 * (n + rb + B) + 195 ≤ 313 * B := by omega
  have hm := Nat.mul_le_mul_left M hi
  have hc : 10 * (n + rb) + 8 * n + 58 ≤ 76 * B := by omega
  have hv : B ≤ M * B := by simpa using Nat.mul_le_mul_right B hM
  have hd : M * (76 * n + 14 * (n + rb + B) + 195) +
      (10 * (n + rb) + 8 * n + 58) ≤ 389 * (M * B) := by nlinarith only [hm, hc, hv]
  have hl : 12 * (n + rb) + 6 * B + 13 ≤ 31 * B := by omega
  have hs := mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℝ).mpr hl)
    (show 0 ≤ ((n + rb : ℕ) : ℝ) * (5 / (128 * scale ^ 3)) * (M : ℝ) by positivity)
  have hd' := Nat.cast_le (α := ℝ).mpr hd
  unfold repairUniformDensityScanCost
  dsimp only [M] at hd' hs
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hd' hs ⊢
  simp only [div_eq_mul_inv] at hs ⊢
  nlinarith only [hd', hs]

theorem repairDensityScanCost_le (p : Par) (X rb R B n : ℕ) (scale : ℝ)
    (hfields : fieldsLen (selectiveLen p X) = n) (hwy : p.wy ≤ n) :
    repairDensityScanCost p X rb R B scale ≤ repairUniformDensityScanCost n rb R B scale := by
  have hcoeff : 2 * (badClassifierCost p.wy + 4 * (n + rb + B) + 4 * n + 4 * 5 + 8) +
      6 * (n + rb + B) + 15 ≤ 76 * n + 14 * (n + rb + B) + 195 := by
    unfold badClassifierCost
    omega
  have hmain := Nat.mul_le_mul_left (R * 2 ^ n) hcoeff
  have hsum : (∑ f, selectiveLen p X f) = n := hfields
  unfold repairDensityScanCost repairUniformDensityScanCost
  dsimp only
  simp only [selectiveKeyWidth, hfields, idxStepCost, hsum]
  norm_num only [show 4 * 5 = 20 by decide, show 8 * 5 + 18 = 58 by decide] at hmain ⊢
  refine add_le_add (add_le_add ?_ (le_refl _)) (le_refl _)
  exact_mod_cast hmain

theorem repairScanCost_density (p : Par) (X rb R B : ℕ) (hguard : p.G + 1 < p.K)
    (scale : ℝ) (hscale : 0 < scale) (hn : (p.n : ℝ) ≤ scale)
    (hradix : 64 * scale ^ 4 ≤ (2 : ℝ) ^ p.G)
    (hgap : 1024 * scale ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G)) :
    (repairScanCost p X rb R B : ℝ) ≤ repairDensityScanCost p X rb R B scale := by
  have hd := selectiveRepair_sortCost_density p X R (fieldsLen (selectiveKeyLen p X rb)) B
    hguard scale hscale hn hradix hgap
  unfold repairScanCost repairDensityScanCost
  dsimp only
  push_cast at hd ⊢
  linarith

noncomputable def repairDensityCoreCost (p : Par) (X rb R B : ℕ) (scale : ℝ)
    (S : Stacks repairT (prime + K)) : ℝ :=
  selectiveKeyPassCost p X rb (R * 2 ^ fieldsLen (selectiveLen p X)) B +
    ((progW.map (fun o => selectiveOpCost p X repairT R (fieldsLen (selectiveKeyLen p X rb) + B)
      (fun c => ∑ j, (S.R (repairHost.swaps c j)).length) o.1)).sum + 1) +
    repairDensityScanCost p X rb R B scale

/-- The complete executed repair core, preserving compact-swap and sparse-sort prices. -/
theorem repairDensityCoreCost_le (p : Par) (X rb R B n bankBound : ℕ) (scale : ℝ)
    (S : Stacks repairT (prime + K)) (hfields : fieldsLen (selectiveLen p X) = n)
    (hwy : p.wy ≤ n) (hbank : ∀ c, (∑ j, (S.R (repairHost.swaps c j)).length) ≤ bankBound) :
    repairDensityCoreCost p X rb R B scale S ≤
      (selectiveUniformKeyPassCost n rb (R * 2 ^ n) B : ℕ) +
      (12 * (selectiveUniformRotationCost n (R * 2 ^ n) (n + rb + B) : ℕ) +
        12 * selectiveUniformSwapCost repairT (R * 2 ^ n) (n + rb + B) p.wc bankBound + 1) +
      repairUniformDensityScanCost n rb R B scale := by
  have hk : (selectiveKeyPassCost p X rb (R * 2 ^ fieldsLen (selectiveLen p X)) B : ℝ) ≤
      (selectiveUniformKeyPassCost n rb (R * 2 ^ n) B : ℕ) := by
    rw [hfields]
    exact_mod_cast selectiveKeyPassCost_le p X rb (R * 2 ^ n) B n hfields
  have hs := selectiveCost_sum_le p X repairT R (fieldsLen (selectiveKeyLen p X rb) + B) n bankBound
    (fun c => ∑ j, (S.R (repairHost.swaps c j)).length) hfields hbank
  rw [selectiveKeyWidth, hfields] at hs
  unfold repairDensityCoreCost
  refine add_le_add ?_ (repairDensityScanCost_le p X rb R B n scale hfields hwy)
  refine add_le_add hk ?_
  rw [selectiveKeyWidth, hfields]
  exact add_le_add hs (le_refl (1 : ℝ))

theorem repairDensityCoreCost_amortized (p : Par) (X rb R B n bankBound : ℕ) (scale : ℝ)
    (S : Stacks repairT (prime + K)) (hfields : fieldsLen (selectiveLen p X) = n)
    (hwy : p.wy ≤ n) (hbank : ∀ c, (∑ j, (S.R (repairHost.swaps c j)).length) ≤ bankBound)
    (hR : 1 ≤ R) (hB : (n + rb + 1) ^ 2 ≤ B) :
    repairDensityCoreCost p X rb R B scale S ≤
      (4988 * (R * 2 ^ n * B) : ℕ) +
        12 * selectiveUniformSwapCost repairT (R * 2 ^ n) (n + rb + B) p.wc bankBound + 1 +
        repairUniformDensityScanCost n rb R B scale := by
  have hM : 1 ≤ R * 2 ^ n := by
    have hp := Nat.two_pow_pos n
    nlinarith
  have hc := repairDensityCoreCost_le p X rb R B n bankBound scale S hfields hwy hbank
  have hk : (selectiveUniformKeyPassCost n rb (R * 2 ^ n) B : ℝ) ≤
      (188 * (R * 2 ^ n * B) : ℕ) :=
    Nat.cast_le.mpr (selectiveUniformKeyPassCost_amortized n rb (R * 2 ^ n) B hM hB)
  have hr : (selectiveUniformRotationCost n (R * 2 ^ n) (n + rb + B) : ℝ) ≤
      (400 * (R * 2 ^ n * B) : ℕ) :=
    Nat.cast_le.mpr (selectiveUniformRotationCost_amortized n rb (R * 2 ^ n) B hM hB)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hk hr ⊢
  linarith only [hc, hk, hr]

theorem repairDensityCoreCost_amortized_swaps (p : Par) (X rb R B n bankBound : ℕ) (scale : ℝ)
    (S : Stacks repairT (prime + K)) (hfields : fieldsLen (selectiveLen p X) = n)
    (hwy : p.wy ≤ n) (hbank : ∀ c, (∑ j, (S.R (repairHost.swaps c j)).length) ≤ bankBound)
    (hR : 1 ≤ R) (hB : (n + rb + 1) ^ 2 ≤ B)
    (hsetup : 6 * bankBound + 2 * repairT + 6 * swapT 6 + 23 ≤ R * 2 ^ n * B) :
    repairDensityCoreCost p X rb R B scale S ≤
      (5816 * (R * 2 ^ n * B) : ℕ) +
        72 * swapConst * (repairT + 12 * swapT 6 + 5 : ℕ) * (R * 2 ^ n * B : ℕ) *
          ((max 1 p.wc : ℕ) : ℝ) ^ Parameters.tau + 1 +
        repairUniformDensityScanCost n rb R B scale := by
  have hc := repairDensityCoreCost_amortized p X rb R B n bankBound scale S hfields hwy hbank hR hB
  have hlong : n + rb ≤ B := by nlinarith only [hB]
  have hs := selectiveUniformSwapCost_amortized repairT n rb (R * 2 ^ n) B p.wc bankBound hlong hsetup
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hc hs ⊢
  linarith only [hc, hs]

theorem repairDensityCoreCost_long_records (p : Par) (X rb R B n bankBound : ℕ) (scale : ℝ)
    (S : Stacks repairT (prime + K)) (hfields : fieldsLen (selectiveLen p X) = n)
    (hwy : p.wy ≤ n) (hbank : ∀ c, (∑ j, (S.R (repairHost.swaps c j)).length) ≤ bankBound)
    (hscale : 0 < scale) (hR : 1 ≤ R) (hB : (n + rb + 1) ^ 2 ≤ B)
    (hsetup : 6 * bankBound + 2 * repairT + 6 * swapT 6 + 23 ≤ R * 2 ^ n * B) :
    repairDensityCoreCost p X rb R B scale S ≤
      (6205 * (R * 2 ^ n * B) : ℕ) +
        72 * swapConst * (repairT + 12 * swapT 6 + 5 : ℕ) * (R * 2 ^ n * B : ℕ) *
          ((max 1 p.wc : ℕ) : ℝ) ^ Parameters.tau + 1 +
        ((n + rb : ℕ) : ℝ) * (155 / (128 * scale ^ 3)) * (R * 2 ^ n * B : ℕ) := by
  have hc := repairDensityCoreCost_amortized_swaps p X rb R B n bankBound scale S
    hfields hwy hbank hR hB hsetup
  have hs := repairUniformDensityScanCost_amortized n rb R B scale hscale hR hB
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hc hs ⊢
  linarith only [hc, hs]

theorem repairDensityCoreCost_long_records_density (p : Par) (X rb R B n bankBound : ℕ) (scale : ℝ)
    (S : Stacks repairT (prime + K)) (hfields : fieldsLen (selectiveLen p X) = n)
    (hwy : p.wy ≤ n) (hbank : ∀ c, (∑ j, (S.R (repairHost.swaps c j)).length) ≤ bankBound)
    (hscale : 0 < scale) (hkey : ((n + rb : ℕ) : ℝ) ≤ scale ^ 3)
    (hR : 1 ≤ R) (hB : (n + rb + 1) ^ 2 ≤ B)
    (hsetup : 6 * bankBound + 2 * repairT + 6 * swapT 6 + 23 ≤ R * 2 ^ n * B) :
    repairDensityCoreCost p X rb R B scale S ≤
      (6207 * (R * 2 ^ n * B) : ℕ) +
        72 * swapConst * (repairT + 12 * swapT 6 + 5 : ℕ) * (R * 2 ^ n * B : ℕ) *
          ((max 1 p.wc : ℕ) : ℝ) ^ Parameters.tau + 1 := by
  have hc := repairDensityCoreCost_long_records p X rb R B n bankBound scale S
    hfields hwy hbank hscale hR hB hsetup
  have hden : 0 < 128 * scale ^ 3 := by positivity
  have hd : ((n + rb : ℕ) : ℝ) * (155 / (128 * scale ^ 3)) ≤ 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).2
    nlinarith only [hkey, pow_pos hscale 3]
  have hm := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (R * 2 ^ n * B))
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hc hm ⊢
  linarith only [hc, hm]

/-- The canonical density scale absorbs the sparse correction when the row key
is no wider than the coordinate key. Other row regimes remain separate. -/
theorem repairUniformDensityScanCost_canonical_amortized (n rb R B : ℕ)
    (hrow : rb ≤ n) (hR : 1 ≤ R) (hB : (n + rb + 1) ^ 2 ≤ B) :
    repairUniformDensityScanCost n rb R B (n + 1 : ℕ) ≤
      (391 * (R * 2 ^ n * B) : ℕ) := by
  have hscale : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hkeyNat : n + rb ≤ (n + 1) ^ 3 := by
    nlinarith only [hrow, Nat.zero_le n, Nat.zero_le (n * n)]
  have hkey : ((n + rb : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast hkeyNat
  have hd : ((n + rb : ℕ) : ℝ) * (155 / (128 * ((n + 1 : ℕ) : ℝ) ^ 3)) ≤ 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [hkey, pow_pos hscale 3]
  have hc := repairUniformDensityScanCost_amortized n rb R B (n + 1 : ℕ) hscale hR hB
  have hm := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (R * 2 ^ n * B))
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hc hm ⊢
  linarith only [hc, hm]

theorem repairCoreCost_density (p : Par) (X rb R B : ℕ) (hguard : p.G + 1 < p.K)
    (scale : ℝ) (hscale : 0 < scale) (hn : (p.n : ℝ) ≤ scale)
    (hradix : 64 * scale ^ 4 ≤ (2 : ℝ) ^ p.G)
    (hgap : 1024 * scale ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G))
    (S : Stacks repairT (prime + K)) :
    repairCoreCost p X rb R B S ≤ repairDensityCoreCost p X rb R B scale S := by
  have hd := repairScanCost_density p X rb R B hguard scale hscale hn hradix hgap
  unfold repairCoreCost repairDensityCoreCost
  linarith

end IntegerMultBounds.MathlibTM2.Routing
