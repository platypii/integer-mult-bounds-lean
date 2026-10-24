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
