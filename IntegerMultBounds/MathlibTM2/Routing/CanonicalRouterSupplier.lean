module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterAmortized

/-! Bound both physical reservoir and compact supplier widths by address width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
noncomputable section

theorem canonicalRouterSupplierWidths_le (n : ℕ) (hn : canonicalRouterStride n ≤ n) :
    max 1 (3 * routingReservoirWidth n (canonicalRouterGap n)) ≤ n ∧
      max 1 (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) ≤ n := by
  have hg := canonicalRouterGap_pos n
  have hres := routingReservoir_fit n (canonicalRouterGap n) hn
  have hb := routerBorrowed_le_reservoir n (canonicalRouterGap n) hg
  have hn0 : 1 ≤ n := by unfold canonicalRouterStride at hn; omega
  change routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) ≤ _ at hb
  exact ⟨max_le hn0 (by omega), max_le hn0 (by omega)⟩

theorem canonicalRouterPlacementSupplierCost_le (n R B : ℕ) (hn : canonicalRouterStride n ≤ n) :
    canonicalRouterPlacementSupplierCost n R B ≤
      9 * swapConst * (inactiveClassifierPlacementT 6 + 12 * swapT 6 + 5 : ℕ) *
        (R * 2 ^ n * B : ℕ) * (n : ℝ) ^ Parameters.tau := by
  have hw := canonicalRouterSupplierWidths_le n hn
  have htau : (0 : ℝ) ≤ Parameters.tau := by norm_num [Parameters.tau]
  have h₁ := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (max 1
    (3 * routingReservoirWidth n (canonicalRouterGap n)) : ℕ))
    (Nat.cast_le (α := ℝ).mpr hw.1) htau
  have h₂ := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (max 1
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) : ℕ))
    (Nat.cast_le (α := ℝ).mpr hw.2) htau
  have hsum : ((max 1 (3 * routingReservoirWidth n (canonicalRouterGap n)) : ℕ) : ℝ) ^ Parameters.tau +
      2 * ((max 1 (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) : ℕ) : ℝ) ^
        Parameters.tau ≤ 3 * (n : ℝ) ^ Parameters.tau := by linarith only [h₁, h₂]
  have hswap := swapConst_pos
  have hm := mul_le_mul_of_nonneg_left hsum
    (show (0 : ℝ) ≤ 3 * swapConst * (inactiveClassifierPlacementT 6 + 12 * swapT 6 + 5 : ℕ) *
      (R * 2 ^ n * B : ℕ) by positivity)
  dsimp only [canonicalRouterPlacementSupplierCost]
  nlinarith only [hm]

def canonicalRouterStageSupplierCoefficient : ℝ :=
  18 * swapConst * (inactiveClassifierPlacementT 6 + 12 * swapT 6 + 5 : ℕ) +
    72 * swapConst * (repairT + 12 * swapT 6 + 5 : ℕ)

/-- Every supplier contribution in a residue stage has the address-width power. -/
theorem canonicalRouterStageAmortizedBound_supplier_le (n B : ℕ)
    (hn : canonicalRouterStride n ≤ n) :
    canonicalRouterStageAmortizedBound n B ≤
      (canonicalRouterStageDimensionOverhead n : ℕ) + (9499 * (2 ^ n * B) : ℕ) +
        canonicalRouterStageSupplierCoefficient * (2 ^ n * B : ℕ) * (n : ℝ) ^ Parameters.tau + 1 := by
  have hp := canonicalRouterPlacementSupplierCost_le n 1 B hn
  have hw := (canonicalRouterSupplierWidths_le n hn).2
  have htau : (0 : ℝ) ≤ Parameters.tau := by norm_num [Parameters.tau]
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (max 1
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) : ℕ))
    (Nat.cast_le (α := ℝ).mpr hw) htau
  have hswap := swapConst_pos
  have hm := mul_le_mul_of_nonneg_left hpow
    (show (0 : ℝ) ≤ 72 * swapConst * (repairT + 12 * swapT 6 + 5 : ℕ) * (2 ^ n * B : ℕ) by positivity)
  unfold canonicalRouterStageAmortizedBound canonicalRouterStageSupplierCoefficient
  simp only [Nat.one_mul] at hp
  linarith only [hp, hm]

def canonicalRouterDirectionalDimensionCost (n count : ℕ) : ℝ :=
  canonicalTerminalPrice n 0 0 (canonicalScalarWidth n) 0 1 (131 * canonicalRouterGap n) +
    (count * (canonicalRouterStageDimensionOverhead n + 1) +
      canonicalRouterDirectionalSetupBudget n 1 0 (canonicalScalarWidth n) 0 1 count : ℕ)

def canonicalRouterDirectionalVolumeCoefficient (n count : ℕ) : ℝ :=
  (131 * canonicalRouterGap n : ℕ) *
      (6 * swapConst * (canonicalTerminalT + 12 * swapT 6 + 5 : ℕ) + 275 + 12 * swapT 6) +
    27 + (9499 * count + canonicalRouterDirectionalSetupSlope count : ℕ)

/-- One direction has dimension-only setup and an explicit volume coefficient,
with the supplier exponent applied solely to the routed address width. -/
theorem canonicalRouterDirectionalAmortizedBound_supplier_le (n B count : ℕ)
    (hn : canonicalRouterStride n ≤ n) :
    canonicalRouterDirectionalAmortizedBound n B count ≤
      canonicalRouterDirectionalDimensionCost n count +
        (canonicalRouterDirectionalVolumeCoefficient n count +
          count * canonicalRouterStageSupplierCoefficient * (n : ℝ) ^ Parameters.tau) * (2 ^ n * B : ℕ) := by
  have hs := canonicalRouterStageAmortizedBound_supplier_le n B hn
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) count)
  dsimp only [canonicalRouterDirectionalAmortizedBound, canonicalTerminalAmortizedBound,
    canonicalRouterDirectionalDimensionCost, canonicalRouterDirectionalVolumeCoefficient]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hm ⊢
  nlinarith only [hm]

def canonicalPermutationDimensionCost (n : ℕ) : ℝ :=
  18 * canonicalRouterDirectionalDimensionCost n (canonicalRouterStride n) +
    (36 * canonicalDirectionalUniformFrameBudget n 1 0 (canonicalScalarWidth n) 0 1
      (canonicalRouterStride n) + 2 : ℕ)

def canonicalPermutationVolumeCoefficient (n : ℕ) : ℝ :=
  18 * canonicalRouterDirectionalVolumeCoefficient n (canonicalRouterStride n) +
    (36 * canonicalDirectionalFrameSlope (canonicalRouterStride n) : ℕ)

theorem canonicalPermutationAmortizedBound_supplier_le (n B : ℕ)
    (hn : canonicalRouterStride n ≤ n) :
    canonicalPermutationAmortizedBound n B ≤ canonicalPermutationDimensionCost n +
      (canonicalPermutationVolumeCoefficient n +
        18 * (canonicalRouterStride n : ℕ) * canonicalRouterStageSupplierCoefficient *
          (n : ℝ) ^ Parameters.tau) * (2 ^ n * B : ℕ) := by
  have hd := canonicalRouterDirectionalAmortizedBound_supplier_le n B (canonicalRouterStride n) hn
  have hm := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 18)
  dsimp only [canonicalPermutationAmortizedBound, canonicalPermutationDimensionCost,
    canonicalPermutationVolumeCoefficient]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hm ⊢
  nlinarith only [hm]

def canonicalPermutationSupplierCoefficient (n : ℕ) : ℝ :=
  canonicalPermutationVolumeCoefficient n +
    18 * (canonicalRouterStride n : ℕ) * canonicalRouterStageSupplierCoefficient

/-- The complete permutation ledger has a single address-width supplier power. -/
theorem canonicalPermutationAmortizedBound_width_le (n B : ℕ)
    (hn : canonicalRouterStride n ≤ n) :
    canonicalPermutationAmortizedBound n B ≤ canonicalPermutationDimensionCost n +
      canonicalPermutationSupplierCoefficient n * (2 ^ n * B : ℕ) * (n : ℝ) ^ Parameters.tau := by
  have hn0 : 1 ≤ n := by
    have hg := canonicalRouterGap_pos n
    unfold canonicalRouterStride at hn
    omega
  have htau : (0 : ℝ) ≤ Parameters.tau := by norm_num [Parameters.tau]
  have hp : (1 : ℝ) ≤ (n : ℝ) ^ Parameters.tau :=
    Real.one_le_rpow (Nat.one_le_cast.mpr hn0) htau
  have hc : 0 ≤ canonicalPermutationVolumeCoefficient n := by
    have pos (g a t s : ℕ) (k : ℝ) (hk : 0 ≤ k) :
        0 ≤ (g : ℝ) * (6 * k * (a : ℝ) + 275 + 12 * (t : ℝ)) + 27 + (s : ℝ) := by positivity
    have hd : 0 ≤ canonicalRouterDirectionalVolumeCoefficient n (canonicalRouterStride n) :=
      pos _ _ _ _ swapConst swapConst_pos.le
    exact add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) hd) (Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_right hp
    (mul_nonneg hc (Nat.cast_nonneg (2 ^ n * B) : (0 : ℝ) ≤ _))
  have h := canonicalPermutationAmortizedBound_supplier_le n B hn
  unfold canonicalPermutationSupplierCoefficient
  nlinarith only [h, hm]

def supplierGeometryPrice (terminalT tapes commonT scheduleT : ℕ) (swap stage : ℝ)
    (gap : ℕ) : ℝ :=
  18 * ((131 * gap : ℕ) * (6 * swap * (terminalT + 12 * tapes + 5 : ℕ) + 275 + 12 * tapes) +
    27 + (9499 * (64 * gap) + ((64 * gap) * (6 + 24 * scheduleT) +
      6 * (commonT + 3) * (1 + 3 * (64 * gap) * scheduleT)) : ℕ)) +
    (36 * ((commonT + 3) * (1 + 3 * (64 * gap) * scheduleT)) : ℕ) + 18 * (64 * gap : ℕ) * stage

private theorem supplierGeometryPrice_affine (terminalT tapes commonT scheduleT : ℕ)
    (swap stage : ℝ) (gap : ℕ) :
    supplierGeometryPrice terminalT tapes commonT scheduleT swap stage gap +
      supplierGeometryPrice terminalT tapes commonT scheduleT swap stage 0 * (gap : ℝ) =
    supplierGeometryPrice terminalT tapes commonT scheduleT swap stage 1 * (gap : ℝ) +
      supplierGeometryPrice terminalT tapes commonT scheduleT swap stage 0 := by
  unfold supplierGeometryPrice
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  ring

/-- Express the coefficient using only the gap parameter; all tape counts are fixed. -/
def canonicalPermutationSupplierCoefficientAt (gap : ℕ) : ℝ :=
  supplierGeometryPrice canonicalTerminalT (swapT 6) canonicalRouterCommonT (originalMatchingScheduleT 6)
    swapConst canonicalRouterStageSupplierCoefficient gap

theorem canonicalPermutationSupplierCoefficient_eq_gap (n : ℕ) :
    canonicalPermutationSupplierCoefficient n =
      canonicalPermutationSupplierCoefficientAt (canonicalRouterGap n) := by
  rfl

theorem canonicalPermutationSupplierCoefficientAt_nonneg (gap : ℕ) :
    0 ≤ canonicalPermutationSupplierCoefficientAt gap := by
  have hs := swapConst_pos
  have hstage : 0 ≤ canonicalRouterStageSupplierCoefficient := by
    have pos (a b : ℕ) (k : ℝ) (hk : 0 ≤ k) :
        0 ≤ 18 * k * (a : ℝ) + 72 * k * (b : ℝ) := by positivity
    exact pos _ _ swapConst hs.le
  have pos (g a t s f c : ℕ) (k v : ℝ) (hk : 0 ≤ k) (hv : 0 ≤ v) :
      0 ≤ 18 * ((g : ℝ) * (6 * k * (a : ℝ) + 275 + 12 * (t : ℝ)) + 27 + (s : ℝ)) +
        (f : ℝ) + 18 * (c : ℝ) * v := by positivity
  exact pos _ _ _ _ _ _ swapConst canonicalRouterStageSupplierCoefficient hs.le hstage

/-- The geometry coefficient is affine in gap; this identity avoids concrete
coefficient expansion in subsequent comparisons. -/
theorem canonicalPermutationSupplierCoefficientAt_affine (gap : ℕ) :
    canonicalPermutationSupplierCoefficientAt gap + canonicalPermutationSupplierCoefficientAt 0 * (gap : ℝ) =
      canonicalPermutationSupplierCoefficientAt 1 * (gap : ℝ) + canonicalPermutationSupplierCoefficientAt 0 := by
  exact supplierGeometryPrice_affine _ _ _ _ _ _ gap


def canonicalPermutationSupplierLogCoefficient : ℝ :=
  7 * (canonicalPermutationSupplierCoefficientAt 1 + canonicalPermutationSupplierCoefficientAt 0)

theorem canonicalPermutationSupplierCoefficient_log_le (n : ℕ) :
    canonicalPermutationSupplierCoefficient n ≤
      canonicalPermutationSupplierLogCoefficient * (Nat.clog 2 (n + 2) + 1 : ℕ) := by
  have h0 := canonicalPermutationSupplierCoefficientAt_nonneg 0
  have h1 := canonicalPermutationSupplierCoefficientAt_nonneg 1
  have ha := canonicalPermutationSupplierCoefficientAt_affine (canonicalRouterGap n)
  have hg : (0 : ℝ) ≤ (canonicalRouterGap n : ℕ) := Nat.cast_nonneg _
  have hb : canonicalPermutationSupplierCoefficientAt (canonicalRouterGap n) ≤
      (canonicalPermutationSupplierCoefficientAt 1 + canonicalPermutationSupplierCoefficientAt 0) *
        ((canonicalRouterGap n : ℕ) + 1 : ℝ) := by
    nlinarith only [ha, mul_nonneg h0 hg, h0, h1]
  have hgap : canonicalRouterGap n + 1 ≤ 7 * (Nat.clog 2 (n + 2) + 1) := by
    unfold canonicalRouterGap
    omega
  have hm := mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℝ).mpr hgap) (add_nonneg h1 h0)
  rw [canonicalPermutationSupplierCoefficient_eq_gap]
  unfold canonicalPermutationSupplierLogCoefficient
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hm ⊢
  nlinarith only [hb, hm]

/-- The complete one-row routing ledger has the desired volume/address-power/
logarithm term; the additive address-dimension setup is still explicit. -/
theorem canonicalPermutationAmortizedBound_log_le (n B : ℕ)
    (hn : canonicalRouterStride n ≤ n) :
    canonicalPermutationAmortizedBound n B ≤ canonicalPermutationDimensionCost n +
      canonicalPermutationSupplierLogCoefficient * (Nat.clog 2 (n + 2) + 1 : ℕ) *
        (2 ^ n * B : ℕ) * (n : ℝ) ^ Parameters.tau := by
  have hc := canonicalPermutationSupplierCoefficient_log_le n
  have hm := mul_le_mul_of_nonneg_right hc
    (mul_nonneg (Nat.cast_nonneg (2 ^ n * B) : (0 : ℝ) ≤ _) (Real.rpow_nonneg (Nat.cast_nonneg n) Parameters.tau))
  have h := canonicalPermutationAmortizedBound_width_le n B hn
  nlinarith only [h, hm]

end
end IntegerMultBounds.MathlibTM2.Routing
