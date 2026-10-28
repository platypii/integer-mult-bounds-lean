module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFamilyFast
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseGeometryCaller
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellAxisDensity

/-! The executed batch pays shared construction once and its complete fast line
cost per replica. The scalar caller retains only setup and scalar header costs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedFamilyBatch_fast_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A u target a b replicas : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      (generatedClosedFamilyComplexBatchCost A p u l s t a b target replicas : ℝ) ≤
        (generatedFamilyComplexSetupCostBound A p u l s t a b target : ℝ)+
          (replicas : ℝ)*C*((t+(t-s)*band^2 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := selectedFamilyLine_fast_le ct
  refine ⟨C,hC,?_⟩
  filter_upwards [hfast] with n hn
  intro h i _ A u target a b replicas hu htarget hband ha hb
  dsimp only
  have hl := hn h i u target a b hu htarget hband ha hb
  have hc := generatedClosedFamilyComplexBatchCost_full_geometry_le (h.good.lt i)
    A (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) a b target replicas hb
  have hcR := (Nat.cast_le (α := ℝ)).mpr hc
  push_cast at hcR
  calc
    _ ≤ _ := hcR
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg replicas))
    _ = _ := by ring

noncomputable def familyInverseSharedSetupCost (A W p u target s t : ℕ) [NeZero s] : ℕ :=
  let l := haloInverseRingLog s t
  inverseScalarAtoms p s t u 0 s*tblC W 0+
    inverseMasterCopyCost W (inverseMasterValues p u l target s t 0 s)+
    generatedFamilyComplexSetupCostBound A p u l s t 0 s target+5+
    inverseReleaseCost W (inverseMasterValues p u l target s t 0 s)

theorem selectedFamilyInverseCaller_fast_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A W u target : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let band := PhaseCellBand.width p u
      (familyInverseCallerCost A W p u (haloInverseRingLog s t) target s t : ℝ) ≤
        (familyInverseSharedSetupCost A W p u target s t : ℝ)+
          C*((t+(t-s)*band^2 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := selectedFamilyBatch_fast_le ct
  refine ⟨C,hC,?_⟩
  filter_upwards [hfast] with n hn
  intro h i _ A W u target hu htarget hband
  dsimp only
  have hc := hn h i A u target 0 (Sizes.s n i) 1 hu htarget hband (Nat.zero_le _) le_rfl
  dsimp only at hc
  simp only [Nat.cast_one,one_mul] at hc
  dsimp only [familyInverseCallerCost,familyInverseSharedSetupCost]
  push_cast at hc ⊢
  linarith only [hc]

theorem selectedFamilyBatch_density_fast_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A u target a b replicas : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      (generatedClosedFamilyComplexBatchCost A p u l s t a b target replicas : ℝ) ≤
        (generatedFamilyComplexSetupCostBound A p u l s t a b target : ℝ)+
          (replicas : ℝ)*C*(t : ℝ)*(1+(band : ℝ)^2/Sizes.d n)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := selectedFamilyBatch_fast_le ct
  refine ⟨C,hC,?_⟩
  filter_upwards [hfast] with n hn
  intro h i _ A u target a b replicas hu htarget hband ha hb
  dsimp only
  have hc := hn h i A u target a b replicas hu htarget hband ha hb
  dsimp only at hc
  have hv := axisGapVolume_le (band := PhaseCellBand.width (Sizes.p n) u)
    (by have := h.one_le_d; omega) (h.good.lt i).le (h.good.bounds i)
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hv (show 0 ≤ (replicas : ℝ)*C from mul_nonneg (Nat.cast_nonneg replicas) hC))
    (Real.rpow_nonneg (Nat.cast_nonneg (Sizes.p n)) (129/128 : ℝ))
  exact hc.trans (by nlinarith only [hs])

theorem selectedFamilyInverseCaller_density_fast_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A W u target : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let band := PhaseCellBand.width p u
      (familyInverseCallerCost A W p u (haloInverseRingLog s t) target s t : ℝ) ≤
        (familyInverseSharedSetupCost A W p u target s t : ℝ)+
          C*(t : ℝ)*(1+(band : ℝ)^2/Sizes.d n)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := selectedFamilyInverseCaller_fast_le ct
  refine ⟨C,hC,?_⟩
  filter_upwards [hfast] with n hn
  intro h i _ A W u target hu htarget hband
  dsimp only
  have hc := hn h i A W u target hu htarget hband
  dsimp only at hc
  have hv := axisGapVolume_le (band := PhaseCellBand.width (Sizes.p n) u)
    (by have := h.one_le_d; omega) (h.good.lt i).le (h.good.bounds i)
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hv (show 0 ≤ C from hC))
    (Real.rpow_nonneg (Nat.cast_nonneg (Sizes.p n)) (129/128 : ℝ))
  exact hc.trans (by nlinarith only [hs])

end IntegerMultBounds.MathlibTM2.Cost
