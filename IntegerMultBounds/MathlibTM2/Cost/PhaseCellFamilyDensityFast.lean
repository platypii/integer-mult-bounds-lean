module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyKernelBatchFast
public import IntegerMultBounds.MathlibTM2.Mult.Sizes

/-! The selected axis inequalities supply the density in the fast inverse kernel budget. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem axisGap_mul_dimension_le {d s t : ℕ} (hst : s ≤ t)
    (haxis : Moduli.AxisBounds d s t) : d*(t-s) ≤ t := by
  have hsum : s+(t-s) = t := Nat.add_sub_of_le hst
  have h := haxis.lower
  nlinarith only [h,hsum,Nat.zero_le (d*(t-s))]

theorem axisGapVolume_le {d s t band : ℕ} (hd : 0 < d) (hst : s ≤ t)
    (haxis : Moduli.AxisBounds d s t) :
    ((t+(t-s)*band^2 : ℕ) : ℝ) ≤ (t : ℝ)*(1+(band : ℝ)^2/d) := by
  have hgap : (d : ℝ)*(t-s : ℕ) ≤ t := by
    exact_mod_cast axisGap_mul_dimension_le hst haxis
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hquot : ((t-s : ℕ) : ℝ) ≤ (t : ℝ)/d :=
    (le_div_iff₀ hd').2 (by nlinarith only [hgap])
  have hscaled := mul_le_mul_of_nonneg_right hquot (sq_nonneg (band : ℝ))
  push_cast
  calc
    (t : ℝ)+(t-s : ℕ)*(band : ℝ)^2 ≤ (t : ℝ)+((t : ℝ)/d)*(band : ℝ)^2 := by
      linarith only [hscaled]
    _ = (t : ℝ)*(1+(band : ℝ)^2/d) := by ring

/-- The actual selected axes meet the kernel density budget. -/
theorem selectedAxisGapVolume_le {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n)) (band : ℕ) :
    ((Sizes.t n i+(Sizes.t n i-Sizes.s n i)*band^2 : ℕ) : ℝ) ≤
      (Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n) :=
  axisGapVolume_le (by have := h.one_le_d; omega) (h.good.lt i).le (h.good.bounds i)

theorem familyInverseCaller_selected_density_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A W p u target s t d : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → 0 < d → Moduli.AxisBounds d s t →
      NLogN.PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      (familyInverseCallerCost A W p u (haloInverseRingLog s t) target s t : ℝ) ≤
        (familyInverseControlRemainingCost A W p u target s t : ℝ)+
          C*(t : ℝ)*(1+(NLogN.PhaseCellBand.width p u : ℝ)^2/d)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := familyInverseCaller_selected_kernel_fast_le ct cG
  refine ⟨C,hC,?_⟩
  intro A W p u target s t d _ hp hst hd haxis hband hθ ht hgeometry
  have h := hfast A W p u target s t hp hst hband hθ ht hgeometry
  have hv := axisGapVolume_le (band := NLogN.PhaseCellBand.width p u) hd hst.le haxis
  have hMp := Real.rpow_nonneg (Nat.cast_nonneg p) (129/128 : ℝ)
  have hscaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC) hMp
  nlinarith only [h,hscaled]

theorem familyComplexBatch_selected_density_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A p u target s t a b replicas d : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → 0 < d → Moduli.AxisBounds d s t →
      PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p → b ≤ s →
      let l := haloInverseRingLog s t
      (generatedClosedFamilyComplexBatchCost A p u l s t a b target replicas : ℝ) ≤
        (generatedFamilyComplexSetupCostBound A p u l s t a b target : ℝ)+
          (replicas : ℝ)*((familyComplexControlRemainingCost p u l s t a b target : ℝ)+
            C*(t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/d)*(p : ℝ)^(129/128 : ℝ)) := by
  obtain ⟨C,hC,hfast⟩ := familyComplexBatch_selected_kernel_fast_le ct cG
  refine ⟨C,hC,?_⟩
  intro A p u target s t a b replicas d _ hp hst hd haxis hband hθ ht hgeometry hb
  have h := hfast A p u target s t a b replicas hp hst hband hθ ht hgeometry hb
  have hv := axisGapVolume_le (band := PhaseCellBand.width p u) hd hst.le haxis
  have hMp := Real.rpow_nonneg (Nat.cast_nonneg p) (129/128 : ℝ)
  have hscaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC) hMp
  have hreplicas := mul_le_mul_of_nonneg_left hscaled (Nat.cast_nonneg replicas)
  dsimp only at h ⊢
  nlinarith only [h,hreplicas]

end IntegerMultBounds.MathlibTM2.Cost
