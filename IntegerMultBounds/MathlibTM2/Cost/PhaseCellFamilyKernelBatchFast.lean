module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyKernelVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseGeometryCaller

/-! The generated batch and scalar caller pay interior, boundary and coupling
kernels by actual phase-gap volume, retaining every remaining control bill. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem familyComplexBatch_selected_kernel_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A p u target s t a b replicas : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p → b ≤ s →
      let l := haloInverseRingLog s t
      (generatedClosedFamilyComplexBatchCost A p u l s t a b target replicas : ℝ) ≤
        (generatedFamilyComplexSetupCostBound A p u l s t a b target : ℝ)+
          (replicas : ℝ)*((familyComplexControlRemainingCost p u l s t a b target : ℝ)+
            C*((t+(t-s)*(PhaseCellBand.width p u)^2 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ)) := by
  obtain ⟨C,hC,hfast⟩ := familyComplexGeometry_selected_gap_fast_le ct cG
  refine ⟨C,hC,?_⟩
  intro A p u target s t a b replicas _ hp hst hband hθ ht hgeometry hb
  let l := haloInverseRingLog s t
  have hline := hfast p u target s t a b hp hst hband hθ ht hgeometry
  have hcost := generatedClosedFamilyComplexBatchCost_full_geometry_le hst A p u l a b target replicas hb
  calc
    _ ≤ (generatedFamilyComplexSetupCostBound A p u l s t a b target : ℝ)+
        (replicas : ℝ)*(generatedFamilyComplexGeometryLineCost p u l s t a b target : ℝ) := by
      exact_mod_cast hcost
    _ ≤ _ := by
      have hscaled := mul_le_mul_of_nonneg_left hline (Nat.cast_nonneg replicas)
      linarith only [hscaled]

noncomputable def familyInverseControlRemainingCost (A W p u target s t : ℕ) [NeZero s] : ℕ :=
  let l := haloInverseRingLog s t
  inverseScalarAtoms p s t u 0 s*tblC W 0+
    inverseMasterCopyCost W (inverseMasterValues p u l target s t 0 s)+
    (generatedFamilyComplexSetupCostBound A p u l s t 0 s target+
      familyComplexControlRemainingCost p u l s t 0 s target+5)+
    inverseReleaseCost W (inverseMasterValues p u l target s t 0 s)

theorem familyInverseCaller_selected_kernel_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A W p u target s t : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      (familyInverseCallerCost A W p u (haloInverseRingLog s t) target s t : ℝ) ≤
        (familyInverseControlRemainingCost A W p u target s t : ℝ)+C*((t+(t-s)*(PhaseCellBand.width p u)^2 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := familyComplexBatch_selected_kernel_fast_le ct cG
  refine ⟨C,hC,?_⟩
  intro A W p u target s t _ hp hst hband hθ ht hgeometry
  have h := hfast A p u target s t 0 s 1 hp hst hband hθ ht hgeometry le_rfl
  simp only [Nat.cast_one,one_mul] at h
  dsimp only [familyInverseCallerCost,familyInverseControlRemainingCost]
  push_cast at h ⊢
  linarith only [h]

end IntegerMultBounds.MathlibTM2.Cost
