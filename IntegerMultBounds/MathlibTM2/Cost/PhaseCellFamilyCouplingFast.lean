module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyBoundaryFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRetainedCouplingPass

/-! Four actual coupling passes share the caller's working precision. Charge
their active nonzeros at the fast rate while preserving all control bills. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def familyCouplingLineCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  placedCachedCouplingGeometryCost (2^15*p) q s t u (PhaseCellBand.width p u) a b

noncomputable def familyCouplingLineControlCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  retainedCouplingControlCost (2^15*p) q s t u (PhaseCellBand.width p u) a b

theorem familyCouplingLine_selected_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p u target s t a b : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      let band := PhaseCellBand.width p u
      let active := haloBoundaryCountBound s t (2*band) a b+4*band
      (familyCouplingLineCost p u (haloInverseRingLog s t) s t a b target : ℝ) ≤
        (familyCouplingLineControlCost p u (haloInverseRingLog s t) s t a b target : ℝ)+
          C*((s+active*(2*band+1) : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  let cw := 1000+8*ct+16*cG
  obtain ⟨C,hC,hfast⟩ := placedCachedCouplingGeometry_fast_le cw
  refine ⟨C,hC,?_⟩
  intro p u target s t a b _ hp hst hband hθ ht hgeometry
  let l := haloInverseRingLog s t
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let stage := initialSchurTarget p u bits 2
  let q := executionPrecision p l stage 2
  have hN : N ≤ s := by simpa using Finset.card_le_univ (s := haloBoundary s t (PhaseCellBand.width p u) a b)
  have hNlog : Nat.size N ≤ cG*p := (Nat.size_le_size (by omega : N ≤ 2*s+1)).trans hgeometry
  have hBlog : Nat.size (2*PhaseCellBand.width p u+1) ≤ cG*p :=
    (Nat.size_le_size (by omega)).trans hgeometry
  have hwidth : 2*q+8 ≤ cw*p := by
    have hw := inverseExecutionWidth_le p l target N (PhaseCellBand.width p u) 20 ct cG cG hp
      (haloInverseRingLog_bounds hp hst hθ).1 ht hNlog hBlog
    change 2*(4*executionExponent p l stage 2)+8 ≤ cw*p
    rw [← inverseExecutionExponent_eq]
    dsimp only [cw]
    nlinarith only [hw]
  exact hfast p (2^15*p) q s t u (PhaseCellBand.width p u) a b hp hwidth hband

noncomputable def familyComplexNonKernelRemainingCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  familyComplexNonBoundaryRemainingCost p u l s t a b target-4*familyCouplingLineCost p u l s t a b target

theorem familyComplexNonBoundaryRemainingCost_coupling_split (p u l s t a b target : ℕ) [NeZero s] :
    familyComplexNonBoundaryRemainingCost p u l s t a b target =
      familyComplexNonKernelRemainingCost p u l s t a b target+4*familyCouplingLineCost p u l s t a b target := by
  apply (Nat.sub_add_cancel ?_).symm
  have h : 4*familyCouplingLineCost p u l s t a b target+2*familyBoundaryLineCost p u l s t a b target ≤
      familyComplexRemainingLineCost p u l s t a b target := by
    dsimp only [familyCouplingLineCost,familyBoundaryLineCost,familyComplexRemainingLineCost,
      familyRealComponentRemainingCost,familyRealResidualRemainingCost,familyRecoveryRemainingCost,
      initialSchurTarget]
    omega
  have heq := familyComplexRemainingLineCost_boundary_split p u l s t a b target
  omega

noncomputable def familyComplexControlRemainingCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  familyComplexNonKernelRemainingCost p u l s t a b target+4*familyCouplingLineControlCost p u l s t a b target

def familyKernelVolume (s t band a b : ℕ) [NeZero s] : ℕ :=
  t+((haloBoundary s t band a b).card+1)*(12*band+1)+s+
    (haloBoundaryCountBound s t (2*band) a b+4*band)*(2*band+1)

theorem familyComplexGeometry_selected_kernel_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p u target s t a b : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      let l := haloInverseRingLog s t
      (generatedFamilyComplexGeometryLineCost p u l s t a b target : ℝ) ≤
        (familyComplexControlRemainingCost p u l s t a b target : ℝ)+
          C*(familyKernelVolume s t (PhaseCellBand.width p u) a b : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hkernels⟩ := familyComplexGeometry_selected_work_fast_le ct cG
  obtain ⟨D,hD,hcoupling⟩ := familyCouplingLine_selected_fast_le ct cG
  refine ⟨K+4*D,by positivity,?_⟩
  intro p u target s t a b _ hp hst hband hθ ht hgeometry
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let active := haloBoundaryCountBound s t (2*band) a b+4*band
  have hk := hkernels p u target s t a b hp hst hband hθ ht hgeometry
  have hc := hcoupling p u target s t a b hp hst hband hθ ht hgeometry
  have hs := congrArg (fun n : ℕ => (n : ℝ)) (familyComplexNonBoundaryRemainingCost_coupling_split p u l s t a b target)
  dsimp only at hc
  have hMp : 0 ≤ (p : ℝ)^(129/128 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hmoreK : 0 ≤ K*((s+active*(2*band+1) : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) :=
    mul_nonneg (mul_nonneg hK (Nat.cast_nonneg _)) hMp
  have hmoreC : 0 ≤ 4*D*((t+(N+1)*(12*band+1) : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD) (Nat.cast_nonneg _)) hMp
  dsimp only [familyComplexControlRemainingCost,familyKernelVolume]
  dsimp only [active,band,N] at hmoreK hmoreC
  push_cast at hk hc hs hmoreK hmoreC ⊢
  nlinarith only [hk,hc,hs,hmoreK,hmoreC]

end IntegerMultBounds.MathlibTM2.Cost
