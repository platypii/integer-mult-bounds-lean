module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyComponentFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedResidual

/-! Combine four interior passes and both prepared boundary solves. Boundary
work retains its actual row-count times bandwidth factor. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def familyBoundaryLineCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let stage := initialSchurTarget p u bits 2
  preparedResidualSolveCost (executionPrecision p l stage 2) (executionWidth p l stage 2)
    N (12*PhaseCellBand.width p u+1)

theorem familyBoundaryLine_selected_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p u target s t a b : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (familyBoundaryLineCost p u (haloInverseRingLog s t) s t a b target : ℝ) ≤
        C*((N+1 : ℕ) : ℝ)*((12*PhaseCellBand.width p u+1 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := preparedResidual_selected_fast_le 20 ct cG cG
  refine ⟨C,hC,?_⟩
  intro p u target s t a b _ hp hst hband hθ ht hgeometry
  dsimp only
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  have hN : N ≤ s := by simpa using Finset.card_le_univ (s := haloBoundary s t (PhaseCellBand.width p u) a b)
  have hNlog : Nat.size N ≤ cG*p := (Nat.size_le_size (by omega : N ≤ 2*s+1)).trans hgeometry
  have hBlog : Nat.size (2*PhaseCellBand.width p u+1) ≤ cG*p :=
    (Nat.size_le_size (by omega)).trans hgeometry
  have h := hfast p (haloInverseRingLog s t) target N (PhaseCellBand.width p u) hp
    (haloInverseRingLog_bounds hp hst hθ).1 ht hNlog hBlog
  dsimp only [familyBoundaryLineCost,executionPrecision,executionWidth]
  rw [← inverseExecutionExponent_eq]
  exact h

noncomputable def familyComplexNonBoundaryRemainingCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  familyComplexRemainingLineCost p u l s t a b target-2*familyBoundaryLineCost p u l s t a b target

theorem familyComplexRemainingLineCost_boundary_split (p u l s t a b target : ℕ) [NeZero s] :
    familyComplexRemainingLineCost p u l s t a b target =
      familyComplexNonBoundaryRemainingCost p u l s t a b target+
        2*familyBoundaryLineCost p u l s t a b target := by
  apply (Nat.sub_add_cancel ?_).symm
  dsimp only [familyComplexRemainingLineCost,familyRealComponentRemainingCost,familyBoundaryLineCost]
  omega

theorem familyComplexGeometry_selected_work_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p u target s t a b : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      let l := haloInverseRingLog s t
      let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let W := 12*PhaseCellBand.width p u+1
      (generatedFamilyComplexGeometryLineCost p u l s t a b target : ℝ) ≤
        (familyComplexNonBoundaryRemainingCost p u l s t a b target : ℝ)+
          C*((t : ℝ)+((N+1 : ℕ) : ℝ)*(W : ℝ))*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hinterior⟩ := familyComplexGeometry_selected_fast_le ct cG
  obtain ⟨D,hD,hboundary⟩ := familyBoundaryLine_selected_fast_le ct cG
  refine ⟨K+2*D,by positivity,?_⟩
  intro p u target s t a b _ hp hst hband hθ ht hgeometry
  dsimp only
  let l := haloInverseRingLog s t
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let W := 12*PhaseCellBand.width p u+1
  have hi := hinterior p u target s t a b hp hst hband hθ ht hgeometry
  have hb := hboundary p u target s t a b hp hst hband hθ ht hgeometry
  have hs := congrArg (fun n : ℕ => (n : ℝ)) (familyComplexRemainingLineCost_boundary_split p u l s t a b target)
  push_cast at hs
  have hMp : 0 ≤ (p : ℝ)^(129/128 : ℝ) := by positivity
  have hmoreI : 0 ≤ K*((N+1 : ℕ) : ℝ)*(W : ℝ)*(p : ℝ)^(129/128 : ℝ) := by positivity
  have hmoreB : 0 ≤ 2*D*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) := by positivity
  dsimp only [N,W] at hmoreI
  nlinarith only [hi,hb,hs,hmoreI,hmoreB]

end IntegerMultBounds.MathlibTM2.Cost
