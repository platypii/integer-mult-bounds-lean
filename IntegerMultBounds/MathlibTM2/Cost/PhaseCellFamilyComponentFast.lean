module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyRecoveryFast
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedFamilyBatchGeometryCost

/-! Charge both real solves' four interior passes to one uniform arithmetic
allowance, preserving every control, coupling and boundary charge explicitly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def familyRealResidualRemainingCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  familyHaloControlCost p l s t u target rhsExp a b+initializeInteriorOutputCost q s+
    placedCachedCouplingGeometryCost (2^15*p) q s t u (PhaseCellBand.width p u) a b+
    realResidualProjectionCost q s

noncomputable def familyRecoveryRemainingCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  let stageTarget := recoveryTarget p target
  let boundaryExp := stableInteriorExponent p rhsExp
  let countExp := couplingCountExponent p u
  let q := executionPrecision p l (recoveryFirstTarget p stageTarget rhsExp boundaryExp countExp) rhsExp
  let recoveryExp := recoveryRhsExponent p rhsExp boundaryExp countExp
  retireAmbientSourceCost q s+
    placedCachedCouplingGeometryCost (2^15*p) q s t u (PhaseCellBand.width p u) a b+
    initializeInteriorOutputCost (executionPrecision p l stageTarget recoveryExp) s+
    familyHaloControlCost p l s t u stageTarget recoveryExp a b+
    publishHaloCost (2^15*p) q s t u (PhaseCellBand.width p u) a b

noncomputable def familyRealComponentRemainingCost (p u l s t a b target V : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  familyRealResidualRemainingCost p l s t u (initialSchurTarget p u bits 2) 2 a b+
    boundaryRhsPrepareCost V w N s+preparedResidualSolveCost q w N (12*PhaseCellBand.width p u+1)+
    retireCountedLineCost s w+sharedPageBoundaryAmbientCost N w s+
    familyRecoveryRemainingCost p l s t u bits 2 a b+sharedPageRetireResidualCost s w+retireCountedLineCost N w

theorem familyRealComponentGeometryCost_split (p u l s t a b target V : ℕ) [NeZero s] :
    let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
    let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 N
    let firstTarget := initialSchurTarget p u bits 2
    let secondTarget := recoveryTarget p bits
    let recoveryExp := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
    familyRealComponentGeometryCost p u l s t a b target V+
      familyHaloControlCost p l s t u firstTarget 2 a b+
      familyHaloControlCost p l s t u secondTarget recoveryExp a b =
    familyRealComponentRemainingCost p u l s t a b target V+
      familyHaloInteriorGeometryCost p l s t u firstTarget 2 a b+
      familyHaloInteriorGeometryCost p l s t u secondTarget recoveryExp a b := by
  dsimp only [familyRealComponentGeometryCost,familyRealComponentRemainingCost,
    familyRealResidualGeometryCost,familyRealResidualRemainingCost,
    familyRecoveryGeometryCost,familyRecoveryRemainingCost]
  ring

theorem familyRealComponentGeometry_selected_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p u target s t a b V : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      let l := haloInverseRingLog s t
      (familyRealComponentGeometryCost p u l s t a b (target+1) V : ℝ) ≤
        (familyRealComponentRemainingCost p u l s t a b (target+1) V : ℝ)+
          C*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := familyInteriorPair_selected_fast_le ct cG
  refine ⟨C,hC,?_⟩
  intro p u target s t a b V _ hp hst hband hθ ht hgeometry
  have h := hfast p u target s t a b hp hst hband hθ ht hgeometry
  have heq := familyRealComponentGeometryCost_split p u (haloInverseRingLog s t) s t a b (target+1) V
  have heqR := congrArg (fun n : ℕ => (n : ℝ)) heq
  push_cast at heqR
  linarith only [h,heqR]

noncomputable def familyComplexRemainingLineCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t (PhaseCellBand.width p u)
  originalComponentInputsCost q s+2*familyRealComponentRemainingCost p u l s t a b (target+1) V+
    cleanComponentTransitionCost q s+cleanFinishComponentsCost q s+24*s*w+15*s+15

theorem familyComplexGeometry_selected_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p u target s t a b : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      let l := haloInverseRingLog s t
      (generatedFamilyComplexGeometryLineCost p u l s t a b target : ℝ) ≤
        (familyComplexRemainingLineCost p u l s t a b target : ℝ)+C*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := familyRealComponentGeometry_selected_fast_le ct cG
  refine ⟨2*C,by positivity,?_⟩
  intro p u target s t a b _ hp hst hband hθ ht hgeometry
  have h := hfast p u target s t a b (publicationGeometryWidth t (PhaseCellBand.width p u))
    hp hst hband hθ ht hgeometry
  dsimp only [generatedFamilyComplexGeometryLineCost,familyComplexRemainingLineCost]
  push_cast
  linarith only [h]

end IntegerMultBounds.MathlibTM2.Cost
