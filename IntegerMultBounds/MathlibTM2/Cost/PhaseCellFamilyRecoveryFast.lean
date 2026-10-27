module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyInteriorFast
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInteriorGeometryCost

/-! Recovery uses the same working exponent as the first interior pass.
Transfer the selected arithmetic bound without suppressing either control bill. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Equal working exponents give equal arithmetic work; controls remain separately charged. -/
theorem familyHaloInteriorArithmetic_congr (p l s t u j k e f a b : ℕ)
    (hE : executionExponent p l j e = executionExponent p l k f) :
    familyHaloInteriorGeometryCost p l s t u j e a b+familyHaloControlCost p l s t u k f a b =
      familyHaloInteriorGeometryCost p l s t u k f a b+familyHaloControlCost p l s t u j e a b := by
  have hcoord : cachedBatchCoordinateCost p l j e = cachedBatchCoordinateCost p l k f := by
    dsimp only [cachedBatchCoordinateCost,executionWidth]
    change 3*rmulCost (8*executionExponent p l j e+8)+835*(8*executionExponent p l j e+8)+
      4*(executionExponent p l j e+2*l+2)+433 = _
    rw [hE]
    rfl
  have hcell : cachedBatchCellCost p l j e = cachedBatchCellCost p l k f := by
    simp only [cachedBatchCellCost,executionPrecision,executionWidth,hE]
  have hw : executionWidth p l j e = executionWidth p l k f := by simp only [executionWidth,hE]
  rw [familyHaloInteriorGeometryCost_eq,familyHaloInteriorGeometryCost_eq,hcoord,hcell,hw]
  ring

/-- Both interior passes share a uniform arithmetic allowance at the actual caller precision. -/
theorem familyInteriorPair_selected_fast_le (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p u target s t a b : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → PhaseCellBand.width p u ≤ s →
      1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      let l := haloInverseRingLog s t
      let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let firstTarget := initialSchurTarget p u bits 2
      let secondTarget := recoveryTarget p bits
      let recoveryExp := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
      (familyHaloInteriorGeometryCost p l s t u firstTarget 2 a b : ℝ)+
        (familyHaloInteriorGeometryCost p l s t u secondTarget recoveryExp a b : ℝ) ≤
      (familyHaloControlCost p l s t u firstTarget 2 a b : ℝ)+
        (familyHaloControlCost p l s t u secondTarget recoveryExp a b : ℝ)+
        C*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := familyInteriorGeometry_selected_fast_le ct cG
  refine ⟨2*C,by positivity,?_⟩
  intro p u target s t a b _ hp hst hband hθ ht hgeometry
  dsimp only
  let l := haloInverseRingLog s t
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
    (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let firstTarget := initialSchurTarget p u bits 2
  let secondTarget := recoveryTarget p bits
  let recoveryExp := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
  have hfirst := hfast p u target s t a b hp hst hband hθ ht hgeometry
  have hE : executionExponent p l firstTarget 2 = executionExponent p l secondTarget recoveryExp :=
    recovery_execution_exponent p l secondTarget 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
  have heq := familyHaloInteriorArithmetic_congr p l s t u firstTarget secondTarget 2 recoveryExp a b hE
  have heqR : (familyHaloInteriorGeometryCost p l s t u firstTarget 2 a b : ℝ)+
      (familyHaloControlCost p l s t u secondTarget recoveryExp a b : ℝ) =
      (familyHaloInteriorGeometryCost p l s t u secondTarget recoveryExp a b : ℝ)+
        (familyHaloControlCost p l s t u firstTarget 2 a b : ℝ) := by exact_mod_cast heq
  linarith only [hfirst,heqR]

end IntegerMultBounds.MathlibTM2.Cost
