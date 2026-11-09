module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBoundaryFactorSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledFactorSetup
import Mathlib.Tactic.Ring

/-! Scale-24 setup is bounded by the established scale-12 construction at
twice the bandwidth. Constants and Newton setup are identical. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast

theorem scaledFactorSetupCost_le_doubled (p q band N : ℕ) :
    scaledFactorSetupCost 24 p q band N ≤ boundaryFactorSetupCost p q (2*band) N := by
  unfold scaledFactorSetupCost scaledFactorHeaderSetupCost boundaryFactorSetupCost
    boundaryFactorHeaderSetupCost scaledFactorDimensionsCost boundaryFactorDimensionsCost
  ring_nf
  omega

theorem scaledFactorSetupCost_poly {p q band N R : ℕ}
    (hR : 1 ≤ R) (hp : p ≤ R) (hq : q ≤ R) (hband : 2*band ≤ R)
    (hN : N ≤ R) (hw : 2*q+8 ≤ R) :
    scaledFactorSetupCost 24 p q band N ≤ 1000000*R^3 := by
  exact (scaledFactorSetupCost_le_doubled p q band N).trans
    (boundaryFactorSetupCost_poly hR hp hq hband hN hw)

/-- Double the bandwidth once to reuse the full setup-and-factorization bill,
including Newton iterations and band-axis preparation. -/
theorem scaledFactorPreparationCost_poly (p q band N : ℕ) :
    scaledFactorSetupCost 24 p q band N+
        bandAxisPrepCost (2*q+8) (24*band) (factorNewtonSteps p q) N ≤
      (1000000+10000000*(ssMulConst+1))*(p+2*q+24*band+N+100)^6 := by
  have h := boundaryFactorPreparationCost_poly p q (2*band) N
  have heq : 12*(2*band) = 24*band := by omega
  rw [heq] at h
  exact (Nat.add_le_add_right (scaledFactorSetupCost_le_doubled p q band N) _).trans h

end IntegerMultBounds.MathlibTM2.Cost
