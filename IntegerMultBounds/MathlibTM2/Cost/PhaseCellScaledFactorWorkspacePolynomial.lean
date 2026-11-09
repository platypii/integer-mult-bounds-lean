module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledInitializedBoundaryFactor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandAxisWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellScaledFactorSetupPolynomial

/-! The shared numerical factorization uses one cubic physical reserve.
Reuse the structural band-axis bound and the established scale-24 setup bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

noncomputable def closedBoundaryFactorNumericalPush (hQ : SS.states ≤ Q) : ℕ :=
  bandNewtonStepPush (P := Empty) (A := A) (U := U) boundaryFactorReg
    boundaryFactorMulReg_injective (by decide) hQ+
  factorRmulPush (P := Empty) (A := A) (U := U) (rsbCr boundaryFactorReg .hv .xa .hc)
    boundaryFactorMulReg_injective (by decide) hQ+
  factorRmulPush (P := Empty) (A := A) (U := U) (rsbCr boundaryFactorReg .ya .xs .pr)
    boundaryFactorMulReg_injective (by decide) hQ+1

noncomputable def closedBoundaryFactorWorkspaceCoefficient (hQ : SS.states ≤ Q) : ℕ :=
  2000000*(scaledFactorSetupPush (P := Empty) (Q := Q) (A := A) (U := U) 24+
    closedBoundaryFactorNumericalPush (A := A) (U := U) hQ+1)*(ssMulConst+1)

theorem scaledInitializedBoundaryFactorWorkspace_two_poly (hQ : SS.states ≤ Q)
    (p q band N : ℕ) :
    scaledInitializedBoundaryFactorWorkspace (P := Empty) (A := A) (U := U) 2 hQ p q band N ≤
      closedBoundaryFactorWorkspaceCoefficient (A := A) (U := U) hQ*(p+2*q+24*band+N+100)^3 := by
  let R := p+2*q+24*band+N+100
  let F := closedBoundaryFactorNumericalPush (A := A) (U := U) hQ
  let setupPush := scaledFactorSetupPush (P := Empty) (Q := Q) (A := A) (U := U) 24
  have hR : 1 ≤ R := by dsimp only [R]; omega
  have hsetup := scaledFactorSetupCost_poly hR (by dsimp only [R]; omega : p ≤ R)
    (by dsimp only [R]; omega : q ≤ R) (by dsimp only [R]; omega : 2*band ≤ R)
    (by dsimp only [R]; omega : N ≤ R) (by dsimp only [R]; omega : 2*q+8 ≤ R)
  have hsetupBound := Nat.mul_le_mul_left setupPush hsetup
  have haxis := boundaryAxisPrepWorkspace_le (P := Empty) (A := A) (U := U) boundaryFactorReg
    boundaryFactorMulReg_injective (by decide) hQ (2*q+8) (12*(2*band)) (factorNewtonSteps p q) N
  change _ ≤ 10000*F*(N+12*(2*band)+2)*(12*(2*band)+2)*(2*q+8+1)+
    2*F*rmulCost (2*q+8)+4*factorNewtonSteps p q at haxis
  have hshape : (N+12*(2*band)+2)*(12*(2*band)+2)*(2*q+8+1) ≤ R^3 := by
    calc
      _ ≤ R*R*R := by gcongr <;> dsimp only [R] <;> omega
      _ = R^3 := by ring
  have hshapeScaled := Nat.mul_le_mul_left (10000*F) hshape
  have hmul := band_rmul_le (show 2*q+8 ≤ R by dsimp only [R]; omega) hR
  have hmulScaled := Nat.mul_le_mul_left (2*F) hmul
  have hsteps : factorNewtonSteps p q ≤ R := by
    have hb := factorNewtonSteps_bound p q
    have hp : Nat.size p ≤ p := Nat.size_le.mpr Nat.lt_two_pow_self
    have hq : Nat.size (q+1) ≤ q+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    dsimp only [R]; omega
  have hpower : R ≤ R^3 := Nat.le_self_pow (by decide) R
  unfold scaledInitializedBoundaryFactorWorkspace closedBoundaryFactorWorkspaceCoefficient
  change setupPush*scaledFactorSetupCost 24 p q band N+_ ≤
    2000000*(setupPush+F+1)*(ssMulConst+1)*R^3
  nlinarith only [hsetupBound,haxis,hshapeScaled,hmulScaled,hsteps,hpower,
    Nat.zero_le (setupPush*ssMulConst*R^3),Nat.zero_le (F*R^3),Nat.zero_le (ssMulConst*R^3)]

end IntegerMultBounds.MathlibTM2.Cost
