module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArithmeticStock
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! Additional replicas add only linear storage to shared cell arithmetic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Mult.ShortConv
open ScalarPlacement

theorem cellArithmeticWorkspace_le_affine (R K q cExp e l w M L : ℕ) :
    cellArithmeticWorkspace R K q cExp e l w M L ≤
      cellArithmeticWorkspace R K q cExp e l w 0 L+
      100000*(R+K+1)*M*(2^l+L+1)*(w+cExp+e+l+1) := by
  unfold cellArithmeticWorkspace normalizedInteriorWorkspace inputInteriorWorkspace
    inputStageWorkspace interiorWorkspace preparedOutputWorkspace outputFromHeadersWorkspace
    closedOutputWorkspace applyWeightsWorkspace runWeightsWorkspace applyWorkspace runWorkspace
    compactPairWorkspace triangularPairWorkspace Fixed.workspace
    realWeightWorkspace realScalarWorkspace
    routeWeightsCost routeCost installInputCost fixedMergeCost fetchScalarCost pairFinishCost
    fetchOutputTableCost fetchPageCost scaleOutputPrefixCost
  ring_nf
  omega

theorem cellArithmeticWorkspace_zero_mono (R K q cExp e l w L M : ℕ) (hL : L ≤ M) :
    cellArithmeticWorkspace R K q cExp e l w 0 L ≤
      cellArithmeticWorkspace R K q cExp e l w 0 M := by
  unfold cellArithmeticWorkspace normalizedInteriorWorkspace inputInteriorWorkspace
    inputStageWorkspace interiorWorkspace preparedOutputWorkspace outputFromHeadersWorkspace
    closedOutputWorkspace applyWeightsWorkspace runWeightsWorkspace applyWorkspace runWorkspace
    compactPairWorkspace triangularPairWorkspace
    realWeightWorkspace realScalarWorkspace
    routeWeightsCost routeCost installInputCost fixedMergeCost fetchScalarCost pairFinishCost
    fetchOutputTableCost fetchPageCost scaleOutputPrefixCost
  simp only [Nat.zero_mul,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
  gcongr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
