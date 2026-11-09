module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArithmeticStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarSetupCostBound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! Additional replicas add only linear storage to shared cell arithmetic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Mult.ShortConv
open ScalarPlacement IntegerMultBounds.MathlibTM2.Fast

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

theorem cellArithmeticWorkspace_zero_le_components (R K q cExp e l w L : ℕ) :
    cellArithmeticWorkspace R K q cExp e l w 0 L ≤
      2*Fixed.workspace R q l w 0+3*K*rmulCost w+
      3*prepareWeightsCost q (cExp+e+1) w+3*prepareWeightsCost q 0 w+3*prepareCost q w+
      10000*(K+1)*(2^l+L+1)*(w+cExp+e+l+1) := by
  unfold cellArithmeticWorkspace normalizedInteriorWorkspace inputInteriorWorkspace
    inputStageWorkspace interiorWorkspace preparedOutputWorkspace outputFromHeadersWorkspace
    closedOutputWorkspace applyWeightsWorkspace runWeightsWorkspace applyWorkspace runWorkspace
    compactPairWorkspace triangularPairWorkspace
    realWeightWorkspace realScalarWorkspace
    routeWeightsCost routeCost installInputCost fixedMergeCost fetchScalarCost pairFinishCost
    fetchOutputTableCost fetchPageCost scaleOutputPrefixCost
  ring_nf
  omega

private theorem three_setup_bounds {x a b c d e u : ℕ}
    (h : x ≤ a+3*b+3*c+3*d+e)
    (hb : b ≤ 20100*u) (hc : c ≤ 20100*u) (hd : d ≤ 20100*u) :
    x ≤ a+180900*u+e := by omega

theorem cellArithmeticWorkspace_zero_le_headers (R K q cExp e l w L : ℕ)
    (hw : 1 ≤ w) (hwidth : q+(cExp+e+1) ≤ w) :
    cellArithmeticWorkspace R K q cExp e l w 0 L ≤
      2*Fixed.workspace R q l w 0+3*K*rmulCost w+
      180900*((2*w).size+1)*(w+1)^2+
      10000*(K+1)*(2^l+L+1)*(w+cExp+e+l+1) := by
  have h := cellArithmeticWorkspace_zero_le_components R K q cExp e l w L
  have hi := prepareWeightsCost_le_header_square q (cExp+e+1) w hw hwidth
  have ho := prepareWeightsCost_le_header_square q 0 w hw (by omega)
  have hs := prepareCost_le_header_square q w hw (by omega)
  have hi' : prepareWeightsCost q (cExp+e+1) w ≤ 20100*(((2*w).size+1)*(w+1)^2) := by
    simpa only [Nat.mul_assoc] using hi
  have ho' : prepareWeightsCost q 0 w ≤ 20100*(((2*w).size+1)*(w+1)^2) := by
    simpa only [Nat.mul_assoc] using ho
  have hs' : prepareCost q w ≤ 20100*(((2*w).size+1)*(w+1)^2) := by
    simpa only [Nat.mul_assoc] using hs
  have ht := three_setup_bounds (a := 2*Fixed.workspace R q l w 0+3*K*rmulCost w)
    (u := ((2*w).size+1)*(w+1)^2) h hi' ho' hs'
  simpa only [Nat.mul_assoc] using ht

theorem fixedWorkspace_zero_le_components (R q l w : ℕ) :
    Fixed.workspace R q l w 0 ≤ (R+1)*rpWorkspace q l w 0+
      1000*(q+l+2^l+1)*(w+1) := by
  unfold Fixed.workspace batchSetupCost operandSetupCost ldrHeaderCost
  ring_nf
  omega

theorem cellArithmeticWorkspace_zero_le_primitives (R K q cExp e l w L : ℕ)
    (hw : 1 ≤ w) (hwidth : q+(cExp+e+1) ≤ w) :
    cellArithmeticWorkspace R K q cExp e l w 0 L ≤
      2*((R+1)*rpWorkspace q l w 0+1000*(q+l+2^l+1)*(w+1))+
      3*K*rmulCost w+180900*((2*w).size+1)*(w+1)^2+
      10000*(K+1)*(2^l+L+1)*(w+cExp+e+l+1) := by
  apply (cellArithmeticWorkspace_zero_le_headers R K q cExp e l w L hw hwidth).trans
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (fixedWorkspace_zero_le_components R q l w)) _) _) _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
