module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeneratedWorkspacePolynomial
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedSetupSizing

/-! The actual generated setup satisfies the mixed polynomial bound without dimension suppliers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

@[irreducible] def generatedSetupScale (p l target rhsExp t u band : ℕ) : ℕ :=
  3000000*(p+l+target+rhsExp+1)^2+4*t.size+2*u.size+band.size+1

theorem generatedBatchSetupBudget_sized_poly (C p l s t u band target rhsExp : ℕ) :
    let Z := generatedSetupScale p l target rhsExp t u band
    generatedBatchSetupBudget C (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) s t u band l (4*p+1) ≤
      288*C*(ssMulConst+1)*Z^3+100000000*(C+1)*(Z+1)^3+
        1000000*(s+t+u+band+1)*(Z+1) := by
  let E := p+l+target+rhsExp+1
  let Z := generatedSetupScale p l target rhsExp t u band
  have hE : E ≤ E^2 := by simpa only [pow_two] using Nat.le_mul_self E
  have hsmall (a : ℕ) (ha : a ≤ 500000*E) : a ≤ Z := by
    dsimp only [Z]
    unfold generatedSetupScale
    change a ≤ 3000000*E^2+4*t.size+2*u.size+band.size+1
    omega
  have hW := generatedIntegerSetupWidth_le p l target rhsExp
  have hW' : integerSetupWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionStagePrecision p l target rhsExp+2) 0 ≤ Z := by
    apply hW.trans
    change 700000*E^2 ≤ Z
    dsimp only [Z]
    unfold generatedSetupScale
    change 700000*E^2 ≤ 3000000*E^2+4*t.size+2*u.size+band.size+1
    omega
  have hV := generatedCoefficientWidth_le p l target rhsExp t u band
  have hV' : coefficientWorkspaceWidth (2^15*p)
      (integerSetupWidth (2^15*p) (executionPrecision p l target rhsExp)
        (executionStagePrecision p l target rhsExp+2) 0) t u band (4*p+1) ≤ Z := by
    apply hV.trans
    change 2000000*E^2+t.size+u.size+band.size ≤ Z
    dsimp only [Z]
    unfold generatedSetupScale
    change 2000000*E^2+t.size+u.size+band.size ≤ 3000000*E^2+4*t.size+2*u.size+band.size+1
    omega
  have hT := generatedWeightWidth_le p l target rhsExp t u
  have hT' : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u ≤ Z := by
    apply hT.trans
    change 500000*E+3*t.size+u.size ≤ Z
    dsimp only [Z]
    unfold generatedSetupScale
    change 500000*E+3*t.size+u.size ≤ 3000000*E^2+4*t.size+2*u.size+band.size+1
    omega
  dsimp only
  apply generatedBatchSetupBudget_poly
  · unfold generatedSetupScale; omega
  · apply hsmall; dsimp only [E]; norm_num; omega
  · apply hsmall; unfold executionStagePrecision executionExponent inputExponent sourceExponent; dsimp only [E]; omega
  · apply hsmall; unfold executionPrecision executionExponent inputExponent sourceExponent; dsimp only [E]; omega
  · apply hsmall; dsimp only [E]; omega
  · apply hsmall; dsimp only [E]; omega
  · simpa only [Nat.add_assoc,Nat.reduceAdd] using hW'
  · simpa only [Nat.add_assoc,Nat.reduceAdd] using hV'
  · exact hT'

theorem generatedBatchSetupWorkspace_sized_poly (C p l s t u band target rhsExp : ℕ) :
    let Z := generatedSetupScale p l target rhsExp t u band
    generatedBatchSetupWorkspace C (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) s t u band l (4*p+1) 0 ≤
      288*C*(ssMulConst+1)*Z^3+100000000*(C+1)*(Z+1)^3+
        1000000*(s+t+u+band+1)*(Z+1) := by
  exact (generatedBatchSetupWorkspace_zero_le_budget C (2^15*p)
    (executionStagePrecision p l target rhsExp+1) (executionPrecision p l target rhsExp)
    s t u band l (4*p+1)).trans
      (generatedBatchSetupBudget_sized_poly C p l s t u band target rhsExp)

end IntegerMultBounds.MathlibTM2.Cost
