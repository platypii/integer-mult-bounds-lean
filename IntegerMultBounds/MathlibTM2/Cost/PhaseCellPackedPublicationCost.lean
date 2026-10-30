module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReusablePackedCellBatchPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBatchCost

/-! Reuse the established scalar batch arithmetic bound. Only packed tape
conversion, publication and disposal need a new polynomial control allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- All dimensions and working widths may share any polynomial envelope.
The scalar arithmetic bill is preserved verbatim. -/
theorem reusablePackedCellBatchPublishCost_le_bound
    (p l target rhsExp V N L K s t u Z : ℕ) (hZ : 1 ≤ Z)
    (hV : V ≤ Z) (hN : N ≤ Z) (hL : L ≤ Z) (hK : K ≤ Z)
    (hq : executionPrecision p l target rhsExp ≤ Z)
    (hw : executionWidth p l target rhsExp ≤ Z) :
    reusablePackedCellBatchPublishCost p l target rhsExp V N L K s t u ≤
      sizedClosedBatchBound p l K L s t u target rhsExp+10000*Z^4 := by
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  have harithmetic := sizedClosedBatchCost_le_bound p l K L s t u target rhsExp
  have hcontrols :
      (4*K+4)+(packedCellGroupInputCost V N L w K q+
        (12*N*w+21*K+6*L*w+9*L+27)+(54*N*w+15))+
        (retireProductLineCost K L w+(2*K+2)) ≤ 10000*Z^4 := by
    have hmono :
        (4*K+4)+(packedCellGroupInputCost V N L w K q+
          (12*N*w+21*K+6*L*w+9*L+27)+(54*N*w+15))+
          (retireProductLineCost K L w+(2*K+2)) ≤
        (4*Z+4)+(packedCellGroupInputCost Z Z Z Z Z Z+
          (12*Z*Z+21*Z+6*Z*Z+9*Z+27)+(54*Z*Z+15))+
          (retireProductLineCost Z Z Z+(2*Z+2)) := by
      unfold packedCellGroupInputCost retireProductLineCost retireCountedLineCost tblC
      dsimp only [q,w]
      gcongr
    apply hmono.trans
    unfold packedCellGroupInputCost retireProductLineCost retireCountedLineCost tblC
    have h₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
    have h₃ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
    have h₄ : Z^3 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
    nlinarith only [hZ,h₂,h₃,h₄]
  dsimp only [reusablePackedCellBatchPublishCost]
  dsimp only [q,w] at hcontrols
  omega

end IntegerMultBounds.MathlibTM2.Cost
