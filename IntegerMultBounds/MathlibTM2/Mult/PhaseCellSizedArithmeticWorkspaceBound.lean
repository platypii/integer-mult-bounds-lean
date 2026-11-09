module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArithmeticWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutionSizing
public import IntegerMultBounds.MathlibTM2.Fast.RingWorkspaceBound

/-! Generated caller precision discharges every arithmetic setup width condition. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast

@[irreducible] def sizedArithmeticSetupWorkspace (R K p l target rhsExp L : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let e := 8*p+1
  2*((R+1)*rpWorkspace q l w 0+1000*(q+l+2^l+1)*(w+1))+
    3*K*rmulCost w+180900*((2*w).size+1)*(w+1)^2+
    10000*(K+1)*(2^l+L+1)*(w+cExp+e+l+1)

theorem sizedCellArithmeticWorkspace_zero_le (R K p l target rhsExp L : ℕ) :
    cellArithmeticWorkspace R K (executionPrecision p l target rhsExp)
      (sourceExponent l target rhsExp) (8*p+1) l (executionWidth p l target rhsExp) 0 L ≤
      sizedArithmeticSetupWorkspace R K p l target rhsExp L := by
  have hroom := execution_width_bound p l target rhsExp
  have hwidth : executionPrecision p l target rhsExp+
      (sourceExponent l target rhsExp+(8*p+1)+1) ≤ executionWidth p l target rhsExp := by
    unfold inputExponent at hroom
    omega
  unfold sizedArithmeticSetupWorkspace
  exact cellArithmeticWorkspace_zero_le_primitives _ _ _ _ _ _ _ _
    (by unfold executionWidth; omega) hwidth

theorem sizedArithmeticSetupWorkspace_le_ring_budget (R K p l target rhsExp L : ℕ) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    sizedArithmeticSetupWorkspace R K p l target rhsExp L ≤
      2*((R+1)*ringWorkspaceBudget q l w+1000*(q+l+2^l+1)*(w+1))+
        3*K*rmulCost w+180900*((2*w).size+1)*(w+1)^2+
        10000*(K+1)*(2^l+L+1)*(w+cExp+(8*p+1)+l+1) := by
  unfold sizedArithmeticSetupWorkspace
  dsimp only
  have h := rpWorkspace_zero_le_budget (executionPrecision p l target rhsExp) l
    (executionWidth p l target rhsExp)
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (Nat.mul_le_mul_left (R+1) h) _)) _) _) _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
