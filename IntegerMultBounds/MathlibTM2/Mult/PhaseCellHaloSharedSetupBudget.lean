module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSizedArithmeticWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLengthPrecisionBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchWorkspaceBound

/-! The actual selected-key reserve uses generated setup and an explicit arithmetic budget. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

@[irreducible] def haloSharedSetupBudget (J R K p l s t u target rhsExp L : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  generatedBatchSetupBudget J (2^15*p) (executionStagePrecision p l target rhsExp+1)
    q s t u (PhaseCellBand.width p u) l L+
  (2*((R+1)*ringWorkspaceBudget q l w+1000*(q+l+2^l+1)*(w+1))+
    3*K*rmulCost w+180900*((2*w).size+1)*(w+1)^2+
    10000*(K+1)*(2^l+L+1)*(w+cExp+(8*p+1)+l+1))

theorem haloKeySharedSetup_le_budget (J R K p l s t u target rhsExp L : ℕ) :
    haloKeySharedSetup J R K p l s t u target rhsExp L ≤
      haloSharedSetupBudget J R K p l s t u target rhsExp L := by
  unfold haloKeySharedSetup haloSharedSetupBudget
  dsimp only
  exact Nat.add_le_add (generatedBatchSetupWorkspace_zero_le_budget _ _ _ _ _ _ _ _ _ _)
    ((sizedCellArithmeticWorkspace_zero_le R K p l target rhsExp L).trans
      (sizedArithmeticSetupWorkspace_le_ring_budget R K p l target rhsExp L))

theorem generatedHaloKeysWorkspace_le_budget
    (J R K p l s t u target rhsExp V a b : ℕ)
    (hp : 0 < p) (hs : 0 < s) (hst : s < t) (ha : a ≤ s) (hb : b ≤ s)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) :
    haloLengthKeyLoopWorkspace J R K p l s t u target rhsExp V a b
      (haloLengthKeys s t (PhaseCellBand.width p u) a b) ≤
      haloSharedSetupBudget J R K p l s t u target rhsExp (4*p+1)+
        haloKeyAuxWorkspace R K p l s t u target rhsExp V := by
  apply (generatedHaloKeysWorkspace_le_precision J R K p l s t u target rhsExp V a b
    hp hs hst ha hb hθ).trans
  exact Nat.add_le_add_right (haloKeySharedSetup_le_budget J R K p l s t u target rhsExp (4*p+1)) _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
