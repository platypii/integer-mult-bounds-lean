module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunCouplingRows

/-! The existing row schedule pays ambient-source capture for every row. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- This is a lower bound on the declared paid allowance, not on every execution time. -/
theorem couplingRowStepCost_capture_le (P q w s t u band a b i : ℕ) :
    18*s*w ≤ couplingRowStepCost P q w s t u band a b i := by
  dsimp only [couplingRowStepCost,rawCouplingRowCost,rawCouplingOperandsCost]
  nlinarith only [Nat.zero_le (prepareCouplingOperandsCost P q w s t u band a b i),
    Nat.zero_le (generatedReadyRowCost (2*band+1) q w band)]

theorem couplingRowLoopCost_capture_le (P q w s t u band a b i N : ℕ) :
    N*(18*s*w) ≤ couplingRowLoopCost P q w s t u band a b i N := by
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun j _ =>
    (couplingRowStepCost_capture_le P q w s t u band a b (i+j)).trans (Nat.le_add_right _ 3))
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at hsum
  exact hsum.trans (Nat.le_add_right _ 2)

theorem runCouplingRowsCost_capture_le (P q w s t u band a b : ℕ) :
    18*s*s*w ≤ runCouplingRowsCost P q w s t u band a b := by
  have h := couplingRowLoopCost_capture_le P q w s t u band a b 0 s
  have heq : 18*s*s*w = s*(18*s*w) := by ring
  rw [heq]
  exact h.trans (by dsimp only [runCouplingRowsCost]; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
