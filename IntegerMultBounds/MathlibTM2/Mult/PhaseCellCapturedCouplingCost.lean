module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCapturedCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowLoop

/-! Compare source retention with the former per-row capture allowance.
The former full-pass capture audit can be restored from dc798e22. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

def legacyCouplingRowsCost (P q w s t u band a b : ℕ) : ℕ :=
  couplingRowLoopCost P q w s t u band a b 0 s+32*s*w+34*s+28

theorem cachedCouplingRowLoopCost_saving (P q w s t u band a b i N : ℕ) :
    couplingRowLoopCost P q w s t u band a b i N =
      cachedCouplingRowLoopCost P q w s t u band a b i N+N*(18*s*w+9*s+18) := by
  have hrow (j : ℕ) : couplingRowStepCost P q w s t u band a b j =
      cachedCouplingRowStepCost P q w s t u band a b j+(18*s*w+9*s+18) := by
    dsimp only [couplingRowStepCost,cachedCouplingRowStepCost]
    rw [cachedCouplingRowCost_saving]
    ring
  have hsum :
      (Finset.range N).sum (fun j => couplingRowStepCost P q w s t u band a b (i+j)+3) =
      (Finset.range N).sum (fun j => cachedCouplingRowStepCost P q w s t u band a b (i+j)+3)+
        N*(18*s*w+9*s+18) := by
    calc
      _ = (Finset.range N).sum (fun j =>
          (cachedCouplingRowStepCost P q w s t u band a b (i+j)+3)+(18*s*w+9*s+18)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hrow]
        omega
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  dsimp only [couplingRowLoopCost,cachedCouplingRowLoopCost]
  rw [hsum]
  omega

theorem capturedCouplingRowsCost_saving (P q w s t u band a b : ℕ) :
    capturedCouplingRowsCost P q w s t u band a b+s*(18*s*w+9*s+18) =
      legacyCouplingRowsCost P q w s t u band a b+(s*(28*w+18)+28) := by
  dsimp only [capturedCouplingRowsCost,legacyCouplingRowsCost,runCachedCouplingRowsCost]
  rw [cachedCouplingRowLoopCost_saving]
  ring

theorem capturedCouplingRowsCost_le (P q w s t u band a b : ℕ) (hs : 2 ≤ s) :
    capturedCouplingRowsCost P q w s t u band a b ≤ legacyCouplingRowsCost P q w s t u band a b := by
  have h := capturedCouplingRowsCost_saving P q w s t u band a b
  have hcopy : 2*(18*s*w+9*s+18) ≤ s*(18*s*w+9*s+18) :=
    Nat.mul_le_mul_right _ hs
  have hfixed : s*(28*w+18)+28 ≤ 2*(18*s*w+9*s+18) := by nlinarith
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
