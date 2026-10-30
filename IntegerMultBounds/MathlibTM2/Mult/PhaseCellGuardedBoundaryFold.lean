module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingField
public import IntegerMultBounds.NLogN.PhaseCellBoundaryFold

/-! Identify the computed guarded residual with the solver's folded RHS. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem guardedCouplingRowField_boundaryFold {s t : ℕ} [NeZero s]
    (P q u band a b : ℕ) (hst : s < t) (hb : b ≤ s)
    (C B : ZMod s → GaussianInt) :
    (bFoldOrder s (haloBoundary s t band a b)).map (guardedCouplingRowField P q t u band a b false C B) =
      (bFoldOrder s (haloBoundary s t band a b)).map (couplingRowField P q t u band a b false C B) := by
  apply List.map_congr_left
  intro i hi
  have hiB : i ∈ haloBoundary s t band a b := by
    rwa [← List.mem_toFinset,bFoldOrder_toFinset] at hi
  exact guardedCouplingRowField_eq hst P q u band a b false hb C B i (Or.inr hiB)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
