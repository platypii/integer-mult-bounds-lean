module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingField
public import IntegerMultBounds.NLogN.PhaseCellBoundaryFold

/-! Identify the computed guarded residual with the solver's folded RHS. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
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

/-- Componentwise bounds in the exact list format consumed by the packed solve. -/
theorem couplingRowField_boundaryFold_bounds {s t p u q band a b rhsExp inputExp countExp : ℕ}
    [NeZero s] {α d : ℝ} (hp : 0 < p) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (C B : ZMod s → GaussianInt) (hcount : 2*band+1 ≤ 2^countExp)
    (hB : ∀ j, ‖value q (B j)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ j ∈ haloInterior s t band a b, ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp) :
    ∀ x ∈ (bFoldOrder s (haloBoundary s t band a b)).map
      (couplingRowField (2^15*p) q t u band a b false C B),
      |gv q x.re| ≤ (2 : ℝ)^couplingRowExponent rhsExp inputExp (8*p+1) countExp ∧
      |gv q x.im| ≤ (2 : ℝ)^couplingRowExponent rhsExp inputExp (8*p+1) countExp := by
  intro x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  have hn := couplingRowField_norm false hp hst hαu hθ hgap hbudget C B hcount hB hC i
  constructor
  · simpa [value,gv] using (Complex.abs_re_le_norm _).trans hn
  · simpa [value,gv] using (Complex.abs_im_le_norm _).trans hn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
