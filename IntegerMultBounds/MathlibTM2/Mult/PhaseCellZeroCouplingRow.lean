module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingWords

/-! Boundary-source recovery rows deep in the halo interior are exactly zero couplings. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Rounding a product with an exact zero input introduces no error. -/
theorem coupling_dot_zero (q : ℕ) (xs zs : List GaussianInt)
    (hzero : ∀ x ∈ xs, x = 0) :
    (List.zipWith (fun x z => tdivN q (x*z)) xs zs).sum = 0 := by
  induction xs generalizing zs with
  | nil => simp
  | cons x xs ih =>
    have hx : x = 0 := hzero x (by simp)
    have hxs : ∀ y ∈ xs, y = 0 := by intro y hy; exact hzero y (by simp [hy])
    cases zs with
    | nil => simp
    | cons z zs =>
      simp only [List.zipWith_cons_cons,List.sum_cons,hx,zero_mul,ih zs hxs,add_zero]
      ext <;> simp [tdivN]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
