module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingWords
public import IntegerMultBounds.NLogN.PhaseCellHaloNeighborhood

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

theorem spatialCouplingInputWords_deep_interior {s t : ℕ} [NeZero s] (hst : s ≤ t)
    (band a b i : ℕ) (C : ZMod s → GaussianInt)
    (hi : (i : ZMod s) ∈ haloInterior s t (2*band) a b) :
    spatialCouplingInputWords true t band a b i C = List.replicate (2*band+1) 0 := by
  have hz : ∀ δ ∈ spatialCouplingOffsets band,
      (if (i : ZMod s)+(δ : ZMod s) ∈ haloBoundary s t band a b then C ((i : ZMod s)+(δ : ZMod s)) else 0) = 0 := by
    intro δ hδ
    simp [haloInterior_stencil_disjoint_boundary hst band a b _ hi hδ]
  dsimp only [spatialCouplingInputWords]
  simp only [ite_true]
  rw [List.map_congr_left hz]
  simp

theorem couplingRowWord_deep_interior {s t : ℕ} [NeZero s] (hst : s ≤ t)
    (P q u band a b i : ℕ) (C : ZMod s → GaussianInt) (rhs : GaussianInt)
    (hi : (i : ZMod s) ∈ haloInterior s t (2*band) a b) :
    couplingRowWord P q t u band a b i true C rhs = rhs := by
  rw [← couplingRowWord_spatial]
  have hz := spatialCouplingInputWords_deep_interior hst band a b i C hi
  rw [hz,coupling_dot_zero q _ _ (by intro x hx; simpa using (List.eq_of_mem_replicate hx))]
  simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
