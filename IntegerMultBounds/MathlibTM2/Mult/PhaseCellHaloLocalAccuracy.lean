module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
public import IntegerMultBounds.NLogN.PhaseCellLocality

/-! Arithmetic accuracy on a principal halo becomes global accuracy on its
owned core. Both solves use the original ambient matrix, including at the seam. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
open Finset IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
variable {s t : ℕ} [NeZero s]

theorem ErrorOn.halo_global (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u target : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (a b : ℕ) (hb : b ≤ s) (core : Finset (ZMod s))
    (hcore : core ⊆ haloLayer s a b (PhaseCellBand.width p u) (localityDepth p target))
    (out x y rhs : ZMod s → ℝ) (arithmetic : ℝ)
    (hx : Solves (realMatrix s t p u) univ x rhs)
    (hy : Solves (realMatrix s t p u) (haloVertices s a b) y rhs)
    (hrhs : ∀ i, |rhs i| ≤ 1)
    (herror : ErrorOn (haloVertices s a b) out y arithmetic) :
    ErrorOn core out x (arithmetic+1/(2 : ℝ)^target) := by
  apply (herror.crop (hcore.trans (haloLayer_subset a b (PhaseCellBand.width p u) _))).trans
  intro i hi
  simpa only [Real.norm_eq_abs] using halo_locality_precision hst hα p u target hp hwidth
    hαu hθ hgap hbudget a b hb x y rhs hx hy hrhs i (hcore hi)

theorem ErrorOn.cyclic_halo_global (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u target : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (origin : ZMod s) (a b : ℕ) (hb : b ≤ s) (core : Finset (ZMod s))
    (hcore : core ⊆ cyclicHaloLayer origin a b (PhaseCellBand.width p u) (localityDepth p target))
    (out x y rhs : ZMod s → ℝ) (arithmetic : ℝ)
    (hx : Solves (realMatrix s t p u) univ x rhs)
    (hy : Solves (realMatrix s t p u) (cyclicHaloLayer origin a b (PhaseCellBand.width p u) 0) y rhs)
    (hrhs : ∀ i, |rhs i| ≤ 1)
    (herror : ErrorOn (cyclicHaloLayer origin a b (PhaseCellBand.width p u) 0) out y arithmetic) :
    ErrorOn core out x (arithmetic+1/(2 : ℝ)^target) := by
  apply (herror.crop (hcore.trans (cyclicHaloLayer_subset origin a b (PhaseCellBand.width p u) _))).trans
  intro i hi
  simpa only [Real.norm_eq_abs] using cyclic_halo_locality_precision hst hα p u target hp hwidth
    hαu hθ hgap hbudget origin a b hb x y rhs hx hy hrhs i (hcore hi)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
