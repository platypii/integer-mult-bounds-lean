module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLocalAccuracy
public import IntegerMultBounds.NLogN.PhaseCellTargetCoreLocality

/-! Local principal accuracy on actual manuscript source cores. The cyclic
version restricts the same original matrix, including its physical seam. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
open Finset IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
variable {s t : ℕ} [NeZero s]

theorem ErrorOn.target_owned_global (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u target L k : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (ha : localityDepth p target*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u ≤ s)
    (out x y rhs : ZMod s → ℝ) (arithmetic : ℝ)
    (hx : Solves (realMatrix s t p u) univ x rhs)
    (hy : Solves (realMatrix s t p u)
      (haloVertices s (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
        (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)) y rhs)
    (hrhs : ∀ i, |rhs i| ≤ 1)
    (herror : ErrorOn
      (haloVertices s (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
        (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)) out y arithmetic) :
    ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1))) out x
      (arithmetic+1/(2 : ℝ)^target) := by
  exact herror.halo_global hst hα p u target hp hwidth hαu hθ hgap hbudget _ _ hb _
    (by rw [owned_haloLayer t L k _ _ ha]) out x y rhs arithmetic hx hy hrhs

theorem ErrorOn.target_owned_cyclic_global (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u target L k : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hfit : rows s t L k+2*(localityDepth p target*PhaseCellBand.width p u) ≤ s)
    (out x y rhs : ZMod s → ℝ) (arithmetic : ℝ)
    (hx : Solves (realMatrix s t p u) univ x rhs)
    (hy : Solves (realMatrix s t p u)
      (cyclicHaloLayer ((cut s t L k : ZMod s)-((localityDepth p target*PhaseCellBand.width p u : ℕ) : ZMod s)) 0
        (rows s t L k+2*(localityDepth p target*PhaseCellBand.width p u)) (PhaseCellBand.width p u) 0) y rhs)
    (hrhs : ∀ i, |rhs i| ≤ 1)
    (herror : ErrorOn
      (cyclicHaloLayer ((cut s t L k : ZMod s)-((localityDepth p target*PhaseCellBand.width p u : ℕ) : ZMod s)) 0
        (rows s t L k+2*(localityDepth p target*PhaseCellBand.width p u)) (PhaseCellBand.width p u) 0) out y arithmetic) :
    ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1))) out x
      (arithmetic+1/(2 : ℝ)^target) := by
  exact herror.cyclic_halo_global hst hα p u target hp hwidth hαu hθ hgap hbudget _ 0 _ hfit _
    (owned_in_cyclic_layer t L k _ _ hfit) out x y rhs arithmetic hx hy hrhs

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
