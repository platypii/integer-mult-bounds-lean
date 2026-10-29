module

public import IntegerMultBounds.NLogN.SchurLocality
public import IntegerMultBounds.NLogN.PhaseCellLocalityPrecision
public import IntegerMultBounds.NLogN.PhaseCellHaloLayers
public import IntegerMultBounds.NLogN.PhaseCellCouplingMass

/-! # Locality for the actual rounded Gaussian matrix

The ambient matrix and its original phase coordinates are unchanged. Geometry
supplies nested supported neighborhoods; the analytic constants follow from
the existing rounded-matrix dominance and row-mass theorems.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance
variable {s t : ℕ} [NeZero s]

/-- A principal solve converges geometrically to the global solve as the owned
core moves deeper into the halo. The bound has no ambient-size factor. -/
theorem principal_locality (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (S : Finset (ZMod s)) (layers : ℕ → Finset (ZMod s))
    (x y b : ZMod s → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hx : Solves (realMatrix s t p u) univ x b)
    (hy : Solves (realMatrix s t p u) S y b)
    (hb : ∀ i, |b i| ≤ B)
    (hlayers : ∀ n, layers n ⊆ S)
    (hexterior : ∀ n i, i ∈ layers (n+1) → ∀ j, j ∉ S → realMatrix s t p u i j = 0)
    (hsupport : ∀ n i, i ∈ layers (n+1) →
      ∀ j ∈ S.erase i, realMatrix s t p u i j ≠ 0 → j ∈ layers n) :
    ∀ n i, i ∈ layers n →
      |y i-x i| ≤ (1-(1/(8*(p : ℝ)))/2)^n * (2*B/(1/(8*(p : ℝ)))) := by
  let : NeZero t := ⟨by omega⟩
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  have hμtwo : (1 : ℝ)/(8*(p : ℝ)) ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hA := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hS := dominates_mono (realMatrix s t p u) univ S _ (subset_univ S) hA
  have hdiag (i : ZMod s) : realMatrix s t p u i i ≤ 2 := by
    have hentry (j : ZMod s) : 0 ≤ realMatrix s t p u i j := by
      unfold realMatrix
      exact_mod_cast matrix_nonneg s t p u i j
    exact (single_le_sum (fun j _ => hentry j) (mem_univ i)).trans
      (matrix_row_sum_le_two hst hα p u hp hwidth hαu hθ hgap hbudget i)
  exact solves_locality (realMatrix s t p u) S univ (subset_univ S) layers
    (1/(8*(p : ℝ))) B hμ hμtwo hB hS hA (fun i _ => hdiag i)
    x y b hx hy (fun i _ => hb i) hlayers
    (fun n i hi j _ hj => hexterior n i hi j hj) hsupport

/-- Concrete interval halos satisfy locality across all original phase cuts. -/
theorem halo_locality (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (a b : ℕ) (hb : b ≤ s) (x y rhs : ZMod s → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hx : Solves (realMatrix s t p u) univ x rhs)
    (hy : Solves (realMatrix s t p u) (PhaseCellDiscreteGeometry.haloVertices s a b) y rhs)
    (hrhs : ∀ i, |rhs i| ≤ B) :
    ∀ n i, i ∈ haloLayer s a b (PhaseCellBand.width p u) n →
      |y i-x i| ≤ (1-(1/(8*(p : ℝ)))/2)^n * (2*B/(1/(8*(p : ℝ)))) := by
  apply principal_locality hst hα p u hp hwidth hαu hθ hgap hbudget
    (PhaseCellDiscreteGeometry.haloVertices s a b)
    (fun n => haloLayer s a b (PhaseCellBand.width p u) n) x y rhs B hB hx hy hrhs
  · exact haloLayer_subset a b (PhaseCellBand.width p u)
  · intro n i hi j hj
    by_contra hne
    obtain ⟨δ,hlo,hhi,rfl⟩ := realMatrix_support p u i j hne
    exact hj (haloLayer_subset a b (PhaseCellBand.width p u) n
      (haloLayer_shift a b (PhaseCellBand.width p u) n hb i hi δ ⟨hlo,hhi⟩))
  · intro n i hi j _ hne
    obtain ⟨δ,hlo,hhi,rfl⟩ := realMatrix_support p u i j hne
    exact haloLayer_shift a b (PhaseCellBand.width p u) n hb i hi δ ⟨hlo,hhi⟩

/-- Selected polynomial depth gives the requested absolute locality tolerance. -/
theorem halo_locality_precision (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u target : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (a b : ℕ) (hb : b ≤ s) (x y rhs : ZMod s → ℝ)
    (hx : Solves (realMatrix s t p u) univ x rhs)
    (hy : Solves (realMatrix s t p u) (PhaseCellDiscreteGeometry.haloVertices s a b) y rhs)
    (hrhs : ∀ i, |rhs i| ≤ 1) (i : ZMod s)
    (hi : i ∈ haloLayer s a b (PhaseCellBand.width p u) (localityDepth p target)) :
    |y i-x i| ≤ 1/(2 : ℝ)^target := by
  have h := halo_locality hst hα p u hp hwidth hαu hθ hgap hbudget
    a b hb x y rhs 1 (by norm_num) hx hy hrhs (localityDepth p target) i hi
  have he : (1 : ℝ)-(1/(8*p))/2 = 1-1/(16*p) := by ring
  have hf : (2 : ℝ)*1/(1/(8*p)) = 16*p := by simp only [div_eq_mul_inv, one_mul, inv_inv]; ring
  rw [he,hf] at h
  exact h.trans (locality_precision p target (by omega))

/-- Cyclic windows obey the same tolerance, including those crossing the ambient
period seam. The principal matrix still uses the original global coordinates. -/
theorem cyclic_halo_locality_precision (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u target : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (origin : ZMod s) (a b : ℕ) (hb : b ≤ s) (x y rhs : ZMod s → ℝ)
    (hx : Solves (realMatrix s t p u) univ x rhs)
    (hy : Solves (realMatrix s t p u)
      (cyclicHaloLayer origin a b (PhaseCellBand.width p u) 0) y rhs)
    (hrhs : ∀ i, |rhs i| ≤ 1) (i : ZMod s)
    (hi : i ∈ cyclicHaloLayer origin a b (PhaseCellBand.width p u) (localityDepth p target)) :
    |y i-x i| ≤ 1/(2 : ℝ)^target := by
  have h := principal_locality hst hα p u hp hwidth hαu hθ hgap hbudget
    (cyclicHaloLayer origin a b (PhaseCellBand.width p u) 0)
    (cyclicHaloLayer origin a b (PhaseCellBand.width p u)) x y rhs 1 (by norm_num) hx hy hrhs
    (cyclicHaloLayer_subset origin a b (PhaseCellBand.width p u))
    (by
      intro n j hj k hk
      by_contra hne
      obtain ⟨δ,hlo,hhi,rfl⟩ := realMatrix_support p u j k hne
      exact hk (cyclicHaloLayer_subset origin a b (PhaseCellBand.width p u) n
        (cyclicHaloLayer_shift origin a b (PhaseCellBand.width p u) n hb j hj δ ⟨hlo,hhi⟩)))
    (by
      intro n j hj k _ hne
      obtain ⟨δ,hlo,hhi,rfl⟩ := realMatrix_support p u j k hne
      exact cyclicHaloLayer_shift origin a b (PhaseCellBand.width p u) n hb j hj δ ⟨hlo,hhi⟩)
    (localityDepth p target) i hi
  have he : (1 : ℝ)-(1/(8*p))/2 = 1-1/(16*p) := by ring
  have hf : (2 : ℝ)*1/(1/(8*p)) = 16*p := by
    simp only [div_eq_mul_inv,one_mul,inv_inv]
    ring
  rw [he,hf] at h
  exact h.trans (locality_precision p target (by omega))

end IntegerMultBounds.NLogN.PhaseCellMatrix
