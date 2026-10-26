module

public import IntegerMultBounds.NLogN.PhaseCellCouplingMass
public import IntegerMultBounds.NLogN.PhaseCellHaloBoundary
public import IntegerMultBounds.NLogN.SchurBoundaryResidual

/-! Dominance and backward-error stability for the actual clipped-halo Schur system. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance PhaseCellDiscreteGeometry

variable {s t : ℕ} [NeZero s]

theorem halo_schur_stageInv (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u a b : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p) :
    let I := haloInterior s t (PhaseCellBand.width p u) a b
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    StageInv (run (realMatrix s t p u) (I∪B) I.toList).1 B (1/(8*(p : ℝ))) 2 := by
  dsimp only
  let : NeZero t := ⟨by omega⟩
  let I := haloInterior s t (PhaseCellBand.width p u) a b
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    positivity
  have hIB : Disjoint I B := haloInterior_disjoint_boundary s t _ a b
  have hA := dominates_mono (realMatrix s t p u) univ (I∪B) _ (subset_univ _)
    (matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget)
  refine ⟨schur_dominates _ I B hIB _ hμ hA I.toList (toList_toFinset I),?_⟩
  intro i hi
  have hmass := run_mass (realMatrix s t p u) (I∪B) _ hμ hA I.toList i
  rw [run_set,toList_toFinset,union_sdiff_left,sdiff_eq_self_of_disjoint hIB.symm] at hmass
  apply hmass.trans
  calc
    _ ≤ ∑ j, |realMatrix s t p u i j| := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
    _ = ∑ j, realMatrix s t p u i j := by
      apply sum_congr rfl
      intro j _
      apply abs_of_nonneg
      unfold realMatrix
      exact_mod_cast matrix_nonneg s t p u i j
    _ ≤ 2 := matrix_row_sum_le_two hst hα p u hp hwidth hαu hθ hgap hbudget i

theorem halo_computed_schur_error (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u a b : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (R : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ c, Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) (R c) c)
    (Sh : Matrix (ZMod s) (ZMod s) ℝ) (εA : ℝ) (hεA : 0 ≤ εA) (hsmall : εA < 1/(8*(p : ℝ)))
    (hSh : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      ∑ j ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
        |Sh i j-(run (realMatrix s t p u) (haloVertices s a b)
          (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 i j| ≤ εA)
    (rhs x r X : ZMod s → ℝ) (hx : Solves (realMatrix s t p u) (haloVertices s a b) x rhs)
    (ρ δ E : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hE : 0 ≤ E)
    (hr : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b, |r i| ≤ ρ)
    (hrE : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |r i-residual (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) R rhs i| ≤ E)
    (hX : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |(∑ j ∈ haloBoundary s t (PhaseCellBand.width p u) a b, Sh i j*X j)-r i| ≤ δ) :
    (∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b, |X i| ≤ (ρ+δ)/(1/(8*(p : ℝ))-εA)) ∧
      ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
        |X i-x i| ≤ (δ+εA*((ρ+δ)/(1/(8*(p : ℝ))-εA))+E)/(1/(8*(p : ℝ))) := by
  let : NeZero t := ⟨by omega⟩
  let I := haloInterior s t (PhaseCellBand.width p u) a b
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  have hU : I∪B = haloVertices s a b := haloInterior_union_boundary s t _ a b
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    positivity
  have hA := dominates_mono (realMatrix s t p u) univ (I∪B) _ (subset_univ _)
    (matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget)
  apply computed_schur_error (realMatrix s t p u) I B (haloInterior_disjoint_boundary s t _ a b)
    (1/(8*(p : ℝ))) 2 hμ hA R hR (halo_schur_stageInv hst hα p u a b hp hwidth hαu hθ hgap hbudget)
    Sh εA hεA hsmall (by simpa only [hU] using hSh) rhs x r X (by simpa only [hU] using hx)
    ρ δ E hρ hδ hE hr hrE hX

end IntegerMultBounds.NLogN.PhaseCellMatrix
