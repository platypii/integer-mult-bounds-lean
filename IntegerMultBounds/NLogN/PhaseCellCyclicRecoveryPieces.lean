module

public import IntegerMultBounds.NLogN.PhaseCellCyclicInteriorSplit
public import IntegerMultBounds.NLogN.SchurBlockSolve

/-! Interior recovery reads only its own physical boundary, even though the
boundary solution was computed by one coupled cyclic solve. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance
open scoped BigOperators
open Finset

theorem couple_eq_of_row_support {ι : Type*} [DecidableEq ι]
    (M : Matrix ι ι ℝ) (B C : Finset ι) (hBC : B ⊆ C) (x : ι → ℝ) (i : ι)
    (hsupport : ∀ j ∈ C, M i j ≠ 0 → j ∈ B) :
    couple M C x i = couple M B x i := by
  symm
  apply sum_subset hBC
  intro j hj hnot
  have hz : M i j = 0 := by
    by_contra hne
    exact hnot (hsupport j hj hne)
  simp only [hz,zero_mul]

end IntegerMultBounds.NLogN.SchurDominance

namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open Finset PhaseCellMatrix SchurDominance
variable {s t : ℕ} [NeZero s]

theorem cyclicPrincipal_recovery_couple (p u a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (x : ZMod s → ℝ) :
    (∀ i ∈ haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a)),
      couple (realMatrix s t p u) (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n) x i =
        couple (realMatrix s t p u) (haloBoundary s t (PhaseCellBand.width p u) a (a+min n (s-a))) x i) ∧
    (∀ i ∈ haloInterior s t (PhaseCellBand.width p u) 0 (n-min n (s-a)),
      couple (realMatrix s t p u) (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n) x i =
        couple (realMatrix s t p u) (haloBoundary s t (PhaseCellBand.width p u) 0 (n-min n (s-a))) x i) := by
  rw [cyclicPrincipalBoundary_eq t (PhaseCellBand.width p u) a n ha hn]
  constructor
  · intro i hi
    apply couple_eq_of_row_support _ _ _ subset_union_left
    intro j hj hne
    have hv := haloInterior_row_support p u a _ (by omega) i j hi hne
    rcases mem_union.mp hj with hj | hj
    · exact hj
    · exact False.elim (disjoint_left.mp (cyclicPrincipalPieces_disjoint a n ha hn)
        hv (mem_sdiff.mp hj).1)
  · intro i hi
    apply couple_eq_of_row_support _ _ _ subset_union_right
    intro j hj hne
    have hv := haloInterior_row_support p u 0 _ (by omega) i j hi hne
    rcases mem_union.mp hj with hj | hj
    · exact False.elim (disjoint_left.mp (cyclicPrincipalPieces_disjoint a n ha hn)
        (mem_sdiff.mp hj).1 hv)
    · exact hj

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
