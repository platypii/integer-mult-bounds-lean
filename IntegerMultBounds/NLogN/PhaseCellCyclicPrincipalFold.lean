module

public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalGeometry
public import IntegerMultBounds.NLogN.PhaseCellHaloBoundaryFold

/-! One folded boundary system retains the original matrix's couplings across the seam. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open Finset PhaseCellMatrix SchurDominance
variable {s t : ℕ} [NeZero s]

theorem cyclicPrincipal_same_cell_interval (hst : s < t) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (i j : ZMod s) (hc : cell s t i = cell s t j) :
    ((cyclicPrincipalBoundary s t band a n).filter (fun k => i.val ≤ k.val ∧ k.val < j.val)).card ≤ 12*band := by
  rw [cyclicPrincipalBoundary_eq t band a n ha hn,filter_union]
  have hu := card_union_le
    ((haloBoundary s t band a (a+min n (s-a))).filter (fun k => i.val ≤ k.val ∧ k.val < j.val))
    ((haloBoundary s t band 0 (n-min n (s-a))).filter (fun k => i.val ≤ k.val ∧ k.val < j.val))
  have h₁ := halo_same_cell_interval hst band a (a+min n (s-a)) i j hc
  have h₂ := halo_same_cell_interval hst band 0 (n-min n (s-a)) i j hc
  omega

theorem cyclicPrincipal_cell_cycRel (hst : s < t) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (i j : ZMod s) (hc : cell s t i = cell s t j) :
    CycRel s (cyclicPrincipalBoundary s t band a n) (12*band) i j := by
  unfold CycRel
  left
  rcases le_total i.val j.val with hle | hle
  · have he := bRank_sub (B := cyclicPrincipalBoundary s t band a n) hle
    have hh := cyclicPrincipal_same_cell_interval hst band a n ha hn i j hc
    omega
  · have he := bRank_sub (B := cyclicPrincipalBoundary s t band a n) hle
    have hh := cyclicPrincipal_same_cell_interval hst band a n ha hn j i hc.symm
    omega

theorem cyclicPrincipal_schur_cycRel (hst : s < t) (p u a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (i j : ZMod s)
    (h : (run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
      (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 i j ≠ 0) :
    CycRel s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)
      (12*PhaseCellBand.width p u) i j := by
  have hks : ∀ k ∈ (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList,
      Interior s t (PhaseCellBand.width p u) k := by
    intro k hk
    have hi := mem_toList.mp hk
    rcases mem_union.mp hi with hi | hi
    all_goals exact (mem_interiorSet _ k).mp (mem_filter.mp hi).1
  rcases boundary_support s t hst p u _ hks (cyclicPrincipalVertices s a n) i j h with ⟨m,hm,hij⟩ | hc
  · exact cycRel_mono s _ (by omega) (band_cycRel s _ _ i j m hm hij)
  · exact cyclicPrincipal_cell_cycRel hst _ a n ha hn i j hc

theorem cyclicPrincipal_schur_foldBRel (hst : s < t) (p u a n : ℕ) (ha : a < s) (hn : n ≤ s)
    {i j : ZMod s}
    (hi : i ∈ cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)
    (hj : j ∈ cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)
    (h : (run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
      (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 i j ≠ 0) :
    FoldBRel s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)
      (24*PhaseCellBand.width p u+1) i j := by
  have hh := cycRel_foldBRel s _ _ hi hj (cyclicPrincipal_schur_cycRel hst p u a n ha hn i j h)
  convert hh using 1
  congr 1
  omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
