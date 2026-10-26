module

public import IntegerMultBounds.NLogN.PhaseCellBoundaryFold
public import IntegerMultBounds.NLogN.PhaseCellHaloBoundary

/-! Local Schur support and folded fill, including the two artificial halo cuts. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open Finset PhaseCellMatrix SchurDominance

variable {s t : ℕ} [NeZero s]

/-- In a single ambient phase cell, the local boundary adds at most two guard bands. -/
theorem halo_same_cell_interval (hst : s < t) (w a b : ℕ) (i j : ZMod s)
    (hc : cell s t i = cell s t j) :
    ((haloBoundary s t w a b).filter fun k => i.val ≤ k.val ∧ k.val < j.val).card ≤ 6*w := by
  let F := (univ\interiorSet s t w).filter fun k => i.val ≤ k.val ∧ k.val < j.val
  have hF : F.card ≤ 4*w := same_cell_interval s t hst w (interiorSet s t w)
    (fun k => mem_interiorSet w k) i j hc
  have hsub : (haloBoundary s t w a b).filter (fun k => i.val ≤ k.val ∧ k.val < j.val) ⊆
      (F ∪ haloVertices s a (a+w)) ∪ haloVertices s (b-w) b := by
    intro k hk
    obtain ⟨hB,hij⟩ := mem_filter.mp hk
    rcases mem_union.mp (haloBoundary_cover s t w a b hB) with h | hright
    · rcases mem_union.mp h with hglobal | hleft
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl
          (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hglobal).2⟩,hij⟩))))
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr hleft)))
    · exact mem_union.mpr (Or.inr hright)
  have hleft := haloVertices_card_le s a (a+w)
  have hright := haloVertices_card_le s (b-w) b
  have hcard := card_le_card hsub
  have h₁ := card_union_le F (haloVertices s a (a+w))
  have h₂ := card_union_le (F ∪ haloVertices s a (a+w)) (haloVertices s (b-w) b)
  omega

theorem halo_cell_cycRel (hst : s < t) (w a b : ℕ) (i j : ZMod s)
    (hc : cell s t i = cell s t j) :
    CycRel s (haloBoundary s t w a b) (6*w) i j := by
  unfold CycRel
  left
  rcases le_total i.val j.val with hle | hle
  · have e := bRank_sub (B := haloBoundary s t w a b) hle
    have h := halo_same_cell_interval hst w a b i j hc
    omega
  · have e := bRank_sub (B := haloBoundary s t w a b) hle
    have h := halo_same_cell_interval hst w a b j i hc.symm
    omega

/-- Interior elimination retains ambient phase and periodic support. Local cuts
only enlarge the boundary rank band by their explicitly charged guard bands. -/
theorem halo_schur_cycRel (hst : s < t) (p u a b : ℕ) (i j : ZMod s)
    (h : (run (realMatrix s t p u) (haloVertices s a b)
      (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 i j ≠ 0) :
    CycRel s (haloBoundary s t (PhaseCellBand.width p u) a b)
      (6*PhaseCellBand.width p u) i j := by
  have hks : ∀ k ∈ (haloInterior s t (PhaseCellBand.width p u) a b).toList,
      Interior s t (PhaseCellBand.width p u) k := by
    intro k hk
    exact (mem_interiorSet _ k).mp (mem_filter.mp (mem_toList.mp hk)).1
  rcases boundary_support s t hst p u _ hks (haloVertices s a b) i j h with ⟨m,hm,hij⟩ | hc
  · exact cycRel_mono s _ (by omega) (band_cycRel s _ _ i j m hm hij)
  · exact halo_cell_cycRel hst _ a b i j hc

/-- A local Schur matrix has folded half-bandwidth `12w+1`, including artificial cuts. -/
theorem halo_schur_foldBRel (hst : s < t) (p u a b : ℕ) {i j : ZMod s}
    (hi : i ∈ haloBoundary s t (PhaseCellBand.width p u) a b)
    (hj : j ∈ haloBoundary s t (PhaseCellBand.width p u) a b)
    (h : (run (realMatrix s t p u) (haloVertices s a b)
      (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 i j ≠ 0) :
    FoldBRel s (haloBoundary s t (PhaseCellBand.width p u) a b)
      (12*PhaseCellBand.width p u+1) i j := by
  have hh := cycRel_foldBRel s _ _ hi hj (halo_schur_cycRel hst p u a b i j h)
  convert hh using 1
  congr 1
  omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
