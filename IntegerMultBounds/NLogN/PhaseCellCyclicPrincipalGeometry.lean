module

public import IntegerMultBounds.NLogN.PhaseCellHaloBoundaryCount
public import IntegerMultBounds.NLogN.PhaseCellHaloLayers
public import IntegerMultBounds.NLogN.SchurIdentify

/-! A cyclic principal window uses two physical intervals and one coupled Schur system. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open Finset PhaseCellMatrix SchurDominance
variable {s : ℕ} [NeZero s]

def cyclicPrincipalVertices (s a n : ℕ) [NeZero s] : Finset (ZMod s) :=
  haloVertices s a (a+min n (s-a)) ∪ haloVertices s 0 (n-min n (s-a))

def cyclicPrincipalInterior (s t band a n : ℕ) [NeZero s] : Finset (ZMod s) :=
  haloInterior s t band a (a+min n (s-a)) ∪ haloInterior s t band 0 (n-min n (s-a))

def cyclicPrincipalBoundary (s t band a n : ℕ) [NeZero s] : Finset (ZMod s) :=
  cyclicPrincipalVertices s a n \ cyclicPrincipalInterior s t band a n

theorem cyclicPrincipalVertices_eq (a n : ℕ) (ha : a < s) :
    cyclicPrincipalVertices s a n = cyclicHaloLayer (a : ZMod s) 0 n 0 0 := by
  ext i
  have hi := ZMod.val_lt i
  simp only [cyclicPrincipalVertices,mem_union,mem_haloVertices,mem_cyclicHaloLayer,haloLayer,
    zero_mul,add_zero,Nat.sub_zero]
  by_cases hai : a ≤ i.val
  · rw [ZMod.val_sub (by simpa only [ZMod.val_natCast_of_lt ha] using hai),ZMod.val_natCast_of_lt ha]
    omega
  · have he : i-(a : ZMod s) = ((i.val+s-a : ℕ) : ZMod s) := by
      rw [Nat.cast_sub (by omega : a ≤ i.val+s),Nat.cast_add,ZMod.natCast_self,ZMod.natCast_zmod_val]
      simp
    rw [he,ZMod.val_natCast_of_lt (by omega : i.val+s-a < s)]
    omega

theorem cyclicPrincipalPieces_disjoint (a n : ℕ) (ha : a < s) (hn : n ≤ s) :
    Disjoint (haloVertices s a (a+min n (s-a))) (haloVertices s 0 (n-min n (s-a))) := by
  apply disjoint_left.mpr
  intro i hi hj
  obtain ⟨hl,hr⟩ := (mem_haloVertices _ _ i).mp hi
  obtain ⟨hl',hr'⟩ := (mem_haloVertices _ _ i).mp hj
  omega

theorem cyclicPrincipalInterior_subset (t band a n : ℕ) :
    cyclicPrincipalInterior s t band a n ⊆ cyclicPrincipalVertices s a n :=
  union_subset_union (haloInterior_subset s t band a _) (haloInterior_subset s t band 0 _)

theorem cyclicPrincipalBoundary_eq (t band a n : ℕ) (ha : a < s) (hn : n ≤ s) :
    cyclicPrincipalBoundary s t band a n =
      haloBoundary s t band a (a+min n (s-a)) ∪ haloBoundary s t band 0 (n-min n (s-a)) := by
  have hd := cyclicPrincipalPieces_disjoint a n ha hn
  have hI := haloInterior_subset s t band a (a+min n (s-a))
  have hJ := haloInterior_subset s t band 0 (n-min n (s-a))
  ext i
  simp only [cyclicPrincipalBoundary,cyclicPrincipalVertices,cyclicPrincipalInterior,
    haloBoundary,mem_sdiff,mem_union]
  constructor
  · rintro ⟨hi,hnot⟩
    rcases hi with hi | hi
    · exact Or.inl ⟨hi,fun hh => hnot (Or.inl hh)⟩
    · exact Or.inr ⟨hi,fun hh => hnot (Or.inr hh)⟩
  · rintro (⟨hi,hnot⟩ | ⟨hi,hnot⟩)
    · refine ⟨Or.inl hi,?_⟩
      rintro (hh | hh)
      · exact hnot hh
      · exact disjoint_left.mp hd hi (hJ hh)
    · refine ⟨Or.inr hi,?_⟩
      rintro (hh | hh)
      · exact disjoint_left.mp hd (hI hh) hi
      · exact hnot hh

theorem cyclicPrincipalBoundary_card (t band a n : ℕ) (hst : s < t) (ha : a < s) (hn : n ≤ s) :
    (cyclicPrincipalBoundary s t band a n).card ≤ min n (4*band*(t-s+2)) := by
  apply Nat.le_min.mpr
  constructor
  · have hb := card_le_card (sdiff_subset : cyclicPrincipalBoundary s t band a n ⊆ cyclicPrincipalVertices s a n)
    have hu := card_union_le (haloVertices s a (a+min n (s-a))) (haloVertices s 0 (n-min n (s-a)))
    have h₁ := haloVertices_card_le s a (a+min n (s-a))
    have h₂ := haloVertices_card_le s 0 (n-min n (s-a))
    change (cyclicPrincipalBoundary s t band a n).card ≤ n
    dsimp only [cyclicPrincipalBoundary,cyclicPrincipalVertices] at hb ⊢
    omega
  · rw [cyclicPrincipalBoundary_eq t band a n ha hn]
    have hu := card_union_le (haloBoundary s t band a (a+min n (s-a)))
      (haloBoundary s t band 0 (n-min n (s-a)))
    have h₁ := (haloBoundary_card_bound hst band a (a+min n (s-a))).trans (Nat.min_le_right _ _)
    have h₂ := (haloBoundary_card_bound hst band 0 (n-min n (s-a))).trans (Nat.min_le_right _ _)
    nlinarith only [hu,h₁,h₂]

/-- Eliminate both guarded interiors against one active matrix, retaining all seam couplings. -/
theorem cyclicPrincipal_schur_gap (t p u a n : ℕ) (mu : ℝ) (hmu : 0 < mu)
    (hdom : DominatesOn (realMatrix s t p u) univ mu) :
    DominatesOn
      (run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
        (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1
      (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n) mu := by
  have hg := run_gap (realMatrix s t p u) (cyclicPrincipalVertices s a n) mu hmu
    (dominates_mono _ univ _ _ (subset_univ _) hdom)
    (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList
  simpa only [run_set,toList_toFinset,cyclicPrincipalBoundary] using hg

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
