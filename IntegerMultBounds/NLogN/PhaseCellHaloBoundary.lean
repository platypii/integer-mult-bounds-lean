module

public import IntegerMultBounds.NLogN.PhaseCellHaloInterval

/-! The halo boundary is computed from the selected interior. Artificial
endpoints add at most two guard bands; original ambient cuts remain charged. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloVertices (s a b : ℕ) [NeZero s] : Finset (ZMod s) :=
  Finset.univ.filter (fun j => a ≤ j.val ∧ j.val < b)

def haloBoundary (s t band a b : ℕ) [NeZero s] : Finset (ZMod s) :=
  haloVertices s a b \ haloInterior s t band a b

theorem mem_haloVertices {s : ℕ} [NeZero s] (a b : ℕ) (j : ZMod s) :
    j ∈ haloVertices s a b ↔ a ≤ j.val ∧ j.val < b := by simp [haloVertices]

theorem haloVertices_card_le (s a b : ℕ) [NeZero s] : (haloVertices s a b).card ≤ b-a := by
  have hsub : (haloVertices s a b).image ZMod.val ⊆ Finset.Ico a b := by
    intro n hn
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Ico.mpr ((mem_haloVertices a b j).mp hj)
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (ZMod.val_injective s),Nat.card_Ico] at hh
  exact hh

theorem haloInterior_subset (s t band a b : ℕ) [NeZero s] :
    haloInterior s t band a b ⊆ haloVertices s a b := by
  intro j hj
  obtain ⟨_,ha,hb⟩ := Finset.mem_filter.mp hj
  apply (mem_haloVertices a b j).mpr
  exact ⟨by omega,hb.trans_le (Nat.sub_le _ _)⟩

theorem haloInterior_disjoint_boundary (s t band a b : ℕ) [NeZero s] :
    Disjoint (haloInterior s t band a b) (haloBoundary s t band a b) := by
  apply Finset.disjoint_left.mpr
  intro j hj hB
  exact (Finset.mem_sdiff.mp hB).2 hj

theorem haloInterior_union_boundary (s t band a b : ℕ) [NeZero s] :
    haloInterior s t band a b ∪ haloBoundary s t band a b = haloVertices s a b := by
  ext j
  constructor
  · intro hj
    rcases Finset.mem_union.mp hj with hi | hB
    · exact haloInterior_subset s t band a b hi
    · exact (Finset.mem_sdiff.mp hB).1
  · intro hj
    by_cases hi : j ∈ haloInterior s t band a b
    · exact Finset.mem_union.mpr (Or.inl hi)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hj,hi⟩))

theorem haloBoundary_cover (s t band a b : ℕ) [NeZero s] :
    haloBoundary s t band a b ⊆
      ((haloVertices s a b \ interiorSet s t band) ∪ haloVertices s a (a+band)) ∪
        haloVertices s (b-band) b := by
  intro j hj
  obtain ⟨hh,hnot⟩ := Finset.mem_sdiff.mp hj
  obtain ⟨ha,hb⟩ := (mem_haloVertices a b j).mp hh
  by_cases hI : j ∈ interiorSet s t band
  · have hc : ¬ (a+band ≤ j.val ∧ j.val < b-band) := by
      intro hc
      exact hnot (Finset.mem_filter.mpr ⟨hI,hc⟩)
    by_cases hleft : j.val < a+band
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr ((mem_haloVertices a (a+band) j).mpr ⟨ha,hleft⟩))))
    · exact Finset.mem_union.mpr (Or.inr ((mem_haloVertices (b-band) b j).mpr ⟨by omega,hb⟩))
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hh,hI⟩))))

/-- Original boundary vertices inside the halo plus the two artificial guard bands. -/
theorem haloBoundary_card_le (s t band a b : ℕ) [NeZero s] :
    (haloBoundary s t band a b).card ≤ (haloVertices s a b \ interiorSet s t band).card+2*band := by
  have hleft := haloVertices_card_le s a (a+band)
  have hright := haloVertices_card_le s (b-band) b
  calc
    _ ≤ (((haloVertices s a b \ interiorSet s t band) ∪ haloVertices s a (a+band)) ∪
        haloVertices s (b-band) b).card := Finset.card_le_card (haloBoundary_cover s t band a b)
    _ ≤ ((haloVertices s a b \ interiorSet s t band).card+(haloVertices s a (a+band)).card)+
        (haloVertices s (b-band) b).card := (Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ _ := by omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
