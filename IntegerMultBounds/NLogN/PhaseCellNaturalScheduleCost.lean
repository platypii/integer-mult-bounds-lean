module

public import IntegerMultBounds.NLogN.PhaseCellPositiveLengthKeys

/-! The natural schedule pays one setup per distinct positive length, one
padded operation per cell, and coordinate work only on the actual interior. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Every positive natural interval occurs in exactly one selected class. -/
theorem naturalPositiveLengthKeys_cell_count {s t : ℕ} (hst : s < t) (band : ℕ) :
    ((naturalPositiveLengthKeys s t band).map (fun L => (naturalLengthGroup s t band L).length)).sum ≤ t-s+1 := by
  let phases := (Finset.range (t-s+1)).filter (fun phase => 0 < naturalLength s t band phase)
  have hmaps : ∀ phase ∈ phases,
      naturalLength s t band phase ∈ (naturalPositiveLengthKeys s t band).toFinset := by
    intro phase hp
    obtain ⟨hr,hpos⟩ := Finset.mem_filter.mp hp
    apply List.mem_toFinset.mpr
    apply naturalLengthKeys_mem_positive
    apply (mem_naturalLengthKeys hst band _).mpr
    exact List.length_pos_of_mem ((mem_naturalLengthGroup s t band _ phase).mpr
      ⟨by have hh := Finset.mem_range.mp hr; omega,hpos,rfl⟩)
  have hfiber (L : ℕ) (hL : L ∈ (naturalPositiveLengthKeys s t band).toFinset) :
      (phases.filter (fun phase => naturalLength s t band phase = L)).card =
        (naturalLengthGroup s t band L).length := by
    have hpos := ((mem_naturalPositiveLengthKeys s t band L).mp (List.mem_toFinset.mp hL)).2
    have he : phases.filter (fun phase => naturalLength s t band phase = L) =
        (naturalLengthGroup s t band L).toFinset := by
      ext phase
      simp [phases,naturalLengthGroup_toFinset,hpos]
      omega
    rw [he]
    exact List.toFinset_card_of_nodup (naturalLengthGroup_nodup s t band L)
  rw [← List.sum_toFinset _ (naturalPositiveLengthKeys_nodup s t band)]
  calc
    _ = ∑ L ∈ (naturalPositiveLengthKeys s t band).toFinset,
        (phases.filter (fun phase => naturalLength s t band phase = L)).card := by
      apply Finset.sum_congr rfl
      intro L hL
      exact (hfiber L hL).symm
    _ = phases.card := by
      simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] using
        Finset.sum_fiberwise_of_maps_to' hmaps (fun _ : ℕ => (1 : ℕ))
    _ ≤ t-s+1 := by
      simpa using Finset.card_le_card (Finset.filter_subset (fun phase => 0 < naturalLength s t band phase)
        (Finset.range (t-s+1)))

/-- A list ledger with setup, coordinate and cell charges separates exactly. -/
theorem sum_class_cost (keys : List ℕ) (count setup : ℕ → ℕ) (coordinateCost cellCost : ℕ) :
    (keys.map (fun L => setup L+(count L*L)*coordinateCost+count L*cellCost)).sum =
      (keys.map setup).sum + (keys.map (fun L => count L*L)).sum*coordinateCost +
        (keys.map count).sum*cellCost := by
  induction keys with
  | nil => simp
  | cons L keys ih => simp only [List.map_cons,List.sum_cons,ih]; ring

/-- The four candidate setups suffice, with no class-count factor on repeated work. -/
theorem naturalPositiveLengthKeys_cost_le {s t : ℕ} [NeZero s] (hst : s < t) (band : ℕ)
    (setup : ℕ → ℕ) (coordinateCost cellCost : ℕ) :
    ((naturalPositiveLengthKeys s t band).map (fun L => setup L+
      ((naturalLengthGroup s t band L).length*L)*coordinateCost+
      (naturalLengthGroup s t band L).length*cellCost)).sum ≤
      ((naturalLengthCandidates s t band).map setup).sum+
        (interiorSet s t band).card*coordinateCost+(t-s+1)*cellCost := by
  rw [sum_class_cost,naturalPositiveLengthKeys_volume hst band]
  have hsub : (naturalPositiveLengthKeys s t band).Sublist (naturalLengthCandidates s t band) :=
    List.filter_sublist.trans (List.dedup_sublist _)
  have hs := (hsub.map setup).sum_le_sum (fun _ _ => Nat.zero_le _)
  have hc := Nat.mul_le_mul_right cellCost (naturalPositiveLengthKeys_cell_count hst band)
  omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
