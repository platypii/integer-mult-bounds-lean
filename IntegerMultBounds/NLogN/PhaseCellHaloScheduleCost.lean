module

public import IntegerMultBounds.NLogN.PhaseCellHaloGroups
public import IntegerMultBounds.NLogN.PhaseCellHaloVolume
public import IntegerMultBounds.NLogN.PhaseCellNaturalScheduleCost

/-! Halo keys partition the positive clipped phases. Coordinate work counts
exactly the clipped interior; shared setup is charged to at most six candidates. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open scoped BigOperators

theorem haloLengthGroup_nodup (s t band a b L : ℕ) :
    (haloLengthGroup s t band a b L).Nodup := (List.nodup_range (n := t-s+1)).filter _

theorem haloLengthGroup_fiber (s t band a b L : ℕ) (hL : 0 < L) :
    (((Finset.range (t-s+1)).filter (fun phase => 0 < haloLength s t band a b phase)).filter
      (fun phase => haloLength s t band a b phase = L)).card =
        (haloLengthGroup s t band a b L).length := by
  have he : ((Finset.range (t-s+1)).filter (fun phase => 0 < haloLength s t band a b phase)).filter
      (fun phase => haloLength s t band a b phase = L) = (haloLengthGroup s t band a b L).toFinset := by
    ext phase
    simp [haloLengthGroup]
    omega
  rw [he]
  exact List.toFinset_card_of_nodup (haloLengthGroup_nodup s t band a b L)

theorem haloLengthKeys_cell_count {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ) :
    ((haloLengthKeys s t band a b).map (fun L => (haloLengthGroup s t band a b L).length)).sum ≤ t-s+1 := by
  let phases := (Finset.range (t-s+1)).filter (fun phase => 0 < haloLength s t band a b phase)
  have hmaps : ∀ phase ∈ phases, haloLength s t band a b phase ∈ (haloLengthKeys s t band a b).toFinset := by
    intro phase hp
    obtain ⟨hr,hpos⟩ := Finset.mem_filter.mp hp
    exact List.mem_toFinset.mpr (haloLengthKeys_cover hst band a b phase
      ((mem_haloCellPhases s t band a b phase).mpr ⟨by have hh := Finset.mem_range.mp hr; omega,hpos⟩))
  rw [← List.sum_toFinset _ (haloLengthKeys_nodup s t band a b)]
  calc
    _ = ∑ L ∈ (haloLengthKeys s t band a b).toFinset,
        (phases.filter (fun phase => haloLength s t band a b phase = L)).card := by
      apply Finset.sum_congr rfl
      intro L hL
      exact (haloLengthGroup_fiber s t band a b L
        (of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hL)).2)).symm
    _ = phases.card := by
      simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] using
        Finset.sum_fiberwise_of_maps_to' hmaps (fun _ : ℕ => (1 : ℕ))
    _ ≤ t-s+1 := by simpa using Finset.card_le_card (Finset.filter_subset _ (Finset.range (t-s+1)))

theorem sum_fiber_card_mul {α : Type*} [DecidableEq α] (phases : Finset α) (keys : Finset ℕ)
    (f : α → ℕ) (hmaps : ∀ phase ∈ phases, f phase ∈ keys) :
    ∑ L ∈ keys, (phases.filter (fun phase => f phase = L)).card*L = ∑ phase ∈ phases, f phase := by
  simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] using
    Finset.sum_fiberwise_of_maps_to' hmaps (fun L : ℕ => L)

theorem haloLengthKeys_volume {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ) :
    ((haloLengthKeys s t band a b).map (fun L => (haloLengthGroup s t band a b L).length*L)).sum =
      (haloInterior s t band a b).card := by
  let f := haloLength s t band a b
  let phases := (Finset.range (t-s+1)).filter (fun phase => 0 < f phase)
  have hmaps : ∀ phase ∈ phases, f phase ∈ (haloLengthKeys s t band a b).toFinset := by
    intro phase hp
    obtain ⟨hr,hpos⟩ := Finset.mem_filter.mp hp
    exact List.mem_toFinset.mpr (haloLengthKeys_cover hst band a b phase
      ((mem_haloCellPhases s t band a b phase).mpr ⟨by have hh := Finset.mem_range.mp hr; omega,hpos⟩))
  have hcounts : (∑ L ∈ (haloLengthKeys s t band a b).toFinset,
      (haloLengthGroup s t band a b L).length*L) =
      ∑ L ∈ (haloLengthKeys s t band a b).toFinset, (phases.filter (fun phase => f phase = L)).card*L := by
    apply Finset.sum_congr rfl
    intro L hL
    exact congrArg (fun n => n*L) (haloLengthGroup_fiber s t band a b L
      (of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hL)).2)).symm
  rw [← List.sum_toFinset _ (haloLengthKeys_nodup s t band a b),hcounts,
    sum_fiber_card_mul phases (haloLengthKeys s t band a b).toFinset f hmaps]
  calc
    _ = ∑ phase ∈ Finset.range (t-s+1), f phase := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro phase hr hn
      have hp : ¬ 0 < f phase := fun hp => hn (Finset.mem_filter.mpr ⟨hr,hp⟩)
      omega
    _ = _ := haloIntervals_volume hst band a b

theorem haloLengthKeys_cost_le {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ)
    (setup : ℕ → ℕ) (coordinateCost cellCost : ℕ) :
    ((haloLengthKeys s t band a b).map (fun L => setup L+
      ((haloLengthGroup s t band a b L).length*L)*coordinateCost+
      (haloLengthGroup s t band a b L).length*cellCost)).sum ≤
      ((haloLengthCandidates s t band a b).map setup).sum+
        (haloInterior s t band a b).card*coordinateCost+(t-s+1)*cellCost := by
  rw [sum_class_cost,haloLengthKeys_volume hst band a b]
  have hsub : (haloLengthKeys s t band a b).Sublist (haloLengthCandidates s t band a b) :=
    List.filter_sublist.trans (List.dedup_sublist _)
  have hs := (hsub.map setup).sum_le_sum (fun _ _ => Nat.zero_le _)
  have hc := Nat.mul_le_mul_right cellCost (haloLengthKeys_cell_count hst band a b)
  omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
