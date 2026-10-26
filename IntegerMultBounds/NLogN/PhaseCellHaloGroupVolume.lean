module

public import IntegerMultBounds.NLogN.PhaseCellHaloVolume
public import IntegerMultBounds.NLogN.PhaseCellHaloGroups

/-! Selecting one equal-length class cannot increase the total interior volume. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open scoped BigOperators

theorem haloGroup_volume_le {s t : ℕ} [NeZero s] (hst : s < t) (band a b L : ℕ) :
    (haloLengthGroup s t band a b L).length*L ≤ s := by
  let f := haloLength s t band a b
  let selected := fun phase => decide (0 < L ∧ f phase = L)
  have hfilter (xs : List ℕ) : ((xs.filter selected).map f).sum ≤ (xs.map f).sum := by
    induction xs with
    | nil => simp
    | cons phase xs ih =>
      by_cases hh : selected phase = true <;> simp [hh] <;> omega
  have hvalues : (haloLengthGroup s t band a b L).map f =
      List.replicate (haloLengthGroup s t band a b L).length L := by
    apply List.map_eq_replicate_iff.mpr
    intro phase hp
    exact ((mem_haloLengthGroup s t band a b L phase).mp hp).2.2
  have hsum (n : ℕ) : ((List.range n).map f).sum = ∑ phase ∈ Finset.range n, f phase := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  have hh := hfilter (List.range (t-s+1))
  change ((haloLengthGroup s t band a b L).map f).sum ≤ _ at hh
  rw [hvalues, List.sum_replicate, smul_eq_mul, hsum] at hh
  have hvolume : ∑ phase ∈ Finset.range (t-s+1), f phase ≤ s := by
    rw [haloIntervals_volume hst band a b]
    exact (Finset.card_le_univ _).trans_eq (by simp)
  exact hh.trans hvolume

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
