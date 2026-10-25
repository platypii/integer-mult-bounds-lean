module

public import IntegerMultBounds.NLogN.PhaseCellNaturalVolume

/-! Selecting one equal-length class cannot increase the total interior volume. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open scoped BigOperators

theorem naturalGroup_volume_le {s t : ℕ} [NeZero s] (hst : s < t) (band L : ℕ) :
    (naturalLengthGroup s t band L).length*L ≤ s := by
  let f := naturalLength s t band
  let selected := fun phase => decide (0 < L ∧ f phase = L)
  have hfilter (xs : List ℕ) : ((xs.filter selected).map f).sum ≤ (xs.map f).sum := by
    induction xs with
    | nil => simp
    | cons phase xs ih =>
      by_cases hh : selected phase = true <;> simp [hh] <;> omega
  have hvalues : (naturalLengthGroup s t band L).map f =
      List.replicate (naturalLengthGroup s t band L).length L := by
    apply List.map_eq_replicate_iff.mpr
    intro phase hp
    exact ((mem_naturalLengthGroup s t band L phase).mp hp).2.2
  have hsum (n : ℕ) : ((List.range n).map f).sum = ∑ phase ∈ Finset.range n, f phase := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  have hh := hfilter (List.range (t-s+1))
  change ((naturalLengthGroup s t band L).map f).sum ≤ _ at hh
  rw [hvalues, List.sum_replicate, smul_eq_mul, hsum] at hh
  exact hh.trans (naturalIntervals_volume_le hst band)

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
