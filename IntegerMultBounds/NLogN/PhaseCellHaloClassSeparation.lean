module

public import IntegerMultBounds.NLogN.PhaseCellHaloGroups

/-! Distinct positive clipped length classes have disjoint ambient intervals. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloClass_intervals_separated {s t band a b L K p q : ℕ} (hLK : L ≠ K)
    (hp : p ∈ haloLengthGroup s t band a b L) (hq : q ∈ haloLengthGroup s t band a b K) :
    haloStart s t band a p+L ≤ haloStart s t band a q ∨
      haloStart s t band a q+K ≤ haloStart s t band a p := by
  obtain ⟨_,hL,hlen⟩ := (mem_haloLengthGroup s t band a b L p).mp hp
  obtain ⟨_,hK,hken⟩ := (mem_haloLengthGroup s t band a b K q).mp hq
  have hpq : p ≠ q := by intro he; subst q; exact hLK (hlen.symm.trans hken)
  dsimp only [haloLength] at hlen hken
  rcases lt_or_gt_of_ne hpq with hh | hh
  · have hsep := haloCells_ordered s t band a b p q hh
    left
    omega
  · have hsep := haloCells_ordered s t band a b q p hh
    right
    omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
