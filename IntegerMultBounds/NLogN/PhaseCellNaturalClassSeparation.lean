module

public import IntegerMultBounds.NLogN.PhaseCellNaturalGroups

/-! Different length classes contain different phases. Their natural intervals
are separated in the original ambient order, including their full row widths. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem naturalStop_le_start {s t band p q : ℕ} (hpq : p < q) :
    naturalStop s t band p ≤ naturalStart s t band q := by
  have hmono : phaseLower s (t-s) (p+1) ≤ phaseLower s (t-s) q := by
    unfold phaseLower
    apply Nat.div_le_div_right
    exact Nat.sub_le_sub_right (Nat.sub_le_sub_right
      (Nat.add_le_add_right (Nat.mul_le_mul_left (2*s) (by omega : p+1 ≤ q)) (2*(t-s))) 1) s
  have hh : naturalStop s t band p ≤ phaseLower s (t-s) (p+1) := by
    unfold naturalStop
    exact (Nat.sub_le _ _).trans (min_le_right _ _)
  unfold naturalStart
  omega

theorem naturalClass_intervals_separated {s t band L K p q : ℕ} (hLK : L ≠ K)
    (hp : p ∈ naturalLengthGroup s t band L) (hq : q ∈ naturalLengthGroup s t band K) :
    naturalStart s t band p+L ≤ naturalStart s t band q ∨
      naturalStart s t band q+K ≤ naturalStart s t band p := by
  obtain ⟨_,hL,hlen⟩ := (mem_naturalLengthGroup s t band L p).mp hp
  obtain ⟨_,hK,hken⟩ := (mem_naturalLengthGroup s t band K q).mp hq
  have hpq : p ≠ q := by intro he; subst q; exact hLK (hlen.symm.trans hken)
  have hpend : naturalStart s t band p+L = naturalStop s t band p := by
    have hh := (naturalLength_pos_iff s t band p).mp (by omega : 0 < naturalLength s t band p)
    unfold naturalLength at hlen
    omega
  have hqend : naturalStart s t band q+K = naturalStop s t band q := by
    have hh := (naturalLength_pos_iff s t band q).mp (by omega : 0 < naturalLength s t band q)
    unfold naturalLength at hken
    omega
  rcases lt_or_gt_of_ne hpq with hh | hh
  · exact Or.inl (hpend.trans_le (naturalStop_le_start hh))
  · exact Or.inr (hqend.trans_le (naturalStop_le_start hh))

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
