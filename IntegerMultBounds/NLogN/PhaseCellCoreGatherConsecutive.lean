module

public import IntegerMultBounds.NLogN.PhaseCellCoreGatherEligibility
import Mathlib.Data.List.Sort

/-! The selected full-width fitting class is a single consecutive interval.
Its publication advances therefore need no origin-table interpretation. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

theorem fullCoreGather_consecutive (s width radius : ℕ) (hw : 0 < width)
    (hr : 0 < radius) (hrw : radius ≤ width) (hroom : 3*width ≤ s) :
    coreGatherIndices s width radius (width+2*radius) =
      List.range' 1 ((s-radius)/width-1) := by
  have hquot : 2 ≤ (s-radius)/width := (Nat.le_div_iff_mul_le hw).mpr (by omega)
  apply (List.pairwise_lt_range.filter _).eq_of_mem_iff (List.pairwise_lt_range' 1 (by decide))
  intro k
  rw [List.mem_range'_1]
  constructor
  · intro hk
    obtain ⟨hleft,hright,hlen⟩ := coreGatherIndices_spec s width radius _ k hk
    have hfull : coreLength s width k = width := by omega
    rw [hfull] at hright
    change radius ≤ k*width at hleft
    change k*width+width+radius ≤ s at hright
    have hmul : (k+1)*width ≤ s-radius := by rw [Nat.add_mul,Nat.one_mul]; omega
    have hdiv := (Nat.le_div_iff_mul_le hw).mpr hmul
    have hkpos : 1 ≤ k := by
      by_cases hk0 : k = 0
      · subst k; simp only [Nat.zero_mul] at hleft; omega
      · omega
    omega
  · intro hk
    have hkpos : 1 ≤ k := hk.1
    have hkquot : k+1 ≤ (s-radius)/width := by omega
    have hmul := Nat.mul_le_mul_right width hkquot
    have hdiv := Nat.div_mul_le_self (s-radius) width
    have hfit : k*width+width+radius ≤ s := by
      rw [Nat.add_mul,Nat.one_mul] at hmul
      omega
    have hleft : radius ≤ k*width := by
      have hh : width ≤ k*width := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right width hkpos
      exact hrw.trans hh
    have hfull : coreLength s width k = width := by
      unfold coreLength coreStart
      exact Nat.min_eq_left (by omega)
    have hqle : (s-radius)/width ≤ (s+width-1)/width := Nat.div_le_div_right (by omega)
    have hindex : k ∈ coreIndices s width := List.mem_range.mpr (by omega)
    simp only [coreGatherIndices,List.mem_filter,decide_eq_true_eq]
    exact ⟨hindex,hleft,by simpa only [coreStart,hfull] using hfit,by rw [hfull]⟩

end IntegerMultBounds.NLogN.PhaseCellMatrix
