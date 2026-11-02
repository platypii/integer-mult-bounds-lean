module

public import IntegerMultBounds.NLogN.PhaseCellCoreGather
import Mathlib.Tactic.Linarith

/-! Fitting core groups have linear total gathered volume. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

theorem coreGather_volume_le_six (s width radius L : ℕ)
    (hwidth : width ≤ s) (hradius : radius ≤ width) :
    (coreGatherIndices s width radius L).length * L ≤ 6*s := by
  by_cases hempty : coreGatherIndices s width radius L = []
  · simp [hempty]
  obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ hempty
  have hspec := (coreGatherIndices_spec s width radius L k hk).2.2
  have hlen : L ≤ 3*width := by
    have hc : coreLength s width k ≤ width := min_le_left _ _
    omega
  have hcount : (coreGatherIndices s width radius L).length * width ≤ s+width := by
    have h := Nat.mul_le_mul_right width
      (List.length_filter_le (fun k => decide
        (radius ≤ coreStart width k ∧ coreStart width k+coreLength s width k+radius ≤ s ∧
          coreLength s width k+2*radius = L)) (coreIndices s width))
    have hd := Nat.div_mul_le_self (s+width-1) width
    simp only [coreGatherIndices, coreIndices, List.length_range] at h ⊢
    omega
  have hvolume := Nat.mul_le_mul_left (coreGatherIndices s width radius L).length hlen
  nlinarith only [hvolume, hcount, hwidth]

end IntegerMultBounds.NLogN.PhaseCellMatrix
