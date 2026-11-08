module

public import IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership

/-! Nonwrapping guarded windows for the manuscript's floor-owned source rows.
Their lengths vary with k; only the uniform upper bound uses the target width. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership

theorem owned_window_span (s t L k radius : ℕ) (ha : radius ≤ cut s t L k) :
    (cut s t L (k+1)+radius)-(cut s t L k-radius) = rows s t L k+2*radius := by
  have hm := cut_mono s t L (show k ≤ k+1 by omega)
  unfold rows
  omega

theorem owned_window_geometry (s t L k radius : ℕ) (ht : 0 < t) (hnear : t ≤ 2*s) (hL : 2 ≤ L)
    (ha : radius ≤ cut s t L k) (hb : cut s t L (k+1)+radius ≤ s) :
    (cut s t L k-radius)+radius = cut s t L k ∧
      cut s t L k-radius ≤ cut s t L (k+1)+radius ∧
      cut s t L k-radius < s := by
  have hp := rows_pos s t L k ht hnear hL
  have hm := cut_mono s t L (show k ≤ k+1 by omega)
  unfold rows at hp
  omega

theorem owned_window_separated (s t L k radius band : ℕ) (ht : 0 < t) (hst : s ≤ t)
    (ha : radius ≤ cut s t L k) (hfit : L+2*radius+band ≤ s) :
    (cut s t L (k+1)+radius)-(cut s t L k-radius)+band ≤ s := by
  rw [owned_window_span s t L k radius ha]
  have hr := rows_le s t L k ht hst
  omega

end IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
