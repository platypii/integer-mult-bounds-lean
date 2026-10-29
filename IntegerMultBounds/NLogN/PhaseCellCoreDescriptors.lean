module

public import IntegerMultBounds.NLogN.PhaseCellCoreWindows

/-! # Interval endpoints for generated S4 windows

These computable endpoints use the existing S3 interval descriptor format.
Their principal sets are exactly the halos used in the locality proof.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open Finset PhaseCellDiscreteGeometry

/-- The same fit decision selects both endpoints atomically. -/
def coreHaloEndpoints (s width k band n : ℕ) : ℕ × ℕ :=
  if n*band ≤ coreStart width k ∧
      coreStart width k+coreLength s width k+n*band ≤ s then
    (coreStart width k-n*band, coreStart width k+coreLength s width k+n*band)
  else (0,s)

theorem coreHaloEndpoints_bounds (s width k band n : ℕ) :
    (coreHaloEndpoints s width k band n).1 ≤ (coreHaloEndpoints s width k band n).2 ∧
      (coreHaloEndpoints s width k band n).2 ≤ s := by
  unfold coreHaloEndpoints
  split
  · rename_i h
    dsimp only
    constructor <;> omega
  · simp

theorem coreHaloEndpoints_set {s : ℕ} [NeZero s] (width k band n : ℕ) :
    haloVertices s (coreHaloEndpoints s width k band n).1
      (coreHaloEndpoints s width k band n).2 = coreHalo s width k band n := by
  unfold coreHaloEndpoints coreHalo
  split
  · rfl
  · ext i
    simp [mem_haloVertices, i.val_lt]

/-- Empty and clipped schedules retain unique descriptor positions. -/
theorem coreIndices_nodup (s width : ℕ) : (coreIndices s width).Nodup := List.nodup_range

/-- Reading a coordinate from its own generated descriptor gives the original
ambient value. The descriptor does not restart phase or period coordinates. -/
theorem coreHaloEndpoints_contains {s : ℕ} [NeZero s] (width k band n : ℕ)
    (i : ZMod s) (hi : i ∈ ownedCore s width k) :
    (coreHaloEndpoints s width k band n).1 ≤ i.val ∧
      i.val < (coreHaloEndpoints s width k band n).2 := by
  apply (mem_haloVertices _ _ i).mp
  rw [coreHaloEndpoints_set]
  exact ownedCore_subset_halo width k band n hi

end IntegerMultBounds.NLogN.PhaseCellMatrix
