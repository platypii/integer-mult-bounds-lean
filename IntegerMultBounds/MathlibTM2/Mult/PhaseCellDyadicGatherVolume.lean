module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicRectangleSizing
public import IntegerMultBounds.NLogN.PhaseCellCoreGatherVolume

/-! Minimal core padding preserves the linear gathered-volume bound. Empty
groups are skipped by the selected caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN.PhaseCellMatrix

theorem dyadicGatherVolume_le (s width radius L replicas w : ℕ)
    (hwidth : width ≤ s) (hradius : radius ≤ width)
    (hcores : 0 < (coreGatherIndices s width radius L).length) :
    replicas * (dyadicCapacity (coreGatherIndices s width radius L).length * (L*w)) ≤
      12*replicas*s*w := by
  have hcap := dyadicCapacity_le_twice (coreGatherIndices s width radius L).length
  rw [max_eq_right hcores] at hcap
  have hvolume := coreGather_volume_le_six s width radius L hwidth hradius
  have hpadded := Nat.mul_le_mul_right L hcap
  have hbound : dyadicCapacity (coreGatherIndices s width radius L).length * L ≤ 12*s := by
    nlinarith only [hpadded, hvolume]
  have h := Nat.mul_le_mul_left replicas (Nat.mul_le_mul_right w hbound)
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
