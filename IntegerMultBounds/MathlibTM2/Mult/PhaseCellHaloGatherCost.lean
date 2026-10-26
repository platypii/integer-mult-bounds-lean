module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloGather
public import IntegerMultBounds.NLogN.PhaseCellHaloGroupVolume

/-! Gathering one equal-length class is linear in the encoded ambient line.
Both copied volume and total seek distance are charged, including counter setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloGatherCost_le {s t : ℕ} [NeZero s] (hst : s < t) (band a b L w : ℕ)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length) (hw : 1 ≤ w) :
    (haloLengthGroup s t band a b L).length*(14*L*w+25)+12*s*w+6*L*w+9*L+29 ≤ 66*s*w+29 := by
  let B := (haloLengthGroup s t band a b L).length
  have hB : 0 < B := hgroup
  have hvol : B*L ≤ s := haloGroup_volume_le hst band a b L
  have hL : 0 < L := ((mem_haloLengthGroup s t band a b L _).mp
    (haloGroupPhase_mem s t band a b L ⟨0, hB⟩)).2.1
  have hBs : B ≤ s := by nlinarith only [hvol, hL]
  have hLs : L ≤ s := by nlinarith only [hvol, hB]
  have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hw
  have hcopy := Nat.mul_le_mul_right w hvol
  have hrow := Nat.mul_le_mul_right w hLs
  change B*(14*L*w+25)+12*s*w+6*L*w+9*L+29 ≤ _
  nlinarith only [hBs, hLs, hsw, hcopy, hrow]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
