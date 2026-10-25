module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireGroupRHS
public import IntegerMultBounds.NLogN.PhaseCellNaturalGroupVolume

/-! Retiring a natural group's gathered RHS costs linear time in the encoded
ambient line, including generated counters and their release. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem retireNaturalGroupCost_le {s t : ℕ} [NeZero s] (hst : s < t) (band L w : ℕ)
    (hgroup : 0 < (naturalLengthGroup s t band L).length) (hw : 1 ≤ w) :
    let B := (naturalLengthGroup s t band L).length
    12*B*L*w+6*L*w+9*L+9*B+19 ≤ 36*s*w+19 := by
  dsimp only
  let B := (naturalLengthGroup s t band L).length
  have hvol : B*L ≤ s := naturalGroup_volume_le hst band L
  have hL : 0 < L := ((mem_naturalLengthGroup s t band L _).mp
    (naturalGroupPhase_mem s t band L ⟨0,hgroup⟩)).2.1
  have hBs : B ≤ s := by nlinarith only [hvol,hL]
  have hLs : L ≤ s := by have hB : 0 < B := hgroup; nlinarith only [hvol,hB]
  have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hw
  have hwork := Nat.mul_le_mul_right w hvol
  have hrow := Nat.mul_le_mul_right w hLs
  change 12*B*L*w+6*L*w+9*L+9*B+19 ≤ _
  nlinarith only [hBs,hLs,hsw,hwork,hrow]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
