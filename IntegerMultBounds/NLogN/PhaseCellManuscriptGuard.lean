module

public import IntegerMultBounds.NLogN.PhaseCellBand
public import IntegerMultBounds.NLogN.PhaseCellLocalityPrecision
public import IntegerMultBounds.NLogN.PhaseCellRowSelectionGeometry

/-! Match the existing locality depth to the manuscript's 4096*p^3 target
halo. No ambient line size enters the selected-row guard estimate. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

theorem width_le_five_mul (p u : ℕ) (hp : 1 ≤ p) : PhaseCellBand.width p u ≤ 5*p := by
  have hroot := Nat.sqrt_le' (16*p/u)
  have hdiv := Nat.div_le_self (16*p) u
  have hp2 : p ≤ p^2 := by nlinarith
  have hh : Nat.sqrt (16*p/u) ≤ 4*p := by nlinarith
  unfold PhaseCellBand.width
  omega

theorem manuscript_guard_room (p u target : ℕ) (hp : 1 ≤ p) (htarget : target ≤ 16*p) :
    2*(localityDepth p target*PhaseCellBand.width p u)+1 ≤ 4096*p^3 := by
  have hsum : target+(p+4) ≤ 21*p := by omega
  have hdepth : localityDepth p target ≤ 336*p^2 := by
    have hh := Nat.mul_le_mul_left (16*p) hsum
    dsimp only [localityDepth]
    nlinarith only [hh]
  have hradius : localityDepth p target*PhaseCellBand.width p u ≤ 1680*p^3 := by
    calc
      _ ≤ (336*p^2)*(5*p) := Nat.mul_le_mul hdepth (width_le_five_mul p u hp)
      _ = _ := by ring
  have hp3 : 1 ≤ p^3 := Nat.one_le_pow _ _ hp
  omega

end IntegerMultBounds.NLogN.PhaseCellMatrix
