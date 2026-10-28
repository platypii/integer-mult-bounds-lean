module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateHaloGeometryWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWeightWidth
public import IntegerMultBounds.NLogN.PhaseCellBand

/-! The generated geometry packets fit the numerical workspace at the selected band. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN

theorem haloGeometryWidth_le_weightWorkspaceWidth {P q w t u band : ℕ} (hband : band ≤ P) :
    haloGeometryWidth t band w ≤ weightWorkspaceWidth P q w t u := by
  have hb : Nat.size band ≤ band := Nat.size_le.mpr Nat.lt_two_pow_self
  have hw : Nat.size w ≤ w := Nat.size_le.mpr Nat.lt_two_pow_self
  dsimp only [haloGeometryWidth,publicationGeometryWidth,weightWorkspaceWidth,coefficientWorkspaceWidth]
  simp only [Nat.size_zero]
  omega

theorem selectedHaloGeometryWidth_le_weightWorkspaceWidth {p : ℕ} (hp : 1 ≤ p) (q w t u : ℕ) :
    haloGeometryWidth t (PhaseCellBand.width p u) w ≤ weightWorkspaceWidth (2^15*p) q w t u := by
  apply haloGeometryWidth_le_weightWorkspaceWidth
  have hs := Nat.sqrt_le_self (16*p/u)
  have hd := Nat.div_le_self (16*p) u
  dsimp only [PhaseCellBand.width]
  norm_num
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
