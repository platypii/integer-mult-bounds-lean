module

public import IntegerMultBounds.NLogN.PhaseCellCoreGatherCount

/-! A core width small against the square root of an ambient axis leaves an
exponentially large quotient count. All inequalities are over natural sizes. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

theorem coreQuotient_large_of_square_width (s width ell : ℕ) (hw : 0 < width) (hell : 2 ≤ ell)
    (haxis : 2^ell ≤ 4*s) (hwidth : 128*width^2 ≤ 2^ell) :
    2^((ell+1)/2)+2 ≤ s/width := by
  let k := (ell+1)/2
  have hk : 1 ≤ k := by dsimp only [k]; omega
  have htwo : 2 ≤ 2^k := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
  have hplus : 2^k+2 ≤ 2*2^k := by omega
  have hsquare := Nat.pow_le_pow_left hplus 2
  have hkbound : 2*k ≤ ell+1 := by dsimp only [k]; omega
  have hpower : (2^k)^2 ≤ 2^(ell+1) := by
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hprod := Nat.mul_le_mul_right (width^2) hsquare
  have hscaled := Nat.mul_le_mul_left (width^2) hpower
  have hwidthScaled := Nat.mul_le_mul_left (2^ell) hwidth
  have haxisSquare := Nat.pow_le_pow_left haxis 2
  have hfinal : ((2^k+2)*width)^2 ≤ s^2 := by
    simp only [mul_pow,pow_succ] at hprod hscaled haxisSquare ⊢
    nlinarith only [hprod,hscaled,hwidthScaled,haxisSquare]
  apply (Nat.le_div_iff_mul_le hw).mpr
  exact (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp hfinal

end IntegerMultBounds.NLogN.PhaseCellMatrix
