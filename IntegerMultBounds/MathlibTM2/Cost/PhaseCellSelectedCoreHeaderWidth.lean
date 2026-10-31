module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawHeaderPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawBatchKeys

/-! The actual scalar header generator needs only linearly many selected precision bits. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedInverseCallerWordWidth_le (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) {u target : ℕ} (hu : u ≤ Sizes.p n)
    (htarget : target ≤ ct*Sizes.p n)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i) :
    inverseCallerWordWidth (Sizes.p n) u
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target
      (Sizes.s n i) (Sizes.t n i) ≤ (2*(ct+21)+22)*Sizes.p n := by
  let p := Sizes.p n
  let t := Sizes.t n i
  let κ := ct+21
  let R := κ*t
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp [p]; omega
  have hpt := selectedPrecision_le_axis h i
  have ht1 : 1 ≤ t := hp.trans hpt
  have htR : t ≤ R := Nat.le_mul_of_pos_left t (by dsimp [κ]; omega)
  have hR : 1 ≤ R := ht1.trans htR
  have hsR : Sizes.s n i ≤ R := (h.good.lt i).le.trans htR
  have hpR : p ≤ R := hpt.trans htR
  have hl := (haloInverseRingLog_bounds hp (h.good.lt i) (h.quarter_p_le_theta i)).1
  have hwork := inverseCallerWorkspace_poly hR hpR (hu.trans hpR)
    (hl.trans (show 20*p ≤ R by dsimp [R,κ]; nlinarith only [hpt]))
    (htarget.trans (show ct*p ≤ R by dsimp [R,κ]; nlinarith only [hpt]))
    hsR htR (hband.trans hsR)
  have htbits : Nat.size t ≤ 2*p := by
    have hb := selectedAxisBits_le n i
    have hell := selectedAxisLog_le_precision h
    dsimp [t,p] at *
    omega
  have htPow : t ≤ 2^(2*p) := (Nat.lt_size_self t).le.trans
    (Nat.pow_le_pow_right (by decide) htbits)
  have hκPow : κ ≤ 2^κ := (Nat.lt_two_pow_self).le
  have hRPow : R ≤ 2^(κ+2*p) := by
    calc
      R ≤ 2^κ*2^(2*p) := Nat.mul_le_mul hκPow htPow
      _ = _ := (pow_add _ _ _).symm
  have hbill : 100000*R^2 < 2^(18+2*(κ+2*p)) := by
    calc
      _ < 2^18*(2^(κ+2*p))^2 := Nat.mul_lt_mul_of_lt_of_le
        (by decide) (Nat.pow_le_pow_left hRPow 2) (by positivity)
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega
  apply Nat.size_le.mpr
  apply lt_of_le_of_lt hwork
  exact hbill.trans_le (Nat.pow_le_pow_right (by decide)
    (show 18+2*(κ+2*p) ≤ (2*(ct+21)+22)*p by dsimp [κ]; nlinarith only [hp]))

end IntegerMultBounds.MathlibTM2.Cost
