module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedColumnCouplingWorkspace

/-! Original columns reuse the uniform feed reserve and linear source/header work. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {P₀ U : Type}

theorem selectedOriginalColumnUniformWorkspace_le (K cw scale : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)),
      ∀ q u : ℕ, 2*q+8 ≤ cw*Sizes.p m → u ≤ Sizes.p m → PhaseCellBand.width (Sizes.p m) u ≤ Sizes.s m i →
      scale*originalColumnUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        K (Sizes.p m) q (Sizes.s m i) (Sizes.t m i) u ≤ 2*Sizes.T m := by
  let C := scale*10000000*(cw+6)*(cw+1)
  filter_upwards [selectedFeedCouplingUniformWorkspace_le (P₀ := P₀) (Q := Q) (A := A) (U := U) true K cw scale,
    selectedAxisPolynomial_le_volume C 2 1] with m hf hv
  intro h i q u hw hu hb
  let p := Sizes.p m
  let t := Sizes.t m i
  let s := Sizes.s m i
  let band := PhaseCellBand.width p u
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hbase : p ≤ t*p := Nat.le_mul_of_pos_left _ ht
  have htp : t ≤ t*p := Nat.le_mul_of_pos_right _ hp
  have hunit : 1 ≤ t*p := Nat.mul_pos ht hp
  have hscaled := Nat.mul_le_mul_left (cw+2) hbase
  have hsum : p+q+s+t+u+band+1 ≤ (cw+6)*t*p := by
    have hst := h.good.lt i
    change s < t at hst
    change band ≤ s at hb
    nlinarith only [hw,hu,hb,hst.le,hbase,htp,hunit,hscaled]
  have hwidth : 2*q+9 ≤ (cw+1)*p := by nlinarith only [hw,hp]
  have hshape := Nat.mul_le_mul_left (scale*10000000) (Nat.mul_le_mul hsum hwidth)
  have hvolume := hv i
  have heq : (scale*10000000)*(((cw+6)*t*p)*((cw+1)*p)) = C*t^1*p^2 := by
    dsimp only [C]; ring
  rw [heq] at hshape
  have hfeed := hf h i q (2*q+8) u band (by omega) hw (by omega) hu hb
  have hcolumn := Nat.mul_le_mul_left scale
    (originalColumnUniformWorkspace_le_feed (P₀ := P₀) (Q := Q) (A := A) (U := U) K p q s t u)
  nlinarith only [hcolumn,hfeed,hshape,hvolume]

end IntegerMultBounds.MathlibTM2.Cost
