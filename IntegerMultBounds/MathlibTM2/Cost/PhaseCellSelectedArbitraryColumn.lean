module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellArbitraryColumnLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedUncachedCoupling

/-! All actual original-column work has a selected polynomial allowance,
uniform over the physical column index, including masks and guard generation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedArbitraryOriginalColumnCost_poly_le (cw : ℕ) :
    ∃ C : ℕ, ∀ n (h : Sizes.Big n) (i : Fin (Sizes.d n)) (q u j : ℕ),
      2*q+8 ≤ cw*Sizes.p n → u ≤ Sizes.p n → j < Sizes.s n i →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      arbitraryOriginalColumnCost (Sizes.p n) q (Sizes.s n i) (Sizes.t n i) u j ≤
        C*(Sizes.t n i)^5 := by
  obtain ⟨C,hcouple⟩ := selectedBorrowedCouplingPass_poly_le cw
  refine ⟨C+1000000*(cw+1),?_⟩
  intro n h i q u j hw hu hj hb
  have hc := hcouple n h i q u _ j (j+1) hw hu hb (by omega) (by omega) true
  have hs := h.good.lt i
  have hp := selectedPrecision_le_axis h i
  have ht : 1 ≤ Sizes.t n i := by omega
  have hq : q ≤ cw*Sizes.t n i := by nlinarith only [hw,Nat.mul_le_mul_left cw hp]
  have hwidth : 2*q+8 ≤ cw*Sizes.t n i := hw.trans (Nat.mul_le_mul_left cw hp)
  have hvol := Nat.mul_le_mul hs.le hwidth
  have hpow : Sizes.t n i ≤ Sizes.t n i^5 := Nat.le_self_pow (by decide) _
  have hpow2 : Sizes.t n i^2 ≤ Sizes.t n i^5 := Nat.pow_le_pow_right ht (by decide)
  have hscaled := Nat.mul_le_mul_left cw hpow2
  have hscaled1 := Nat.mul_le_mul_left cw hpow
  have hone : 1 ≤ Sizes.t n i^5 := Nat.one_le_pow _ _ ht
  have hcost := arbitraryOriginalColumnCost_controls_le (Sizes.p n) q (Sizes.s n i) (Sizes.t n i) u j hj
  rw [show (2 : ℕ)^15 = 32768 by decide] at hcost
  ring_nf at hq hwidth hvol hscaled hscaled1 hc hcost ⊢
  omega

end IntegerMultBounds.MathlibTM2.Cost
