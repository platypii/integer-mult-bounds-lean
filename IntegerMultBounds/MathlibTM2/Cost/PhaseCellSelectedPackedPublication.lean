module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedPublicationCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Packed publication adds polynomial control work to the existing scalar
batch arithmetic ledger. The latter is deliberately retained for reuse. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedPackedPublication_poly_le (cv cw : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) (p l target rhsExp V N L K u : ℕ)
    (hV : V ≤ cv*Sizes.p n) (hN : N ≤ Sizes.s n i) (hL : L ≤ Sizes.s n i) (hK : K ≤ Sizes.s n i)
    (hq : executionPrecision p l target rhsExp ≤ cw*Sizes.p n)
    (hw : executionWidth p l target rhsExp ≤ cw*Sizes.p n) :
    reusablePackedCellBatchPublishCost p l target rhsExp V N L K (Sizes.s n i) (Sizes.t n i) u ≤
      sizedClosedBatchBound p l K L (Sizes.s n i) (Sizes.t n i) u target rhsExp+
        (10000*(cv+cw+1)^4)*(Sizes.t n i)^4*(Sizes.p n)^4 := by
  let C := cv+cw+1
  let Z := C*Sizes.t n i*Sizes.p n
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have hC : 1 ≤ C := by dsimp only [C]; omega
  have hZ : 1 ≤ Z := Nat.mul_pos (Nat.mul_pos hC ht) hp
  have htZ : Sizes.t n i ≤ Z := by
    have hc := Nat.le_mul_of_pos_left (Sizes.t n i) hC
    exact hc.trans (Nat.le_mul_of_pos_right _ hp)
  have hcv : cv*Sizes.p n ≤ Z := by
    apply Nat.mul_le_mul_right
    have h := Nat.le_mul_of_pos_right C ht
    dsimp only [C] at h ⊢
    omega
  have hcw : cw*Sizes.p n ≤ Z := by
    apply Nat.mul_le_mul_right
    have h := Nat.le_mul_of_pos_right C ht
    dsimp only [C] at h ⊢
    omega
  have h := reusablePackedCellBatchPublishCost_le_bound p l target rhsExp V N L K
    (Sizes.s n i) (Sizes.t n i) u Z hZ (hV.trans hcv)
    (hN.trans ((h.good.lt i).le.trans htZ)) (hL.trans ((h.good.lt i).le.trans htZ))
    (hK.trans ((h.good.lt i).le.trans htZ)) (hq.trans hcw) (hw.trans hcw)
  convert h using 1 <;> dsimp only [Z,C] <;> ring

/-- Any fixed multiple of the added packed control work fits one selected
volume allowance, leaving the reusable scalar arithmetic bill unchanged. -/
theorem selectedPackedPublication_scaled_volume_le (cv cw scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ p l target rhsExp V N L K u : ℕ,
      V ≤ cv*Sizes.p n → N ≤ Sizes.s n i → L ≤ Sizes.s n i → K ≤ Sizes.s n i →
      executionPrecision p l target rhsExp ≤ cw*Sizes.p n →
      executionWidth p l target rhsExp ≤ cw*Sizes.p n →
      scale*reusablePackedCellBatchPublishCost p l target rhsExp V N L K (Sizes.s n i) (Sizes.t n i) u ≤
        scale*sizedClosedBatchBound p l K L (Sizes.s n i) (Sizes.t n i) u target rhsExp+Sizes.T n := by
  filter_upwards [selectedAxisPolynomial_le_volume (scale*(10000*(cv+cw+1)^4)) 4 4] with n hv
  intro h i p l target rhsExp V N L K u hV hN hL hK hq hw
  have hc := Nat.mul_le_mul_left scale
    (selectedPackedPublication_poly_le cv cw h i p l target rhsExp V N L K u hV hN hL hK hq hw)
  have hvol := hv i
  nlinarith only [hc,hvol]

end IntegerMultBounds.MathlibTM2.Cost
