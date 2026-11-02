module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedDyadicGather
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDyadicGatherBudget

/-! Count-derived dimensions and both metadata cleanup passes retain linear
payload overhead around the sharp restoring transpose kernel. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellMatrix
open PackedTranspose
variable {Q : ℕ}

theorem countedGatherCosts_le (hstates : FixedStreamedBank.stateCount ≤ Q)
    (s a width radius L w V : ℕ) (hpacket : 0 < L*w)
    (hwidth : V ≤ 2^a*2^Nat.clog 2 (coreGatherIndices s width radius L).length*(L*w)) :
    let b := Nat.clog 2 (coreGatherIndices s width radius L).length
    let volume := 2^a*2^b*(L*w)
    countedGatherTimeCost hstates s a width radius L w V ≤
      400*volume+150+2*FixedStreamedBank.restoringTimeCost hstates a b (L*w) V ∧
    countedGatherStockAllowance hstates s a width radius L w V ≤
      600*volume+256+FixedStreamedBank.restoringStockAllowance hstates a b (L*w) V := by
  dsimp only
  let rows := (coreGatherIndices s width radius L).length
  let b := Nat.clog 2 rows
  let volume := 2^a*2^b*(L*w)
  have hfit : rows ≤ 2^b := Nat.le_pow_clog (by decide) rows
  have hr : 2^a ≤ volume := by
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.two_pow_pos b) hpacket) |>.trans_eq (by simp [volume,Nat.mul_assoc])
  have hc : 2^b ≤ volume := by
    have h := Nat.le_mul_of_pos_left (2^b) (Nat.two_pow_pos a)
    exact h.trans (Nat.le_mul_of_pos_right _ hpacket)
  have hp : L*w ≤ volume := Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.two_pow_pos a) (Nat.two_pow_pos b))
  have ha : a ≤ volume := (Nat.lt_two_pow_self.le).trans hr
  have hb : b ≤ volume := (Nat.lt_two_pow_self.le).trans hc
  have hm : rows ≤ volume := hfit.trans hc
  have ht := gatherRouteTimeCost_le hstates s a b width radius L w V hfit hpacket
  have hs := gatherRouteStockAllowance_le hstates s a b width radius L w V hfit hpacket
  change V ≤ volume at hwidth
  change gatherRouteTimeCost hstates s a b width radius L w V ≤
    176*volume+24+2*FixedStreamedBank.restoringTimeCost hstates a b (L*w) V at ht
  change gatherRouteStockAllowance hstates s a b width radius L w V ≤
    300*volume+38+FixedStreamedBank.restoringStockAllowance hstates a b (L*w) V at hs
  constructor
  · unfold countedGatherTimeCost
    dsimp only
    simp only [volume,b,rows] at hr hc hp ha hb hm ht hs hwidth ⊢
    omega
  · unfold countedGatherStockAllowance
    dsimp only
    simp only [volume,b,rows] at hr hc hp ha hb hm ht hs hwidth ⊢
    omega

end IntegerMultBounds.MathlibTM2.Cost
