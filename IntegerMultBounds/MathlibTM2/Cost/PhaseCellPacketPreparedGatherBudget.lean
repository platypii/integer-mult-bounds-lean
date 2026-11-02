module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketPreparedDyadicGather
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCountedDyadicGatherBudget

/-! Runtime packet-width production and retirement preserve linear overhead
around the restoring-kernel time and stock bills. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellMatrix
open PackedTranspose
variable {Q : ℕ}

theorem packetPreparedGatherCosts_le (hstates : FixedStreamedBank.stateCount ≤ Q)
    (s a width radius L w V : ℕ) (hpacket : 0 < L*w)
    (hwidth : V ≤ 2^a*2^Nat.clog 2 (coreGatherIndices s width radius L).length*(L*w)) :
    let b := Nat.clog 2 (coreGatherIndices s width radius L).length
    let volume := 2^a*2^b*(L*w)
    gatherPacketWidthCost V L w+(countedGatherTimeCost hstates s a width radius L w V+(2*(L*w)+2)) ≤
      500*volume+200+2*FixedStreamedBank.restoringTimeCost hstates a b (L*w) V ∧
    3*gatherPacketWidthCost V L w+countedGatherStockAllowance hstates s a width radius L w V ≤
      700*volume+300+FixedStreamedBank.restoringStockAllowance hstates a b (L*w) V := by
  dsimp only
  obtain ⟨ht,hs⟩ := countedGatherCosts_le hstates s a width radius L w V hpacket hwidth
  have hw : 0 < w := by
    by_contra hn
    have hz : w = 0 := by omega
    simp [hz] at hpacket
  have hL : L ≤ L*w := Nat.le_mul_of_pos_right _ hw
  have hp : L*w ≤ 2^a*2^Nat.clog 2 (coreGatherIndices s width radius L).length*(L*w) :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
  unfold gatherPacketWidthCost
  constructor <;> nlinarith only [ht,hs,hwidth,hL,hp]

end IntegerMultBounds.MathlibTM2.Cost
