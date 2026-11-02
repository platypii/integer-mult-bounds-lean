module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeometryDyadicGather
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPacketPreparedGatherBudget

/-! Count generation and retirement are absorbed by the existing geometry-pass
bill; all remaining overhead is linear in padded payload volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellMatrix
open PackedTranspose
variable {Q : ℕ}

theorem geometryGatherCosts_le (hstates : FixedStreamedBank.stateCount ≤ Q)
    (V s a width radius L w : ℕ) (hpacket : 0 < L*w)
    (hwidth : V ≤ 2^a*2^Nat.clog 2 (coreGatherIndices s width radius L).length*(L*w)) :
    let b := Nat.clog 2 (coreGatherIndices s width radius L).length
    let volume := 2^a*2^b*(L*w)
    geometryGatherTimeCost hstates V s a width radius L w ≤
      2*preparedCoreOriginsCost V s width radius L+500*volume+200+
        2*FixedStreamedBank.restoringTimeCost hstates a b (L*w) V ∧
    geometryGatherStockAllowance hstates V s a width radius L w ≤
      4*preparedCoreOriginsCost V s width radius L+700*volume+300+
        FixedStreamedBank.restoringStockAllowance hstates a b (L*w) V := by
  dsimp only
  obtain ⟨ht,hs⟩ := packetPreparedGatherCosts_le hstates s a width radius L w V hpacket hwidth
  let rows := (coreGatherIndices s width radius L).length
  have hcount : rows*(8*V+6)+6 ≤ preparedCoreOriginsCost V s width radius L := by
    unfold preparedCoreOriginsCost
    simp only [rows]
    omega
  have htime : (2*rows+2)+(2*(rows*V)+2)+(2*rows+2) ≤ preparedCoreOriginsCost V s width radius L := by
    nlinarith only [hcount]
  have hstock : 2*(2*rows+2) ≤ preparedCoreOriginsCost V s width radius L := by
    nlinarith only [hcount,Nat.zero_le (rows*V)]
  unfold geometryGatherTimeCost geometryGatherStockAllowance
  dsimp only
  simp only [rows] at htime hstock
  constructor <;> omega

end IntegerMultBounds.MathlibTM2.Cost
