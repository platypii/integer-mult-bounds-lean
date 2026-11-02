module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeometryGatherBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellTotalDyadicBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherVolume

/-! Apply actual fitting-core geometry to the complete route. Minimal padding
costs constant source traffic; the sharp charge also covers singleton groups. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellMatrix
open PackedTranspose
variable {Q : ℕ}

theorem geometryGatherTimeCost_le_source (hstates : FixedStreamedBank.stateCount ≤ Q)
    (V s a width radius L w : ℕ) (hwidth : width ≤ s) (hradius : radius ≤ width)
    (hcores : 0 < (coreGatherIndices s width radius L).length) (hpacket : 0 < L*w)
    (hV : V ≤ 2^a*2^Nat.clog 2 (coreGatherIndices s width radius L).length*(L*w)) :
    let b := Nat.clog 2 (coreGatherIndices s width radius L).length
    (geometryGatherTimeCost hstates V s a width radius L w : ℝ) ≤
      (2*preparedCoreOriginsCost V s width radius L+6000*(2^a*s*w)+204+
        2*(116*V+143+32921*(V+1)^5) : ℕ)+
      24*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*(2^a*s*w : ℕ)*dyadicRouteCharge a b := by
  dsimp only
  let b := Nat.clog 2 (coreGatherIndices s width radius L).length
  have hv : 2^a*2^b*(L*w) ≤ 12*(2^a*s*w) := by
    simpa only [dyadicCapacity,Nat.mul_assoc] using dyadicGatherVolume_le s width radius L (2^a) w hwidth hradius hcores
  have ht := (Nat.cast_le (α := ℝ)).mpr (geometryGatherCosts_le hstates V s a width radius L w hpacket hV).1
  have hr := restoringTimeCost_total_le hstates a b (L*w) V hpacket hV
  have hc : 0 ≤ (2*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300) : ℝ)*dyadicRouteCharge a b :=
    mul_nonneg (by
      have := IntegerMultBounds.MathlibTM2.Node.swapConst_pos
      unfold generatedDyadicStageCoeff
      positivity) (dyadicRouteCharge_nonneg a b)
  have hweighted := mul_le_mul_of_nonneg_left ((Nat.cast_le (α := ℝ)).mpr hv) hc
  have hlinear := (Nat.cast_le (α := ℝ)).mpr (Nat.mul_le_mul_left 500 hv)
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at ht hr hweighted hlinear ⊢
  dsimp only [b] at hr hweighted hlinear
  nlinarith only [ht,hr,hweighted,hlinear]

theorem geometryGatherStockAllowance_le_source (hstates : FixedStreamedBank.stateCount ≤ Q)
    (V s a width radius L w : ℕ) (hwidth : width ≤ s) (hradius : radius ≤ width)
    (hcores : 0 < (coreGatherIndices s width radius L).length) (hpacket : 0 < L*w)
    (hV : V ≤ 2^a*2^Nat.clog 2 (coreGatherIndices s width radius L).length*(L*w)) :
    geometryGatherStockAllowance hstates V s a width radius L w ≤
      (342*V+423+98763*(V+1)^5)+4*preparedCoreOriginsCost V s width radius L+
        12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700)*(2^a*s*w)+300 := by
  let b := Nat.clog 2 (coreGatherIndices s width radius L).length
  have hv : 2^a*2^b*(L*w) ≤ 12*(2^a*s*w) := by
    simpa only [dyadicCapacity,Nat.mul_assoc] using dyadicGatherVolume_le s width radius L (2^a) w hwidth hradius hcores
  have hs := (geometryGatherCosts_le hstates V s a width radius L w hpacket hV).2
  have hr := packedDyadicStockAllowance_le hstates a b (L*w) V hpacket hV
  have hm := Nat.mul_le_mul_left (streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700) hv
  dsimp only [b] at hr hm
  nlinarith only [hs,hr,hm]

end IntegerMultBounds.MathlibTM2.Cost
