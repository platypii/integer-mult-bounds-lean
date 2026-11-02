module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherRouting
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedDyadicBudget

/-! Padding and dummy retirement add only linear-volume work to the actual
packed router. The complete route retains its sharp transpose charge. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q : ℕ}

private theorem gatherBoundaryCosts_le (rows capacity replicas packet : ℕ)
    (hfit : rows ≤ capacity) (hcapacity : 0 < capacity)
    (hreplicas : 0 < replicas) (hpacket : 0 < packet) :
    gatherCounterSetupCost rows capacity packet+
        (replicas*(6*(capacity*packet)+13)+6)+(2*(capacity*packet)+4)+
        retireDummyBatchesCost rows capacity replicas packet ≤ 150*(replicas*capacity*packet) ∧
    (2*gatherCounterSetupCost rows capacity packet+
        (replicas*((capacity-rows)*packet)+2*(4*(capacity*packet)+10)))+
        2*retireDummyBatchesCost rows capacity replicas packet ≤ 260*(replicas*capacity*packet) := by
  have hsetup := gatherCounterSetupCost_le (width := packet) hfit
  have hpad := paddingCounterSetupCost_le (width := replicas*packet) hfit
  have hmissing := Nat.mul_le_mul_right (replicas*packet) (Nat.sub_le capacity rows)
  have hcp : 1 ≤ capacity*packet := Nat.mul_pos hcapacity hpacket
  have hrp : replicas*packet ≤ replicas*capacity*packet := by
    exact Nat.mul_le_mul_right packet (Nat.le_mul_of_pos_right replicas hcapacity)
  have hc : capacity ≤ capacity*packet := Nat.le_mul_of_pos_right capacity hpacket
  have hr : replicas ≤ replicas*packet := Nat.le_mul_of_pos_right replicas hpacket
  have hcpv : capacity*packet ≤ replicas*capacity*packet := by
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left (capacity*packet) hreplicas
  have hone : 1 ≤ replicas*capacity*packet := Nat.mul_pos (Nat.mul_pos hreplicas hcapacity) hpacket
  unfold retireDummyBatchesCost retireDummyRowsCost
  constructor <;> nlinarith only [hsetup,hpad,hmissing,hcp,hrp,hc,hr,hcpv,hone]

theorem gatherRouteTimeCost_le (hstates : FixedStreamedBank.stateCount ≤ Q)
    (s a b width radius L w V : ℕ)
    (hfit : (coreGatherIndices s width radius L).length ≤ 2^b) (hpacket : 0 < L*w) :
    PackedTranspose.gatherRouteTimeCost hstates s a b width radius L w V ≤
      176*(2^a*2^b*(L*w))+24+2*FixedStreamedBank.restoringTimeCost hstates a b (L*w) V := by
  have h := (gatherBoundaryCosts_le _ (2^b) (2^a) (L*w) hfit
    (Nat.two_pow_pos _) (Nat.two_pow_pos _) hpacket).1
  unfold PackedTranspose.gatherRouteTimeCost
  simp only [Nat.mul_assoc] at h ⊢
  omega

theorem gatherRouteStockAllowance_le (hstates : FixedStreamedBank.stateCount ≤ Q)
    (s a b width radius L w V : ℕ)
    (hfit : (coreGatherIndices s width radius L).length ≤ 2^b) (hpacket : 0 < L*w) :
    PackedTranspose.gatherRouteStockAllowance hstates s a b width radius L w V ≤
      300*(2^a*2^b*(L*w))+38+FixedStreamedBank.restoringStockAllowance hstates a b (L*w) V := by
  have h := (gatherBoundaryCosts_le _ (2^b) (2^a) (L*w) hfit
    (Nat.two_pow_pos _) (Nat.two_pow_pos _) hpacket).2
  unfold PackedTranspose.gatherRouteStockAllowance
  simp only [Nat.mul_assoc] at h ⊢
  omega

theorem gatherRouteTimeCost_sharp_le (hstates : FixedStreamedBank.stateCount ≤ Q)
    (s a b width radius L w V : ℕ) (hb : 0 < b)
    (hfit : (coreGatherIndices s width radius L).length ≤ 2^b) (hpacket : 0 < L*w)
    (hwidth : V ≤ 2^a*2^b*(L*w)) :
    (PackedTranspose.gatherRouteTimeCost hstates s a b width radius L w V : ℝ) ≤
      (176*(2^a*2^b*(L*w))+28+2*(116*V+143+32921*(V+1)^5) : ℕ)+
        2*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*(2^a*2^b*(L*w) : ℕ)*
          ((a : ℝ)/b*((b : ℝ)^Parameters.tau+1)+4*b) := by
  have hroute := gatherRouteTimeCost_le hstates s a b width radius L w V hfit hpacket
  have hroute' := (Nat.cast_le (α := ℝ)).mpr hroute
  have htranspose := restoringTimeCost_le hstates a b (L*w) V hb hpacket hwidth
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hroute' htranspose ⊢
  linarith only [hroute',htranspose]

theorem gatherRouteStockAllowance_linear_le (hstates : FixedStreamedBank.stateCount ≤ Q)
    (s a b width radius L w V : ℕ)
    (hfit : (coreGatherIndices s width radius L).length ≤ 2^b) (hpacket : 0 < L*w)
    (hwidth : V ≤ 2^a*2^b*(L*w)) :
    PackedTranspose.gatherRouteStockAllowance hstates s a b width radius L w V ≤
      (342*V+423+98763*(V+1)^5)+
        (streamedDyadicStockCoeff FixedStreamedBank.tapeCount+300)*(2^a*2^b*(L*w))+38 := by
  have hroute := gatherRouteStockAllowance_le hstates s a b width radius L w V hfit hpacket
  have htranspose := packedDyadicStockAllowance_le hstates a b (L*w) V hpacket hwidth
  nlinarith only [hroute,htranspose]

end IntegerMultBounds.MathlibTM2.Cost
