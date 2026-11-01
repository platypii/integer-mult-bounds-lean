module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchedReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaRecoveryInteriorFast

/-! Audit the actual amortized caller: one initialized interior bill, plus
per-row preparation and linear traffic. The preparation estimate remains explicit. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s : ℕ} [NeZero s]

theorem batchedReplicaRecoveryTime_affine (H : ReplicaHaloProblem s) (target : ℕ)
    (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X) htarget :
    batchedReplicaRecoveryTime H (B.problem htarget) = initializedReplicaHaloTime (B.problem htarget)+
      H.Fs.length*(replicaRecoveryPreparationRowCost H+40*(H.span*H.wordWidth)+25*H.span+50)+24 := by
  unfold batchedReplicaRecoveryTime
  rw [replicaRecoveryInteriorTime_affine H target X B htarget]
  unfold retainedPackedPublicationMergeCost
  ring

end IntegerMultBounds.MathlibTM2.Cost
