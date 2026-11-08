module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedReplicaRecoveryReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPassReindex
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryJobs

/-! The original caller returns producer certificates, retained bank views and
original RHS headers. These supply recovery readiness after archive handoff. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "extendCaller" => CyclicRecoveryPlacement.extend
variable {s A : ℕ} [NeZero s]

theorem cyclicRecoveryCallerReady (H K : ReplicaHaloProblem s)
    (buffersL buffersR : ReplicaLoopBuffers A) (S₁ S₂ producer : Stacks 834 A)
    (Cs Ds : List (ZMod s → GaussianInt))
    (postL : CachedReplicaPassPost H CyclicReplicaPlacement.left buffersL S₁ producer Cs)
    (postR : CachedReplicaPassPost K CyclicReplicaPlacement.right buffersR S₂ producer Ds)
    (F : Stacks 840 A)
    (hbankL : embStk CyclicReplicaPlacement.left.coupling.bank (embStk extendCaller F) =
      embStk CyclicReplicaPlacement.left.coupling.bank producer)
    (hbankR : embStk CyclicReplicaPlacement.right.coupling.bank (embStk extendCaller F) =
      embStk CyclicReplicaPlacement.right.coupling.bank producer)
    (headersL : ReplicaRecoveryRhsHeaders H CyclicReplicaPlacement.left.plan.gather buffersL (embStk extendCaller F))
    (headersR : ReplicaRecoveryRhsHeaders K CyclicReplicaPlacement.right.plan.gather buffersR (embStk extendCaller F)) :
    RetainedReplicaRecoveryReady H CyclicRecoveryPlacement.leftJob buffersL
      (S₁.R (CyclicReplicaPlacement.left.coupling.bank 138)) F ∧
    RetainedReplicaRecoveryReady K CyclicRecoveryPlacement.rightJob buffersR
      (S₂.R (CyclicReplicaPlacement.right.coupling.bank 138)) F := by
  constructor
  · apply postL.recovery_ready.of_bank_frame
    · change embStk (CyclicReplicaPlacement.left.reindex extendCaller (Fin.castLE_injective _)).coupling.bank F = _
      rw [CyclicReplicaPlacement.left.reindex_bank_view]
      exact hbankL
    · exact ⟨headersL.count,headersL.volume,headersL.source,headersL.fresh⟩
  · apply postR.recovery_ready.of_bank_frame
    · change embStk (CyclicReplicaPlacement.right.reindex extendCaller (Fin.castLE_injective _)).coupling.bank F = _
      rw [CyclicReplicaPlacement.right.reindex_bank_view]
      exact hbankR
    · exact ⟨headersR.count,headersR.volume,headersR.source,headersR.fresh⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
