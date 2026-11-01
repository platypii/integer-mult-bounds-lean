module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBatchCoupling

/-! Retain the generated factor language across the first interior/coupling pass.
All premises are restored workspace or structural frames from its execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

theorem ReplicaBoundaryFactorData.after_batch_first_pass (H : ReplicaHaloProblem s) (target : ℕ)
    (columns : List (ZMod s → GaussianInt)) {S F : Stacks 392 A}
    (h : ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryBoundaryFactoryReg S))
    (raw : List (Fin (A+4)))
    (hnative : (embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver F)).L =
      (embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver S)).L)
    (hleft : ∀ k, (∀ i, replicaRecoveryBatchInterior.gather i ≠ k) →
      (∀ i, replicaRecoveryBatchInterior.solver i ≠ k) → (247 : Fin 392) ≠ k → F.L k = S.L k)
    (hright : ∀ k, (∀ i, replicaRecoveryBatchCoupling.bank i ≠ k) →
      (∀ i, replicaRecoveryBatchInterior.gather i ≠ k) →
      (∀ i, replicaRecoveryBatchInterior.solver i ≠ k) →
      (247 : Fin 392) ≠ k → (248 : Fin 392) ≠ k → F.R k = S.R k)
    (hready : RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) raw (embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver F)))
    (h119 : F.R (replicaRecoveryPreparationCallerWorkerReg 119) =
      S.R (replicaRecoveryPreparationCallerWorkerReg 119)) :
    ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryBoundaryFactoryReg F) := by
  apply h.of_recovery_frame H target columns (F := embStk replicaRecoveryBoundaryFactoryReg F)
    (replicaRecoveryBatchCoupling_factor_left_frame hnative hleft)
  · rw [replicaRecoveryBatchCoupling_native_view F] at hready
    intro i
    exact (hready.clean i).2
  · exact h119
  · intro k hk _
    exact replicaRecoveryBatchCoupling_factor_extension_frame hright (Fin.castLE (by decide : 242 ≤ 257) k) hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
