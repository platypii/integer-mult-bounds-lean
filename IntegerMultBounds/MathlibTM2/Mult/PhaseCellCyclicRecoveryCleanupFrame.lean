module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCouplingCursor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorCleanupBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCyclicRecoveryCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedNativeCyclicBoundaryBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryMaskReady

/-! The recovery cursor changes payloads but preserves both disposable native
banks. Thus second-interior cleanup keeps its first-pass allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
variable {s A : ℕ} [NeZero s]
variable {H K : ReplicaHaloProblem s} {buffersL buffersR : ReplicaLoopBuffers A}
variable {done todo : List (CyclicRecoveryRow s)}
variable {tail rhsL rhsR rawL rawR pageL pageR : List (Fin (A+4))} {S F : Stacks 840 A}

theorem CyclicRecoveryCouplingCursor.disposable_left_frame
    (h : CyclicRecoveryCouplingCursor H K buffersL buffersR done todo tail rhsL rhsR rawL rawR pageL pageR S F)
    (i : Fin 117) (hi : i ∈ replicaCouplingNativeIndices) :
    F.R (CyclicRecoveryPlacement.leftJob.plan.solver (weightCacheCoreReg i)) =
      S.R (CyclicRecoveryPlacement.leftJob.plan.solver (weightCacheCoreReg i)) := by
  have hn : i ≠ 93 ∧ i ≠ 110 := by simpa [replicaCouplingNativeIndices] using hi
  have h93 : i.val ≠ 93 := by intro he; apply hn.1; exact Fin.ext he
  have h110 : i.val ≠ 110 := by intro he; apply hn.2; exact Fin.ext he
  apply h.frame
  simp only [cyclicRecoveryCouplingPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
  change ¬(126+i.val = 732 ∨ 126+i.val = 219 ∨ 126+i.val = 236 ∨
    126+i.val = 125 ∨ 126+i.val = 519 ∨ 126+i.val = 536 ∨ 126+i.val = 425 ∨ 126+i.val = 828)
  have := i.isLt
  omega

theorem CyclicRecoveryCouplingCursor.disposable_right_frame
    (h : CyclicRecoveryCouplingCursor H K buffersL buffersR done todo tail rhsL rhsR rawL rawR pageL pageR S F)
    (i : Fin 117) (hi : i ∈ replicaCouplingNativeIndices) :
    F.R (CyclicRecoveryPlacement.rightJob.plan.solver (weightCacheCoreReg i)) =
      S.R (CyclicRecoveryPlacement.rightJob.plan.solver (weightCacheCoreReg i)) := by
  have hn : i ≠ 93 ∧ i ≠ 110 := by simpa [replicaCouplingNativeIndices] using hi
  have h93 : i.val ≠ 93 := by intro he; apply hn.1; exact Fin.ext he
  have h110 : i.val ≠ 110 := by intro he; apply hn.2; exact Fin.ext he
  apply h.frame
  simp only [cyclicRecoveryCouplingPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
  change ¬(300+(126+i.val) = 732 ∨ 300+(126+i.val) = 219 ∨ 300+(126+i.val) = 236 ∨
    300+(126+i.val) = 125 ∨ 300+(126+i.val) = 519 ∨ 300+(126+i.val) = 536 ∨ 300+(126+i.val) = 425 ∨ 300+(126+i.val) = 828)
  have := i.isLt
  omega

theorem CyclicRecoveryCouplingCursor.cleanup_costs
    (h : CyclicRecoveryCouplingCursor H K buffersL buffersR done todo tail rhsL rhsR rawL rawR pageL pageR S F) :
    releaseReplicaInteriorBankCost CyclicRecoveryPlacement.leftJob.plan F =
      releaseReplicaInteriorBankCost CyclicRecoveryPlacement.leftJob.plan S ∧
    releaseReplicaInteriorBankCost CyclicRecoveryPlacement.rightJob.plan F =
      releaseReplicaInteriorBankCost CyclicRecoveryPlacement.rightJob.plan S := by
  exact ⟨releaseReplicaInteriorBankCost_eq_of_disposable_frame _ _ S F h.disposable_left_frame,
    releaseReplicaInteriorBankCost_eq_of_disposable_frame _ _ S F h.disposable_right_frame⟩

/-- Preparing masks and reversing the RHS leaves every disposable native port
unchanged; these ports are shared controls, not the consumed RHS queue. -/
theorem prepareRetainedReplicaRecoveryState_disposable_frame {T : ℕ}
    (R : ReplicaHaloProblem s) (job : CachedReplicaPassPlacement T) (S : Stacks T A)
    (i : Fin 117) (hi : i ∈ replicaCouplingNativeIndices) :
    (prepareRetainedReplicaRecoveryState R job S).R (job.plan.solver (weightCacheCoreReg i)) =
      S.R (job.plan.solver (weightCacheCoreReg i)) := by
  have hn : i ≠ 93 ∧ i ≠ 110 := by simpa [replicaCouplingNativeIndices] using hi
  have h93 : job.plan.solver (weightCacheCoreReg i) ≠ job.coupling.bank 93 := by
    rw [←job.coupling.bank_native]
    apply job.coupling.bank_injective.ne
    intro he
    apply hn.1
    exact Fin.ext (congrArg (fun j : Fin 168 => j.val) he)
  have hoff (j : Fin 168) (hj : 117 ≤ j.val) :
      job.plan.solver (weightCacheCoreReg i) ≠ job.coupling.bank j := by
    rw [←job.coupling.bank_native]
    apply job.coupling.bank_injective.ne
    intro he
    have hv := congrArg Fin.val he
    have hh := i.isLt
    dsimp only [Fin.castLE] at hv
    omega
  simp only [prepareRetainedReplicaRecoveryState,couplingMasksState,
    Function.update_of_ne h93,Function.update_of_ne (hoff 159 (by decide)),
    Function.update_of_ne (hoff 161 (by decide))]

theorem prepareCyclicRecoveryCouplingState_disposable_frame
    (H K : ReplicaHaloProblem s) (S : Stacks 840 A) (i : Fin 117)
    (hi : i ∈ replicaCouplingNativeIndices) :
    (prepareCyclicRecoveryCouplingState H K S).R
        (CyclicRecoveryPlacement.leftJob.plan.solver (weightCacheCoreReg i)) =
      S.R (CyclicRecoveryPlacement.leftJob.plan.solver (weightCacheCoreReg i)) ∧
    (prepareCyclicRecoveryCouplingState H K S).R
        (CyclicRecoveryPlacement.rightJob.plan.solver (weightCacheCoreReg i)) =
      S.R (CyclicRecoveryPlacement.rightJob.plan.solver (weightCacheCoreReg i)) := by
  constructor
  · unfold prepareCyclicRecoveryCouplingState
    rw [prepareRetainedReplicaRecoveryState_frame K CyclicRecoveryPlacement.rightJob _ _
      (CyclicRecoveryPlacement.jobs_disjoint _ (.solver _))]
    exact prepareRetainedReplicaRecoveryState_disposable_frame H _ S i hi
  · unfold prepareCyclicRecoveryCouplingState
    rw [prepareRetainedReplicaRecoveryState_disposable_frame K _ _ i hi]
    apply prepareRetainedReplicaRecoveryState_frame H CyclicRecoveryPlacement.leftJob S
    intro hk
    exact CyclicRecoveryPlacement.jobs_disjoint _ hk (.solver _)

private theorem projection_native_frame (H K : ReplicaHaloProblem s) (S : Stacks 840 A)
    (solveTail rows : List (Fin (A+4))) (k : Fin 840)
    (hoff : ∀ i : Fin 240, k ≠ CyclicRecoveryPlacement.bank i) :
    (placedNativeCyclicBoundaryBatchState (cyclicRecoveryMaskState H K S) solveTail rows).R k = S.R k := by
  simp only [placedNativeCyclicBoundaryBatchState,cyclicRecoveryMaskState,
    Function.update_of_ne (hoff 224),Function.update_of_ne (hoff 132),
    Function.update_of_ne (hoff 238),Function.update_of_ne (hoff 239)]

/-- The complete cursor base is mask setup, boundary projection, and coupling
preparation. All three preserve the original disposable-bank cleanup cost. -/
theorem CyclicRecoveryCouplingCursor.cleanup_from_input
    {H K : ReplicaHaloProblem s} {S F : Stacks 840 A}
    (solveTail rows : List (Fin (A+4)))
    (h : CyclicRecoveryCouplingCursor H K buffersL buffersR done todo tail rhsL rhsR rawL rawR pageL pageR
      (prepareCyclicRecoveryCouplingState H K
        (placedNativeCyclicBoundaryBatchState (cyclicRecoveryMaskState H K S) solveTail rows)) F) :
    releaseReplicaInteriorBankCost CyclicRecoveryPlacement.leftJob.plan F =
      releaseReplicaInteriorBankCost CyclicRecoveryPlacement.leftJob.plan S ∧
    releaseReplicaInteriorBankCost CyclicRecoveryPlacement.rightJob.plan F =
      releaseReplicaInteriorBankCost CyclicRecoveryPlacement.rightJob.plan S := by
  constructor
  · apply releaseReplicaInteriorBankCost_eq_of_disposable_frame _ _ S F
    intro i hi
    rw [h.disposable_left_frame i hi,
      (prepareCyclicRecoveryCouplingState_disposable_frame H K _ i hi).1]
    exact projection_native_frame H K S solveTail rows _
      (fun j => CyclicRecoveryPlacement.native_left_disjoint j _ (.solver _))
  · apply releaseReplicaInteriorBankCost_eq_of_disposable_frame _ _ S F
    intro i hi
    rw [h.disposable_right_frame i hi,
      (prepareCyclicRecoveryCouplingState_disposable_frame H K _ i hi).2]
    exact projection_native_frame H K S solveTail rows _
      (fun j => CyclicRecoveryPlacement.native_right_disjoint j _ (.solver _))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
