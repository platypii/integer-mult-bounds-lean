module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCyclicRecoveryCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorResumeReady

/-! Recovery preparation changes coupling masks and the temporary RHS loader.
The retained peripheral state for the second interior pass survives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T A : ℕ} [NeZero s]

theorem prepareRetainedReplicaRecoveryState_streams (H : ReplicaHaloProblem s)
    (job : CachedReplicaPassPlacement T) (S : Stacks T A) :
    (prepareRetainedReplicaRecoveryState H job S).inp = S.inp ∧
      (prepareRetainedReplicaRecoveryState H job S).out = S.out ∧
      (prepareRetainedReplicaRecoveryState H job S).L = S.L := ⟨rfl,rfl,rfl⟩

theorem ReplicaInteriorResumeReady.prepare_coupling {H : ReplicaHaloProblem s}
    {job : CachedReplicaPassPlacement T} {buffers : ReplicaLoopBuffers A} {S : Stacks T A}
    (h : ReplicaInteriorResumeReady H job buffers S) :
    ReplicaInteriorResumeReady H job buffers (prepareRetainedReplicaRecoveryState H job S) := by
  have hf (k : Fin T) (h93 : k ≠ job.coupling.bank 93)
      (h159 : k ≠ job.coupling.bank 159) (h161 : k ≠ job.coupling.bank 161) :
      (prepareRetainedReplicaRecoveryState H job S).R k = S.R k := by
    simpa only [prepareRetainedReplicaRecoveryState,Function.update_of_ne h93] using
      couplingMasksState_frame job.coupling.bank true s H.t H.band H.origin
        (H.origin+H.span) H.origin H.span S k h159 h161
  apply h.transport (job' := job) (F := prepareRetainedReplicaRecoveryState H job S) rfl rfl
  · intro i _
    exact hf _ (job.coupling.bank_gather_disjoint 93 i).symm
      (job.coupling.bank_gather_disjoint 159 i).symm (job.coupling.bank_gather_disjoint 161 i).symm
  · intro i hi
    exact hf _ (job.coupling.bank_reserved_disjoint 93 i hi).symm
      (job.coupling.bank_reserved_disjoint 159 i hi).symm (job.coupling.bank_reserved_disjoint 161 i hi).symm
  · intro i; rfl
  · exact hf _ (job.bank_output 93).symm (job.bank_output 159).symm (job.bank_output 161).symm

theorem prepareCyclicRecoveryCoupling_resume {H K : ReplicaHaloProblem s}
    {buffersL buffersR : ReplicaLoopBuffers A} {S : Stacks 840 A}
    (hL : ReplicaInteriorResumeReady H CyclicRecoveryPlacement.leftJob buffersL S)
    (hR : ReplicaInteriorResumeReady K CyclicRecoveryPlacement.rightJob buffersR S) :
    ReplicaInteriorResumeReady H CyclicRecoveryPlacement.leftJob buffersL (prepareCyclicRecoveryCouplingState H K S) ∧
      ReplicaInteriorResumeReady K CyclicRecoveryPlacement.rightJob buffersR (prepareCyclicRecoveryCouplingState H K S) := by
  let J := prepareRetainedReplicaRecoveryState H CyclicRecoveryPlacement.leftJob S
  let F := prepareRetainedReplicaRecoveryState K CyclicRecoveryPlacement.rightJob J
  have hLJ : ReplicaInteriorResumeReady H CyclicRecoveryPlacement.leftJob buffersL J := hL.prepare_coupling
  have hRJ : ReplicaInteriorResumeReady K CyclicRecoveryPlacement.rightJob buffersR J := by
    apply hR.of_frame (F := J) rfl rfl
    intro k hk
    exact ⟨rfl,prepareRetainedReplicaRecoveryState_frame H CyclicRecoveryPlacement.leftJob S k
      (fun hl => CyclicRecoveryPlacement.jobs_disjoint k hl hk)⟩
  constructor
  · change ReplicaInteriorResumeReady H CyclicRecoveryPlacement.leftJob buffersL F
    have hstreams := prepareRetainedReplicaRecoveryState_streams K CyclicRecoveryPlacement.rightJob J
    apply hLJ.of_frame (F := F) hstreams.1 hstreams.2.1
    intro k hk
    exact ⟨congrFun hstreams.2.2 k,prepareRetainedReplicaRecoveryState_frame K CyclicRecoveryPlacement.rightJob J k
      (CyclicRecoveryPlacement.jobs_disjoint k hk)⟩
  · exact hRJ.prepare_coupling

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
