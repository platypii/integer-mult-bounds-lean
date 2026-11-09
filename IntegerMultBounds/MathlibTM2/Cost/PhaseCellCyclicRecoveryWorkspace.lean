module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvedCyclicRecovery

/-! Actual cyclic recovery separates shared mask/coupling scratch from row traffic.
Preparation copies are included in the replica term, even at zero loop count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s Q A : ℕ} [NeZero s] {U : Type}

noncomputable def cyclicRecoveryPreparationSharedWorkspace (H K : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) : ℕ :=
  mnProgPush (initializeCouplingMasks true (P := Empty) (Q := Q) (A := A) (U := U))*
    (initializeRecoveryMasksCost H.metadataWidth H.span H.band+
      initializeRecoveryMasksCost K.metadataWidth K.span K.band)+
    (cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) H hQ+
      cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) K hQ)+32

theorem preparedProjectedCyclicRecoveryWorkspace_eq_shared_add (H K : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (replicas : ℕ)
    (hH : H.Fs.length = replicas) (hK : K.Fs.length = replicas) :
    preparedProjectedCyclicRecoveryWorkspace (A := A) (U := U) H K replicas hQ =
      cyclicRecoveryPreparationSharedWorkspace (A := A) (U := U) H K hQ+
        replicas*(32*(H.span*H.wordWidth)+32*(K.span*K.wordWidth)+84) := by
  unfold preparedProjectedCyclicRecoveryWorkspace replicaRecoveryPreparationWorkspace
    cyclicRecoveryPreparationSharedWorkspace reverseCopyRowsCost
  rw [hH,hK]
  ring

noncomputable def solvedCyclicRecoverySharedWorkspace (H K : ReplicaHaloProblem s)
    (N n w : ℕ) (hQ : SS.states ≤ Q) : ℕ :=
  cyclicRecoveryMasksWorkspace (Q := Q) (A := A) (U := U) H K+
    max (nativeCyclicBoundaryBatchWorkspace 0 N n w)
      (cyclicRecoveryPreparationSharedWorkspace (A := A) (U := U) H K hQ)

private theorem max_replica_reserves_le (base x y replicas volume left right : ℕ) :
    base+max (x+replicas*(volume+8))
      (replicas*volume+(y+replicas*(32*left+32*right+84))) ≤
      base+max x y+replicas*(volume+32*left+32*right+84) := by
  have hx := le_max_left x y
  have hy := le_max_right x y
  apply (Nat.add_le_add_left (max_le ?_ ?_) base).trans_eq (Nat.add_assoc _ _ _).symm
  · nlinarith only [hx,Nat.zero_le (replicas*left),Nat.zero_le (replicas*right)]
  · nlinarith only [hy]

theorem solvedCyclicRecoveryWorkspace_le_shared_add (H K : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (replicas N n w : ℕ)
    (hH : H.Fs.length = replicas) (hK : K.Fs.length = replicas) :
    solvedCyclicRecoveryWorkspace (A := A) (U := U) H K replicas N n w hQ ≤
      solvedCyclicRecoverySharedWorkspace (A := A) (U := U) H K N n w hQ+
        replicas*(n*w+32*(H.span*H.wordWidth)+32*(K.span*K.wordWidth)+84) := by
  have hnative : nativeCyclicBoundaryBatchWorkspace replicas N n w =
      nativeCyclicBoundaryBatchWorkspace 0 N n w+replicas*(n*w+8) := by
    unfold nativeCyclicBoundaryBatchWorkspace
    ring
  have hprep := preparedProjectedCyclicRecoveryWorkspace_eq_shared_add (A := A) (U := U) H K hQ replicas hH hK
  simpa only [solvedCyclicRecoveryWorkspace,solvedCyclicRecoverySharedWorkspace,hnative,hprep] using
    max_replica_reserves_le
      (cyclicRecoveryMasksWorkspace (Q := Q) (A := A) (U := U) H K)
      (nativeCyclicBoundaryBatchWorkspace 0 N n w)
      (cyclicRecoveryPreparationSharedWorkspace (A := A) (U := U) H K hQ)
      replicas (n*w) (H.span*H.wordWidth) (K.span*K.wordWidth)

end IntegerMultBounds.MathlibTM2.Cost
