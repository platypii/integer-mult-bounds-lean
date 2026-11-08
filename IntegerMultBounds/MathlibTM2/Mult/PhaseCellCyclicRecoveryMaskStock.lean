module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryMasks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryMaskStock

/-! The shared mask setup is closed native work. Its reserve is paid once
for the geometry, independently of the number of RHS replicas. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem cyclicRecoveryMasks_native {Q A : ℕ} {P U : Type} :
    mnNativePushBound (replicaBoundaryMaskPush (Q := Q) (A := A) (U := U))
      (cyclicRecoveryMasks (P := P) (Q := Q) (A := A) (U := U)) :=
  ⟨placedReplicaBoundaryMask_native _ _,placedReplicaBoundaryMask_native _ _⟩

def cyclicRecoveryMasksWorkspace {s Q A : ℕ} {U : Type} (H K : ReplicaHaloProblem s) : ℕ :=
  replicaBoundaryMaskPush (Q := Q) (A := A) (U := U)*
    (placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K)

theorem cyclicRecoveryMasks_exec_within_of_exec {s Q A : ℕ} {P U : Type}
    {body : P → Pr P 840 Q A U} (H K : ReplicaHaloProblem s)
    {v vf : HS 840 Q A U} {S F : Stacks 840 A} {steps : ℕ}
    (he : Exec body cyclicRecoveryMasks (mk v S) steps (mk vf F))
    (htime : steps ≤ placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      cyclicRecoveryMasksWorkspace (Q := Q) (A := A) (U := U) H K) depth
      cyclicRecoveryMasks (mk v S) steps (mk vf F) := by
  apply mn_native_exec_within he _ cyclicRecoveryMasks_native depth _
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ htime) _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
