module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCallerReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryMaskReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedNativeCyclicBoundaryBatch

/-! Recovery contracts survive native mask setup and the complete boundary
projection, by the same ownership frame used for the actual caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

theorem cyclicRecoveryMaskState_recoveryReady (H K : ReplicaHaloProblem s)
    (buffersL buffersR : ReplicaLoopBuffers A) (pageL pageR : List (Fin (A+4))) (S : Stacks 840 A)
    (hl : RetainedReplicaRecoveryReady H CyclicRecoveryPlacement.leftJob buffersL pageL S)
    (hr : RetainedReplicaRecoveryReady K CyclicRecoveryPlacement.rightJob buffersR pageR S) :
    RetainedReplicaRecoveryReady H CyclicRecoveryPlacement.leftJob buffersL pageL (cyclicRecoveryMaskState H K S) ∧
    RetainedReplicaRecoveryReady K CyclicRecoveryPlacement.rightJob buffersR pageR (cyclicRecoveryMaskState H K S) := by
  constructor
  · apply hl.of_owns_frame (G := cyclicRecoveryMaskState H K S) rfl rfl
    intro k hk
    refine ⟨rfl,?_⟩
    simp only [cyclicRecoveryMaskState,
      Function.update_of_ne (CyclicRecoveryPlacement.native_left_disjoint 238 k hk),
      Function.update_of_ne (CyclicRecoveryPlacement.native_left_disjoint 239 k hk)]
  · apply hr.of_owns_frame (G := cyclicRecoveryMaskState H K S) rfl rfl
    intro k hk
    refine ⟨rfl,?_⟩
    simp only [cyclicRecoveryMaskState,
      Function.update_of_ne (CyclicRecoveryPlacement.native_right_disjoint 238 k hk),
      Function.update_of_ne (CyclicRecoveryPlacement.native_right_disjoint 239 k hk)]

theorem placedNativeCyclicBoundaryBatchState_recoveryReady (H K : ReplicaHaloProblem s)
    (buffersL buffersR : ReplicaLoopBuffers A) (pageL pageR : List (Fin (A+4))) (S : Stacks 840 A)
    (tail output : List (Fin (A+4)))
    (hl : RetainedReplicaRecoveryReady H CyclicRecoveryPlacement.leftJob buffersL pageL S)
    (hr : RetainedReplicaRecoveryReady K CyclicRecoveryPlacement.rightJob buffersR pageR S) :
    RetainedReplicaRecoveryReady H CyclicRecoveryPlacement.leftJob buffersL pageL
      (placedNativeCyclicBoundaryBatchState S tail output) ∧
    RetainedReplicaRecoveryReady K CyclicRecoveryPlacement.rightJob buffersR pageR
      (placedNativeCyclicBoundaryBatchState S tail output) := by
  constructor
  · apply hl.of_owns_frame (G := placedNativeCyclicBoundaryBatchState S tail output) rfl rfl
    intro k hk
    refine ⟨rfl,?_⟩
    simp only [placedNativeCyclicBoundaryBatchState,
      Function.update_of_ne (CyclicRecoveryPlacement.native_left_disjoint 224 k hk),
      Function.update_of_ne (CyclicRecoveryPlacement.native_left_disjoint 132 k hk)]
  · apply hr.of_owns_frame (G := placedNativeCyclicBoundaryBatchState S tail output) rfl rfl
    intro k hk
    refine ⟨rfl,?_⟩
    simp only [placedNativeCyclicBoundaryBatchState,
      Function.update_of_ne (CyclicRecoveryPlacement.native_right_disjoint 224 k hk),
      Function.update_of_ne (CyclicRecoveryPlacement.native_right_disjoint 132 k hk)]

theorem cyclicRecoveryMasks_ready_exec {Q q w W N : ℕ} {P U : Type} {body : P → Pr P 840 Q A U}
    (H K : ReplicaHaloProblem s) (buffersL buffersR : ReplicaLoopBuffers A)
    (pageL pageR : List (Fin (A+4))) (v : HS 840 Q A U) (S : Stacks 840 A)
    (hl : RetainedReplicaRecoveryReady H CyclicRecoveryPlacement.leftJob buffersL pageL S)
    (hr : RetainedReplicaRecoveryReady K CyclicRecoveryPlacement.rightJob buffersR pageR S)
    (h239 : S.R (CyclicRecoveryPlacement.bank 239) = []) (h238 : S.R (CyclicRecoveryPlacement.bank 238) = [])
    (hwork : NativeBoundaryUnfoldWorkspace N
      (embStk CyclicReplicaPlacement.factorReg (embStk CyclicRecoveryPlacement.extend S)))
    (hready : BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 234))
      (embStk CyclicReplicaPlacement.factorReg (embStk CyclicRecoveryPlacement.extend S)))) q w W N) :
    let F := cyclicRecoveryMaskState H K S
    ∃ vf m, vf.user = v.user ∧ m ≤ placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K ∧
      Exec body cyclicRecoveryMasks (mk v S) m (mk vf F) ∧
      NativeBoundaryUnfoldWorkspace N (embStk (Fin.castLE (by decide : 234 ≤ 240)) (embStk CyclicRecoveryPlacement.bank F)) ∧
      BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240))
        (embStk CyclicRecoveryPlacement.bank F))) q w W N ∧
      embStk CyclicRecoveryPlacement.extend F = embStk CyclicRecoveryPlacement.extend S := by
  have hviewL : embStk cyclicRecoveryLeftBank S = embStk CyclicRecoveryPlacement.leftJob.coupling.bank S :=
    (CyclicReplicaPlacement.left.reindex_bank_view CyclicRecoveryPlacement.extend (Fin.castLE_injective _) S).symm
  have hviewR : embStk cyclicRecoveryRightBank S = embStk CyclicRecoveryPlacement.rightJob.coupling.bank S :=
    (CyclicReplicaPlacement.right.reindex_bank_view CyclicRecoveryPlacement.extend (Fin.castLE_injective _) S).symm
  apply cyclicRecoveryMasks_prepare_exec (body := body) H K v S
    (by rw [hviewL]; exact hl.metadata) (by rw [hviewR]; exact hr.metadata)
    ?_ ?_ h239 h238 hwork hready
  · intro i hi
    have hh := congrArg (fun F : Stacks 168 A => F.R i) hviewL
    apply hh.trans
    have hc := (hl.ready.clean (⟨i.val,by omega⟩ : Fin 64)).2
    simpa [embStk,groupReg,intervalPageReg,mul] using hc
  · intro i hi
    have hh := congrArg (fun F : Stacks 168 A => F.R i) hviewR
    apply hh.trans
    have hc := (hr.ready.clean (⟨i.val,by omega⟩ : Fin 64)).2
    simpa [embStk,groupReg,intervalPageReg,mul] using hc

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
