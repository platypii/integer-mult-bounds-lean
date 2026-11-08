module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryMasks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNativeBoundaryUnfoldWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolveReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPassPost

/-! One mask setup transports the actual old caller's workspace and factor
readiness into the native recovery view, without moving any factor tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "recoveryBank" => CyclicRecoveryPlacement.bank
local notation "extendCaller" => CyclicRecoveryPlacement.extend
local notation "oldFactor" => CyclicReplicaPlacement.factorReg
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 840 Q A U}

theorem cyclicRecoveryMaskState_workspace {s N : ℕ} (H K : ReplicaHaloProblem s) (S : Stacks 840 A)
    (hwork : NativeBoundaryUnfoldWorkspace N (embStk oldFactor (embStk extendCaller S))) :
    NativeBoundaryUnfoldWorkspace N (embStk (Fin.castLE (by decide : 234 ≤ 240))
      (embStk recoveryBank (cyclicRecoveryMaskState H K S))) := by
  rw [CyclicRecoveryPlacement.bank_old_view,cyclicRecoveryMaskState_old]
  exact hwork

theorem cyclicRecoveryMaskState_solveReady {s q w W N : ℕ} (H K : ReplicaHaloProblem s) (S : Stacks 840 A)
    (hready : BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 234))
      (embStk oldFactor (embStk extendCaller S)))) q w W N) :
    BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240))
      (embStk recoveryBank (cyclicRecoveryMaskState H K S)))) q w W N := by
  rw [CyclicRecoveryPlacement.bank_core_view,cyclicRecoveryMaskState_old]
  exact hready

theorem cyclicRecoveryMasks_prepare_exec {s q w W N : ℕ} [NeZero s]
    (H K : ReplicaHaloProblem s) (v : HS 840 Q A U) (S : Stacks 840 A)
    (hl : CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
      (embStk cyclicRecoveryLeftBank S))
    (hr : CouplingIntervalMetadata K.metadataWidth s K.t K.band K.origin (K.origin+K.span) K.origin K.span
      (embStk cyclicRecoveryRightBank S))
    (hlblank : ∀ i : Fin 168, i.val < 32 → S.R (cyclicRecoveryLeftBank i) = [])
    (hrblank : ∀ i : Fin 168, i.val < 32 → S.R (cyclicRecoveryRightBank i) = [])
    (h239 : S.R (recoveryBank 239) = []) (h238 : S.R (recoveryBank 238) = [])
    (hwork : NativeBoundaryUnfoldWorkspace N (embStk oldFactor (embStk extendCaller S)))
    (hready : BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 234))
      (embStk oldFactor (embStk extendCaller S)))) q w W N) :
    let F := cyclicRecoveryMaskState H K S
    ∃ vf m, vf.user = v.user ∧ m ≤ placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K ∧
      Exec body cyclicRecoveryMasks (mk v S) m (mk vf F) ∧
      NativeBoundaryUnfoldWorkspace N (embStk (Fin.castLE (by decide : 234 ≤ 240)) (embStk recoveryBank F)) ∧
      BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240))
        (embStk recoveryBank F))) q w W N ∧
      embStk extendCaller F = embStk extendCaller S := by
  obtain ⟨vf,m,hu,hm,he,hold⟩ := cyclicRecoveryMasks_exec (body := body) H K v S
    hl hr hlblank hrblank h239 h238
  exact ⟨vf,m,hu,hm,he,cyclicRecoveryMaskState_workspace H K S hwork,
    cyclicRecoveryMaskState_solveReady H K S hready,hold⟩

/-- The actual first-pass certificates and retained bank views supply the mask
metadata and workspace; neither is a new numerical supplier. -/
theorem cyclicRecoveryMasks_cached_exec {s q w W N : ℕ} [NeZero s]
    (H K : ReplicaHaloProblem s) (leftBuffers rightBuffers : ReplicaLoopBuffers A)
    (S₀ S₁ producer : Stacks 834 A) (Cs Ds : List (ZMod s → GaussianInt))
    (hl : CachedReplicaPassPost H CyclicReplicaPlacement.left leftBuffers S₀ producer Cs)
    (hr : CachedReplicaPassPost K CyclicReplicaPlacement.right rightBuffers S₁ producer Ds)
    (v : HS 840 Q A U) (S : Stacks 840 A)
    (hleft : embStk cyclicRecoveryLeftBank S = embStk CyclicReplicaPlacement.left.coupling.bank producer)
    (hright : embStk cyclicRecoveryRightBank S = embStk CyclicReplicaPlacement.right.coupling.bank producer)
    (h239 : S.R (recoveryBank 239) = []) (h238 : S.R (recoveryBank 238) = [])
    (hwork : NativeBoundaryUnfoldWorkspace N (embStk oldFactor (embStk extendCaller S)))
    (hready : BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 234))
      (embStk oldFactor (embStk extendCaller S)))) q w W N) :
    let F := cyclicRecoveryMaskState H K S
    ∃ vf m, vf.user = v.user ∧ m ≤ placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K ∧
      Exec body cyclicRecoveryMasks (mk v S) m (mk vf F) ∧
      NativeBoundaryUnfoldWorkspace N (embStk (Fin.castLE (by decide : 234 ≤ 240)) (embStk recoveryBank F)) ∧
      BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240))
        (embStk recoveryBank F))) q w W N ∧
      embStk extendCaller F = embStk extendCaller S := by
  apply cyclicRecoveryMasks_prepare_exec (body := body) H K v S
    (by rw [hleft]; exact hl.metadata) (by rw [hright]; exact hr.metadata)
    ?_ ?_ h239 h238 hwork hready
  · intro i hi
    have hh := congrArg (fun R => R.R i) hleft
    exact hh.trans (hl.maskBlank i hi)
  · intro i hi
    have hh := congrArg (fun R => R.R i) hright
    exact hh.trans (hr.maskBlank i hi)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
