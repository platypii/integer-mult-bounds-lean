module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCyclicReplicaBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCallerReady
public import IntegerMultBounds.MathlibTM2.Host.ExtendStacks

/-! The actual cyclic boundary caller executes in the recovery layout by a
single injective lift. Its time and original output state are preserved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicReplicaPlacement
local notation "extendCaller" => CyclicRecoveryPlacement.extend
variable {Q A : ℕ} {P U : Type}

def cyclicReplicaCallerBody (body : P → Pr P 117 Q A U) : P → Pr P 834 Q A U :=
  embTab factorReg (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg
    (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body)))))))

noncomputable def liftedCachedCyclicReplicaBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 840 Q A U :=
  embProg extendCaller id (cachedCyclicReplicaBatch hR hQ)

theorem cachedCyclicReplicaBatch_exec_lift (body : P → Pr P 117 Q A U)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (v vf : HS 834 Q A U) (S F : Stacks 834 A) (steps : ℕ)
    (hex : Exec (cyclicReplicaCallerBody body) (cachedCyclicReplicaBatch hR hQ) (mk v S) steps (mk vf F))
    (w : HS 840 Q A U) (hw : embDn extendCaller w = v) :
    ∃ wf, embDn extendCaller wf = vf ∧ wf.user = vf.user ∧
      Exec (embTab extendCaller (cyclicReplicaCallerBody body)) (liftedCachedCyclicReplicaBatch hR hQ)
        (mk w (extendStacks (by decide : 834 ≤ 840) S)) steps
        (mk wf (extendStacks (by decide : 834 ≤ 840) F)) := by
  exact exec_extendStacks (by decide : 834 ≤ 840) (ι := id) (fun _ => rfl) hex w hw

theorem liftedCyclicRecoveryCallerReady {s : ℕ} [NeZero s] (H K : ReplicaHaloProblem s)
    (buffersL buffersR : ReplicaLoopBuffers A) (S₁ S₂ producer F : Stacks 834 A)
    (Cs Ds : List (ZMod s → GaussianInt))
    (postL : CachedReplicaPassPost H left buffersL S₁ producer Cs)
    (postR : CachedReplicaPassPost K right buffersR S₂ producer Ds)
    (hbankL : embStk left.coupling.bank F = embStk left.coupling.bank producer)
    (hbankR : embStk right.coupling.bank F = embStk right.coupling.bank producer)
    (headersL : ReplicaRecoveryRhsHeaders H left.plan.gather buffersL F)
    (headersR : ReplicaRecoveryRhsHeaders K right.plan.gather buffersR F) :
    RetainedReplicaRecoveryReady H CyclicRecoveryPlacement.leftJob buffersL
      (S₁.R (left.coupling.bank 138)) (extendStacks (by decide : 834 ≤ 840) F) ∧
    RetainedReplicaRecoveryReady K CyclicRecoveryPlacement.rightJob buffersR
      (S₂.R (right.coupling.bank 138)) (extendStacks (by decide : 834 ≤ 840) F) := by
  apply cyclicRecoveryCallerReady H K buffersL buffersR S₁ S₂ producer Cs Ds postL postR
    (extendStacks (by decide : 834 ≤ 840) F)
  · simpa only [CyclicRecoveryPlacement.extend,embStk_extendStacks] using hbankL
  · simpa only [CyclicRecoveryPlacement.extend,embStk_extendStacks] using hbankR
  · simpa only [CyclicRecoveryPlacement.extend,embStk_extendStacks] using headersL
  · simpa only [CyclicRecoveryPlacement.extend,embStk_extendStacks] using headersR

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
