module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallReplicaBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaFactoryPublicationWidth
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Produce the canonical packed factory input by execution. The publication
width is generated in a disposable gather register, while retained masters and
the RHS source survive the existing structural installer. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 389 Q A U}

def prepareReplicaBoundaryFactory : Pr P 389 Q A U :=
  .seq generateReplicaFactoryPublicationWidth installReplicaBoundaryFactory

def preparedReplicaBoundaryFactoryInput (H : ReplicaHaloProblem s) (S : Stacks 389 A) : Stacks 389 A :=
  replicaBoundaryFactoryInstalled H
    {S with R := Function.update S.R 119 (List.replicate (publicationGeometryWidth H.t H.band) tick)}

def prepareReplicaBoundaryFactoryCost (H : ReplicaHaloProblem s) :=
  generatePublicationWidthCost H.t H.band+installReplicaBoundaryFactoryCost H

def prepareReplicaBoundaryFactoryWorkspace (H : ReplicaHaloProblem s) :=
  7*generatePublicationWidthCost H.t H.band+
    (2*replicaBoundaryFactoryMasterCost H+(8*H.origin+8*(H.origin+H.span)+24*publicationGeometryWidth H.t H.band+40))

theorem prepareReplicaBoundaryFactory_exec (H : ReplicaHaloProblem s) (buffers : ReplicaLoopBuffers A)
    (v : HS 389 Q A U) (S : Stacks 389 A)
    (headers : ReplicaLoopHeaders H replicaRecoveryCallerInterior.gather buffers S)
    (h119 : S.R 119 = [])
    (hblank : ∀ i, S.R (replicaRecoveryCallerFactoryReg i) = [])
    (hleft : ∀ i, S.L (replicaRecoveryCallerFactoryReg i) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareReplicaBoundaryFactoryCost H ∧
      embStk replicaRecoveryCallerFactoryReg (preparedReplicaBoundaryFactoryInput H S) =
        replicaBoundaryFactoryInput H (embStk replicaRecoveryCallerFactoryReg S) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+prepareReplicaBoundaryFactoryWorkspace H)
        depth prepareReplicaBoundaryFactory (mk v S) n (mk v' (preparedReplicaBoundaryFactoryInput H S)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generateReplicaFactoryPublicationWidth_exec (body := body)
    H buffers v S headers h119 depth
  let M : Stacks 389 A := {S with R := Function.update S.R 119 (List.replicate (publicationGeometryWidth H.t H.band) tick)}
  have hheadersM : ReplicaLoopHeaders H replicaRecoveryCallerInterior.gather buffers M := by
    apply headers.of_frame
    intro k h87 hk
    exact Function.update_of_ne (replicaRecoveryCallerInterior.gather_injective.ne hk) _ _
  obtain ⟨v₂,n₂,hu₂,hn₂,hview,he₂⟩ := installReplicaBoundaryFactory_exec (body := body)
    H buffers v₁ M hheadersM (by simp [M])
    (by
      intro i
      have hne : replicaRecoveryCallerFactoryReg i ≠ 119 := replicaRecoveryCallerFactoryReg_gather i 119
      change Function.update S.R 119 _ (replicaRecoveryCallerFactoryReg i) = []
      rw [Function.update_of_ne hne]
      exact hblank i)
    hleft depth
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,hview,mn_seq_within_add he₁ he₂⟩

theorem preparedReplicaBoundaryFactoryInput_gather (H : ReplicaHaloProblem s) (S : Stacks 389 A) :
    embStk replicaRecoveryCallerInterior.gather (preparedReplicaBoundaryFactoryInput H S) =
      embStk replicaRecoveryCallerInterior.gather
        {S with R := Function.update S.R 119 (List.replicate (publicationGeometryWidth H.t H.band) tick)} :=
  replicaBoundaryFactoryInstalled_gather H _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
