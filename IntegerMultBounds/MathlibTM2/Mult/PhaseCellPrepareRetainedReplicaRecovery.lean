module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedReplicaRecoveryMasks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedReplicaRecoveryRhs
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget

/-! The recovery phase prepares selectors and the original RHS queue once,
starting from the actual cached first-pass endpoint. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def prepareRetainedReplicaRecovery (job : CachedReplicaPassPlacement T) : Pr P T Q A U :=
  .seq (placedInitializeCouplingMasks job.coupling.bank true)
    (prepareReversedReplicaRecoveryRhs job.plan (job.coupling.bank 93))

def prepareRetainedReplicaRecoveryState (H : ReplicaHaloProblem s)
    (job : CachedReplicaPassPlacement T) (F : Stacks T A) : Stacks T A :=
  let G := couplingMasksState job.coupling.bank true s H.t H.band H.origin
    (H.origin+H.span) H.origin H.span F
  {G with R := (Function.update G.R (job.coupling.bank 93)
    (H.Fs.reverse.flatMap (fun C => cstream A H.wordWidth
      (packedInterval H.origin H.span C))++G.R (job.coupling.bank 93)))}

theorem prepareRetainedReplicaRecovery_exec_within (H : ReplicaHaloProblem s)
    (job : CachedReplicaPassPlacement T) (buffers : ReplicaLoopBuffers A)
    (pageTail : List (Fin (A+4))) (F : Stacks T A)
    (state : RetainedReplicaRecoveryReady H job buffers pageTail F)
    (v : HS T Q A U) (depth : ℕ) :
    let G := prepareRetainedReplicaRecoveryState H job F
    ∃ vf m, vf.user = v.user ∧
      m ≤ initializeRecoveryMasksCost H.metadataWidth H.span H.band+
        reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+
        (mnProgPush (initializeCouplingMasks true (P := Empty) (Q := Q) (A := A) (U := U))*
          initializeRecoveryMasksCost H.metadataWidth H.span H.band+
          2*reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)))
        depth (prepareRetainedReplicaRecovery job) (mk v F) m (mk vf G) ∧
      ReplicaRecoveryRhsHeaders H job.plan.gather buffers G ∧
      RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
        H.origin (H.origin+H.span) buffers.rhsTail
        (embStk weightCacheCoreReg (embStk job.plan.solver G)) := by
  dsimp only
  let M := couplingMasksState job.coupling.bank true s H.t H.band H.origin
    (H.origin+H.span) H.origin H.span F
  obtain ⟨vi,mi,hu₁,hm₁,he₁,hr₁⟩ := retainedReplicaRecoveryMasks_exec_within (body := body)
    H job buffers pageTail F state v
  have hheaders : ReplicaRecoveryRhsHeaders H job.plan.gather buffers M := by
    apply state.recoveryRhs.of_frame H job.plan.gather buffers F M
    intro k
    exact couplingMasksState_frame job.coupling.bank true s H.t H.band H.origin
      (H.origin+H.span) H.origin H.span F (job.plan.gather k)
      (job.coupling.bank_gather_disjoint 159 k).symm
      (job.coupling.bank_gather_disjoint 161 k).symm
  obtain ⟨vf,mf,hu₂,hm₂,he₂,hh₂,hr₂⟩ := prepareRetainedReplicaRecoveryRhs_exec_within
    (body := body) H job.plan job.coupling buffers buffers.rhsTail vi M hheaders hr₁ depth
  refine ⟨vf,mi+mf,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,?_,hh₂,hr₂⟩
  exact execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ (he₁ depth) he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
