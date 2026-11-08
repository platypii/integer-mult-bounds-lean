module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedRecoveryCouplingReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryJobs

/-! Both recovery banks are prepared from actual first-pass certificates. Each
preparation retains the other's cache and the complete native boundary bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 840 Q A U}

theorem prepareRetainedReplicaRecoveryState_frame (H : ReplicaHaloProblem s)
    (job : CachedReplicaPassPlacement T) (S : Stacks T A) (k : Fin T) (hk : ¬job.Owns k) :
    (prepareRetainedReplicaRecoveryState H job S).R k = S.R k := by
  have hoff (i : Fin 168) : k ≠ job.coupling.bank i := by
    intro he; apply hk; rw [he]; exact .bank i
  simp [prepareRetainedReplicaRecoveryState,couplingMasksState,hoff]

theorem prepareRetainedReplicaRecoveryState_view (H : ReplicaHaloProblem s)
    (job : CachedReplicaPassPlacement T) (S : Stacks T A) {N : ℕ} (e : Fin N → Fin T)
    (hoff : ∀ i, ¬job.Owns (e i)) :
    embStk e (prepareRetainedReplicaRecoveryState H job S) = embStk e S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  exact prepareRetainedReplicaRecoveryState_frame H job S (e i) (hoff i)

def replicaRecoveryPreparationWorkspace (H : ReplicaHaloProblem s) : ℕ :=
  mnProgPush (initializeCouplingMasks true (P := Empty) (Q := Q) (A := A) (U := U))*
    initializeRecoveryMasksCost H.metadataWidth H.span H.band+
      2*reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)

def replicaRecoveryPreparationCost (H : ReplicaHaloProblem s) : ℕ :=
  initializeRecoveryMasksCost H.metadataWidth H.span H.band+reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)

def prepareCyclicRecoveryCoupling : Pr P 840 Q A U :=
  .seq (prepareRetainedReplicaRecovery CyclicRecoveryPlacement.leftJob)
    (prepareRetainedReplicaRecovery CyclicRecoveryPlacement.rightJob)

def prepareCyclicRecoveryCouplingState (H K : ReplicaHaloProblem s) (S : Stacks 840 A) : Stacks 840 A :=
  prepareRetainedReplicaRecoveryState K CyclicRecoveryPlacement.rightJob
    (prepareRetainedReplicaRecoveryState H CyclicRecoveryPlacement.leftJob S)

theorem prepareCyclicRecoveryCoupling_exec_within (H K : ReplicaHaloProblem s)
    (buffersL buffersR : ReplicaLoopBuffers A) (pageL pageR : List (Fin (A+4))) (F : Stacks 840 A)
    (stateL : RetainedReplicaRecoveryReady H CyclicRecoveryPlacement.leftJob buffersL pageL F)
    (stateR : RetainedReplicaRecoveryReady K CyclicRecoveryPlacement.rightJob buffersR pageR F)
    (v : HS 840 Q A U) (depth : ℕ) :
    let G := prepareCyclicRecoveryCouplingState H K F
    ∃ vf m, vf.user = v.user ∧ m ≤ replicaRecoveryPreparationCost H+replicaRecoveryPreparationCost K ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+
        (replicaRecoveryPreparationWorkspace (Q := Q) (A := A) (U := U) H+
          replicaRecoveryPreparationWorkspace (Q := Q) (A := A) (U := U) K))
        depth prepareCyclicRecoveryCoupling (mk v F) m (mk vf G) ∧
      ReplicaRecoveryRhsHeaders H CyclicRecoveryPlacement.leftJob.plan.gather buffersL G ∧
      ReplicaRecoveryRhsHeaders K CyclicRecoveryPlacement.rightJob.plan.gather buffersR G ∧
      CachedRecoveryCouplingReady H buffersL.rhsTail pageL
        (embStk CyclicRecoveryPlacement.leftJob.coupling.bank G) ∧
      CachedRecoveryCouplingReady K buffersR.rhsTail pageR
        (embStk CyclicRecoveryPlacement.rightJob.coupling.bank G) := by
  dsimp only
  let J := prepareRetainedReplicaRecoveryState H CyclicRecoveryPlacement.leftJob F
  obtain ⟨vi,mi,hu₁,hm₁,he₁,hhL,hrL⟩ := prepareRetainedReplicaRecovery_exec_within (body := body)
    H CyclicRecoveryPlacement.leftJob buffersL pageL F stateL v depth
  have hcL := preparedRecoveryCouplingReady H CyclicRecoveryPlacement.leftJob buffersL pageL F stateL hrL
  have hframe (k : Fin 840) (hk : CyclicRecoveryPlacement.rightJob.Owns k) : J.L k = F.L k ∧ J.R k = F.R k := by
    refine ⟨rfl,prepareRetainedReplicaRecoveryState_frame H CyclicRecoveryPlacement.leftJob F k ?_⟩
    intro hl; exact CyclicRecoveryPlacement.jobs_disjoint k hl hk
  have hbankR := prepareRetainedReplicaRecoveryState_view H CyclicRecoveryPlacement.leftJob F
    CyclicRecoveryPlacement.rightJob.coupling.bank (fun i hl => CyclicRecoveryPlacement.jobs_disjoint _ hl (.bank i))
  have hheadersR : ReplicaRecoveryRhsHeaders K CyclicRecoveryPlacement.rightJob.plan.gather buffersR J := by
    apply stateR.recoveryRhs.of_frame K CyclicRecoveryPlacement.rightJob.plan.gather buffersR F J
    intro i; exact (hframe _ (.gather i)).2
  have stateRJ := stateR.of_bank_frame hbankR hheadersR
  obtain ⟨vf,mf,hu₂,hm₂,he₂,hhR,hrR⟩ := prepareRetainedReplicaRecovery_exec_within (body := body)
    K CyclicRecoveryPlacement.rightJob buffersR pageR J stateRJ vi depth
  have hcR := preparedRecoveryCouplingReady K CyclicRecoveryPlacement.rightJob buffersR pageR J stateRJ hrR
  have hframeR (k : Fin 840) (hk : CyclicRecoveryPlacement.leftJob.Owns k) :
      (prepareRetainedReplicaRecoveryState K CyclicRecoveryPlacement.rightJob J).R k = J.R k :=
    prepareRetainedReplicaRecoveryState_frame K CyclicRecoveryPlacement.rightJob J k
      (CyclicRecoveryPlacement.jobs_disjoint k hk)
  refine ⟨vf,mi+mf,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,?_,?_,hhR,?_,hcR⟩
  · exact execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ he₁ he₂
  · apply hhL.of_frame H CyclicRecoveryPlacement.leftJob.plan.gather buffersL J
    intro i; exact hframeR _ (.gather i)
  · have hview : embStk CyclicRecoveryPlacement.leftJob.coupling.bank
        (prepareRetainedReplicaRecoveryState K CyclicRecoveryPlacement.rightJob J) =
        embStk CyclicRecoveryPlacement.leftJob.coupling.bank J := by
      apply prepareRetainedReplicaRecoveryState_view
      intro i
      exact CyclicRecoveryPlacement.jobs_disjoint _ (.bank i)
    exact hview.symm ▸ hcL

theorem prepareCyclicRecoveryCouplingState_native (H K : ReplicaHaloProblem s) (S : Stacks 840 A) (i : Fin 240) :
    (prepareCyclicRecoveryCouplingState H K S).R (CyclicRecoveryPlacement.bank i) = S.R (CyclicRecoveryPlacement.bank i) := by
  have hnL : ¬CyclicRecoveryPlacement.leftJob.Owns (CyclicRecoveryPlacement.bank i) := by
    intro h; exact CyclicRecoveryPlacement.native_left_disjoint i _ h rfl
  have hnR : ¬CyclicRecoveryPlacement.rightJob.Owns (CyclicRecoveryPlacement.bank i) := by
    intro h; exact CyclicRecoveryPlacement.native_right_disjoint i _ h rfl
  unfold prepareCyclicRecoveryCouplingState
  rw [prepareRetainedReplicaRecoveryState_frame K _ _ _ hnR,
    prepareRetainedReplicaRecoveryState_frame H _ _ _ hnL]

theorem prepareRetainedReplicaRecoveryState_rhs (H : ReplicaHaloProblem s)
    (job : CachedReplicaPassPlacement T) (S : Stacks T A) :
    (prepareRetainedReplicaRecoveryState H job S).R (job.coupling.bank 93) =
      H.Fs.reverse.flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++S.R (job.coupling.bank 93) := by
  simp [prepareRetainedReplicaRecoveryState,couplingMasksState,job.coupling.bank_injective.eq_iff]

theorem prepareCyclicRecoveryCouplingState_rhs (H K : ReplicaHaloProblem s) (S : Stacks 840 A) :
    (prepareCyclicRecoveryCouplingState H K S).R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) =
      H.Fs.reverse.flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++S.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) ∧
    (prepareCyclicRecoveryCouplingState H K S).R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) =
      K.Fs.reverse.flatMap (fun C => cstream A K.wordWidth (packedInterval K.origin K.span C))++S.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) := by
  constructor
  · unfold prepareCyclicRecoveryCouplingState
    rw [prepareRetainedReplicaRecoveryState_frame K _ _ _ (CyclicRecoveryPlacement.jobs_disjoint _ (.bank 93)),
      prepareRetainedReplicaRecoveryState_rhs]
  · unfold prepareCyclicRecoveryCouplingState
    rw [prepareRetainedReplicaRecoveryState_rhs,prepareRetainedReplicaRecoveryState_frame H _ _ _]
    intro h
    exact CyclicRecoveryPlacement.jobs_disjoint _ h (.bank 93)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
