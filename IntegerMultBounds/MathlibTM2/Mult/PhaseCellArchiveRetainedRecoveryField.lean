module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedRecoveryCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaRecoveryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.StackResources
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Advance the recovery boundary source while saving its field for final
assembly. The original gather volume and scratch headers already suffice. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def archiveRetainedRecoveryField {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) : Pr P T Q A U :=
  takePrefix (plan.gather 123) (placement.bank 132) (plan.gather 125)
    (plan.gather 88) (plan.gather 89)

def archivedRetainedRecoveryFieldState (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update S.R (placement.bank 132) tail)
    (plan.gather 125) (cstream A H.wordWidth (packedInterval H.origin H.span C)++S.R (plan.gather 125)))}

theorem archiveRetainedRecoveryField_exec_within (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (buffers : ReplicaLoopBuffers A) (C : ZMod s → GaussianInt)
    (tail raw pageTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaRecoveryRhsHeaders H plan.gather buffers S)
    (cache : CachedRecoveryCouplingReady H raw pageTail (embStk placement.bank S))
    (hsource : S.R (placement.bank 132) = cstream A H.wordWidth (packedInterval H.origin H.span C)++tail)
    (depth : ℕ) :
    let F := archivedRetainedRecoveryFieldState H placement C tail S
    ∃ vf, vf.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*(6*(H.span*H.wordWidth)+6)) depth (archiveRetainedRecoveryField placement)
        (mk v S) (6*(H.span*H.wordWidth)+6) (mk vf F) ∧
      ReplicaRecoveryRhsHeaders H plan.gather buffers F ∧
      CachedRecoveryCouplingReady H raw pageTail (embStk placement.bank F) := by
  dsimp only
  have hdis (i : Fin 126) (j : Fin 168) : plan.gather i ≠ placement.bank j :=
    (placement.bank_gather_disjoint j i).symm
  have hreg : [plan.gather 123,placement.bank 132,plan.gather 125,plan.gather 88,plan.gather 89].Nodup := by
    simp [List.nodup_cons,plan.gather_injective.eq_iff,hdis,placement.bank_gather_disjoint]
  have hlen : (cstream A H.wordWidth (packedInterval H.origin H.span C)).length = H.span*H.wordWidth := by
    simp [length_cstream,packedInterval_length C H.span_fit]
  obtain ⟨vf,hu,he⟩ := takePrefix_exec (body := body) hreg v S _ tail hsource
    (headers.volume.trans hlen.symm) (headers.fresh 88 (by simp)) (headers.fresh 89 (by simp))
  have he' : Exec body (archiveRetainedRecoveryField placement) (mk v S)
      (6*(H.span*H.wordWidth)+6) (mk vf (archivedRetainedRecoveryFieldState H placement C tail S)) := by
    simpa only [hlen,archiveRetainedRecoveryField,archivedRetainedRecoveryFieldState] using he
  refine ⟨vf,hu,mn_native_exec_within he' 2 ?_ depth _ (le_refl _),?_,?_⟩
  · simp [archiveRetainedRecoveryField,takePrefix,transfer,transferAct,scanR,drainR,popDo,keepIn,
      moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  · apply headers.of_archive_frame H plan.gather buffers S
    intro i hi
    simp [archivedRetainedRecoveryFieldState,plan.gather_injective.eq_iff,hi,hdis]
  · have hview : embStk placement.bank (archivedRetainedRecoveryFieldState H placement C tail S) =
        {embStk placement.bank S with R := Function.update (embStk placement.bank S).R 132 tail} := by
      change embStk placement.bank
        {{S with R := Function.update S.R (placement.bank 132) tail} with
          R := Function.update (Function.update S.R (placement.bank 132) tail) (plan.gather 125)
            (cstream A H.wordWidth (packedInterval H.origin H.span C)++S.R (plan.gather 125))} = _
      rw [embStk_updateR_off _ _ _ (fun i => placement.bank_gather_disjoint i 125)]
      exact embStk_updateR placement.bank_injective S 132 tail
    rw [hview]
    exact cache.update_source tail

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
