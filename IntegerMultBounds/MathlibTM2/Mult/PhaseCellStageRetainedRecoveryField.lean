module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveRetainedRecoveryField

/-! Stage one packed boundary field from the joint queue. Its retained piece
volume and gather scratch suffice; all shared coupling data survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def stageRetainedRecoveryField {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (source : Fin T) : Pr P T Q A U :=
  takePrefix (plan.gather 123) source (placement.bank 132) (plan.gather 88) (plan.gather 89)

def stagedRetainedRecoveryFieldState (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (source : Fin T) (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update S.R source tail) (placement.bank 132)
    (cstream A H.wordWidth (packedInterval H.origin H.span C)++S.R (placement.bank 132)))}

theorem stageRetainedRecoveryField_exec_within (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (source : Fin T) (hbank : ∀ i, placement.bank i ≠ source)
    (hgather : ∀ i, plan.gather i ≠ source)
    (buffers : ReplicaLoopBuffers A) (C : ZMod s → GaussianInt)
    (tail raw pageTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaRecoveryRhsHeaders H plan.gather buffers S)
    (cache : CachedRecoveryCouplingReady H raw pageTail (embStk placement.bank S))
    (hsource : S.R source = cstream A H.wordWidth (packedInterval H.origin H.span C)++tail)
    (depth : ℕ) :
    let F := stagedRetainedRecoveryFieldState H placement source C tail S
    ∃ vf, vf.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*(6*(H.span*H.wordWidth)+6)) depth (stageRetainedRecoveryField placement source)
        (mk v S) (6*(H.span*H.wordWidth)+6) (mk vf F) ∧
      ReplicaRecoveryRhsHeaders H plan.gather buffers F ∧
      CachedRecoveryCouplingReady H raw pageTail (embStk placement.bank F) := by
  dsimp only
  have hdis (i : Fin 126) (j : Fin 168) : plan.gather i ≠ placement.bank j :=
    (placement.bank_gather_disjoint j i).symm
  have hreg : [plan.gather 123,source,placement.bank 132,plan.gather 88,plan.gather 89].Nodup := by
    simp [List.nodup_cons,plan.gather_injective.eq_iff,hdis,hgather,placement.bank_gather_disjoint,
      (hbank 132).symm,(hgather 88).symm,(hgather 89).symm]
  have hlen : (cstream A H.wordWidth (packedInterval H.origin H.span C)).length = H.span*H.wordWidth := by
    simp [length_cstream,packedInterval_length C H.span_fit]
  obtain ⟨vf,hu,he⟩ := takePrefix_exec (body := body) hreg v S _ tail hsource
    (headers.volume.trans hlen.symm) (headers.fresh 88 (by simp)) (headers.fresh 89 (by simp))
  have he' : Exec body (stageRetainedRecoveryField placement source) (mk v S)
      (6*(H.span*H.wordWidth)+6) (mk vf (stagedRetainedRecoveryFieldState H placement source C tail S)) := by
    simpa only [hlen,stageRetainedRecoveryField,stagedRetainedRecoveryFieldState] using he
  refine ⟨vf,hu,mn_native_exec_within he' 2 ?_ depth _ (le_refl _),?_,?_⟩
  · simp [stageRetainedRecoveryField,takePrefix,transfer,transferAct,scanR,drainR,popDo,keepIn,
      moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  · apply headers.of_frame H plan.gather buffers S
    intro i
    simp [stagedRetainedRecoveryFieldState,hdis,hgather]
  · have hview : embStk placement.bank (stagedRetainedRecoveryFieldState H placement source C tail S) =
        {embStk placement.bank S with R := (Function.update (embStk placement.bank S).R 132
          (cstream A H.wordWidth (packedInterval H.origin H.span C)++S.R (placement.bank 132)))} := by
      change embStk placement.bank {{S with R := Function.update S.R source tail} with
        R := (Function.update (Function.update S.R source tail) (placement.bank 132)
          (cstream A H.wordWidth (packedInterval H.origin H.span C)++S.R (placement.bank 132)))} = _
      rw [embStk_updateR placement.bank_injective,embStk_updateR_off _ _ _ hbank]
    rw [hview]
    exact cache.update_source _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
