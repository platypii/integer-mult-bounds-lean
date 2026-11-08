module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageRetainedRecoveryField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedRecoveryCouplingTransition
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget

/-! Consume one piece directly from the joint boundary queue, compute its
recovery RHS and save its boundary field. No intermediate replica queue is built. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def jointSourceRecoveryCoupling {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (source : Fin T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (stageRetainedRecoveryField placement source) (retainedRecoveryCouplingTransition placement hQ)

def jointSourceRecoveryCouplingState (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (source : Fin T) (C : ZMod s → GaussianInt) (tail rhsTail output : List (Fin (A+4)))
    (S : Stacks T A) : Stacks T A :=
  retainedRecoveryCouplingTransitionState H placement C (S.R (placement.bank 132)) rhsTail output
    (stagedRetainedRecoveryFieldState H placement source C tail S)

omit [NeZero s] in
/-- Staging and retiring the field restore its borrowed local suffix. -/
theorem jointSourceRecoveryCouplingState_eq (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (source : Fin T) (hbank : ∀ i, placement.bank i ≠ source)
    (hgather : ∀ i, plan.gather i ≠ source)
    (C : ZMod s → GaussianInt) (tail rhsTail output : List (Fin (A+4))) (S : Stacks T A) :
    jointSourceRecoveryCouplingState H placement source C tail rhsTail output S =
      {S with R := (Function.update (Function.update (Function.update (Function.update S.R source tail)
        (placement.bank 93) rhsTail) (placement.bank 110) (output++S.R (placement.bank 110)))
        (plan.gather 125) (cstream A H.wordWidth (packedInterval H.origin H.span C)++S.R (plan.gather 125)))} := by
  have hdis (i : Fin 126) (j : Fin 168) : plan.gather i ≠ placement.bank j :=
    (placement.bank_gather_disjoint j i).symm
  have hsourceBank (i : Fin 168) : source ≠ placement.bank i := (hbank i).symm
  have hsourceGather (i : Fin 126) : source ≠ plan.gather i := (hgather i).symm
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hs : k = source <;> by_cases h132 : k = placement.bank 132 <;>
    by_cases h93 : k = placement.bank 93 <;> by_cases h110 : k = placement.bank 110 <;>
    by_cases h125 : k = plan.gather 125 <;>
    simp [jointSourceRecoveryCouplingState,retainedRecoveryCouplingTransitionState,
      archivedRetainedRecoveryFieldState,placedCachedRecoveryCouplingState,stagedRetainedRecoveryFieldState,
      hs,h132,h93,h110,h125,hbank,hgather,hsourceBank,hsourceGather,
      placement.bank_gather_disjoint,hdis,placement.bank_injective.eq_iff]

omit [NeZero s] in
theorem jointSourceRecoveryCouplingState_frame (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (source : Fin T) (hbank : ∀ i, placement.bank i ≠ source)
    (hgather : ∀ i, plan.gather i ≠ source)
    (C : ZMod s → GaussianInt) (tail rhsTail output : List (Fin (A+4))) (S : Stacks T A)
    (k : Fin T) (hs : k ≠ source) (h93 : k ≠ placement.bank 93)
    (h110 : k ≠ placement.bank 110) (h125 : k ≠ plan.gather 125) :
    (jointSourceRecoveryCouplingState H placement source C tail rhsTail output S).R k = S.R k := by
  rw [jointSourceRecoveryCouplingState_eq H placement source hbank hgather]
  simp [hs,h93,h110,h125]

theorem jointSourceRecoveryCoupling_exec_within (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (source : Fin T) (hbank : ∀ i, placement.bank i ≠ source)
    (hgather : ∀ i, plan.gather i ≠ source)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hsep : H.span+H.band ≤ s)
    (buffers : ReplicaLoopBuffers A) (C B : ZMod s → GaussianInt)
    (hC : ∀ j, Fits H.wordWidth (C j)) (tail rhsTail raw pageTail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaRecoveryRhsHeaders H plan.gather buffers S)
    (cache : CachedRecoveryCouplingReady H raw pageTail (embStk placement.bank S))
    (hsource : S.R source = cstream A H.wordWidth (packedInterval H.origin H.span C)++tail)
    (hrhs : S.R (placement.bank 93) = cstream A H.wordWidth (packedInterval H.origin H.span B)++rhsTail)
    (depth : ℕ) :
    let output := cstream A H.wordWidth (packedInterval H.origin H.span
      (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
        H.origin (H.origin+H.span) true C B))
    let F := jointSourceRecoveryCouplingState H placement source C tail rhsTail output S
    ∃ vf m, vf.user = v.user ∧
      m ≤ (6*(H.span*H.wordWidth)+6)+(cachedRecoveryCouplingRowCost H+(6*(H.span*H.wordWidth)+6)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*(6*(H.span*H.wordWidth)+6)+
          (cachedRecoveryCouplingWorkspace (A := A) (U := U) H hQ+2*(6*(H.span*H.wordWidth)+6))))
        depth (jointSourceRecoveryCoupling placement source hQ) (mk v S) m (mk vf F) ∧
      ReplicaRecoveryRhsHeaders H plan.gather buffers F ∧
      CachedRecoveryCouplingReady H (output++raw) pageTail (embStk placement.bank F) := by
  dsimp only
  let J := stagedRetainedRecoveryFieldState H placement source C tail S
  obtain ⟨vi,hu₁,he₁,hh₁,hc₁⟩ := stageRetainedRecoveryField_exec_within (body := body)
    H placement source hbank hgather buffers C tail raw pageTail v S headers cache hsource depth
  have hsrcJ : J.R (placement.bank 132) =
      cstream A H.wordWidth (packedInterval H.origin H.span C)++S.R (placement.bank 132) := by
    simp [J,stagedRetainedRecoveryFieldState]
  have hrhsJ : J.R (placement.bank 93) =
      cstream A H.wordWidth (packedInterval H.origin H.span B)++rhsTail := by
    have hn := placement.bank_injective.ne (by decide : (93 : Fin 168) ≠ 132)
    simpa [J,stagedRetainedRecoveryFieldState,hn,hbank] using hrhs
  obtain ⟨vf,m,hu₂,hm₂,he₂,hh₂,hc₂⟩ := retainedRecoveryCouplingTransition_exec_within (body := body)
    H placement hQ hA hsep buffers C B hC (S.R (placement.bank 132)) rhsTail raw pageTail vi J hh₁ hc₁ hsrcJ hrhsJ depth
  refine ⟨vf,(6*(H.span*H.wordWidth)+6)+m,hu₂.trans hu₁,Nat.add_le_add_left hm₂ _,?_,hh₂,hc₂⟩
  exact execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ he₁ he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
