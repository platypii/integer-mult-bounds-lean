module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCachedRecoveryCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveRetainedRecoveryField
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget

/-! One recovery row consumes its original RHS, computes the second-pass RHS,
and saves the boundary field while advancing the boundary queue. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def retainedRecoveryCouplingTransition {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (placedCachedRecoveryCouplingRow placement hQ) (archiveRetainedRecoveryField placement)

def retainedRecoveryCouplingTransitionState (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (C : ZMod s → GaussianInt) (tail rhsTail output : List (Fin (A+4))) (S : Stacks T A) : Stacks T A :=
  archivedRetainedRecoveryFieldState H placement C tail
    (placedCachedRecoveryCouplingState placement S rhsTail output)

theorem retainedRecoveryCouplingTransition_exec_within (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hsep : H.span+H.band ≤ s)
    (buffers : ReplicaLoopBuffers A) (C B : ZMod s → GaussianInt)
    (hC : ∀ j, Fits H.wordWidth (C j)) (tail rhsTail raw pageTail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaRecoveryRhsHeaders H plan.gather buffers S)
    (cache : CachedRecoveryCouplingReady H raw pageTail (embStk placement.bank S))
    (hsource : S.R (placement.bank 132) = cstream A H.wordWidth (packedInterval H.origin H.span C)++tail)
    (hrhs : S.R (placement.bank 93) = cstream A H.wordWidth (packedInterval H.origin H.span B)++rhsTail)
    (depth : ℕ) :
    let output := cstream A H.wordWidth (packedInterval H.origin H.span
      (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
        H.origin (H.origin+H.span) true C B))
    let F := retainedRecoveryCouplingTransitionState H placement C tail rhsTail output S
    ∃ vf m, vf.user = v.user ∧ m ≤ cachedRecoveryCouplingRowCost H+(6*(H.span*H.wordWidth)+6) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (cachedRecoveryCouplingWorkspace (A := A) (U := U) H hQ+2*(6*(H.span*H.wordWidth)+6)))
        depth (retainedRecoveryCouplingTransition placement hQ) (mk v S) m (mk vf F) ∧
      ReplicaRecoveryRhsHeaders H plan.gather buffers F ∧
      CachedRecoveryCouplingReady H (output++raw) pageTail (embStk placement.bank F) := by
  dsimp only
  let output := cstream A H.wordWidth (packedInterval H.origin H.span
    (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
      H.origin (H.origin+H.span) true C B))
  let G := placedCachedRecoveryCouplingState placement S rhsTail output
  obtain ⟨vi,mi,hu₁,hm₁,he₁,hcache⟩ := placedCachedRecoveryCouplingRow_exec_within (body := body)
    H placement hQ hA hsep C B hC tail rhsTail raw pageTail v S cache hsource hrhs
  have hheaders : ReplicaRecoveryRhsHeaders H plan.gather buffers G := by
    apply headers.of_frame H plan.gather buffers S G
    intro i
    have h93 := (placement.bank_gather_disjoint 93 i).symm
    have h110 := (placement.bank_gather_disjoint 110 i).symm
    simp [G,placedCachedRecoveryCouplingState,h93,h110]
  have hsourceG : G.R (placement.bank 132) =
      cstream A H.wordWidth (packedInterval H.origin H.span C)++tail := by
    have h93 := placement.bank_injective.ne (by decide : (132 : Fin 168) ≠ 93)
    have h110 := placement.bank_injective.ne (by decide : (132 : Fin 168) ≠ 110)
    simpa [G,placedCachedRecoveryCouplingState,h93,h110] using hsource
  obtain ⟨vf,hu₂,he₂,hh₂,hc₂⟩ := archiveRetainedRecoveryField_exec_within (body := body)
    H placement buffers C tail (output++raw) pageTail vi G hheaders hcache hsourceG depth
  refine ⟨vf,mi+(6*(H.span*H.wordWidth)+6),hu₂.trans hu₁,Nat.add_le_add_right hm₁ _,?_,hh₂,hc₂⟩
  exact execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ (he₁ depth) he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
