module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedRecoveryCouplingLoop

/-! Initialize the recovery clock from the retained replica master once. The
complete traversal restores the clock and preserves the master and cache. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def retainedRecoveryCouplingBatch {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (ucopy (plan.gather 121) (plan.gather 122) (plan.gather 89))
    (countedLoop (plan.gather 122) (retainedRecoveryCouplingTransition placement hQ))

def retainedRecoveryCouplingBatchCost (H : ReplicaHaloProblem s) (replicas : ℕ) : ℕ :=
  (4*replicas+4)+(replicas*(cachedRecoveryCouplingRowCost H+(6*(H.span*H.wordWidth)+6)+3)+2)

theorem retainedRecoveryCouplingBatch_exec (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hsep : H.span+H.band ≤ s)
    (buffers : ReplicaLoopBuffers A) (rows : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt)))
    (hlen : rows.length = H.Fs.length)
    (hfits : ∀ row ∈ rows, ∀ j, Fits H.wordWidth (row.1 j))
    (tail rhsTail raw pageTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaRecoveryRhsHeaders H plan.gather buffers S)
    (cache : CachedRecoveryCouplingReady H raw pageTail (embStk placement.bank S))
    (hsource : S.R (placement.bank 132) = rows.flatMap
      (fun row => cstream A H.wordWidth (packedInterval H.origin H.span row.1))++tail)
    (hrhs : S.R (placement.bank 93) = rows.flatMap
      (fun row => cstream A H.wordWidth (packedInterval H.origin H.span row.2))++rhsTail)
    (hclock : S.R (plan.gather 122) = []) :
    let field := fun (C : ZMod s → GaussianInt) => cstream A H.wordWidth (packedInterval H.origin H.span C)
    let output := fun row => field (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
      H.origin (H.origin+H.span) true row.1 row.2)
    let F := retainedRecoveryCouplingLoopState placement S tail rhsTail
      (rows.reverse.flatMap output++S.R (placement.bank 110))
      (rows.reverse.flatMap (fun row => field row.1)++S.R (plan.gather 125)) []
    ∃ vf m, vf.user = v.user ∧ m ≤ retainedRecoveryCouplingBatchCost H rows.length ∧
      Exec body (retainedRecoveryCouplingBatch placement hQ) (mk v S) m (mk vf F) ∧
      ReplicaRecoveryRhsHeaders H plan.gather buffers F ∧
      CachedRecoveryCouplingReady H (rows.reverse.flatMap output++raw) pageTail (embStk placement.bank F) := by
  dsimp only
  let field := fun (C : ZMod s → GaussianInt) => cstream A H.wordWidth (packedInterval H.origin H.span C)
  let output := fun row : (ZMod s → GaussianInt) × (ZMod s → GaussianInt) =>
    field (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
      H.origin (H.origin+H.span) true row.1 row.2)
  have hdis (i : Fin 168) : placement.bank i ≠ plan.gather 122 := placement.bank_gather_disjoint i 122
  obtain ⟨vi,hu₁,he₁⟩ := ucopy_exec (body := body)
    (plan.gather_injective.ne (by decide : (121 : Fin 126) ≠ 122))
    (plan.gather_injective.ne (by decide : (121 : Fin 126) ≠ 89))
    (plan.gather_injective.ne (by decide : (122 : Fin 126) ≠ 89)) v S (headers.fresh 89 (by simp))
  let J : Stacks T A := {S with R := Function.update S.R (plan.gather 122) (List.replicate rows.length tick)}
  have he₁' : Exec body (ucopy (plan.gather 121) (plan.gather 122) (plan.gather 89))
      (mk v S) (4*rows.length+4) (mk vi J) := by
    simpa only [J,headers.count,← hlen,hclock,List.append_nil] using he₁
  have hbank : embStk placement.bank J = embStk placement.bank S :=
    embStk_updateR_off S _ _ hdis
  obtain ⟨vf,m,hu₂,hm,he₂,hh,hc⟩ := retainedRecoveryCouplingLoop_exec (body := body)
    H placement hQ hA hsep buffers rows hfits tail rhsTail raw pageTail vi J
    (headers.update_clock H plan buffers S _) (hbank ▸ cache)
    (by simpa [J,hdis] using hsource) (by simpa [J,hdis] using hrhs) (by simp [J])
  have hfinal : retainedRecoveryCouplingLoopState placement J tail rhsTail
      (rows.reverse.flatMap output++J.R (placement.bank 110))
      (rows.reverse.flatMap (fun row => field row.1)++J.R (plan.gather 125)) [] =
      retainedRecoveryCouplingLoopState placement S tail rhsTail
        (rows.reverse.flatMap output++S.R (placement.bank 110))
        (rows.reverse.flatMap (fun row => field row.1)++S.R (plan.gather 125)) [] := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = plan.gather 122 <;>
      simp [retainedRecoveryCouplingLoopState,J,Function.update_apply,hk,hdis,
        plan.gather_injective.eq_iff]
  refine ⟨vf,(4*rows.length+4)+m,hu₂.trans hu₁,Nat.add_le_add_left hm _,?_,?_,?_⟩
  · exact (Exec.seq he₁' he₂).cast rfl (congrArg (mk vf) hfinal)
  · rw [← hfinal]
    exact hh
  · rw [← hfinal]
    exact hc

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
