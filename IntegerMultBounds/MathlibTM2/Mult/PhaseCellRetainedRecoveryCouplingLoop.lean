module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedRecoveryCouplingTransition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! A structural traversal computes all recovery RHS rows and retains all
boundary fields. Coefficients, selectors and scalar counters are shared. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def retainedRecoveryCouplingLoopState {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (S : Stacks T A)
    (source rhs output archive count : List (Fin (A+4))) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update
    (Function.update S.R (placement.bank 132) source) (placement.bank 93) rhs)
    (placement.bank 110) output) (plan.gather 125) archive) (plan.gather 122) count)}

omit [NeZero s] in
theorem ReplicaRecoveryRhsHeaders.update_clock (H : ReplicaHaloProblem s)
    (plan : ReplicaInteriorPlacement T) (buffers : ReplicaLoopBuffers A) (S : Stacks T A)
    (h : ReplicaRecoveryRhsHeaders H plan.gather buffers S) (xs : List (Fin (A+4))) :
    ReplicaRecoveryRhsHeaders H plan.gather buffers {S with R := Function.update S.R (plan.gather 122) xs} := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa [plan.gather_injective.ne (by decide : (121 : Fin 126) ≠ 122)] using h.count
  · simpa [plan.gather_injective.ne (by decide : (123 : Fin 126) ≠ 122)] using h.volume
  · simpa [plan.gather_injective.ne (by decide : (124 : Fin 126) ≠ 122)] using h.source
  · intro k hk
    have hn : k ≠ (122 : Fin 126) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide
    simpa [plan.gather_injective.ne hn] using h.fresh k hk

theorem retainedRecoveryCouplingLoop_exec (H : ReplicaHaloProblem s)
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hsep : H.span+H.band ≤ s)
    (buffers : ReplicaLoopBuffers A) (rows : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt)))
    (hfits : ∀ row ∈ rows, ∀ j, Fits H.wordWidth (row.1 j))
    (tail rhsTail raw pageTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaRecoveryRhsHeaders H plan.gather buffers S)
    (cache : CachedRecoveryCouplingReady H raw pageTail (embStk placement.bank S))
    (hsource : S.R (placement.bank 132) = rows.flatMap
      (fun row => cstream A H.wordWidth (packedInterval H.origin H.span row.1))++tail)
    (hrhs : S.R (placement.bank 93) = rows.flatMap
      (fun row => cstream A H.wordWidth (packedInterval H.origin H.span row.2))++rhsTail)
    (hcount : (S.R (plan.gather 122)).length = rows.length) :
    let field := fun (C : ZMod s → GaussianInt) => cstream A H.wordWidth (packedInterval H.origin H.span C)
    let output := fun row => field (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
      H.origin (H.origin+H.span) true row.1 row.2)
    let F := retainedRecoveryCouplingLoopState placement S tail rhsTail
      (rows.reverse.flatMap output++S.R (placement.bank 110))
      (rows.reverse.flatMap (fun row => field row.1)++S.R (plan.gather 125)) []
    ∃ vf m, vf.user = v.user ∧
      m ≤ rows.length*(cachedRecoveryCouplingRowCost H+(6*(H.span*H.wordWidth)+6)+3)+2 ∧
      Exec body (countedLoop (plan.gather 122) (retainedRecoveryCouplingTransition placement hQ))
        (mk v S) m (mk vf F) ∧
      ReplicaRecoveryRhsHeaders H plan.gather buffers F ∧
      CachedRecoveryCouplingReady H (rows.reverse.flatMap output++raw) pageTail (embStk placement.bank F) := by
  dsimp only
  let field := fun (C : ZMod s → GaussianInt) => cstream A H.wordWidth (packedInterval H.origin H.span C)
  let output := fun row : (ZMod s → GaussianInt) × (ZMod s → GaussianInt) =>
    field (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
      H.origin (H.origin+H.span) true row.1 row.2)
  have hdis (i : Fin 126) (j : Fin 168) : plan.gather i ≠ placement.bank j :=
    (placement.bank_gather_disjoint j i).symm
  let Inv := fun j (F : Stacks T A) => ∃ done todo count,
    rows = done++todo ∧ done.length = j ∧
    F = retainedRecoveryCouplingLoopState placement S
      (todo.flatMap (fun row => field row.1)++tail)
      (todo.flatMap (fun row => field row.2)++rhsTail)
      (done.reverse.flatMap output++S.R (placement.bank 110))
      (done.reverse.flatMap (fun row => field row.1)++S.R (plan.gather 125)) count ∧
    ReplicaRecoveryRhsHeaders H plan.gather buffers F ∧
    CachedRecoveryCouplingReady H (done.reverse.flatMap output++raw) pageTail (embStk placement.bank F)
  have hstable : ∀ j F xs, Inv j F → Inv j {F with R := Function.update F.R (plan.gather 122) xs} := by
    intro j F xs hI
    obtain ⟨done,todo,count,heq,hlen,hstate,hh,hc⟩ := hI
    refine ⟨done,todo,xs,heq,hlen,?_,hh.update_clock H plan buffers F xs,?_⟩
    · rw [hstate]; simp only [retainedRecoveryCouplingLoopState,Function.update_idem]
    · rw [embStk_updateR_off _ _ _ (fun i => placement.bank_gather_disjoint i 122)]
      exact hc
  have hstep : ∀ j < rows.length, ∀ (vi : HS T Q A U) F, Inv j F →
      ∃ vf G m, vf.user = vi.user ∧ m ≤ cachedRecoveryCouplingRowCost H+(6*(H.span*H.wordWidth)+6) ∧
        Exec body (retainedRecoveryCouplingTransition placement hQ) (mk vi F) m (mk vf G) ∧
        G.R (plan.gather 122) = F.R (plan.gather 122) ∧ Inv (j+1) G := by
    intro j hj vi F hI
    obtain ⟨done,todo,count,heq,hlen,hstate,hh,hc⟩ := hI
    cases todo with
    | nil => simp only [List.append_nil] at heq; have hl := congrArg List.length heq; omega
    | cons row todo =>
      have hrow : row ∈ rows := by rw [heq]; simp
      have hsrc : F.R (placement.bank 132) = field row.1++(todo.flatMap (fun row => field row.1)++tail) := by
        rw [hstate]
        simp [retainedRecoveryCouplingLoopState,placement.bank_injective.eq_iff,
          placement.bank_gather_disjoint,List.append_assoc]
      have hrhsF : F.R (placement.bank 93) = field row.2++(todo.flatMap (fun row => field row.2)++rhsTail) := by
        rw [hstate]
        simp [retainedRecoveryCouplingLoopState,placement.bank_injective.eq_iff,
          placement.bank_gather_disjoint,List.append_assoc]
      obtain ⟨vf,m,hu,hm,he,hhG,hcG⟩ := retainedRecoveryCouplingTransition_exec_within (body := body)
        H placement hQ hA hsep buffers row.1 row.2 (hfits row hrow)
        (todo.flatMap (fun row => field row.1)++tail) (todo.flatMap (fun row => field row.2)++rhsTail)
        (done.reverse.flatMap output++raw) pageTail vi F hh hc hsrc hrhsF 0
      refine ⟨vf,_,m,hu,hm,he.toExec,?_,done++[row],todo,count,?_,?_,?_,hhG,?_⟩
      · simp [retainedRecoveryCouplingTransitionState,archivedRetainedRecoveryFieldState,
          placedCachedRecoveryCouplingState,plan.gather_injective.eq_iff,hdis]
      · simpa only [List.append_assoc,List.singleton_append] using heq
      · simp [hlen]
      · rw [hstate]
        refine Stacks.ext rfl rfl rfl ?_
        funext k
        by_cases h132 : k = placement.bank 132 <;> by_cases h93 : k = placement.bank 93 <;>
          by_cases h110 : k = placement.bank 110 <;> by_cases h125 : k = plan.gather 125 <;>
          by_cases h122 : k = plan.gather 122 <;>
          simp [retainedRecoveryCouplingTransitionState,archivedRetainedRecoveryFieldState,
            placedCachedRecoveryCouplingState,retainedRecoveryCouplingLoopState,
            h132,h93,h110,h125,h122,placement.bank_injective.eq_iff,
            placement.bank_gather_disjoint,hdis,plan.gather_injective.eq_iff,
            List.reverse_append,List.append_assoc,field,output]
      · simpa [List.reverse_append,List.append_assoc,output,field] using hcG
  have hinit : Inv 0 S := by
    refine ⟨[],rows,S.R (plan.gather 122),rfl,rfl,?_,headers,cache⟩
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h132 : k = placement.bank 132 <;> by_cases h93 : k = placement.bank 93 <;>
      by_cases h110 : k = placement.bank 110 <;> by_cases h125 : k = plan.gather 125 <;>
      by_cases h122 : k = plan.gather 122 <;>
      simp [retainedRecoveryCouplingLoopState,h132,h93,h110,h125,h122,
        hsource,hrhs,field,placement.bank_injective.eq_iff,placement.bank_gather_disjoint,
        plan.gather_injective.eq_iff]
  obtain ⟨vf,F,m,hu,hm,he,hclock,hI⟩ := countedLoop_exec (body := body)
    (plan.gather 122) (retainedRecoveryCouplingTransition placement hQ) rows.length
    (cachedRecoveryCouplingRowCost H+(6*(H.span*H.wordWidth)+6)) Inv hstable hstep v S hcount hinit
  obtain ⟨done,todo,count,heq,hlen,hstate,hh,hc⟩ := hI
  have ht : todo = [] := by
    have hl := congrArg List.length heq
    simp only [List.length_append] at hl
    apply List.eq_nil_of_length_eq_zero
    omega
  subst todo
  simp only [List.append_nil] at heq
  subst done
  have hcountNil : count = [] := by
    simpa [hstate,retainedRecoveryCouplingLoopState,field,output] using hclock
  subst count
  refine ⟨vf,m,hu,hm,he.cast rfl (congrArg (mk vf) ?_),?_,?_⟩
  · simpa [retainedRecoveryCouplingLoopState,field,output] using hstate
  · simpa [hstate,retainedRecoveryCouplingLoopState,field,output] using hh
  · simpa [hstate,retainedRecoveryCouplingLoopState,field,output] using hc

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
