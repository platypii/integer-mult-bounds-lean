module

public import IntegerMultBounds.MathlibTM2.Host.BinArith
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Emit a constant-symbol run from a retained binary count.
Conversion and emission are linear; the same execution carries a stack-volume invariant. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def emitRun (a count dst work saved tmp : Fin T) (symbol : Fin (A+4)) : Pr P T Q A U :=
  .seq (toUnary a count work saved tmp) (moveR count dst (fun _ => symbol))

theorem emitRun_pushBound (a count dst work saved tmp : Fin T) (symbol : Fin (A+4)) :
    mnNativePushBound 2 (emitRun (P := P) (Q := Q) (U := U) a count dst work saved tmp symbol) := by
  simp [emitRun,toUnary,eachSym,hornerIter,udbl,drainR,popDo,pushN,popPush,
    moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]

theorem emitRun_exec {a count dst work saved tmp : Fin T}
    (hreg : [a,count,dst,work,saved,tmp].Nodup) (W n : ℕ) (hn : n < 2^W) (symbol : Fin (A+4))
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms W n)
    (hfresh : ∀ k ∈ [count,work,saved,tmp], S.R k = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ 8*n+11*W+8 ∧
      Exec body (emitRun a count dst work saved tmp symbol) (mk v S) steps
        (mk v' {S with R := Function.update S.R dst (List.replicate n symbol++S.R dst)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear (body := body)
    (show [a,count,work,saved,tmp].Nodup by simp_all) hn v S ha
    (hfresh work (by simp)) (hfresh saved (by simp)) (hfresh tmp (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R count (List.replicate n tick)}
  have he₁' : Exec body (toUnary a count work saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hfresh count (by simp)] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (body := body) count dst ‹count ≠ dst› (fun _ => symbol) v₁ S₁
  refine ⟨v₂,n₁+(2*n+2),hu₂.trans hu₁,by omega,
    (Exec.seq he₁' he₂).cast (by simp [S₁]) ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k = dst
  · subst k; simp [S₁,movedR,Ne.symm ‹count ≠ dst›]
  by_cases hkc : k = count
  · subst k; simp [S₁,movedR,‹count ≠ dst›,hfresh count (by simp)]
  simp [S₁,movedR,hk,hkc]

/-- Every intermediate store, including retained caller stacks, meets the stated bound. -/
theorem emitRun_within {a count dst work saved tmp : Fin T}
    (hreg : [a,count,dst,work,saved,tmp].Nodup) (W n : ℕ) (hn : n < 2^W) (symbol : Fin (A+4))
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms W n)
    (hfresh : ∀ k ∈ [count,work,saved,tmp], S.R k = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ 8*n+11*W+8 ∧
      ExecWithin body (fun depth z => mnSize z+depth ≤ mnSize (mk v S)+2*(8*n+11*W+8)) 0
        (emitRun a count dst work saved tmp symbol) (mk v S) steps
        (mk v' {S with R := Function.update S.R dst (List.replicate n symbol++S.R dst)}) := by
  obtain ⟨v',steps,hu,hs,he⟩ := emitRun_exec (body := body) hreg W n hn symbol v S ha hfresh
  exact ⟨v',steps,hu,hs,mn_native_exec_within he 2
    (emitRun_pushBound a count dst work saved tmp symbol) 0 _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Host
