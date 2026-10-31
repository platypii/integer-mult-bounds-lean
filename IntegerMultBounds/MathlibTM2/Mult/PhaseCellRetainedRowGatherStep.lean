module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrderedGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeCopyPrefix

/-! A row step reuses one retained local sweep control page. It advances the
packed source once, archives it for restoration, and erases only its working copy. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retainedRowGatherStep (count source archive dst control savedControl advance window src acc current
    savedSource buf tmp initialControl initialSource rowCount wordR : Fin T) : Pr P T Q A U :=
  .seq (takeCopyPrefix count source src archive buf tmp)
    (.seq (naturalGather dst control savedControl advance window src acc current savedSource buf tmp
      initialControl initialSource rowCount wordR) (uclear src))

def retainedRowGatherStepCost (volume B L w : ℕ) : ℕ :=
  B*(14*L*w+25)+28*volume+6*L*w+9*L+45

theorem retainedRowGatherStep_exec
    {count source archive dst control savedControl advance window src acc current savedSource buf tmp
      initialControl initialSource rowCount wordR : Fin T}
    (hreg : [count,source,archive,dst,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
      initialControl,initialSource,rowCount,wordR].Nodup)
    (L w : ℕ) (origins : List ℕ) (E tail : List (Fin (A+4)))
    (hne : origins ≠ []) (hordered : origins.Pairwise (· ≤ ·))
    (hfit : ∀ p ∈ origins, p+L*w ≤ E.length)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = match origins with | [] => [] | p::ps => gatherControls A (p::windowAdvances p ps))
    (hs : S.R source = E++tail) (hcount : (S.R count).length = E.length)
    (hrow : (S.R rowCount).length = L) (hw : (S.R wordR).length = w)
    (hsrc : S.R src = [])
    (hclean : ∀ k ∈ [savedControl,advance,window,acc,current,savedSource,buf,tmp,
      initialControl,initialSource], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retainedRowGatherStepCost E.length origins.length L w ∧
      Exec body (retainedRowGatherStep count source archive dst control savedControl advance window src acc current
        savedSource buf tmp initialControl initialSource rowCount wordR) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R source tail)
          archive (E.reverse++S.R archive)) dst
          (origins.flatMap (fun p => (E.drop p).take (L*w))++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := takeCopyPrefix_exec (body := body) count source src archive buf tmp
    (by regs_nodup) E tail v S hcount hs (hclean buf (by simp)) (hclean tmp (by simp))
  let M : Stacks T A := {S with R := (Function.update (Function.update (Function.update S.R source tail)
    src E) archive (E.reverse++S.R archive))}
  have he₁' : Exec body (takeCopyPrefix count source src archive buf tmp) (mk v S)
      (14*E.length+14) (mk v₁ M) := by
    simpa only [hsrc,List.append_nil,M] using he₁
  have hoff (k : Fin T) (hkSource : k ≠ source) (hkSrc : k ≠ src) (hkArchive : k ≠ archive) :
      M.R k = S.R k := by simp [M,hkSource,hkSrc,hkArchive]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := orderedGather_exec (body := body)
    (show [dst,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
      initialControl,initialSource,rowCount,wordR].Nodup by regs_nodup)
    L w origins E hne hordered hfit v₁ M
    (by
      rw [hoff control (by first | assumption | (exact Ne.symm (by assumption)))
        (by first | assumption | (exact Ne.symm (by assumption)))
        (by first | assumption | (exact Ne.symm (by assumption)))]
      cases ho : origins with
      | nil => exact (hne ho).elim
      | cons p ps => simpa only [ho] using hc)
    (by simp [M,(Ne.symm ‹archive ≠ src›)])
    (by simpa only [hoff rowCount (by first | assumption | (exact Ne.symm (by assumption))) (by first | assumption | (exact Ne.symm (by assumption))) (by first | assumption | (exact Ne.symm (by assumption)))] using hrow)
    (by simpa only [hoff wordR (by first | assumption | (exact Ne.symm (by assumption))) (by first | assumption | (exact Ne.symm (by assumption))) (by first | assumption | (exact Ne.symm (by assumption)))] using hw) (by
      intro k hk
      have hn : k ≠ source ∧ k ≠ src ∧ k ≠ archive := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals exact ⟨by first | assumption | (exact Ne.symm (by assumption)),
          by first | assumption | (exact Ne.symm (by assumption)),
          by first | assumption | (exact Ne.symm (by assumption))⟩
      rw [hoff k hn.1 hn.2.1 hn.2.2]
      exact hclean k hk)
  let F : Stacks T A := {M with R := (Function.update M.R dst
    (origins.flatMap (fun p => (E.drop p).take (L*w))++M.R dst))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) src v₂ F
  have hlength : (F.R src).length = E.length := by simp [F,M,(Ne.symm ‹dst ≠ src›),(Ne.symm ‹archive ≠ src›)]
  refine ⟨v₃,(14*E.length+14)+(n₂+(2*E.length+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hlength]) ?_⟩
  · unfold retainedRowGatherStepCost
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hSrc : k = src
    · subst k
      simp [F,M,hsrc,(Ne.symm ‹dst ≠ src›),(Ne.symm ‹source ≠ src›),(Ne.symm ‹archive ≠ src›)]
    by_cases hDst : k = dst
    · subst k
      simp [F,M,‹dst ≠ src›,(Ne.symm ‹source ≠ dst›),(Ne.symm ‹archive ≠ dst›)]
    simp [F,M,Function.update_apply,hSrc,hDst]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
