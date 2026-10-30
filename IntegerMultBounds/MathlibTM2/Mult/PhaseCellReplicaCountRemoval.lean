module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRemoveDummyPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate the real output-symbol count from replicas and output row width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def replicaCountRemoval (replicas width src keep count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct replicas width keep saved tmp)
    (.seq (removeDummyPrefix src keep count tmp) (uclear keep))

/-- The input and output row widths may differ. The retained replica count
and current output width generate the exact real-symbol count for erasure. -/
theorem replicaCountRemoval_exec {replicas width src keep count saved tmp : Fin T}
    (hreg : [replicas,width,src,keep,count,saved,tmp].Nodup)
    (N W : ℕ) (dummy real : List (Fin (A+4))) (hreal : real.length = N*W)
    (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = N) (hwidth : (S.R width).length = W)
    (hsrc : S.R src = dummy++real)
    (hkeep : S.R keep = []) (hcount : S.R count = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 10*dummy.length+14*real.length+9*N+20 ∧
      Exec body (replicaCountRemoval replicas width src keep count saved tmp) (mk v S) n
        (mk v' {S with R := Function.update S.R src real}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [replicas,width,keep,saved,tmp].Nodup by regs_nodup) v S hsaved htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R keep (List.replicate real.length tick)}
  have he₁' : Exec body (unaryProduct replicas width keep saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hreplicas,hwidth,hkeep,hreal] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := removeDummyPrefix_exec (body := body)
    (show [src,keep,count,tmp].Nodup by regs_nodup) dummy real v₁ S₁
    (by simpa [S₁,‹src ≠ keep›] using hsrc) (by simp [S₁])
    (by simpa [S₁,‹keep ≠ count›.symm] using hcount)
    (by simpa [S₁,‹keep ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src real}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) keep v₂ S₂
  refine ⟨v₃,n₁+(10*dummy.length+8*real.length+14)+(2*real.length+2),
    hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · rw [hreplicas,hwidth] at hn₁
    have hc : N*(4*W+9) = 4*real.length+9*N := by rw [hreal]; ring
    rw [hc] at hn₁
    omega
  · simp [S₂,S₁,‹src ≠ keep›.symm,Nat.add_assoc]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases his : i = src
    · subst i; simp [S₂,S₁,‹src ≠ keep›]
    by_cases hik : i = keep
    · subst i; simp [S₂,S₁,‹src ≠ keep›.symm,hkeep]
    · simp [S₂,S₁,his,hik]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
