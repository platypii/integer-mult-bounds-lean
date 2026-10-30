module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComplexPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate the output-core count from retained replica/row dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def pairComplexKey (replicas width count src buf saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct replicas width count saved tmp) (pairComplexPrefix count src buf saved tmp)

/-- The row width is the published core width, independently of the input halo
width. Borrowed dimensions restore, and the generated pairing count is consumed. -/
theorem pairComplexKey_exec {replicas width count src buf saved tmp : Fin T}
    (hreg : [replicas,width,count,src,buf,saved,tmp].Nodup) (hA : 4 ≤ A)
    (N W w : ℕ) (xs ys : List GaussianInt) (hlen : xs.length = ys.length)
    (hsize : xs.length*w = N*W) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = N) (hwidth : (S.R width).length = W)
    (hsrc : S.R src = cstream A w (xs++ys)++tail)
    (hcount : S.R count = []) (hbuf : S.R buf = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ N*(16*W+9)+14 ∧
      Exec body (pairComplexKey replicas width count src buf saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update S.R src
          (cstream A w (List.zipWith pairComponentWord xs ys)++tail))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [replicas,width,count,saved,tmp].Nodup by regs_nodup) v S hsaved htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R count (List.replicate (N*W) tick)}
  have he₁' : Exec body (unaryProduct replicas width count saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hreplicas,hwidth,hcount] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := pairComplexPrefix_exec (body := body)
    (show [count,src,buf,saved,tmp].Nodup by regs_nodup) hA w xs ys hlen tail v₁ S₁
    (by simpa [S₁,‹count ≠ src›.symm] using hsrc) (by simp [S₁,hsize])
    (by simpa [S₁,‹count ≠ buf›.symm] using hbuf)
    (by simpa [S₁,‹count ≠ saved›.symm] using hsaved)
    (by simpa [S₁,‹count ≠ tmp›.symm] using htmp)
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁' he₂).cast rfl ?_⟩
  · rw [hreplicas,hwidth] at hn₁
    rw [hsize] at hn₂
    have hc : N*(16*W+9) = N*(4*W+9)+12*(N*W) := by ring
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hic : i = count
    · subst i; simp [S₁,‹count ≠ src›,hcount]
    by_cases his : i = src
    · subst i; simp [S₁]
    · simp [S₁,his,hic]

def releaseComplexCounts (hold replicas nativeCount tmp : Fin T) : Pr P T Q A U :=
  .seq (usub hold replicas tmp) (.seq (uclear nativeCount) (uclear hold))

/-- Restore the original replica-header symbols after the 2N solve and erase
both owned counters. Every output and borrowed dimension remains untouched. -/
theorem releaseComplexCounts_exec {hold replicas nativeCount tmp : Fin T}
    (hreg : [hold,replicas,nativeCount,tmp].Nodup) (N : ℕ)
    (original : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hhold : (S.R hold).length = N)
    (hreplicas : S.R replicas = List.replicate N tick++original)
    (hnative : (S.R nativeCount).length = 2*N) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (releaseComplexCounts hold replicas nativeCount tmp) (mk v S) (10*N+8)
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          replicas original) nativeCount []) hold [])}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := usub_exec (body := body) ‹hold ≠ replicas› ‹hold ≠ tmp›
    ‹replicas ≠ tmp› v S htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R replicas original}
  have he₁' : Exec body (usub hold replicas tmp) (mk v S) (4*N+4) (mk v₁ S₁) := by
    simpa [S₁,hhold,hreplicas] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec (body := body) nativeCount v₁ S₁
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R nativeCount []}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) hold v₂ S₂
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ rfl⟩
  simp only [S₂,S₁,Function.update_of_ne ‹hold ≠ nativeCount›,
    Function.update_of_ne ‹hold ≠ replicas›,Function.update_of_ne ‹replicas ≠ nativeCount›.symm,
    hhold,hnative]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
