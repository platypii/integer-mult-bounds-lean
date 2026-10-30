module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExpandComplexPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate a key-local expansion count before the shared real factor batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def expandComplexKey (replicas width count src imag saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct replicas width count saved tmp)
    (.seq (expandComplexPrefix count src imag saved tmp) (uclear count))

/-- Expand only the current key, generating and erasing its symbol count from
retained replica/packet dimensions. The resulting 2N real RHSs can share one
factor setup. No counter or transformed-source witness is supplied. -/
theorem expandComplexKey_exec {replicas width count src imag saved tmp : Fin T}
    (hreg : [replicas,width,count,src,imag,saved,tmp].Nodup) (hA : 4 ≤ A)
    (N W w : ℕ) (zs : List GaussianInt) (hlen : zs.length*w = N*W)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = N) (hwidth : (S.R width).length = W)
    (hsrc : S.R src = cstream A w zs++tail)
    (hcount : S.R count = []) (himag : S.R imag = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ N*(26*W+9)+26 ∧
      Exec body (expandComplexKey replicas width count src imag saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update S.R src
          (cstream A w (zs.map realPartWord++zs.map imagPartWord)++tail))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [replicas,width,count,saved,tmp].Nodup by regs_nodup) v S hsaved htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R count (List.replicate (N*W) tick)}
  have he₁' : Exec body (unaryProduct replicas width count saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hreplicas,hwidth,hcount] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := expandComplexPrefix_exec (body := body)
    (show [count,src,imag,saved,tmp].Nodup by regs_nodup) hA w zs tail v₁ S₁
    (by simpa [S₁,‹count ≠ src›.symm] using hsrc) (by simp [S₁,hlen])
    (by simpa [S₁,‹count ≠ imag›.symm] using himag)
    (by simpa [S₁,‹count ≠ saved›.symm] using hsaved)
    (by simpa [S₁,‹count ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := {S₁ with R := (Function.update S₁.R src
    (cstream A w (zs.map realPartWord++zs.map imagPartWord)++tail))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) count v₂ S₂
  refine ⟨v₃,n₁+(20*(zs.length*w)+20)+(2*(N*W)+2),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · rw [hreplicas,hwidth] at hn₁
    rw [hlen]
    have hc : N*(26*W+9) = N*(4*W+9)+22*(N*W) := by ring
    omega
  · simp [S₂,S₁,‹count ≠ src›,Nat.add_assoc]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hic : i = count
    · subst i; simp [S₂,S₁,‹count ≠ src›,hcount]
    by_cases his : i = src
    · subst i; simp [S₂,S₁,‹count ≠ src›.symm]
    · simp [S₂,S₁,his,hic]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
