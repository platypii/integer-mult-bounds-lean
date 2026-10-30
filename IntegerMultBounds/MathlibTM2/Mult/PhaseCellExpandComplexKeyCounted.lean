module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExpandComplexKey

/-! Retain the original replica count while preparing a single 2N RHS solve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def expandComplexKeyCounted (replicas width count src imag saved tmp hold : Fin T) : Pr P T Q A U :=
  .seq (ucopy replicas hold tmp)
    (.seq (expandComplexKey replicas width count src imag saved tmp) (ucopy hold replicas tmp))

/-- The expanded key has 2N real RHSs. Preserve N in an owned counter for
output pairing and later restoration of the original replica-header symbols. -/
theorem expandComplexKeyCounted_exec {replicas width count src imag saved tmp hold : Fin T}
    (hreg : [replicas,width,count,src,imag,saved,tmp,hold].Nodup) (hA : 4 ≤ A)
    (N W w : ℕ) (zs : List GaussianInt) (hlen : zs.length*w = N*W)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = N) (hwidth : (S.R width).length = W)
    (hsrc : S.R src = cstream A w zs++tail)
    (hcount : S.R count = []) (himag : S.R imag = []) (hsaved : S.R saved = [])
    (htmp : S.R tmp = []) (hhold : S.R hold = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ N*(26*W+17)+34 ∧
      Exec body (expandComplexKeyCounted replicas width count src imag saved tmp hold) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R hold
          (List.replicate N tick)) src (cstream A w (zs.map realPartWord++zs.map imagPartWord)++tail))
            replicas (List.replicate N tick++S.R replicas))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) ‹replicas ≠ hold› ‹replicas ≠ tmp›
    ‹tmp ≠ hold›.symm v S htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R hold (List.replicate N tick)}
  have he₁' : Exec body (ucopy replicas hold tmp) (mk v S) (4*N+4) (mk v₁ S₁) := by
    simpa [S₁,hreplicas,hhold] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := expandComplexKey_exec (body := body)
    (show [replicas,width,count,src,imag,saved,tmp].Nodup by regs_nodup) hA N W w zs hlen tail v₁ S₁
    (by simpa [S₁,‹replicas ≠ hold›] using hreplicas)
    (by simpa [S₁,‹width ≠ hold›] using hwidth)
    (by simpa [S₁,‹src ≠ hold›] using hsrc)
    (by simpa [S₁,‹count ≠ hold›] using hcount)
    (by simpa [S₁,‹imag ≠ hold›] using himag)
    (by simpa [S₁,‹saved ≠ hold›] using hsaved)
    (by simpa [S₁,‹tmp ≠ hold›] using htmp)
  let S₂ : Stacks T A := {S₁ with R := (Function.update S₁.R src
    (cstream A w (zs.map realPartWord++zs.map imagPartWord)++tail))}
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec (body := body) ‹replicas ≠ hold›.symm ‹tmp ≠ hold›.symm
    ‹replicas ≠ tmp› v₂ S₂ (by simpa [S₂,S₁,‹src ≠ tmp›.symm,‹tmp ≠ hold›] using htmp)
  refine ⟨v₃,(4*N+4)+n₂+(4*N+4),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · have hc : N*(26*W+17) = N*(26*W+9)+8*N := by ring
    omega
  · simp [S₂,S₁,‹src ≠ hold›.symm,Nat.add_assoc]
  · apply congrArg (mk v₃)
    simp [S₂,S₁,‹replicas ≠ hold›,‹replicas ≠ src›,‹src ≠ hold›.symm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
