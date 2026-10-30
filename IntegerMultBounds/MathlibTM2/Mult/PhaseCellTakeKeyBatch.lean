module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream

/-! Isolate one routed key batch before key-specific numerical conversion. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def takeKeyBatch (replicas width count src dst buf saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct replicas width count saved tmp)
    (.seq (takePrefix count src dst buf tmp) (uclear count))

/-- Take precisely one key's replicas. Generate and dispose the total prefix
counter, preserving all dimension symbols and the untouched later-key suffix. -/
theorem takeKeyBatch_exec {replicas width count src dst buf saved tmp : Fin T}
    (hreg : [replicas,width,count,src,dst,buf,saved,tmp].Nodup)
    (N W : ℕ) (xs tail : List (Fin (A+4))) (hlen : xs.length = N*W)
    (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = N) (hwidth : (S.R width).length = W)
    (hsrc : S.R src = xs++tail) (hcount : S.R count = [])
    (hbuf : S.R buf = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ N*(12*W+9)+12 ∧
      Exec body (takeKeyBatch replicas width count src dst buf saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src tail) dst (xs++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [replicas,width,count,saved,tmp].Nodup by regs_nodup) v S hsaved htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R count (List.replicate (N*W) tick)}
  have he₁' : Exec body (unaryProduct replicas width count saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hreplicas,hwidth,hcount] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := takePrefix_exec (body := body)
    (show [count,src,dst,buf,tmp].Nodup by regs_nodup) v₁ S₁ xs tail
    (by simpa [S₁,‹count ≠ src›.symm] using hsrc) (by simp [S₁,hlen])
    (by simpa [S₁,‹count ≠ buf›.symm] using hbuf)
    (by simpa [S₁,‹count ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := {S₁ with R := (Function.update (Function.update S₁.R src tail) dst (xs++S₁.R dst))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) count v₂ S₂
  refine ⟨v₃,n₁+(6*xs.length+6)+(2*(N*W)+2),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · rw [hreplicas,hwidth] at hn₁
    rw [hlen]
    have hc : N*(12*W+9) = N*(4*W+9)+8*(N*W) := by ring
    omega
  · simp [S₂,S₁,‹count ≠ src›,‹count ≠ dst›,Nat.add_assoc]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hic : i = count
    · subst i; simp [S₂,S₁,‹count ≠ src›,‹count ≠ dst›,hcount]
    by_cases his : i = src
    · subst i; simp [S₂,S₁,‹count ≠ src›.symm,‹src ≠ dst›]
    by_cases hid : i = dst
    · subst i; simp [S₂,S₁,‹count ≠ dst›.symm]
    · simp [S₂,S₁,hic,his,hid]

/-- The isolated source is exactly the numerical coefficient stream, with the
remaining key batches retained verbatim on the routing source. -/
theorem takeCoefficientKeyBatch_exec {replicas width count src dst buf saved tmp : Fin T}
    (hreg : [replicas,width,count,src,dst,buf,saved,tmp].Nodup)
    (N L w : ℕ) (xs : List GaussianInt) (hlen : xs.length = N*L)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = N) (hwidth : (S.R width).length = L*w)
    (hsrc : S.R src = cstream A w xs++tail) (hdst : S.R dst = [])
    (hcount : S.R count = []) (hbuf : S.R buf = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ N*(12*(L*w)+9)+12 ∧
      Exec body (takeKeyBatch replicas width count src dst buf saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src tail) dst (cstream A w xs))}) := by
  simpa only [hdst,List.append_nil] using takeKeyBatch_exec (body := body) hreg N (L*w)
    (cstream A w xs) tail (by simp [hlen,Nat.mul_assoc]) v S hreplicas hwidth hsrc hcount hbuf hsaved htmp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
