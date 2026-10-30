module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenPackedPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate and dispose the local common-width publication count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def widenPackedKey (wide width replicas rowWidth count src work saved tmp extra : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct replicas rowWidth count saved tmp)
    (.seq (widenPackedPrefix wide width count src work saved tmp extra) (uclear count))

def widenPackedKeyCost (w W N R coefficients : ℕ) : ℕ :=
  widenPackedPrefixCost w W coefficients+N*(6*R+9)+6

/-- Generate the current key's symbol count from N and its narrow output row
width. Retained headers restore, generated count and scratch clear, and later
keys retain their original encoding. -/
theorem widenPackedKey_exec {wide width replicas rowWidth count src work saved tmp extra : Fin T}
    (hreg : [wide,width,replicas,rowWidth,count,src,work,saved,tmp,extra].Nodup)
    (w W N R : ℕ) (hw : 1 ≤ w) (hwidth : w ≤ W)
    (xs : List GaussianInt) (hfit : ∀ z ∈ xs, TopFitsZ w z) (hlen : xs.length*w = N*R)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwide : (S.R wide).length = W) (hword : (S.R width).length = w)
    (hreplicas : (S.R replicas).length = N) (hrow : (S.R rowWidth).length = R)
    (hsrc : S.R src = cstream A w xs++tail)
    (hblank : ∀ r ∈ [count,work,saved,tmp,extra], S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ widenPackedKeyCost w W N R xs.length ∧
      Exec body (widenPackedKey wide width replicas rowWidth count src work saved tmp extra) (mk v S) n
        (mk v' {S with R := Function.update S.R src (cstream A W xs++tail)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [replicas,rowWidth,count,saved,tmp].Nodup by regs_nodup) v S
    (hblank saved (by simp)) (hblank tmp (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R count (List.replicate (N*R) tick)}
  have he₁' : Exec body (unaryProduct replicas rowWidth count saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hreplicas,hrow,hblank count (by simp)] using he₁
  have hsmall : ∀ r ∈ [work,saved,tmp,extra], S₁.R r = [] := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [S₁, *, Ne.symm]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := widenPackedPrefix_exec (body := body)
    (show [wide,width,count,src,work,saved,tmp,extra].Nodup by regs_nodup) w W hw hwidth xs hfit tail v₁ S₁
    (by simpa [S₁,‹wide ≠ count›] using hwide) (by simpa [S₁,‹width ≠ count›] using hword)
    (by simp [S₁,hlen]) (by simpa [S₁,‹count ≠ src›.symm] using hsrc) hsmall
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src (cstream A W xs++tail)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) count v₂ S₂
  refine ⟨v₃,n₁+n₂+(2*(N*R)+2),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · rw [hreplicas,hrow] at hn₁
    unfold widenPackedKeyCost
    have hc : N*(6*R+9) = N*(4*R+9)+2*(N*R) := by ring
    omega
  · simp [S₂,S₁,‹count ≠ src›,Nat.add_assoc]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hic : i = count
    · subst i; simp [S₂,S₁,‹count ≠ src›,hblank count (by simp)]
    by_cases his : i = src
    · subst i; simp [S₂,S₁,‹count ≠ src›.symm]
    · simp [S₂,S₁,hic,his]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
