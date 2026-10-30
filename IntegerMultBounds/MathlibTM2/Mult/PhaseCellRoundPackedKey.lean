module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundPackedPrefix

/-! Generate and release the current key's rounding prefix count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def roundPackedKey (rg : TblR 8 → Fin T) (ports : Fin 4 → Fin T)
    (replicas width count src work saved tmp sp sg cy : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct replicas width count saved tmp)
    (.seq (roundPackedPrefix rg ports count src work saved tmp sp sg cy) (uclear count))

def roundPackedKeyCost (B w k N W coefficients : ℕ) : ℕ :=
  13*tblC B 0+16*w+44*B+54+N*(6*W+9)+coefficients*(20*w+4*k+23)

/-- The caller provides retained dimensions, not a prepared symbol count.
Generated count and rounding controls restore, along with all scalar state;
only the current output packets change. -/
theorem roundPackedKey_exec (hA : 4 ≤ A)
    (rg : TblR 8 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports)
    (hsep : ∀ i r, rg r ≠ ports i)
    {replicas width count src work saved tmp sp sg cy : Fin T}
    (hreg : [replicas,width,count,src,work,saved,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup)
    (hscalar : ∀ r, rg r ∉ [count,src,work,saved])
    (B w q p j E N W : ℕ) (wl : List (Fin (A+4))) (hwl : wl.length = B)
    (st : TblSt 8 A) (hval : st.val = ![w,q,p,j,E,0,0,0])
    (hp : p ≤ q) (hw : 1 ≤ w) (hsize : q-p+j+(p+E+5) ≤ w)
    (hroom : w < 2^B) (hfit : ∀ i, st.val i < 2^B)
    (xs : List GaussianInt) (hlen : xs.length*w = N*W)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho B wl [] st))
    (hreplicas : (S.R replicas).length = N) (hwidth : (S.R width).length = W)
    (hsrc : S.R src = cstream A w xs++tail)
    (hblank : ∀ r ∈ [count,work,saved,tmp,sp,sg,cy], S.R r = [])
    (hheaders : ∀ i, S.R (ports i) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ roundPackedKeyCost B w (p+E+5) N W xs.length ∧
      Exec body (roundPackedKey rg ports replicas width count src work saved tmp sp sg cy) (mk v S) n
        (mk v' {S with R := (Function.update S.R src
          (cstream A (p+E+5) (xs.map (finalRoundWord w q p j))++tail))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [replicas,width,count,saved,tmp].Nodup by regs_nodup) v S
    (hblank saved (by simp)) (hblank tmp (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R count (List.replicate (N*W) tick)}
  have he₁' : Exec body (unaryProduct replicas width count saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hreplicas,hwidth,hblank count (by simp)] using he₁
  have htable : tblHolds rg S₁ (tblRho B wl [] st) := by
    intro r
    have hne : rg r ≠ count := by intro he; exact hscalar r (by simp [he])
    simpa [S₁,hne] using hS r
  have hsmall : ∀ r ∈ [work,saved,tmp,sp,sg,cy], S₁.R r = [] := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [S₁,Function.update_apply, *, Ne.symm]
  have hhead : ∀ i, S₁.R (ports i) = [] := by
    intro i
    fin_cases i <;> simp [S₁,Function.update_apply, *, Ne.symm]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := roundPackedPrefix_exec (body := body) hA rg hrg ports hports hsep
    (show [count,src,work,saved,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup by regs_nodup)
    (by intro r hr; exact hscalar r (List.mem_cons_of_mem count hr))
    B w q p j E wl hwl st hval hp hw hsize hroom hfit xs tail v₁ S₁ htable
    (by simpa [S₁,‹count ≠ src›.symm] using hsrc) (by simp [S₁,hlen]) hsmall hhead
  let output := cstream A (p+E+5) (xs.map (finalRoundWord w q p j))++tail
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src output}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) count v₂ S₂
  refine ⟨v₃,n₁+n₂+(2*(N*W)+2),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · rw [hreplicas,hwidth] at hn₁
    unfold roundPackedKeyCost
    have hc : N*(6*W+9) = N*(4*W+9)+2*(N*W) := by ring
    omega
  · simp [S₂,S₁,‹count ≠ src›,Nat.add_assoc]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hic : i = count
    · subst i; simp [S₂,S₁,‹count ≠ src›,hblank count (by simp)]
    by_cases his : i = src
    · subst i; simp [S₂,S₁,‹count ≠ src›.symm,output]
    · simp [S₂,S₁,hic,his]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
