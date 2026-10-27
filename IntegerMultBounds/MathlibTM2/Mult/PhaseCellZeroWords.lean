module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Append a generated number of encoded zero words above a borrowed suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def zeroWords (rows width dst count saved tmp : Fin T) : Pr P₀ T Q A U :=
  .seq (unaryProduct rows width count saved tmp)
    (.seq (copyR count dst saved (fun _ => pairSym A false false)) (uclear count))

theorem zeroWords_exec {rows width dst count saved tmp : Fin T}
    (hreg : [rows,width,dst,count,saved,tmp].Nodup) (n w : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hn : (S.R rows).length = n) (hw : (S.R width).length = w)
    (hcount : S.R count = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 10*n*w+9*n+10 ∧
      Exec body (zeroWords rows width dst count saved tmp) (mk v S) m
        (mk v' {S with R := Function.update S.R dst (cstream A w (List.replicate n 0)++S.R dst)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := rows) (b := width) (dst := count) (t₁ := saved) (t₂ := tmp) (by regs_nodup) v S hsaved htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R count (List.replicate (n*w) tick)}
  have he₁' : Exec body (unaryProduct rows width count saved tmp) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,hn,hw,hcount] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := copyR_exec body count dst saved ‹dst ≠ count›.symm ‹count ≠ saved› ‹dst ≠ saved›
    (fun _ => pairSym A false false) v₁ S₁ (by simpa [S₁,‹count ≠ saved›.symm] using hsaved)
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R dst (List.replicate (n*w) (pairSym A false false)++S.R dst)}
  have he₂' : Exec body (copyR count dst saved (fun _ => pairSym A false false))
      (mk v₁ S₁) (4*(n*w)+4) (mk v₂ S₂) := by simpa [S₂,S₁,‹dst ≠ count›] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) count v₂ S₂
  refine ⟨v₃,m₁+((4*(n*w)+4)+(2*(n*w)+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast (by simp [S₂,S₁,‹dst ≠ count›.symm]) ?_⟩
  · have hh : m₁ ≤ n*(4*w+9)+4 := by simpa only [hn,hw] using hm₁
    nlinarith only [hh]
  · have hz : cstream A w (List.replicate n 0) = List.replicate (n*w) (pairSym A false false) := by
      simp [cstream,csyms_zero,List.flatMap_replicate,List.flatten_replicate_replicate]
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hd : k = dst <;> by_cases hc : k = count <;>
      simp_all [S₂,S₁,hz,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
