module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Restoring indexed word access with a generated symbol offset and paid source motion. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def copyIndexedWord (index width src dst skip savedSkip saved tmp work₁ work₂ : Fin T) : Pr P₀ T Q A U :=
  .seq (unaryProduct index width skip work₁ work₂)
    (.seq (copySlice skip width src dst savedSkip saved tmp) (uclear skip))

theorem copyIndexedWord_exec {index width src dst skip savedSkip saved tmp work₁ work₂ : Fin T}
    (hreg : [index,width,src,dst,skip,savedSkip,saved,tmp,work₁,work₂].Nodup)
    (w j : ℕ) (xs : List GaussianInt) (hj : j < xs.length)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hindex : (S.R index).length = j) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = cstream A w xs++tail)
    (hfresh : ∀ r ∈ [skip,savedSkip,saved,tmp,work₁,work₂], S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ j*(12*w+9)+10*w+22 ∧
      Exec body (copyIndexedWord index width src dst skip savedSkip saved tmp work₁ work₂) (mk v S) m
        (mk v' {S with R := Function.update S.R dst (csyms A w xs[j]++S.R dst)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := index) (b := width) (dst := skip) (t₁ := work₁) (t₂ := work₂)
    (by regs_nodup) v S (hfresh work₁ (by simp)) (hfresh work₂ (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R skip (List.replicate (j*w) tick)}
  have he₁' : Exec body (unaryProduct index width skip work₁ work₂) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hindex,hwidth,hfresh skip (by simp)] using he₁
  have hn₁' : n₁ ≤ j*(4*w+9)+4 := by simpa [hindex,hwidth] using hn₁
  have hpart : xs.take j ++ [xs[j]] ++ xs.drop (j+1) = xs := by
    simpa only [List.take_one_drop_eq_of_lt_length hj,List.get_eq_getElem,List.drop_drop,Nat.add_comm 1] using slice_split xs j 1
  obtain ⟨v₂,hu₂,he₂⟩ := copySlice_coeffs_exec (body := body)
    (skip := skip) (count := width) (src := src) (dst := dst) (savedSkip := savedSkip) (saved := saved) (tmp := tmp)
    (by regs_nodup) v₁ S₁ w (xs.take j) [xs[j]] (xs.drop (j+1)) tail
    (by simpa [S₁,‹src ≠ skip›,hpart] using hsrc)
    (by simp [S₁,List.length_take,Nat.min_eq_left hj.le])
    (by simpa [S₁,‹width ≠ skip›] using hwidth)
    (by simpa [S₁,‹skip ≠ savedSkip›.symm] using hfresh savedSkip (by simp))
    (by simpa [S₁,‹skip ≠ saved›.symm] using hfresh saved (by simp))
    (by simpa [S₁,‹skip ≠ tmp›.symm] using hfresh tmp (by simp))
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R dst (csyms A w xs[j]++S₁.R dst)}
  have he₂' : Exec body (copySlice skip width src dst savedSkip saved tmp) (mk v₁ S₁)
      (6*(j*w)+10*w+16) (mk v₂ S₂) := by
    simpa [S₂,List.length_take,Nat.min_eq_left hj.le] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body skip v₂ S₂
  have he₃' : Exec body (uclear skip) (mk v₂ S₂) (2*(j*w)+2)
      (mk v₃ {S with R := Function.update S.R dst (csyms A w xs[j]++S.R dst)}) := by
    convert he₃ using 1
    · simp [S₂,S₁,‹dst ≠ skip›.symm]
    · apply congrArg (mk v₃)
      refine Stacks.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · funext r
        by_cases hs : r = skip
        · subst r; simp [S₂,S₁,‹dst ≠ skip›.symm,hfresh skip (by simp)]
        by_cases hd : r = dst
        · subst r; simp [S₂,S₁,‹dst ≠ skip›]
        simp [S₂,S₁,hs,hd]
  refine ⟨v₃,n₁+((6*(j*w)+10*w+16)+(2*(j*w)+2)),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁' (Exec.seq he₂' he₃')⟩
  nlinarith only [hn₁']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
