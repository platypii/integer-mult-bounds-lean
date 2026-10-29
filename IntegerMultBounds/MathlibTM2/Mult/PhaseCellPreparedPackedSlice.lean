module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSliceExec
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate symbol counts from word headers, publish a packed slice, and restore
all private controls. No ambient-prefix traversal or supplied scaled tape is needed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def preparedPackedSlice (offsetRows rows wordWidth src dst skip count savedSkip saved trash tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct offsetRows wordWidth skip trash tmp)
    (.seq (unaryProduct rows wordWidth count trash tmp)
      (.seq (copySlice skip count src dst savedSkip saved tmp) (clearWords [skip,count])))

def preparedPackedSliceCost (offset n w : ℕ) : ℕ :=
  offset*(12*w+9)+n*(16*w+9)+29

theorem preparedPackedSlice_exec {s : ℕ}
    (offsetRows rows wordWidth src dst skip count savedSkip saved trash tmp : Fin T)
    (hreg : [offsetRows,rows,wordWidth,src,dst,skip,count,savedSkip,saved,trash,tmp].Nodup)
    (a L offset n w : ℕ) (F : ZMod s → GaussianInt) (hfit : a+L ≤ s) (hpart : offset+n ≤ L)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hoffset : (S.R offsetRows).length = offset) (hrows : (S.R rows).length = n)
    (hwidth : (S.R wordWidth).length = w)
    (hsrc : S.R src = cstream A w (packedInterval a L F)++tail)
    (hfresh : ∀ i ∈ [skip,count,savedSkip,saved,trash,tmp], S.R i = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ preparedPackedSliceCost offset n w ∧
      Exec body (preparedPackedSlice offsetRows rows wordWidth src dst skip count savedSkip saved trash tmp)
        (mk v S) m (mk v' {S with R := (Function.update S.R dst
          (cstream A w (packedInterval (a+offset) n F)++S.R dst))}) := by
  have h₁ : [offsetRows,wordWidth,skip,trash,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg ⊢
    tauto
  have h₂ : [rows,wordWidth,count,trash,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg ⊢
    tauto
  have hslice : [skip,count,src,dst,savedSkip,saved,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg ⊢
    tauto
  have hne : skip ≠ count ∧ src ≠ skip ∧ src ≠ count ∧ dst ≠ skip ∧ dst ≠ count ∧
      rows ≠ skip ∧ wordWidth ≠ skip ∧ count ≠ skip ∧ trash ≠ skip ∧ tmp ≠ skip ∧
      trash ≠ count ∧ tmp ≠ count ∧ savedSkip ≠ skip ∧ savedSkip ≠ count ∧ saved ≠ skip ∧ saved ≠ count := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg
    tauto
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body) h₁ v S
    (hfresh trash (by simp)) (hfresh tmp (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R skip (List.replicate (offset*w) tick)}
  have he₁' : Exec body (unaryProduct offsetRows wordWidth skip trash tmp) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hoffset,hwidth,hfresh skip (by simp),List.append_nil] using he₁
  have hm₁' : m₁ ≤ offset*(4*w+9)+4 := by simpa only [hoffset,hwidth] using hm₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := unaryProduct_exec (body := body) h₂ v₁ S₁
    (by simpa [S₁,hne] using hfresh trash (by simp)) (by simpa [S₁,hne] using hfresh tmp (by simp))
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R count (List.replicate (n*w) tick)}
  have he₂' : Exec body (unaryProduct rows wordWidth count trash tmp) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,hne,hrows,hwidth,hfresh count (by simp)] using he₂
  have hm₂' : m₂ ≤ n*(4*w+9)+4 := by simpa [S₁,hne,hrows,hwidth] using hm₂
  obtain ⟨v₃,hu₃,he₃⟩ := packedSlice_exec (body := body) hslice a L offset n w F hfit hpart tail v₂ S₂
    (by simpa [S₂,S₁,hne] using hsrc)
    (by simp [S₂,S₁,hne]) (by simp [S₂])
    (by simpa [S₂,S₁,hne] using hfresh savedSkip (by simp))
    (by simpa [S₂,S₁,hne] using hfresh saved (by simp))
    (by simpa [S₂,S₁,hne] using hfresh tmp (by simp))
  let S₃ : Stacks T A := {S₂ with R := (Function.update S₂.R dst
    (cstream A w (packedInterval (a+offset) n F)++S.R dst))}
  have he₃' : Exec body (copySlice skip count src dst savedSkip saved tmp) (mk v₂ S₂)
      (6*(offset*w)+10*(n*w)+16) (mk v₃ S₃) := by simpa only [S₁,S₂,Function.update_of_ne hne.2.2.2.1,Function.update_of_ne hne.2.2.2.2.1] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [skip,count] (by simp [hne.1]) v₃ S₃
  have hclear : 2*(([skip,count].map fun i => (S₃.R i).length).sum)+2*[skip,count].length+1 =
      2*(offset*w+n*w)+5 := by simp [S₃,S₂,S₁,hne,hne.2.2.2.1.symm,hne.2.2.2.2.1.symm]
  refine ⟨v₄,m₁+(m₂+((6*(offset*w)+10*(n*w)+16)+(2*(offset*w+n*w)+5))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast (by rw [hclear]) ?_⟩
  · dsimp [preparedPackedSliceCost]
    nlinarith only [hm₁',hm₂']
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hskip : i = skip <;> by_cases hcount : i = count <;>
      by_cases hdst : i = dst <;>
      simp [S₃,S₂,S₁,hskip,hcount,hdst,hne,hne.2.2.2.1.symm,hne.2.2.2.2.1.symm,hfresh skip (by simp),hfresh count (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
