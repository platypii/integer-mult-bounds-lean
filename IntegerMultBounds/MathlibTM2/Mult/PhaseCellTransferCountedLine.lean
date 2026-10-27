module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Transfer a line prefix with generated row/width controls and exact restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def transferCountedLine (rows width src dst count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct rows width count saved tmp)
    (.seq (transfer count src dst tmp) (uclear count))

def transferCountedLineCost (s w : ℕ) : ℕ := s*(10*w+9)+10

theorem transferCountedLine_exec (rows width src dst count saved tmp : Fin T)
    (hreg : [rows,width,src,dst,count,saved,tmp].Nodup) (s w : ℕ)
    (words tail : List (Fin (A+4))) (hlen : words.length = s*w)
    (v : HS T Q A U) (S : Stacks T A)
    (hs : (S.R rows).length = s) (hw : (S.R width).length = w)
    (hsource : S.R src = words++tail) (hcount : S.R count = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ transferCountedLineCost s w ∧
      Exec body (transferCountedLine rows width src dst count saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src tail) dst (words.reverse++S.R dst))}) := by
  have h5 : [rows,width,count,saved,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg ⊢
    tauto
  have hc : [count,src,dst,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg ⊢
    tauto
  have hn : src ≠ count ∧ dst ≠ count ∧ saved ≠ count ∧ tmp ≠ count := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg
    tauto
  have hsd : src ≠ dst := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hc
    tauto
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := rows) (b := width) (dst := count) (t₁ := saved) (t₂ := tmp) h5 v S hsaved htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R count (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct rows width count saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hs,hw,hcount,List.append_nil] using he₁
  have hn₁' : n₁ ≤ s*(4*w+9)+4 := by simpa only [hs,hw] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) hc v₁ S₁ words tail
    (by simpa [S₁,hn.1] using hsource) (by simp [S₁,hlen])
    (by simpa [S₁,hn.2.2.2] using htmp)
  let S₂ : Stacks T A := {S₁ with R := (Function.update (Function.update S₁.R src tail) dst (words.reverse++S₁.R dst))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body count v₂ S₂
  have hclock : (S₂.R count).length = s*w := by simp [S₂,S₁,hn.2.1.symm,hn.1.symm]
  refine ⟨v₃,n₁+((4*words.length+4)+(2*(S₂.R count).length+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hlen,hclock]
    dsimp only [transferCountedLineCost]
    nlinarith only [hn₁']
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hiCount : i = count <;> by_cases hiDst : i = dst <;> by_cases hiSrc : i = src <;>
      simp [S₂,S₁,hiCount,hiDst,hiSrc,hn.1,hn.1.symm,hn.2.1,hn.2.1.symm,hsd,hcount]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
