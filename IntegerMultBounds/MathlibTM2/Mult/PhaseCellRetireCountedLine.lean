module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Retire an owned line using retained row and word-width masters, restoring all private controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retireCountedLine (rows width src count trash tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct rows width count trash tmp)
    (.seq (discardPrefix count src trash tmp) (uclear count))

def retireCountedLineCost (s w : ℕ) : ℕ := s*(12*w+9)+12

theorem retireCountedLine_exec (rows width src count trash tmp : Fin T)
    (hreg : [rows,width,src,count,trash,tmp].Nodup) (s w : ℕ) (residual tail : List (Fin (A+4)))
    (hlen : residual.length = s*w) (v : HS T Q A U) (S : Stacks T A)
    (hs : (S.R rows).length = s) (hw : (S.R width).length = w)
    (hsource : S.R src = residual++tail)
    (hcount : S.R count = []) (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retireCountedLineCost s w ∧
      Exec body (retireCountedLine rows width src count trash tmp) (mk v S) n
        (mk v' {S with R := Function.update S.R src tail}) := by
  have h5 : [rows,width,count,trash,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg ⊢
    tauto
  have h4 : [count,src,trash,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg ⊢
    tauto
  have hsrcCount : src ≠ count := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg
    tauto
  have htrashCount : trash ≠ count := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at h4
    tauto
  have htmpCount : tmp ≠ count := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at h4
    tauto
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := rows) (b := width) (dst := count) (t₁ := trash) (t₂ := tmp) h5 v S htrash htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R count (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct rows width count trash tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hs,hw,hcount,List.append_nil] using he₁
  have hn₁' : n₁ ≤ s*(4*w+9)+4 := by simpa only [hs,hw] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := count) (src := src) (trash := trash) (tmp := tmp) h4
    residual tail v₁ S₁ (by simpa [S₁,hsrcCount] using hsource) (by simp [S₁,hlen])
    (by simpa [S₁,htrashCount] using htrash) (by simpa [S₁,htmpCount] using htmp)
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src tail}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body count v₂ S₂
  have hclock : (S₂.R count).length = s*w := by simp [S₂,S₁,hsrcCount.symm]
  refine ⟨v₃,n₁+((6*residual.length+6)+(2*(S₂.R count).length+2)),
    hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hlen,hclock]
    dsimp only [retireCountedLineCost]
    nlinarith only [hn₁']
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hsrc : i = src <;> by_cases hcountIdx : i = count <;> simp [S₂,S₁,hsrc,hcountIdx,hcount,hsrcCount,hsrcCount.symm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
