module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Layer.Format

/-! Consume two owned words and a mask bit, retaining exactly the selected word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def publicationChoose (width chosen other dst trash tmp : Fin T) : Pr P₀ T Q A U :=
  .seq (transfer width chosen dst tmp) (discardPrefix width other trash tmp)

theorem publicationChoose_exec {width chosen other dst trash tmp : Fin T}
    (hreg : [width,chosen,other,dst,trash,tmp].Nodup)
    (selected rejected restSelected restRejected : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R chosen = selected++restSelected) (ho : S.R other = rejected++restRejected)
    (hlen : (S.R width).length = selected.length) (hlen' : rejected.length = selected.length)
    (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (publicationChoose width chosen other dst trash tmp) (mk v S)
        (10*selected.length+10)
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R chosen restSelected)
          other restRejected) dst (selected.reverse++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body)
    (count := width) (src := chosen) (dst := dst) (tmp := tmp)
    (show [width,chosen,dst,tmp].Nodup by simp_all) v S selected restSelected hs hlen htmp
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R chosen restSelected)
    dst (selected.reverse++S.R dst))}
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := width) (src := other) (trash := trash) (tmp := tmp)
    (show [width,other,trash,tmp].Nodup by simp_all) rejected restRejected v₁ S₁
    (by simpa [S₁,‹chosen ≠ other›.symm,‹other ≠ dst›] using ho)
    (by simpa [S₁,‹width ≠ chosen›,‹width ≠ dst›,hlen'] using hlen)
    (by simpa [S₁,‹chosen ≠ trash›.symm,‹dst ≠ trash›.symm] using htrash)
    (by simpa [S₁,‹chosen ≠ tmp›.symm,‹dst ≠ tmp›.symm] using htmp)
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · rw [hlen']; ring
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hc : k = chosen <;> by_cases ho' : k = other <;> by_cases hd : k = dst <;>
      simp_all [S₁]

def publicationSelectWord (width mask x y dst trash tmp : Fin T) : Pr P₀ T Q A U :=
  .seq (.act (.pop (.rt mask) (fun v o => {v with flag := pairRe (o.getD blank)}) .done))
    (.cond (·.flag) (publicationChoose width x y dst trash tmp)
      (publicationChoose width y x dst trash tmp))

theorem publicationSelectWord_exec {width mask x y dst trash tmp : Fin T}
    (hreg : [width,mask,x,y,dst,trash,tmp].Nodup) (hA : 4 ≤ A)
    (flag : Bool) (xs ys tailX tailY maskTail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hmask : S.R mask = pairSym A flag flag::maskTail)
    (hx : S.R x = xs++tailX) (hy : S.R y = ys++tailY)
    (hw : (S.R width).length = xs.length) (hlen : ys.length = xs.length)
    (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (publicationSelectWord width mask x y dst trash tmp) (mk v S)
        (10*xs.length+12)
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update
          S.R mask maskTail) x tailX) y tailY) dst ((if flag then xs else ys).reverse++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  let S₀ : Stacks T A := {S with R := Function.update S.R mask maskTail}
  have hpop : Exec body (.act (.pop (.rt mask)
      (fun v o => {v with flag := pairRe (o.getD blank)}) .done)) (mk v S) 1
      (mk {v with flag := flag} S₀) := by
    simpa [S₀,Action.run,update_rt,hmask,pairRe_pairSym hA] using
      (Exec.act (body := body) (.pop (.rt mask) (fun v o => {v with flag := pairRe (o.getD blank)}) .done) (mk v S))
  cases flag
  · obtain ⟨v',hu,he⟩ := publicationChoose_exec (body := body)
      (width := width) (chosen := y) (other := x) (dst := dst) (trash := trash) (tmp := tmp)
      (by regs_nodup) ys xs tailY tailX {v with flag := false} S₀
      (by simpa [S₀,‹mask ≠ y›.symm] using hy) (by simpa [S₀,‹mask ≠ x›.symm] using hx)
      (by simpa [S₀,‹width ≠ mask›,hlen] using hw) hlen.symm
      (by simpa [S₀,‹mask ≠ trash›.symm] using htrash)
      (by simpa [S₀,‹mask ≠ tmp›.symm] using htmp)
    refine ⟨v',hu,(Exec.seq hpop (Exec.cond_false rfl he)).cast ?_ ?_⟩
    · omega
    · apply congrArg (mk v')
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hx' : k = x <;> by_cases hy' : k = y <;> by_cases hm : k = mask <;> by_cases hd : k = dst <;>
        simp_all [S₀,Function.update_apply]
  · obtain ⟨v',hu,he⟩ := publicationChoose_exec (body := body)
      (width := width) (chosen := x) (other := y) (dst := dst) (trash := trash) (tmp := tmp)
      (by regs_nodup) xs ys tailX tailY {v with flag := true} S₀
      (by simpa [S₀,‹mask ≠ x›.symm] using hx) (by simpa [S₀,‹mask ≠ y›.symm] using hy)
      (by simpa [S₀,‹width ≠ mask›] using hw) hlen
      (by simpa [S₀,‹mask ≠ trash›.symm] using htrash)
      (by simpa [S₀,‹mask ≠ tmp›.symm] using htmp)
    exact ⟨v',hu,(Exec.seq hpop (Exec.cond_true rfl he)).cast (by omega)
      (by simp [S₀,‹mask ≠ dst›.symm])⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
