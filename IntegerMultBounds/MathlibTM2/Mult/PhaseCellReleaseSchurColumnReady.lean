module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseSchurColumnInput

/-! Release the intermediate original column while preserving solver readiness. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

theorem releaseSchurColumnInput_ready {P N q l s t u band : ℕ}
    (xs ys tail : List (Fin (A+4))) (hx : xs.length = s*(2*q+8)) (hy : ys.length = s*(2*q+8))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 (xs++(ys++tail)) (embStk componentReg S))
    (h138 : S.R 138 = []) (h147 : S.R 147 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseSchurColumnInputCost q s ∧
      Exec (embTab componentReg body) releaseSchurColumnInput (mk v S) m
        (mk v' {S with R := Function.update S.R 110 (xs++tail)}) ∧
      LengthKeyReady P N q l s t u band 0 0 (xs++tail)
        (embStk componentReg {S with R := Function.update S.R 110 (xs++tail)}) := by
  have hq : (S.R 119).length = q := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  have hfresh (r : Fin 144) (hr : r ∈ [(131 : Fin 144),134,135,136,137,140]) : S.R (componentReg r) = [] := hready.fresh r hr
  obtain ⟨v',m,hu,hm,he⟩ := releaseSchurColumnInput_exec (body := body) q s xs ys tail hx hy v S hq hs
    (by simpa [embStk,componentReg] using hready.source)
    (by simpa [embStk,componentReg] using hready.blank 94 (by decide) (by decide) (by decide))
    (by simpa [componentReg] using hfresh 131 (by simp)) (by simpa [componentReg] using hfresh 134 (by simp))
    (by simpa [componentReg] using hfresh 135 (by simp)) (by simpa [componentReg] using hfresh 137 (by simp)) h138 h147
  refine ⟨v',m,hu,hm,he,?_⟩
  have hproject : embStk componentReg {S with R := Function.update S.R 110 (xs++tail)} =
      {(embStk componentReg S) with R := Function.update (embStk componentReg S).R 110 (xs++tail)} := by
    simpa [componentReg] using componentProject_updateR_inner S 110 (xs++tail)
  rw [hproject]
  exact hready.update_source (xs++tail)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
