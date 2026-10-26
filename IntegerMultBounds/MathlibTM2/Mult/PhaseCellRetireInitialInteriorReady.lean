module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireInitialInterior

/-! Release the owned initial interior result and retain the computed residual. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

theorem retireInitialInterior_ready {P N q l s t u band : ℕ}
    (xs tail input : List (Fin (A+4))) (hlen : xs.length = s*(2*q+8))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 input (embStk componentReg S))
    (hsource : S.R 132 = xs++tail) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retireInitialInteriorCost q s ∧
      Exec (embTab componentReg body) retireInitialInterior (mk v S) n
        (mk v' {S with R := Function.update S.R 132 tail}) ∧
      LengthKeyReady P N q l s t u band 0 0 input
        (embStk componentReg {S with R := Function.update S.R 132 tail}) := by
  have hq : (S.R 119).length = q := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  have hfresh (r : Fin 144) (hr : r ∈ [(131 : Fin 144),134,135,136,137,140]) : S.R (componentReg r) = [] :=
    hready.fresh r hr
  obtain ⟨v',n,hu,hn,he⟩ := retireInitialInterior_exec (body := body) q s xs tail hlen v S hq hs
    hsource
    (by simpa [embStk,componentReg] using hready.blank 94 (by decide) (by decide) (by decide))
    (by simpa [componentReg] using hfresh 131 (by simp))
    (by simpa [componentReg] using hfresh 134 (by simp))
    (by simpa [componentReg] using hfresh 135 (by simp)) h147
  refine ⟨v',n,hu,hn,he,?_⟩
  have hproject : embStk componentReg {S with R := Function.update S.R 132 tail} =
      {(embStk componentReg S) with R := Function.update (embStk componentReg S).R 132 tail} := by
    simpa [componentReg] using componentProject_updateR_inner S 132 tail
  rw [hproject]
  exact hready.update_output tail

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
