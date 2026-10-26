module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentTransition

/-! The component transition returns the released bank ready for the second real solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

theorem componentTransition_spec {P N q l s t u band : ℕ}
    (recovery rhs result next tail outputTail parkedTail : List (Fin (A+4)))
    (hr : recovery.length = s*(2*q+8)) (hb : rhs.length = s*(2*q+8))
    (hout : result.length = s*(2*q+8)) (hnext : next.length = s*(2*q+8))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 (recovery++(rhs++tail)) (embStk componentReg S))
    (hresult : S.R 132 = result++outputTail) (hparked : S.R 144 = next++parkedTail) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ componentTransitionCost q s ∧
      Exec (embTab componentReg body) componentTransition (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          110 (next++tail)) 132 outputTail) 144 parkedTail) 145 (result++S.R 145))}) ∧
      LengthKeyReady P N q l s t u band 0 0 (next++tail)
        (embStk componentReg {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          110 (next++tail)) 132 outputTail) 144 parkedTail) 145 (result++S.R 145))}) := by
  have hq : (S.R 119).length = q := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  have hfresh (r : Fin 144) (hr : r ∈ [(131 : Fin 144),134,135,136,137,140]) : S.R (componentReg r) = [] :=
    hready.fresh r hr
  obtain ⟨v',n,hu,hn,he⟩ := componentTransition_exec (body := body) q s recovery rhs result next tail outputTail parkedTail
    hr hb hout hnext v S hq hs (by simpa [embStk,componentReg] using hready.source) hresult hparked
    (by simpa [embStk,componentReg] using hready.blank 94 (by decide) (by decide) (by decide))
    (by simpa [componentReg] using hfresh 131 (by simp))
    (by simpa [componentReg] using hfresh 134 (by simp))
    (by simpa [componentReg] using hfresh 135 (by simp))
    (by simpa [componentReg] using hfresh 136 (by simp)) h147
  refine ⟨v',n,hu,hn,he,?_⟩
  have hproject : embStk componentReg {S with R := (Function.update (Function.update (Function.update (Function.update S.R
        110 (next++tail)) 132 outputTail) 144 parkedTail) 145 (result++S.R 145))} =
      {(embStk componentReg S) with R := (Function.update (Function.update (embStk componentReg S).R
        110 (next++tail)) 132 outputTail)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110
    · subst k; simp [embStk,componentReg]
    by_cases h132 : k = 132
    · subst k; simp [embStk,componentReg]
    have hne110 : componentReg k ≠ 110 := by
      intro he; apply h110; apply Fin.ext; exact congrArg (fun r : Fin 148 => r.val) he
    have hne132 : componentReg k ≠ 132 := by
      intro he; apply h132; apply Fin.ext; exact congrArg (fun r : Fin 148 => r.val) he
    simp [embStk,Function.comp_def,h110,h132,hne110,hne132,
      componentReg_off 144 (by decide) k,componentReg_off 145 (by decide) k]
  rw [hproject]
  exact (hready.update_source (next++tail)).update_output outputTail

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
