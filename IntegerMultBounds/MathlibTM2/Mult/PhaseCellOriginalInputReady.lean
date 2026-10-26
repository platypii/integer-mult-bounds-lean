module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedOriginalPrefix

/-! Original-input preservation from the released solver bank, with no supplied clock. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

theorem saveOriginalInput_ready {P N q l s t u band : ℕ}
    (xs tail : List (Fin (A+4))) (hlen : xs.length = s*(2*q+8))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 (xs++tail) (embStk componentReg S))
    (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ saveOriginalInputCost q s ∧
      Exec (embTab componentReg body) saveOriginalInput (mk v S) n
        (mk v' {S with R := Function.update S.R 146 (xs++S.R 146)}) ∧
      LengthKeyReady P N q l s t u band 0 0 (xs++tail)
        (embStk componentReg {S with R := Function.update S.R 146 (xs++S.R 146)}) := by
  have hq : (S.R 119).length = q := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  have hfresh (r : Fin 144) (hr : r ∈ [(131 : Fin 144),134,135,136,137,140]) : S.R (componentReg r) = [] :=
    hready.fresh r hr
  obtain ⟨v',n,hu,hn,he⟩ := saveOriginalInput_exec (body := body) q s xs tail hlen v S hq hs
    (by simpa [embStk,componentReg] using hready.source)
    (by simpa [embStk,componentReg] using hready.blank 94 (by decide) (by decide) (by decide))
    (by simpa [componentReg] using hfresh 131 (by simp))
    (by simpa [componentReg] using hfresh 134 (by simp))
    (by simpa [componentReg] using hfresh 135 (by simp)) h147
  refine ⟨v',n,hu,hn,he,?_⟩
  rw [componentProject_updateR S 146 (xs++S.R 146) (by decide)]
  exact hready

theorem restoreOriginalInput_ready {P N q l s t u band : ℕ}
    (xs tail savedTail : List (Fin (A+4))) (hlen : xs.length = s*(2*q+8))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 tail (embStk componentReg S))
    (hsaved : S.R 146 = xs++savedTail) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ restoreOriginalInputCost q s ∧
      Exec (embTab componentReg body) restoreOriginalInput (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 146 savedTail) 110 (xs++tail))}) ∧
      LengthKeyReady P N q l s t u band 0 0 (xs++tail)
        (embStk componentReg {S with R := (Function.update (Function.update S.R 146 savedTail) 110 (xs++tail))}) := by
  have hq : (S.R 119).length = q := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  have hfresh (r : Fin 144) (hr : r ∈ [(131 : Fin 144),134,135,136,137,140]) : S.R (componentReg r) = [] :=
    hready.fresh r hr
  have hsource : S.R 110 = tail := by simpa [embStk,componentReg] using hready.source
  obtain ⟨v',n,hu,hn,he⟩ := restoreOriginalInput_exec (body := body) q s xs savedTail hlen v S hq hs hsaved
    (by simpa [embStk,componentReg] using hready.blank 94 (by decide) (by decide) (by decide))
    (by simpa [componentReg] using hfresh 131 (by simp))
    (by simpa [componentReg] using hfresh 134 (by simp))
    (by simpa [componentReg] using hfresh 135 (by simp)) h147
  refine ⟨v',n,hu,hn,by simpa only [hsource] using he,?_⟩
  have hproject : embStk componentReg {S with R := (Function.update
      (Function.update S.R 146 savedTail) 110 (xs++tail))} =
      {(embStk componentReg S) with R := Function.update (embStk componentReg S).R 110 (xs++tail)} := by
    have hinner := componentProject_updateR_inner {S with R := Function.update S.R 146 savedTail} 110 (xs++tail)
    simp only [componentProject_updateR S 146 savedTail (by decide)] at hinner
    simpa [componentReg] using hinner
  rw [hproject]
  exact hready.update_source (xs++tail)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
