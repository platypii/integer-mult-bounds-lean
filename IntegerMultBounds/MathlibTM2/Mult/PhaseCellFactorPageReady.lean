module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPageSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedBoundaryTable

/-! Obtain all factor-page controls from the ordinary retained-master invariant. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 154 Q A U}

theorem generatedFactorPage_ready_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s))
    (P N q l t u band V w : ℕ) (input tail : List (Fin (A+4)))
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (v : HS 154 Q A U) (S : Stacks 154 A)
    (hready : LengthKeyReady P N q l s t u band V w input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S))))
    (hcard : (S.R 116).length = B.card)
    (hsource : S.R 132 = bandTableWords A (2*q+8) B (12*band+1) columns 0++tail)
    (h138 : S.R 138 = []) (h151 : S.R 151 = []) (h152 : S.R 152 = []) (h153 : S.R 153 = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ generatedFactorPageCost q band B.card ∧
      Exec body generatedFactorPage (mk v S) steps
        (mk v' {S with R := (Function.update S.R 140
          (cstream A (2*q+8) ((factorWindowValues B (12*band+1) columns).flatten++
            (factorInputValues B (12*band+1) B.card columns).flatten)++S.R 140))}) := by
  have hq : (S.R 119).length = q := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,groupHeaderValue] using
      hready.masters (119,112) (by simp [groupHeaderCopies])
  have hband : (S.R 124).length = band := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,groupHeaderValue] using
      hready.masters (124,100) (by simp [groupHeaderCopies])
  have h0 : S.R 0 = [] := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 0 (by decide) (by decide) (by decide)
  have h94 : S.R 94 = [] := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 94 (by decide) (by decide) (by decide)
  apply generatedFactorPage_exec (body := body) B q band columns hlen hformat hA tail v S hq hband hcard hsource h0 h94
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 105 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 106 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 107 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 108 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 111 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 112 (by decide) (by decide) (by decide)
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 131 (by simp)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 134 (by simp)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 135 (by simp)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 136 (by simp)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 137 (by simp)
    · exact h138
    · exact h151
    · exact h152
    · exact h153
  · intro r hr1 hr7
    have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 1 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 2 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 3 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 4 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 5 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 6 (by decide) (by decide) (by decide)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
