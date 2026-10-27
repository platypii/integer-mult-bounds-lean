module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedResidualLift

/-! Recover ordinary arithmetic readiness from the preserved physical boundary frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

/-- Boundary-owned page tapes are outside the recovery register image. -/
theorem boundaryRecoveryReady_of_frame {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S S' : Stacks 224 A}
    (hready : LengthKeyReady P N q l s t u band V w input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (hinp : S'.inp = S.inp) (hout : S'.out = S.out) (hL : S'.L = S.L)
    (hframe : ∀ i : Fin 154, i ≠ 109 → i ≠ 110 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
      S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) :
    LengthKeyReady P N q l s t u band V w (S'.R 110)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S')))) := by
  have hproject : embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S'))) =
      {(embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))) with
        R := Function.update (Function.update
          (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))).R
          110 (S'.R 110)) 132 (S'.R 132)} := by
    refine Stacks.ext hinp hout ?_ ?_
    · funext i
      simp only [embStk,hL]
    · funext i
      by_cases h110 : i = 110
      · subst i; simp [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg]
      by_cases h132 : i = 132
      · subst i; simp [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg]
      simp only [Function.update_of_ne h132,Function.update_of_ne h110]
      let j := tableReg (boundaryArithmeticReg (componentReg i))
      have hj109 : j ≠ 109 := by
        have hh := (boundaryArithmeticReg_off (componentReg i)).1
        simpa [j,tableReg,Fin.ext_iff] using hh
      have hj115 : j ≠ 115 := by
        have hh := (boundaryArithmeticReg_off (componentReg i)).2.1
        simpa [j,tableReg,Fin.ext_iff] using hh
      have hj116 : j ≠ 116 := by
        have hh := (boundaryArithmeticReg_off (componentReg i)).2.2
        simpa [j,tableReg,Fin.ext_iff] using hh
      have hj110 : j ≠ 110 := by
        dsimp [j,tableReg,boundaryArithmeticReg,componentReg]
        split_ifs <;> simp_all [Fin.ext_iff]
      have hj132 : j ≠ 132 := by
        dsimp [j,tableReg,boundaryArithmeticReg,componentReg]
        split_ifs <;> simp_all [Fin.ext_iff]
      exact hframe j hj109 hj110 hj115 hj116 hj132
  rw [hproject]
  exact (hready.update_source (S'.R 110)).update_output (S'.R 132)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
