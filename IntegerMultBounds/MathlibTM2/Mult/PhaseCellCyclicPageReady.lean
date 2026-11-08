module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthKeyReadFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentWorkspace

/-! Generated cyclic coordinates and endpoints preserve the arithmetic readiness contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host

theorem cyclicPageReady_of_frame {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S S' : Stacks 154 A}
    (h : LengthKeyReady P N q l s t u band V w input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S))))
    (hL : S'.L = S.L)
    (hframe : ∀ k : Fin 154, k ∉ [109,115,116,141,142,144,145,146] → S'.R k = S.R k) :
    LengthKeyReady P N q l s t u band V w input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S'))) := by
  apply h.of_read_frame
  · funext i
    change S'.L (tableReg (boundaryArithmeticReg (componentReg i))) =
      S.L (tableReg (boundaryArithmeticReg (componentReg i)))
    rw [hL]
  · intro i hi
    change S'.R (tableReg (boundaryArithmeticReg (componentReg i))) = _
    apply hframe
    by_cases h109 : i.val = 109
    · have he : i = 109 := Fin.ext h109
      subst i; decide
    by_cases h115 : i.val = 115
    · have he : i = 115 := Fin.ext h115
      subst i; decide
    by_cases h116 : i.val = 116
    · have he : i = 116 := Fin.ext h116
      subst i; decide
    have h141 : i.val ≠ 141 := by omega
    have h142 : i.val ≠ 142 := by omega
    have h144 : i.val ≠ 144 := by omega
    have h145 : i.val ≠ 145 := by omega
    have h146 : i.val ≠ 146 := by omega
    simp [componentReg,boundaryArithmeticReg,tableReg,Fin.ext_iff,h109,h115,h116,h141,h142,h144,h145,h146]

theorem cyclicRecoveryReady_of_frame {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S S' : Stacks 154 A}
    (h : LengthKeyReady P N q l s t u band V w input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S))))
    (hL : S'.L = S.L)
    (hframe : ∀ k : Fin 154, k ∉ [109,115,116,132,141,142,144,145,146] → S'.R k = S.R k) :
    LengthKeyReady P N q l s t u band V w input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S'))) := by
  apply h.of_read_frame_except_output
  · funext i
    change S'.L (tableReg (boundaryArithmeticReg (componentReg i))) =
      S.L (tableReg (boundaryArithmeticReg (componentReg i)))
    rw [hL]
  · intro i hi h132
    change S'.R (tableReg (boundaryArithmeticReg (componentReg i))) = _
    apply hframe
    by_cases h109 : i.val = 109
    · have he : i = 109 := Fin.ext h109
      subst i; decide
    by_cases h115 : i.val = 115
    · have he : i = 115 := Fin.ext h115
      subst i; decide
    by_cases h116 : i.val = 116
    · have he : i = 116 := Fin.ext h116
      subst i; decide
    have h141 : i.val ≠ 141 := by omega
    have h142 : i.val ≠ 142 := by omega
    have h144 : i.val ≠ 144 := by omega
    have h145 : i.val ≠ 145 := by omega
    have h146 : i.val ≠ 146 := by omega
    simp [componentReg,boundaryArithmeticReg,tableReg,Fin.ext_iff,h109,h115,h116,show i.val ≠ 132 from fun he => h132 (Fin.ext he),h141,h142,h144,h145,h146]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
