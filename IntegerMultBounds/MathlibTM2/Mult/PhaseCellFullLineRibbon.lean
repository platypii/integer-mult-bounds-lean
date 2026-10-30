module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPadCouplingSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRibbonMask

/-! Generate the full-system gathered ribbon directly from the current iterate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

theorem rawCouplingRibbon_fullLine {s : ℕ} [NeZero s] (band : ℕ)
    (F : ZMod s → GaussianInt) :
    rawCouplingRibbon band 0 s F = cyclicPaddedLine F band := by
  simp only [rawCouplingRibbon,List.drop_zero]
  apply List.take_of_length_le
  simp only [cyclicPaddedLine,List.length_map,List.length_range]
  omega

namespace ScalarPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 144 Q A U}

theorem padCouplingSource_fullRibbon_exec {s : ℕ} [NeZero s] (F : ZMod s → GaussianInt)
    (band w : ℕ) (hb : band ≤ s) (tail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 97).length = s) (hband : (S.R 100).length = band) (hw : (S.R 94).length = w)
    (hsrc : S.R 141 = cstream A w (chirpLine s F)++tail)
    (h107 : S.R 107 = []) (h108 : S.R 108 = []) (h109 : S.R 109 = [])
    (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) (h106 : S.R 106 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ padCouplingSourceCost s band w ∧
      Exec body padCouplingSource (mk v S) m
        (mk v' {S with R := Function.update S.R 141 (cstream A w (rawCouplingRibbon band 0 s F)++tail)}) := by
  simpa only [rawCouplingRibbon_fullLine] using
    padCouplingSource_exec (body := body) F band w hb tail v S hs hband hw hsrc
      h107 h108 h109 h115 h116 h104 h105 h106

end ScalarPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
