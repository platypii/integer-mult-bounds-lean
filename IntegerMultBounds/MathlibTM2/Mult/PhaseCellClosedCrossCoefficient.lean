module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedLiftedCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftedCoefficientAccuracy

/-! The closed signed-offset caller has a decoded error against the original
selected coefficient, with generated workspace and no supplied fit premises. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem closedCrossCoefficient_spec {w q P s t u band i d : ℕ}
    (negative : Bool) (hA : 96 ≤ A) (hw : q+2 ≤ w)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hd : d ≤ band)
    (hi : i < s)
    (hphase : PhaseCellCrossCell.phaseQ s t i ≠
      PhaseCellCrossCell.phaseQ s t ((i : ℤ)+couplingOffset negative d))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (hdSrc : (S.R 108).length = d)
    (h115 : S.R 115 = []) (h104 : S.R 104 = []) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ closedLiftedCoefficientCost P q w s t u band i d ∧
      Exec body (closedLiftedCoefficient negative) (mk v S) m
        (mk v' {S with R := (Function.update S.R 110
          (csyms A w (rationalWord q (PhaseCellCrossCell.direct P s t u
            (liftedSource s band i) (liftedTarget negative s band i d)))++S.R 110))}) ∧
      |(value q (decodeWord ((csyms A w (rationalWord q (PhaseCellCrossCell.direct P s t u
        (liftedSource s band i) (liftedTarget negative s band i d)))++S.R 110).take w))).re-
        (PhaseCellCrossCell.entry P s t u band i ((i : ℤ)+couplingOffset negative d) : ℝ)| ≤
          1/(2 : ℝ)^q := by
  obtain ⟨v',m,hu',hm,he⟩ := closedLiftedCoefficient_exec (body := body) negative hs0 hst hP hd hi v S
    hPsrc hqsrc hsSrc htSrc huSrc hbSrc hiSrc hdSrc h115 h104 hwsrc h106 hblank
  refine ⟨v',m,hu',hm,he,?_⟩
  let z := rationalWord q (PhaseCellCrossCell.direct P s t u
    (liftedSource s band i) (liftedTarget negative s band i d))
  have hlen : (csyms A w z).length = w := by simp [csyms]
  have hword : (csyms A w z++S.R 110).take w = csyms A w z := by
    simp only [List.take_append,hlen,Nat.sub_self,List.take_zero,List.append_nil]
    simpa only [hlen] using (show (csyms A w z).take (csyms A w z).length = csyms A w z from List.take_length)
  rw [hword,decodeWord_of_fits (by omega) (by omega) z (cross_coefficient_fits hw hP hs0 hst)]
  exact lifted_cross_coefficient_error negative q P t u hs0 hd hphase

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
