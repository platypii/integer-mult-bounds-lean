module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedSelectedCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedCoefficientAccuracy

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

theorem closedSelectedCoefficient_spec {w q p s t u band i d : ℕ} {α D : ℝ}
    (negative : Bool) (hA : 96 ≤ A) (hw : q+(8*p+1)+2 ≤ w)
    (hs0 : 0 < s) (hst : s < t) (hp : 0 < p) (hd : d ≤ band)
    (hi : i < s)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ D*((t : ℝ)/s-1)) (hbudget : α^2*D ≤ p)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = 2^15*p) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (hdSrc : (S.R 108).length = d)
    (h115 : S.R 115 = []) (h104 : S.R 104 = []) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ closedSelectedCoefficientCost (2^15*p) q w s t u band i d ∧
      Exec body (closedSelectedCoefficient negative) (mk v S) m
        (mk v' {S with R := (Function.update S.R 110
          (csyms A w (rationalWord q (PhaseCellCrossCell.entry (2^15*p) s t u band i ((i : ℤ)+couplingOffset negative d)))++S.R 110))}) ∧
      |(value q (decodeWord ((csyms A w (rationalWord q (PhaseCellCrossCell.entry (2^15*p) s t u band i ((i : ℤ)+couplingOffset negative d)))++S.R 110).take w))).re-
        (PhaseCellCrossCell.entry (2^15*p) s t u band i ((i : ℤ)+couplingOffset negative d) : ℝ)| ≤
          1/(2 : ℝ)^q := by
  have hP := (PhaseCellConcreteCoefficients.selected_precision p hp).1
  obtain ⟨v',m,hu',hm,he⟩ := closedSelectedCoefficient_exec (body := body) negative hs0 hst hP hd hi v S
    hPsrc hqsrc hsSrc htSrc huSrc hbSrc hiSrc hdSrc h115 h104 hwsrc h106 hblank
  refine ⟨v',m,hu',hm,he,?_⟩
  let z := rationalWord q (PhaseCellCrossCell.entry (2^15*p) s t u band i ((i : ℤ)+couplingOffset negative d))
  have hlen : (csyms A w z).length = w := by simp [csyms]
  have hword : (csyms A w z++S.R 110).take w = csyms A w z := by
    simp only [List.take_append,hlen,Nat.sub_self,List.take_zero,List.append_nil]
    simpa only [hlen] using (show (csyms A w z).take (csyms A w z).length = csyms A w z from List.take_length)
  rw [hword,decodeWord_of_fits (by omega) (by omega) z (selected_coefficient_fits (i : ℤ) ((i : ℤ)+couplingOffset negative d) hp hs0 hst hαu hθ hgap hbudget hw)]
  exact rationalWord_error q _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
