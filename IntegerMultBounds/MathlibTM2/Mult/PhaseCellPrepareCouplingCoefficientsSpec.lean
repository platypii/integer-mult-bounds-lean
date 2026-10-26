module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCouplingCoefficients
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientAccuracy

/-! Prepare both the generated coefficient stream and the row arithmetic count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem prepareCouplingCoefficients_spec {w q p s t u band i : ℕ} {α d : ℝ}
    (hs0 : 0 < s) (hst : s < t) (hp : 0 < p)
    (hA : 96 ≤ A) (hw : q+(8*p+1)+2 ≤ w)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p) (hi : i < s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = 2^15*p) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (h108 : S.R 108 = [])
    (h115 : S.R 115 = []) (h104 : S.R 104 = []) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = [])
    (h116 : S.R 116 = []) (h109 : S.R 109 = []) (h102 : S.R 102 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCouplingCoefficientsCost (2^15*p) q w s t u band i ∧
      Exec body prepareCouplingCoefficients (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 111
          (cstream A w (couplingCoefficientWords (2^15*p) q s t u band i)++S.R 111))
          102 (List.replicate (2*band+1) tick))}) ∧
      (cstream A w (couplingCoefficientWords (2^15*p) q s t u band i)).length = (2*band+1)*w ∧
      ∀ j < 2*band+1,
        |(value q (decodeWord (((cstream A w (couplingCoefficientWords (2^15*p) q s t u band i)++S.R 111).drop (j*w)).take w))).re-
          (PhaseCellCrossCell.entry (2^15*p) s t u band i
            ((i : ℤ)+(PhaseCellMatrix.couplingOffsets band).reverse.getD j 0) : ℝ)| ≤ 1/(2 : ℝ)^q := by
  have hP := (PhaseCellConcreteCoefficients.selected_precision p hp).1
  obtain ⟨v',m,hu,hm,he⟩ := prepareCouplingCoefficients_exec (body := body)
    hs0 hst hP hi v S hPsrc hqsrc hsSrc htSrc huSrc hbSrc hiSrc h108 h115 h104 hwsrc h106
    hblank h116 h109 h102
  refine ⟨v',m,hu,hm,he,by simp,?_⟩
  intro j hj
  exact couplingCoefficientWords_decode hA hw hp hs0 hst hαu hθ hgap hbudget (S.R 111) j hj

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
