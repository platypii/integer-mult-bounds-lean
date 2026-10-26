module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftedDirectCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientFromHeaders

/-! Load ordinary unary parameters, construct the lifted direct coefficient,
and release every private table register. Only the coefficient output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def liftedCoefficientFromHeaders (negative : Bool) : Pr P₀ 117 Q A U :=
  .seq initializeCoefficientBank (.seq (loadCoefficientList liftedCoefficientHeaders)
    (coefficientTableHost (liftedDirectCoefficientCode negative)))

def liftedCoefficientFromHeadersCost (P q V w s t u band i d : ℕ) : ℕ :=
  (292*V+4*w+393)+((P+q+s+t+u+i+band+d)*(4*V+10)+48*V+81)+
    ((464*P+4*q+545)*tblC V w+2*w+126*V+129)

theorem liftedCoefficientFromHeaders_exec {V w q P s t u band i d : ℕ}
    (negative : Bool)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hd : d ≤ band)
    (hfit : i+band*s+d < 2^V)
    (hjV : 2*t*liftedSource s band i+s < 2^V)
    (hkV : 2*t*liftedTarget negative s band i d+s < 2^V) (hsV : 2*s < 2^V)
    (hnjV : s*nearestNatural s t (liftedSource s band i) < 2^V)
    (hnkV : s*nearestNatural s t (liftedTarget negative s band i d) < 2^V)
    (hdjV : latticeDistance s t (liftedSource s band i) (liftedTarget negative s band i d)^2 < 2^V)
    (hdkV : latticeDistance s t (liftedTarget negative s band i d) (liftedTarget negative s band i d)^2 < 2^V)
    (hsqV : s^2 < 2^V) (hV : 13*P+8 ≤ V)
    (haV : latticeNumerator s t u (liftedSource s band i) (liftedTarget negative s band i d)*
      2^(5*P+2) < 2^V) (hqV : q+P+2 ≤ V)
    (htV : t < 2^V) (huV : u < 2^V) (hw : w ≤ V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (hdSrc : (S.R 108).length = d)
    (hVsrc : (S.R 115).length = V) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ liftedCoefficientFromHeadersCost P q V w s t u band i d ∧
      Exec body (liftedCoefficientFromHeaders negative) (mk v S) m
        (mk v' {S with R := (Function.update S.R 110
          (csyms A w (rationalWord q (PhaseCellCrossCell.direct P s t u
            (liftedSource s band i) (liftedTarget negative s band i d)))++S.R 110))}) := by
  let st := liftedCoefficientHeaderState (A := A) P q s t u band i d
  have hstV : ∀ r, st.val r < 2^V := by
    have hPV : P < 2^V := (show P ≤ V by omega).trans_lt Nat.lt_two_pow_self
    have hqbound : q < 2^V := (show q ≤ V by omega).trans_lt Nat.lt_two_pow_self
    have hiV : i < 2^V := by omega
    have hdV : d < 2^V := by omega
    have hbV : band < 2^V := by
      have hh : band ≤ band*s := by nlinarith only [hs0]
      omega
    intro r
    simp only [st,liftedCoefficientHeaderState,Function.update_apply]
    split_ifs <;> first | assumption | omega
  have hc := liftedDirectCoefficientCode_do (w := w) negative st
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    hs0 hst hP hd hfit hjV hkV hsV hnjV hnkV hdjV hdkV hsqV hV haV hqV
  simpa only [coefficientFromHeaders,coefficientFromHeadersCost,
    liftedCoefficientFromHeaders,liftedCoefficientFromHeadersCost] using
    (coefficientFromHeaders_exec (body := body) (liftedDirectCoefficientCode negative)
      (rationalWord q (PhaseCellCrossCell.direct P s t u
        (liftedSource s band i) (liftedTarget negative s band i d)))
      (by simpa only [st,liftedCoefficientHeaderState,List.append_nil] using hc) hstV hw v S
      hPsrc hqsrc hsSrc htSrc huSrc hbSrc hiSrc hdSrc hVsrc hwsrc h106 hblank)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
