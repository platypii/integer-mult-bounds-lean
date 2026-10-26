module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftedSelectedCoefficient

/-! Select and generate the complete selected-coefficient workspace, execute from
ordinary headers and release that width. No workspace inequalities are inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def closedSelectedCoefficient (negative : Bool) : Pr P₀ 117 Q A U :=
  closedCoefficient (liftedSelectedCoefficientCode negative)

def closedSelectedCoefficientCost (P q w s t u band i d : ℕ) : ℕ :=
  closedCoefficientCost (1084*P+4*q+783) P q w s t u band i d

theorem closedSelectedCoefficient_exec {w q P s t u band i d : ℕ}
    (negative : Bool)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hd : d ≤ band)
    (hi : i < s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (hdSrc : (S.R 108).length = d)
    (h115 : S.R 115 = []) (h104 : S.R 104 = []) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ closedSelectedCoefficientCost P q w s t u band i d ∧
      Exec body (closedSelectedCoefficient negative) (mk v S) m
        (mk v' {S with R := (Function.update S.R 110
          (csyms A w (rationalWord q (PhaseCellCrossCell.entry P s t u band i ((i : ℤ)+couplingOffset negative d)))++S.R 110))}) := by
  let st := liftedCoefficientHeaderState (A := A) P q s t u band i d
  have hc := liftedSelectedCoefficientCode_do (w := w) (q := q) (P := P) (s := s) (t := t)
    (u := u) (band := band) (i := i) (d := d) negative st
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    hs0 hst hP hd hi
  exact closedCoefficient_exec (body := body) (liftedSelectedCoefficientCode negative)
    (rationalWord q (PhaseCellCrossCell.entry P s t u band i ((i : ℤ)+couplingOffset negative d)))
    (by simpa only [st,liftedCoefficientHeaderState,List.append_nil] using hc) hd hi v S
    hPsrc hqsrc hsSrc htSrc huSrc hbSrc hiSrc hdSrc h115 h104 hwsrc h106 hblank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
