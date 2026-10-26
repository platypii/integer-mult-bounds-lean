module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftedCoefficientFromHeaders

/-! Select and generate the complete direct-coefficient workspace, execute from
ordinary headers and release that width. No workspace inequalities are inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def closedLiftedCoefficient (negative : Bool) : Pr P₀ 117 Q A U :=
  .seq generateLiftedCoefficientWidth (.seq (liftedCoefficientFromHeaders negative) (uclear 115))

def closedLiftedCoefficientCost (P q w s t u band i d : ℕ) : ℕ :=
  let V := liftedCoefficientWidth P q w s t u band
  generateLiftedCoefficientWidthCost P q w s t u band+
    liftedCoefficientFromHeadersCost P q V w s t u band i d+(2*V+2)

theorem closedLiftedCoefficient_exec {w q P s t u band i d : ℕ}
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
    ∃ v' m, v'.user = v.user ∧ m ≤ closedLiftedCoefficientCost P q w s t u band i d ∧
      Exec body (closedLiftedCoefficient negative) (mk v S) m
        (mk v' {S with R := (Function.update S.R 110
          (csyms A w (rationalWord q (PhaseCellCrossCell.direct P s t u
            (liftedSource s band i) (liftedTarget negative s band i d)))++S.R 110))}) := by
  let st := liftedCoefficientHeaderState (A := A) P q s t u band i d
  have hf := liftedCoefficientWidth_fits negative P q w s t u band i d hi hd
  have hc := liftedDirectCoefficientCode_do (w := w) negative st
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    hs0 hst hP hd hf.coordinates hf.sourceIndex hf.targetIndex hf.twiceModulus hf.sourceNearest
    hf.targetNearest hf.sourceSquare hf.targetSquare hf.modulusSquare hf.semanticWidth hf.exponentWidth
    hf.gridWidth
  simpa only [closedCoefficient,closedCoefficientCost,coefficientFromHeaders,coefficientFromHeadersCost,
    closedLiftedCoefficient,closedLiftedCoefficientCost,liftedCoefficientFromHeaders,
    liftedCoefficientFromHeadersCost] using
    (closedCoefficient_exec (body := body) (liftedDirectCoefficientCode negative)
      (rationalWord q (PhaseCellCrossCell.direct P s t u
        (liftedSource s band i) (liftedTarget negative s band i d)))
      (by simpa only [st,liftedCoefficientHeaderState,List.append_nil] using hc) hd hi v S
      hPsrc hqsrc hsSrc htSrc huSrc hbSrc hiSrc hdSrc h115 h104 hwsrc h106 hblank)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
