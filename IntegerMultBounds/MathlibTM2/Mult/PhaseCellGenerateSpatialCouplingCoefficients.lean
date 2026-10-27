module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedRowCoefficient

/-! Generate a complete alias-preserving coefficient row from ordinary headers.
Only the row prefix changes; all offset counters and table banks restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateSpatialCouplingCoefficients : Pr P₀ 117 Q A U := closedRowCoefficient

def generateSpatialCouplingCoefficientsCost (P q w s t u band i : ℕ) : ℕ :=
  closedRowCoefficientCost P q w s t u band i

theorem generateSpatialCouplingCoefficients_exec {w q P s t u band i : ℕ}
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (h108 : S.R 108 = [])
    (h115 : S.R 115 = []) (h104 : S.R 104 = []) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = [])
    (h105 : S.R 105 = []) (h116 : S.R 116 = []) (h109 : S.R 109 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generateSpatialCouplingCoefficientsCost P q w s t u band i ∧
      Exec body generateSpatialCouplingCoefficients (mk v S) m
        (mk v' {S with R := (Function.update S.R 111
          (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++S.R 111))}) := by
  exact closedRowCoefficient_exec (body := body) hs0 hst hP hi v S hPsrc hqsrc hsSrc htSrc huSrc hbSrc
    hiSrc h115 h104 hwsrc h106 (by
      intro r hr
      simp only [mem_rowCoefficientPorts] at hr
      rcases hr with hr | rfl | rfl
      · exact hblank r hr
      · exact h108
      · exact h116)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
