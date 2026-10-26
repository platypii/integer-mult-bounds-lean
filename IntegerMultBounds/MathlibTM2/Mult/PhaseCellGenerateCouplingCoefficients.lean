module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientOffsetPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientWords

/-! Generate a complete alias-preserving coefficient row from ordinary headers.
Only the row prefix changes; all offset counters and table banks restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateCouplingCoefficients : Pr P₀ 117 Q A U :=
  .seq (appendSelectedCoefficient false) (.seq (coefficientOffsetPass false) (coefficientOffsetPass true))

def generateCouplingCoefficientsCost (P q w s t u band i : ℕ) : ℕ :=
  appendSelectedCoefficientCost P q w s t u band i 0+2*coefficientOffsetPassCost P q w s t u band i

theorem generateCouplingCoefficients_exec {w q P s t u band i : ℕ}
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (h108 : S.R 108 = [])
    (h115 : S.R 115 = []) (h104 : S.R 104 = []) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = [])
    (h116 : S.R 116 = []) (h109 : S.R 109 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generateCouplingCoefficientsCost P q w s t u band i ∧
      Exec body generateCouplingCoefficients (mk v S) m
        (mk v' {S with R := (Function.update S.R 111
          (cstream A w (couplingCoefficientWords P q s t u band i)++S.R 111))}) := by
  let zero := csyms A w (signedCoefficientWord false P q s t u band i 0)
  let pos := cstream A w (offsetCoefficientWords false P q s t u band i band)
  let neg := cstream A w (offsetCoefficientWords true P q s t u band i band)
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := appendSelectedCoefficient_exec (body := body)
    (w := w) (q := q) (P := P) (s := s) (t := t) (u := u) (band := band) (i := i) (d := 0)
    false hs0 hst hP (by omega) hi v S hPsrc hqsrc hsSrc htSrc huSrc hbSrc hiSrc
    (by simp [h108]) h115 h104 hwsrc h106 hblank
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 111 (zero++S.R 111)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := coefficientOffsetPass_exec (body := body)
    (w := w) (q := q) (P := P) (s := s) (t := t) (u := u) (band := band) (i := i)
    false hs0 hst hP hi v₁ S₁
    (by simpa [S₁] using hPsrc)
    (by simpa [S₁] using hqsrc)
    (by simpa [S₁] using hsSrc)
    (by simpa [S₁] using htSrc)
    (by simpa [S₁] using huSrc)
    (by simpa [S₁] using hbSrc)
    (by simpa [S₁] using hiSrc)
    (by simpa [S₁] using h108)
    (by simpa [S₁] using h115)
    (by simpa [S₁] using h104)
    (by simpa [S₁] using hwsrc)
    (by simpa [S₁] using h106)
    (by intro r hr
        have hne : r ≠ 111 := by intro he; subst r; norm_num at hr
        simpa [S₁,hne] using hblank r hr)
    (by simpa [S₁] using h116) (by simpa [S₁] using h109)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 111 (pos++S₁.R 111)}
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := coefficientOffsetPass_exec (body := body)
    (w := w) (q := q) (P := P) (s := s) (t := t) (u := u) (band := band) (i := i)
    true hs0 hst hP hi v₂ S₂
    (by simpa [S₂,S₁] using hPsrc)
    (by simpa [S₂,S₁] using hqsrc)
    (by simpa [S₂,S₁] using hsSrc)
    (by simpa [S₂,S₁] using htSrc)
    (by simpa [S₂,S₁] using huSrc)
    (by simpa [S₂,S₁] using hbSrc)
    (by simpa [S₂,S₁] using hiSrc)
    (by simpa [S₂,S₁] using h108)
    (by simpa [S₂,S₁] using h115)
    (by simpa [S₂,S₁] using h104)
    (by simpa [S₂,S₁] using hwsrc)
    (by simpa [S₂,S₁] using h106)
    (by intro r hr
        have hne : r ≠ 111 := by intro he; subst r; norm_num at hr
        simpa [S₂,S₁,hne] using hblank r hr)
    (by simpa [S₂,S₁] using h116) (by simpa [S₂,S₁] using h109)
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · dsimp only [generateCouplingCoefficientsCost]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · funext r
      by_cases h111' : r = 111
      · subst r
        simp [S₂,S₁,couplingCoefficientWords_split,cstream,neg,pos,zero,List.append_assoc]
      · simp [S₂,S₁,h111']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
