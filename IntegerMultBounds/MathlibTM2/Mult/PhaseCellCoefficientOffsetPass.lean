module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientOffsetLoop

/-! Generate and retire the counted-pass controls; only the coefficient prefix changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def coefficientOffsetPass (negative : Bool) : Pr P₀ 117 Q A U :=
  .seq (ucopy 100 116 109) (.seq (coefficientOffsetLoop negative) (uclear 108))

def coefficientOffsetPassCost (P q w s t u band i : ℕ) : ℕ :=
  coefficientOffsetLoopCost P q w s t u band i+6*band+6

theorem coefficientOffsetPass_exec {w q P s t u band i : ℕ} (negative : Bool)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (h108 : S.R 108 = [])
    (h115 : S.R 115 = []) (h104 : S.R 104 = []) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = [])
    (h116 : S.R 116 = []) (h109 : S.R 109 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ coefficientOffsetPassCost P q w s t u band i ∧
      Exec body (coefficientOffsetPass negative) (mk v S) m
        (mk v' {S with R := (Function.update S.R 111
          (cstream A w (offsetCoefficientWords negative P q s t u band i band)++S.R 111))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 100) (b := 116) (t := 109)
    (by decide) (by decide) (by decide) v S h109
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 116 (List.replicate band tick)}
  have he₁' : Exec body (ucopy 100 116 109) (mk v S) (4*band+4) (mk v₁ S₁) := by
    simpa [S₁,hbSrc,h116] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := coefficientOffsetLoop_exec (body := body) (w := w) (q := q) (P := P) (s := s)
    (t := t) (u := u) (band := band) (i := i) negative hs0 hst hP hi v₁ S₁
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
        have hne : r ≠ 116 := by intro he; subst r; norm_num at hr
        simpa [S₁,hne] using hblank r hr) (by simp [S₁])
  let words := cstream A w (offsetCoefficientWords negative P q s t u band i band)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update (Function.update (Function.update S₁.R
    108 (List.replicate band tick)) 111 (words++S₁.R 111)) 116 []}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 108 v₂ S₂
  have he₃' : Exec body (uclear 108) (mk v₂ S₂) (2*band+2)
      (mk v₃ {S with R := Function.update S.R 111 (words++S.R 111)}) := by
    convert he₃ using 1
    · simp [S₂]
    · apply congrArg (mk v₃)
      refine Stacks.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · funext r
        by_cases h108' : r = 108 <;> by_cases h111' : r = 111 <;> by_cases h116' : r = 116 <;>
          simp [S₂,S₁,h108',h111',h116',h108,h116]
  refine ⟨v₃,(4*band+4)+(m₂+(2*band+2)),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁' (Exec.seq he₂ he₃')⟩
  dsimp only [coefficientOffsetPassCost]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
