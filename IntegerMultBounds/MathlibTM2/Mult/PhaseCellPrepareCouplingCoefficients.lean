module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateCouplingCoefficients

/-! Prepare both the generated coefficient stream and the row arithmetic count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def prepareCouplingCoefficients : Pr P₀ 117 Q A U :=
  .seq generateCouplingCoefficients
    (.seq (.act (.push (.rt 102) (fun _ => tick) .done)) (umul 2 100 102 109))

def prepareCouplingCoefficientsCost (P q w s t u band i : ℕ) : ℕ :=
  generateCouplingCoefficientsCost P q w s t u band i+4*band+5

theorem prepareCouplingCoefficientsCost_le (P q w s t u band i : ℕ) :
    prepareCouplingCoefficientsCost P q w s t u band i ≤
      (2*band+1)*appendSelectedCoefficientCost P q w s t u band i band+24*band+21 := by
  have hh := appendSelectedCoefficientCost_mono P q w s t u band i (Nat.zero_le band)
  dsimp only [prepareCouplingCoefficientsCost,generateCouplingCoefficientsCost,
    coefficientOffsetPassCost,coefficientOffsetLoopCost]
  nlinarith only [hh]

theorem prepareCouplingCoefficients_exec {w q P s t u band i : ℕ}
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (h108 : S.R 108 = [])
    (h115 : S.R 115 = []) (h104 : S.R 104 = []) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = [])
    (h116 : S.R 116 = []) (h109 : S.R 109 = []) (h102 : S.R 102 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCouplingCoefficientsCost P q w s t u band i ∧
      Exec body prepareCouplingCoefficients (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 111
          (cstream A w (couplingCoefficientWords P q s t u band i)++S.R 111))
          102 (List.replicate (2*band+1) tick))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := generateCouplingCoefficients_exec (body := body)
    hs0 hst hP hi v S hPsrc hqsrc hsSrc htSrc huSrc hbSrc hiSrc h108 h115 h104 hwsrc h106 hblank h116 h109
  let word := cstream A w (couplingCoefficientWords P q s t u band i)
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 111 (word++S.R 111)}
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 102 [tick]}
  have he₂ : Exec body (.act (.push (.rt 102) (fun _ => tick) .done)) (mk v₁ S₁) 1 (mk v₁ S₂) := by
    simpa [S₂,S₁,h102,Action.run,update_rt] using
      (Exec.act (body := body) (.push (.rt 102) (fun _ => tick) .done) (mk v₁ S₁))
  obtain ⟨v₂,hu₂,he₃⟩ := umul_exec (body := body) 2 (a := 100) (b := 102) (t := 109)
    (by decide) (by decide) (by decide) v₁ S₂ (by simpa [S₂,S₁] using h109)
  refine ⟨v₂,m₁+(1+(4*band+4)),hu₂.trans hu₁,?_,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · dsimp only [prepareCouplingCoefficientsCost]
    omega
  · simp [S₂,S₁,hbSrc]
  · apply congrArg (mk v₂)
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · funext r
      by_cases h102' : r = 102
      · subst r
        simp [S₂,S₁,hbSrc,List.replicate_add]
      · simp [S₂,S₁,h102',word]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
