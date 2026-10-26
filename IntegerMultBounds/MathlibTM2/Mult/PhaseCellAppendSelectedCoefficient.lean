module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedSelectedCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix

/-! Generate one selected coefficient and move its word to the row coefficient
port, preserving the input suffix and releasing all conversion scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def appendSelectedCoefficient (negative : Bool) : Pr P₀ 117 Q A U :=
  .seq (closedSelectedCoefficient negative) (takePrefix 94 110 111 104 106)

def appendSelectedCoefficientCost (P q w s t u band i d : ℕ) : ℕ :=
  closedSelectedCoefficientCost P q w s t u band i d+6*w+6

theorem appendSelectedCoefficientCost_mono (P q w s t u band i : ℕ) {d e : ℕ} (hd : d ≤ e) :
    appendSelectedCoefficientCost P q w s t u band i d ≤
      appendSelectedCoefficientCost P q w s t u band i e := by
  have hh : P+q+s+t+u+i+band+d ≤ P+q+s+t+u+i+band+e := by omega
  have hm := Nat.mul_le_mul_right (4*liftedCoefficientWidth P q w s t u band+10) hh
  dsimp only [appendSelectedCoefficientCost,closedSelectedCoefficientCost,
    closedCoefficientCost,coefficientFromHeadersCost]
  omega

theorem appendSelectedCoefficient_exec {w q P s t u band i d : ℕ}
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
    ∃ v' m, v'.user = v.user ∧ m ≤ appendSelectedCoefficientCost P q w s t u band i d ∧
      Exec body (appendSelectedCoefficient negative) (mk v S) m
        (mk v' {S with R := (Function.update S.R 111
          (csyms A w (rationalWord q (PhaseCellCrossCell.entry P s t u band i ((i : ℤ)+couplingOffset negative d)))++S.R 111))}) := by
  let z := rationalWord q (PhaseCellCrossCell.entry P s t u band i ((i : ℤ)+couplingOffset negative d))
  let word := csyms A w z
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := closedSelectedCoefficient_exec (body := body) negative
    hs0 hst hP hd hi v S hPsrc hqsrc hsSrc htSrc huSrc hbSrc hiSrc hdSrc h115 h104 hwsrc h106 hblank
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 110 (word++S.R 110)}
  obtain ⟨v₂,hu₂,he₂⟩ := takePrefix_exec (body := body)
    (count := 94) (src := 110) (dst := 111) (buf := 104) (tmp := 106) (by decide)
    v₁ S₁ word (S.R 110) (by simp [S₁])
    (by simpa [S₁,word,csyms] using hwsrc)
    (by simpa [S₁] using h104) (by simpa [S₁] using h106)
  refine ⟨v₂,m₁+(6*w+6),hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · dsimp only [appendSelectedCoefficientCost]
    omega
  · simp [word,csyms]
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h110 : r = 110 <;> by_cases h111 : r = 111 <;> simp [S₁,h110,h111,word,z]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
