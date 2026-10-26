module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateCouplingInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCouplingCoefficients

/-! Generate aligned masked inputs, selected coefficients and their common row count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def prepareCouplingOperands (boundary : Bool) : Pr P₀ 117 Q A U :=
  .seq prepareCouplingCoefficients (generateCouplingInputs boundary)

def prepareCouplingOperandsCost (P q w s t u band a b i : ℕ) : ℕ :=
  prepareCouplingCoefficientsCost P q w s t u band i+generateCouplingInputsCost P q w s t u band a b i

theorem prepareCouplingOperands_exec {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 4 ≤ A)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q) (husrc : (S.R 99).length = u)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbandSrc : (S.R 100).length = band) (hiSrc : (S.R 107).length = i) (h105 : S.R 105 = [])
    (haSrc : (S.R 101).length = a) (hbSrc : (S.R 103).length = b)
    (hwsrc : (S.R 94).length = w) (h115 : S.R 115 = []) (h104 : S.R 104 = [])
    (h109 : S.R 109 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = [])
    (hsrc : S.R 92 = cstream A w (chirpLine s C)++tail) (h116 : S.R 116 = []) (h102 : S.R 102 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCouplingOperandsCost P q w s t u band a b i ∧
      Exec body (prepareCouplingOperands boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          111 (cstream A w (couplingCoefficientWords P q s t u band i)++S.R 111))
          102 (List.replicate (2*band+1) tick))
          110 (cstream A w (couplingInputWords boundary t band a b i C)++S.R 110))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := prepareCouplingCoefficients_exec (body := body)
    (NeZero.pos s) hst hP hi v S hPsrc hqsrc hsSrc htSrc husrc hbandSrc hiSrc h108 h115 h104 hwsrc h106
    hblank h116 h109 h102
  let coeffs := cstream A w (couplingCoefficientWords P q s t u band i)
  let S₁ : Stacks 117 A := {S with R := (Function.update (Function.update S.R
    111 (coeffs++S.R 111)) 102 (List.replicate (2*band+1) tick))}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := generateCouplingInputs_exec (body := body)
    (P := P) (q := q) (w := w) (s := s) (t := t) (u := u) (band := band) (a := a) (b := b) (i := i)
    boundary hA hst haS hbS hbandS hi C tail v₁ S₁
    (by simpa [S₁] using hPsrc)
    (by simpa [S₁] using hqsrc)
    (by simpa [S₁] using husrc)
    (by simpa [S₁] using hsSrc)
    (by simpa [S₁] using htSrc)
    (by simpa [S₁] using hbandSrc)
    (by simpa [S₁] using hiSrc)
    (by simpa [S₁] using h105)
    (by simpa [S₁] using haSrc)
    (by simpa [S₁] using hbSrc)
    (by simpa [S₁] using hwsrc)
    (by simpa [S₁] using h115)
    (by simpa [S₁] using h104)
    (by simpa [S₁] using h109)
    (by simpa [S₁] using h106)
    (by simpa [S₁] using h108)
    (by intro r hr
        have h102' : r ≠ 102 := by intro he; subst r; norm_num at hr
        have h111 : r ≠ 111 := by intro he; subst r; norm_num at hr
        simpa [S₁,h102',h111] using hblank r (by omega))
    (by simpa [S₁] using hsrc) (by simpa [S₁] using h116)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · dsimp only [prepareCouplingOperandsCost]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · funext r
      by_cases h110 : r = 110 <;> simp [S₁,h110,coeffs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
