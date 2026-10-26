module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawCouplingOperands
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingInputAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientAccuracy

/-! Decoded accuracy and exact volume of both executed coupling operand streams. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem rawCouplingOperands_spec {p q w inputExp s t u band a b i : ℕ} {α D : ℝ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw : q+max inputExp (8*p+1)+2 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hi : i < s) (hp : 0 < p)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ D*((t : ℝ)/s-1)) (hbudget : α^2*D ≤ p)
    (C : ZMod s → GaussianInt) (x : ZMod s → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (hx : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      |(value q (C j)).re-x j| ≤ ε)
    (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = 2^15*p) (hqsrc : (S.R 112).length = q) (husrc : (S.R 99).length = u)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbandSrc : (S.R 100).length = band) (hiSrc : (S.R 107).length = i) (h105 : S.R 105 = [])
    (haSrc : (S.R 101).length = a) (hbSrc : (S.R 103).length = b)
    (hwsrc : (S.R 94).length = w) (h115 : S.R 115 = []) (h104 : S.R 104 = [])
    (h109 : S.R 109 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = [])
    (hsrc : S.R 110 = cstream A w (chirpLine s C)++tail) (h92 : S.R 92 = []) (h116 : S.R 116 = []) (h102 : S.R 102 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ rawCouplingOperandsCost (2^15*p) q w s t u band a b i ∧
      Exec body (rawCouplingOperands boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          111 (cstream A w (couplingCoefficientWords (2^15*p) q s t u band i)++S.R 111))
          102 (List.replicate (2*band+1) tick))
          110 (cstream A w (couplingInputWords boundary t band a b i C)++S.R 110))}) ∧
      (cstream A w (couplingCoefficientWords (2^15*p) q s t u band i)).length = (2*band+1)*w ∧
      (cstream A w (couplingInputWords boundary t band a b i C)).length = (2*band+1)*w ∧
      ∀ n < 2*band+1,
        let δ := (IntegerMultBounds.NLogN.PhaseCellMatrix.couplingOffsets band).reverse.getD n 0
        let j : ZMod s := (i : ZMod s)+(δ : ZMod s)
        let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
        |(value q (decodeWord (((cstream A w (couplingCoefficientWords (2^15*p) q s t u band i)++S.R 111).drop (n*w)).take w))).re-
            (IntegerMultBounds.NLogN.PhaseCellCrossCell.entry (2^15*p) s t u band i (i+δ) : ℝ)| ≤ 1/(2 : ℝ)^q ∧
        |(value q (decodeWord (((cstream A w (couplingInputWords boundary t band a b i C)++S.R 110).drop (n*w)).take w))).re-(if j ∈ T then x j else 0)| ≤ ε := by
  have hP := (IntegerMultBounds.NLogN.PhaseCellConcreteCoefficients.selected_precision p hp).1
  obtain ⟨v',m,hu,hm,he⟩ := rawCouplingOperands_exec (body := body) boundary (by omega)
    hst haS hbS hbandS hi hP C tail v S hPsrc hqsrc husrc hsSrc htSrc hbandSrc hiSrc h105
    haSrc hbSrc hwsrc h115 h104 h109 h106 h108 hblank hsrc h92 h116 h102
  refine ⟨v',m,hu,hm,he,by simp,by simp,?_⟩
  intro n hn
  constructor
  · exact couplingCoefficientWords_decode hA (by omega) hp (NeZero.pos s) hst hαu hθ hgap hbudget (S.R 111) n hn
  · exact couplingInputWords_decode boundary t band a b i C x ε hA (by omega) hε hC hx (S.R 110) n hn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
