module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedCouplingRowError

/-! The raw coupling row has derived word fits and original-matrix accuracy. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem rawCouplingRow_spec (hQ : SS.states ≤ Q) {p q w s t u band a b i rhsExp inputExp countExp : ℕ} {α d : ℝ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A)
    (hw : q+couplingRowExponent rhsExp inputExp (8*p+1) countExp+2 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hi : i < s) (hp : 0 < p)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : band = PhaseCellBand.width p u)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = 2^15*p) (hqsrc : (S.R 112).length = q) (husrc : (S.R 99).length = u)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbandSrc : (S.R 100).length = band) (hiSrc : (S.R 107).length = i) (h105 : S.R 105 = [])
    (haSrc : (S.R 101).length = a) (hbSrc : (S.R 103).length = b)
    (hwsrc : (S.R 94).length = w) (h115 : S.R 115 = []) (h104 : S.R 104 = [])
    (h109 : S.R 109 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = [])
    (hsrc : S.R 110 = cstream A w (chirpLine s C)++tail) (h92 : S.R 92 = []) (h116 : S.R 116 = []) (h102 : S.R 102 = [])
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4)))
    (hrhs : S.R 93 = csyms A w rhs++rhsTail) (hc : CClean mul S)
    (hcr : ∀ r : CR, S.R (cr r) = [])
    (hleft : ∀ k ∈ [(97 : Fin 117),98,99,100], S.L k = []) (h96 : S.R 96 = [])
    (x : ZMod s → ℝ) (b₀ K ε rhsError : ℝ) (hε : 0 ≤ ε)
    (hcount : 2*band+1 ≤ 2^countExp) (hrhsBound : ‖value q rhs‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (hx : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      |(value q (C j)).re-x j| ≤ ε)
    (hmass : (((IntegerMultBounds.NLogN.PhaseCellMatrix.couplingOffsets band).reverse).map (fun δ =>
      |(IntegerMultBounds.NLogN.PhaseCellCrossCell.entry (2^15*p) s t u band i (i+δ) : ℝ)|)).sum ≤ K)
    (hrhsError : |(value q rhs).re-b₀| ≤ rhsError) :
    ∃ v' m, v'.user = v.user ∧ m ≤ rawCouplingRowCost (2^15*p) q w s t u band a b i ∧
      Exec body (rawCouplingRow hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 113
          (csyms A w (rhs-(List.zipWith (fun x z => tdivN q (x*z))
            (couplingInputWords boundary t band a b i C)
            (couplingCoefficientWords (2^15*p) q s t u band i)).sum)++S.R 113))}) ∧
      |(value q (decodeWord ((csyms A w (rhs-(List.zipWith (fun x z => tdivN q (x*z))
          (couplingInputWords boundary t band a b i C)
          (couplingCoefficientWords (2^15*p) q s t u band i)).sum)++S.R 113).take w))).re-
        (b₀-SchurDominance.couple (realMatrix s t p u)
          (if boundary then haloBoundary s t band a b else haloInterior s t band a b) x (i : ZMod s))| ≤
        (2*band+1)*(2/(2 : ℝ)^q)+rhsError+(2*band+1)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+K*ε := by
  have hwInput : q+inputExp+2 ≤ w := by dsimp [couplingRowExponent] at hw; omega
  have hwCoeff : q+(8*p+1)+2 ≤ w := by dsimp [couplingRowExponent] at hw; omega
  have hw5 : 5 ≤ w := by omega
  have hqw : q+4 ≤ w := by omega
  have hP := (IntegerMultBounds.NLogN.PhaseCellConcreteCoefficients.selected_precision p hp).1
  have hxs := couplingInputWords_norm boundary t band a b i C hC
  have has := couplingCoefficientWords_bounds (q := q) (band := band) (i := i)
    hp (NeZero.pos s) hst hαu hθ hgap hbudget
  obtain ⟨v',m,hu,hm,he⟩ := rawCouplingRow_exec (body := body) hQ boundary hA hw5 hqw
    hst haS hbS hbandS hi hP C tail v S hPsrc hqsrc husrc hsSrc htSrc hbandSrc hiSrc h105
    haSrc hbSrc hwsrc h115 h104 h109 h106 h108 hblank hsrc h92 h116 h102 rhs rhsTail hrhs hc hcr hleft h96
    (fun z hz => fits_of_value_power hwInput z (hxs z hz))
    (fun z hz => ⟨fits_of_value_power hwCoeff z (has z hz).1,(has z hz).2⟩)
  refine ⟨v',m,hu,hm,he,?_⟩
  subst band
  exact maskedCouplingRow_error boundary hA hp hst hαu hθ hgap hbudget hw hi C x rhs b₀ K ε rhsError
    hε hcount hrhsBound hC hx hmass hrhsError (S.R 113)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
