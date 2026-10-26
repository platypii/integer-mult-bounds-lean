module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBorrowedCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowField

/-! Restoring physical line handoff with uniform residual/recovery accuracy
and a reusable ambient integer output and norm bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem borrowedCouplingPass_spec (hQ : SS.states ≤ Q)
    {p q w s t u band a b rhsExp inputExp countExp : ℕ} [NeZero s] {α d : ℝ}
    (boundary : Bool) (hA : 96 ≤ A) (hp : 0 < p) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent rhsExp inputExp (8*p+1) countExp+2 ≤ w)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hband : band = PhaseCellBand.width p u)
    (C B : ZMod s → GaussianInt) (x b₀ : ZMod s → ℝ) (K ε rhsError : ℝ) (hε : 0 ≤ ε)
    (hcount : 2*band+1 ≤ 2^countExp)
    (hB : ∀ j, ‖value q (B j)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (hx : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      |(value q (C j)).re-x j| ≤ ε)
    (hmass : ∀ i < s, (((couplingOffsets band).reverse).map (fun δ =>
      |(PhaseCellCrossCell.entry (2^15*p) s t u band i (i+δ) : ℝ)|)).sum ≤ K)
    (hBError : ∀ j, |(value q (B j)).re-b₀ j| ≤ rhsError)
    (tail sourceTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady (2^15*p) q w s t u band a b
      (cstream A w (chirpLine s B)++tail) (embStk groupReg S))
    (hindex : S.R 107 = []) (hsource : S.R 132 = cstream A w (chirpLine s C)++sourceTail)
    (h143 : S.R 143 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    let ys := couplingRowWords (2^15*p) q t u band a b boundary C 0 (chirpLine s B)
    ∃ v' m, v'.user = v.user ∧ m ≤ borrowedCouplingPassCost (2^15*p) q w s t u band a b ∧
      Exec (embTab groupReg body) (borrowedCouplingPass hQ boundary) (mk v S) m
        (mk v' {S with R := Function.update S.R 113 (cstream A w ys++S.R 113)}) ∧
      ys = chirpLine s (couplingRowField (2^15*p) q t u band a b boundary C B) ∧
      (cstream A w ys).length = s*w ∧
      (∀ j, ‖value q (couplingRowField (2^15*p) q t u band a b boundary C B j)‖ ≤
        (2 : ℝ)^couplingRowExponent rhsExp inputExp (8*p+1) countExp) ∧
      ∀ j < s, |(value q (decodeWord (((cstream A w ys++S.R 113).drop (j*w)).take w))).re-
        (b₀ (j : ZMod s)-SchurDominance.couple (realMatrix s t p u)
          (if boundary then haloBoundary s t band a b else haloInterior s t band a b) x (j : ZMod s))| ≤
          (2*band+1)*(2/(2 : ℝ)^q)+rhsError+(2*band+1)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+K*ε := by
  dsimp only
  have hwInput : q+inputExp+2 ≤ w := by dsimp [couplingRowExponent] at hw; omega
  have hwCoeff : q+(8*p+1)+2 ≤ w := by dsimp [couplingRowExponent] at hw; omega
  have hw5 : 5 ≤ w := by omega
  have hqw : q+4 ≤ w := by omega
  have hP := (PhaseCellConcreteCoefficients.selected_precision p hp).1
  obtain ⟨v',m,hu,hm,he⟩ := borrowedCouplingPass_exec (body := body) hQ boundary hA hw5 hqw
    hst haS hbS hbandS hP C B tail sourceTail v S hready hsource hindex h143 h131 h134 h135
    (by intro j _ z hz
        exact fits_of_value_power hwInput z (couplingInputWords_norm boundary t band a b j C hC z hz))
    (by intro j _ z hz
        have hh := couplingCoefficientWords_bounds (q := q) (band := band) (i := j)
          hp (NeZero.pos s) hst hαu hθ hgap hbudget z hz
        exact ⟨fits_of_value_power hwCoeff z hh.1,hh.2⟩)
  refine ⟨v',m,hu,hm,he,couplingRowWords_eq_chirpLine _ _ _ _ _ _ _ _ _ _,by simp,?_,?_⟩
  · exact couplingRowField_norm boundary hp hst hαu hθ hgap hbudget C B hcount hB hC
  · intro j hj
    let ys := couplingRowWords (2^15*p) q t u band a b boundary C 0 (chirpLine s B)
    have hj' : j < ys.length := by simpa [ys] using hj
    have hget : ys[j] = couplingRowWord (2^15*p) q t u band a b j boundary C (B (j : ZMod s)) := by
      have hh := couplingRowWords_getElem (2^15*p) q t u band a b 0 boundary C (chirpLine s B) j
        (by simpa using hj)
      simpa [ys,chirpLine] using hh
    rw [cstream_word w ys (S.R 113) j hj',hget]
    have herror := maskedCouplingRow_error boundary hA hp hst hαu hθ hgap hbudget hw hj C x (B (j : ZMod s))
      (b₀ (j : ZMod s)) K ε rhsError hε (by simpa [hband] using hcount) (hB _)
      (by simpa [hband] using hC) (by simpa [hband] using hx) (by simpa [hband] using hmass j hj)
      (hBError _) (S.R 113)
    have hword (z : GaussianInt) : (csyms A w z++S.R 113).take w = csyms A w z := by
      have hlen : (csyms A w z).length = w := by simp
      simp only [List.take_append,hlen,Nat.sub_self,List.take_zero,List.append_nil]
      simpa only [hlen] using (show (csyms A w z).take (csyms A w z).length = csyms A w z from List.take_length)
    dsimp only at herror
    rw [hword] at herror
    simpa only [couplingRowWord,hband] using herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
