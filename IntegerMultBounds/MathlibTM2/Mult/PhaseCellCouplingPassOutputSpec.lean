module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingRowValue
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

variable {A : ℕ}

theorem couplingPass_output_spec
    {p q w s t u band a b rhsExp inputExp countExp : ℕ} [NeZero s] {α d : ℝ}
    (boundary : Bool) (hA : 96 ≤ A) (hp : 0 < p) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent rhsExp inputExp (8*p+1) countExp+2 ≤ w)
    (hbS : b ≤ s) (hband : band = PhaseCellBand.width p u)
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
    (suffix : List (Fin (A+4))) :
    let ys := guardedCouplingRowWords (2^15*p) q t u band a b boundary C 0 (chirpLine s B)
    ys = chirpLine s (guardedCouplingRowField (2^15*p) q t u band a b boundary C B) ∧
      (cstream A w ys).length = s*w ∧
      (∀ j, ‖value q (guardedCouplingRowField (2^15*p) q t u band a b boundary C B j)‖ ≤
        (2 : ℝ)^couplingRowExponent rhsExp inputExp (8*p+1) countExp) ∧
      ∀ j < s, (boundary = true ∨ (j : ZMod s) ∈ haloBoundary s t band a b) → |(value q (decodeWord (((cstream A w ys++suffix).drop (j*w)).take w))).re-
        (b₀ (j : ZMod s)-SchurDominance.couple (realMatrix s t p u)
          (if boundary then haloBoundary s t band a b else haloInterior s t band a b) x (j : ZMod s))| ≤
          (2*band+1)*(2/(2 : ℝ)^q)+rhsError+(2*band+1)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+K*ε := by
  dsimp only
  refine ⟨guardedCouplingRowWords_eq_chirpLine _ _ _ _ _ _ _ _ _ _,by simp,?_,?_⟩
  · exact guardedCouplingRowField_norm boundary hp hst hαu hθ hgap hbudget C B hcount hB hC
  · intro j hj hobserved
    let ys := guardedCouplingRowWords (2^15*p) q t u band a b boundary C 0 (chirpLine s B)
    have hj' : j < ys.length := by simpa [ys] using hj
    have hget : ys[j] = guardedCouplingRowWord (2^15*p) q t u band a b j boundary C (B (j : ZMod s)) := by
      have hh := guardedCouplingRowWords_getElem (2^15*p) q t u band a b 0 boundary C (chirpLine s B) j
        (by simpa using hj)
      simpa [ys,chirpLine] using hh
    rw [cstream_word w ys (suffix) j hj',hget]
    rw [guardedCouplingRowWord_eq hst (2^15*p) q u band a b j boundary hbS hj C (B (j : ZMod s)) hobserved]
    have herror := maskedCouplingRow_error boundary hA hp hst hαu hθ hgap hbudget hw hj C x (B (j : ZMod s))
      (b₀ (j : ZMod s)) K ε rhsError hε (by simpa [hband] using hcount) (hB _)
      (by simpa [hband] using hC) (by simpa [hband] using hx) (by simpa [hband] using hmass j hj)
      (hBError _) (suffix)
    have hword (z : GaussianInt) : (csyms A w z++suffix).take w = csyms A w z := by
      have hlen : (csyms A w z).length = w := by simp
      simp only [List.take_append,hlen,Nat.sub_self,List.take_zero,List.append_nil]
      simpa only [hlen] using (show (csyms A w z).take (csyms A w z).length = csyms A w z from List.take_length)
    dsimp only at herror
    rw [hword] at herror
    simpa only [couplingRowWord,hband] using herror


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
