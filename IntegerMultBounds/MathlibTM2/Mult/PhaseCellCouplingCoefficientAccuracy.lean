module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedCoefficientAccuracy

/-! Every generated row word has selected magnitude and original-entry accuracy. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

theorem couplingCoefficientWords_bounds {s t u p q band i : ℕ} {α d : ℝ}
    (hp : 0 < p) (hs : 0 < s) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : α^2*d ≤ p) :
    ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u band i,
      ‖value q z‖ ≤ (2 : ℝ)^(8*p+1) ∧ z.im = 0 := by
  intro z hz
  obtain ⟨δ,_,rfl⟩ := List.mem_map.mp hz
  exact ⟨selected_coefficient_norm _ _ hp hs hst hαu hθ hgap hbudget,rfl⟩

theorem couplingCoefficientWords_decode {A w s t u p q band i : ℕ} {α d : ℝ}
    (hA : 96 ≤ A) (hw : q+(8*p+1)+2 ≤ w)
    (hp : 0 < p) (hs : 0 < s) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : α^2*d ≤ p) (tail : List (Fin (A+4))) (j : ℕ) (hj : j < 2*band+1) :
    |(value q (decodeWord (((cstream A w (couplingCoefficientWords (2^15*p) q s t u band i)++tail).drop (j*w)).take w))).re-
      (PhaseCellCrossCell.entry (2^15*p) s t u band i
        ((i : ℤ)+(PhaseCellMatrix.couplingOffsets band).reverse.getD j 0) : ℝ)| ≤ 1/(2 : ℝ)^q := by
  have hword : j < (couplingCoefficientWords (2^15*p) q s t u band i).length := by simpa using hj
  have hoff : j < (PhaseCellMatrix.couplingOffsets band).reverse.length := by simpa using hj
  rw [cstream_word w _ tail j hword]
  have hget : (couplingCoefficientWords (2^15*p) q s t u band i)[j] =
      rationalWord q (PhaseCellCrossCell.entry (2^15*p) s t u band i
        ((i : ℤ)+(PhaseCellMatrix.couplingOffsets band).reverse.getD j 0)) := by
    rw [List.getD_eq_getElem _ _ hoff]
    simp only [couplingCoefficientWords,List.getElem_map]
  rw [hget,decodeWord_of_fits (by omega) (by omega) _
    (selected_coefficient_fits _ _ hp hs hst hαu hθ hgap hbudget hw)]
  exact rationalWord_error q _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
