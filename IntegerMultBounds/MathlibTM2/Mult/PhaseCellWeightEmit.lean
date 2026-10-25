module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightNumerators
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientExp

/-! Two exact grid words from one corrected similarity sample. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

def weightEmit : TblCode 48 :=
  tblBlock 48 [.mul 42 23 40, .div 40 43 40, .emit 40 25, .div 44 23 41]
    (.emit 41 25)

/-- Emit the similarity word and its reciprocal from the same sampled numerator.
The statement also covers the natural zero-division convention; positivity is
proved separately when selecting the actual phase-cell precision. -/
theorem weightEmit_do {A V w q P n : ℕ} (st : TblSt 48 A)
    (hn : st.val 23 = n) (hz : st.val 25 = 0)
    (hq : st.val 42 = 2 ^ q) (hP : st.val 43 = 2 ^ P)
    (hqp : st.val 44 = 2 ^ (q + P)) (hnV : 2 ^ q * n < 2 ^ V) :
    TblDo A V w weightEmit st (fun st' =>
      st'.acc = (csyms A w (reciprocalWeightWord q ((n : ℚ) / (2 : ℚ) ^ P))).reverse ++
        (csyms A w (rationalWord q ((n : ℚ) / (2 : ℚ) ^ P))).reverse ++ st.acc ∧
      ∀ k, k ∉ [(40 : Fin 48), 41] → st'.val k = st.val k) 5 := by
  have hout := rationalWord_nat_ratio q n (2 ^ P)
  have hrec : reciprocalWeightWord q ((n : ℚ) / (2 : ℚ) ^ P) =
      (⟨((2 ^ (q + P) / n : ℕ) : ℤ), 0⟩ : GaussianInt) := by
    unfold reciprocalWeightWord
    rw [one_div_div]
    simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_add] using rationalWord_nat_ratio q (2 ^ P) n
  have hout' : rationalWord q ((n : ℚ) / (2 : ℚ) ^ P) =
      (⟨((2 ^ q * n / 2 ^ P : ℕ) : ℤ), 0⟩ : GaussianInt) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hout
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, hq, hn, hnV]
  · simp only [List.cons_append, List.nil_append, tblExactList, TblIns.exact]
    simp [hq, hP, hqp, hn, hz, hout', hrec, csyms,
      tbl_pairs_red, List.append_assoc]
    intro k hk40 hk41
    simp [hk40, hk41]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
