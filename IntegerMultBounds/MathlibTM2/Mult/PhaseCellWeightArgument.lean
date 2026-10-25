module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientExp
public import IntegerMultBounds.NLogN.PhaseCellSimilarityArgs

/-! Execute the natural similarity argument on the table machine. Geometry
headers are retained; only the exponential inputs and two temporaries change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

def weightArgument : TblCode 48 :=
  tblBlock 48 [.mul 35 37 40, .add 40 40 40, .add 40 34 40,
    .mod 40 38 40, .sub 38 40 41, .mul 40 41 20, .mul 36 20 20]
    (.copy 39 21)

/-- All intermediate products are bounded explicitly, with no modular wrap. -/
theorem weightArgument_do {A V w s t u j : ℕ} (st : TblSt 48 A)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = j) (hdouble : st.val 38 = 2 * s)
    (hden : st.val 39 = similarityDenominator s t)
    (hs0 : 0 < s) (hindex : 2 * t * j + s < 2 ^ V)
    (hsV : 2 * s < 2 ^ V) (hsq : s ^ 2 < 2 ^ V)
    (huV : u * s ^ 2 < 2 ^ V) :
    TblDo A V w weightArgument st (fun st' =>
      st'.val 20 = similarityNumerator s t u j ∧
      st'.val 21 = similarityDenominator s t ∧ st'.acc = st.acc ∧
      ∀ k, k ∉ [(20 : Fin 48), 21, 40, 41] → st'.val k = st.val k) 8 := by
  have hr : similarityResidue s t j < 2 * s := Nat.mod_lt _ (by omega)
  have hprod : similarityResidue s t j * (2 * s - similarityResidue s t j) ≤ s ^ 2 := by
    have he : similarityResidue s t j + (2 * s - similarityResidue s t j) = 2 * s := by omega
    nlinarith [sq_nonneg ((similarityResidue s t j : ℤ) - s)]
  have hbase : t * j + t * j + s = 2 * t * j + s := by ring
  have hres : (2 * t * j + s) % (2 * s) = similarityResidue s t j := rfl
  have hnum : u * (similarityResidue s t j * (2 * s - similarityResidue s t j)) < 2 ^ V :=
    (Nat.mul_le_mul_left u hprod).trans_lt huV
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hs, ht, hu, hj, hdouble,
      hbase, hres, hr.le, hsV, hprod.trans_lt hsq, hnum]
    omega
  · simp only [List.cons_append, List.nil_append,
      tblExactList, TblIns.exact]
    simp [hs, ht, hu, hj, hdouble, hden, hbase, similarityNumerator,
      similarityResidue, mul_assoc]
    intro k hk20 hk21 hk40 hk41
    simp [hk20, hk21, hk40, hk41]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
