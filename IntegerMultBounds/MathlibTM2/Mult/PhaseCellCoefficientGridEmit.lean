module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightNumerators
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientExp

/-! Emit one corrected sample on the requested arithmetic grid. The sample's
semantic precision P and its stored grid precision q remain distinct. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

def coefficientGridEmit : TblCode 48 :=
  tblBlock 48 [.mul 39 23 41, .div 41 40 41] (.emit 41 25)

theorem coefficientGridEmit_do {A V w q P n : ℕ} (st : TblSt 48 A)
    (hn : st.val 23 = n) (hz : st.val 25 = 0)
    (hq : st.val 39 = 2^q) (hP : st.val 40 = 2^P) (hnV : 2^q*n < 2^V) :
    TblDo A V w coefficientGridEmit st (fun st' =>
      st'.acc = (csyms A w (rationalWord q ((n : ℚ)/(2 : ℚ)^P))).reverse++st.acc ∧
      ∀ k, k ≠ 41 → st'.val k = st.val k) 3 := by
  have hout : rationalWord q ((n : ℚ)/(2 : ℚ)^P) =
      (⟨((2^q*n/2^P : ℕ) : ℤ),0⟩ : GaussianInt) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using rationalWord_nat_ratio q n (2^P)
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,hq,hn,hnV]
  · simp only [List.cons_append,List.nil_append,tblExactList,TblIns.exact]
    simp [hq,hP,hn,hz,hout,csyms,tbl_pairs_red]
    intro k hk
    simp [hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
