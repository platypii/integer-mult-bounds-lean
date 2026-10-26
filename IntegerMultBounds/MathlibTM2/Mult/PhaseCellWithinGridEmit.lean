module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithinCoefficientWord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientGridEmit

/-! Combine the two retained similarity samples and the distance sample using
natural multiplication and division. Zero denominators follow rational division. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

def withinGridEmit : TblCode 48 :=
  tblBlock 48 [.mul 41 23 45, .mul 39 45 45, .mul 42 40 46, .div 45 46 45]
    (.emit 45 25)

theorem withinGridEmit_do {A V w q P a b c : ℕ} (st : TblSt 48 A)
    (ha : st.val 41 = a) (hb : st.val 42 = b) (hc : st.val 23 = c)
    (hz : st.val 25 = 0) (hq : st.val 39 = 2^q) (hP : st.val 40 = 2^P)
    (hac : a*c < 2^V) (hnum : 2^q*(a*c) < 2^V) (hden : b*2^P < 2^V) :
    TblDo A V w withinGridEmit st (fun st' =>
      st'.acc = (csyms A w (rationalWord q ((a*c : ℕ)/(b*2^P : ℕ) : ℚ))).reverse ++ st.acc ∧
      ∀ r, r ≠ 45 → r ≠ 46 → st'.val r = st.val r) 5 := by
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact,ha,hb,hc,hq,hP,hac,hnum,hden]
  · simp only [List.cons_append,List.nil_append,tblExactList,TblIns.exact]
    rw [rationalWord_nat_ratio]
    simp [ha,hb,hc,hq,hP,hz,csyms,tbl_pairs_red]
    intro r hr45 hr46
    simp [hr45,hr46]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
