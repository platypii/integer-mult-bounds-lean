module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhaseCoefficient

/-! All retained signed offsets, including the unit diagonal, use one program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

def unitCoefficientEmit : TblCode 48 := tblBlock 48 [.zero 25] (.emit 39 25)

theorem unitCoefficientEmit_do {A V w q : ℕ} (st : TblSt 48 A) (hq : st.val 39 = 2^q) :
    TblDo A V w unitCoefficientEmit st
      (fun st' => st'.acc = (csyms A w (rationalWord q 1)).reverse ++ st.acc) 2 := by
  have hout : rationalWord q 1 = (⟨((2^q : ℕ) : ℤ),0⟩ : GaussianInt) := by
    simpa using rationalWord_nat_ratio q 1 1
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact]
  · simp [tblExactList,TblIns.exact,hq,hout,csyms,tbl_pairs_red]

def selectedCoefficientBody : TblCode 48 :=
  tableIfEq 37 38 unitCoefficientEmit phaseCoefficientBody

theorem selectedCoefficientBody_do {A w q P s t u band i d : ℕ}
    (negative : Bool) (st : TblSt 48 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = liftedSource s band i) (hk : st.val 38 = liftedTarget negative s band i d)
    (hq : st.val 39 = 2^q) (hpowP : st.val 40 = 2^P)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hd : d ≤ band) (hi : i < s) :
    TblDo A (liftedCoefficientWidth P q w s t u band) w selectedCoefficientBody st
      (fun st' => st'.acc = (csyms A w (rationalWord q
        (PhaseCellCrossCell.entry P s t u band (liftedSource s band i)
          (liftedTarget negative s band i d)))).reverse ++ st.acc) (930*P+367) := by
  unfold selectedCoefficientBody
  apply tableIfEq_do
  · intro he
    have hcoords : liftedSource s band i = liftedTarget negative s band i d := by
      simpa only [hj,hk] using he
    have hentry : PhaseCellCrossCell.entry P s t u band (liftedSource s band i)
        (liftedTarget negative s band i d) = 1 := by
      simp [← hcoords,PhaseCellCrossCell.entry,PhaseCellConcreteCoefficients.entry,
        PhaseCellExecutableCoefficients.entry]
    exact (unitCoefficientEmit_do (V := liftedCoefficientWidth P q w s t u band) (w := w) st hq).mono
      (fun _ h => by simpa only [hentry] using h) (by omega)
  · intro he
    have hcoords : liftedSource s band i ≠ liftedTarget negative s band i d := by
      simpa only [hj,hk] using he
    exact phaseCoefficientBody_do negative st hpi hP' hneg hs ht hu hj hk hq hpowP hs0 hst hP hd hi hcoords

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
