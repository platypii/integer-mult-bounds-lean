module

public import IntegerMultBounds.NLogN.PhaseCellCouplingIndex
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhaseArguments

/-! Construct a wrapped physical address before any input access or mask test. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

def couplingIndexCode (negative : Bool) : TblCode 16 :=
  tblBlock 16 [.mul 2 0 4, .add 7 4 4,
    (if negative then .sub 4 3 4 else .add 4 3 4), .mod 4 0 4, .zero 5] (.emit 4 5)

theorem couplingIndexCode_do {A V s band i d : ℕ} (negative : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (hb : st.val 2 = band) (hd' : st.val 3 = d) (hi : st.val 7 = i)
    (hs0 : 0 < s) (hd : d ≤ band) (hfit : i+band*s+d < 2^V) :
    TblDo A V V (couplingIndexCode negative) st (fun st' =>
      st'.acc = (tblPairs A V (couplingIndex negative s band i d) 0).reverse++st.acc) 6 := by
  have hoff := offset_le_liftedSource (s := s) (band := band) (i := i) hs0 hd
  dsimp only [liftedSource] at hoff
  cases negative
  · apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact,hs,hb,hd',hi]
      omega
    · simp [tblExactList,TblIns.exact,hs,hb,hd',hi,couplingIndex,liftedTarget,liftedSource]
  · apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact,hs,hb,hd',hi]
      omega
    · simp [tblExactList,TblIns.exact,hs,hb,hd',hi,couplingIndex,liftedTarget,liftedSource]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
