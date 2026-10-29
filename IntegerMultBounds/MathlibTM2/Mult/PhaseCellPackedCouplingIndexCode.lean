module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIndexCode

/-! Compute a wrapped coupling query directly in the packed lookup table.
Ambient geometry remains in registers 0,1,2,4,5; row and offset are in 7,8. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

def packedCouplingIndexCode (negative : Bool) : TblCode 16 :=
  tblBlock 16 [.mul 2 0 10,.add 7 10 10,
    (if negative then .sub 10 8 10 else .add 10 8 10)] (.mod 10 0 3)

theorem packedCouplingIndexCode_do {A V s band i d : ℕ} (negative : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (hb : st.val 2 = band) (hi : st.val 7 = i) (hd' : st.val 8 = d)
    (hs0 : 0 < s) (hd : d ≤ band) (hfit : i+band*s+d < 2^V) :
    TblDo A V V (packedCouplingIndexCode negative) st (fun st' =>
      st'.val 3 = couplingIndex negative s band i d ∧ st'.acc = st.acc ∧
      ∀ r, r ≠ 3 → r ≠ 10 → st'.val r = st.val r) 4 := by
  have hoff := offset_le_liftedSource (s := s) (band := band) (i := i) hs0 hd
  dsimp only [liftedSource] at hoff
  cases negative <;> apply TblDo.block
  all_goals first
    | (simp [tblFitsList,TblIns.fits,TblIns.exact,hs,hb,hi,hd']; omega)
    | (simp [tblExactList,TblIns.exact,hs,hb,hi,hd',couplingIndex,liftedTarget,liftedSource])
  all_goals
    intro r h3 h10
    simp [h3,h10]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
