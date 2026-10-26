module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLatticeArgument
public import IntegerMultBounds.NLogN.PhaseCellCouplingLift

/-! Generate the two nonnegative lattice coordinates before coefficient
selection. The negative sweep subtracts only an offset proved to fit below the lift. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

def liftCouplingCoordinates (negative : Bool) : TblCode 48 :=
  tblBlock 48 [.mul 41 34 43, .add 37 43 37]
    (if negative then .sub 37 42 38 else .add 37 42 38)

theorem liftCouplingCoordinates_do {A V w s band i d : ℕ} (negative : Bool) (st : TblSt 48 A)
    (hs : st.val 34 = s) (hi : st.val 37 = i) (hb : st.val 41 = band) (hd' : st.val 42 = d)
    (hs0 : 0 < s) (hd : d ≤ band) (hfit : i+band*s+d < 2^V) :
    TblDo A V w (liftCouplingCoordinates negative) st (fun st' =>
      st'.val 37 = liftedSource s band i ∧ st'.val 38 = liftedTarget negative s band i d ∧
      st'.acc = st.acc ∧ ∀ r, r ∉ [(37 : Fin 48),38,43] → st'.val r = st.val r) 3 := by
  have hsub := offset_le_liftedSource (i := i) hs0 hd
  cases negative <;> apply TblDo.block
  all_goals first
    | (simp [tblFitsList,TblIns.fits,TblIns.exact,hs,hi,hb,hd',liftedSource] at *; omega)
    | (simp only [List.cons_append,List.nil_append,tblExactList,TblIns.exact]
       simp [hs,hi,hb,hd',liftedSource,liftedTarget]
       intro r hr37 hr38 hr43
       simp [hr37,hr38,hr43])

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
