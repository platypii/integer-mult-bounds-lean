module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg
public import Mathlib.Data.ZMod.Basic

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- Position 16 follows the padded source; variable 3 is the ambient query. -/
def ribbonCoordinateCode : TblCode 18 :=
  tblBlock 18 [.add 16 0 3,.sub 3 2 3] (.mod 3 0 3)

theorem ribbonCoordinateCode_do {A V w s band k : ℕ} (st : TblSt 18 A)
    (hs : st.val 0 = s) (hb : st.val 2 = band) (hk : st.val 16 = k)
    (hs0 : 0 < s) (hband : band ≤ s) (hfit : k+s < 2^V) :
    TblDo A V w ribbonCoordinateCode st (fun st' =>
      st'.val 3 = (k+s-band)%s ∧ st'.acc = st.acc ∧
      ∀ r, r ≠ 3 → st'.val r = st.val r) 3 := by
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact,hs,hb,hk]
    omega
  · simp [tblExactList,TblIns.exact,hs,hb,hk]
    intro r hr
    simp [hr]

/-- The arithmetic query agrees with the padded source's cyclic indexing. -/
theorem ribbonCoordinate_cast {s : ℕ} [NeZero s] (band k : ℕ) (hband : band ≤ s) :
    (((k+s-band)%s : ℕ) : ZMod s) = (k : ZMod s)-(band : ZMod s) := by
  have hh : band ≤ k+s := by omega
  simp [Nat.cast_sub hh,Nat.cast_add]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
