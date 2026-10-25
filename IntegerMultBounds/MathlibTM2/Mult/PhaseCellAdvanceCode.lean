module

public import IntegerMultBounds.MathlibTM2.Fast.TableBounds

/-! Compute the next forward symbol advance from a decoded origin. The previous
origin is retained in the table; no unary advance is supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def originAdvanceCode : TblCode 4 :=
  tblBlock 4 [.sub 0 1 3, .mul 3 2 3] (.copy 0 1)

theorem originAdvanceCode_do {A W e origin previous w : ℕ} (st : TblSt 4 A)
    (ho : st.val 0 = origin) (hp : st.val 1 = previous) (hw : st.val 2 = w)
    (hpo : previous ≤ origin) (hfit : ∀ i, st.val i < 2^W)
    (hadvance : (origin-previous)*w < 2^W) :
    TblDo A W e originAdvanceCode st
      (fun st' => st'.val 0 = origin ∧ st'.val 1 = origin ∧ st'.val 2 = w ∧
        st'.val 3 = (origin-previous)*w ∧ st'.acc = st.acc) 3 := by
  have hoW : origin < 2^W := by simpa only [ho] using hfit 0
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, TblIns.exact, ho, hp, hw, hpo, hoW, hadvance]
  · simp [tblExactList, TblIns.exact, ho, hp, hw]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
