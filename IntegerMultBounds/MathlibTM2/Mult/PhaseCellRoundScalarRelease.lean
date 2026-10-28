module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundScalarSetup

/-! Erase computed dimensions after copying their headers, restoring the binary input bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblRoundRelease : TblCode 8 := tblBlock 8 [.zero 5,.zero 6] (.zero 7)

theorem tblRoundRelease_do {A W e : ℕ} (st z : TblSt 8 A)
    (hkeep : ∀ i : Fin 5, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩)
    (h5 : st.val 5 = 0) (h6 : st.val 6 = 0) (h7 : st.val 7 = 0) (hacc : z.acc = st.acc) :
    TblDo A W e tblRoundRelease z (fun out => out = st) 3 := by
  unfold tblRoundRelease
  refine TblDo.block _ _ (by simp [tblFitsList,TblIns.fits]) ?_
  simp only [List.cons_append,List.nil_append,tblExactList,TblIns.exact]
  have hv : Function.update (Function.update (Function.update z.val 5 0) 6 0) 7 0 = st.val := by
    funext i
    fin_cases i
    · simpa using hkeep 0
    · simpa using hkeep 1
    · simpa using hkeep 2
    · simpa using hkeep 3
    · simpa using hkeep 4
    · simpa using h5.symm
    · simpa using h6.symm
    · simpa using h7.symm
  rw [hv,hacc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
