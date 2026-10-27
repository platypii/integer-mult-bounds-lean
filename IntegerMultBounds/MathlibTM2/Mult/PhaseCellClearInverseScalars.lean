module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellParameterArithmetic

/-! Restore the scalar bank after installation, retaining its eight original inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblClearInverseScalars : TblCode 25 :=
  tblBlock 25 [.zero 8,.zero 9,.zero 10,.zero 11,.zero 12,.zero 13,.zero 14,.zero 15,
    .zero 16,.zero 17,.zero 18,.zero 19,.zero 20,.zero 21,.zero 22,.zero 23] (.zero 24)

theorem tblClearInverseScalars_do {A W e : ℕ} (st initial : TblSt 25 A)
    (hkeep : ∀ i : Fin 25, i.val < 8 → st.val i = initial.val i)
    (hzero : ∀ i : Fin 25, 8 ≤ i.val → initial.val i = 0) (hacc : st.acc = initial.acc) :
    TblDo A W e tblClearInverseScalars st (fun z => z = initial) 17 := by
  have hr : TblDo A W e tblClearInverseScalars st
      (fun z => z.val = initial.val ∧ z.acc = initial.acc) 17 := by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact]
    · refine ⟨?_,hacc⟩
      funext i
      fin_cases i <;> simp only [tblExactList,TblIns.exact,Function.update_apply,Fin.reduceEq,ite_true,ite_false]
      all_goals first | exact hkeep _ (by decide) | exact (hzero _ (by decide)).symm
  exact hr.mono (fun z ⟨hv,ha⟩ => by
    cases z
    cases initial
    dsimp only at hv ha
    cases hv
    cases ha
    rfl) (le_refl _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
