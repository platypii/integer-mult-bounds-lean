module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! Truncated natural subtraction on the table VM, including the underflow
branch required by clipped and empty phase intervals. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblNatSub {n : ℕ} (a b c : Fin n) : TblCode n :=
  .ite a b (.ins (.zero c)) (.ins (.sub a b c))

theorem tblNatSub_do {n A W w : ℕ} (a b c : Fin n) (st : TblSt n A)
    (ha : st.val a < 2^W) :
    TblDo A W w (tblNatSub a b c) st
      (fun st' => st' = ⟨Function.update st.val c (st.val a-st.val b), st.acc⟩) 2 := by
  by_cases hab : st.val a < st.val b
  · apply TblDo.iteT hab
    apply TblDo.insX (.zero c) (by trivial)
    simp [TblIns.exact, Nat.sub_eq_zero_of_le hab.le]
  · apply TblDo.iteF hab
    exact TblDo.insX (.sub a b c) ⟨by omega, ha⟩ rfl

def tblNatMin {n : ℕ} (a b c : Fin n) : TblCode n :=
  .ite a b (.ins (.copy a c)) (.ins (.copy b c))

theorem tblNatMin_do {n A W w : ℕ} (a b c : Fin n) (st : TblSt n A) :
    TblDo A W w (tblNatMin a b c) st
      (fun st' => st' = ⟨Function.update st.val c (min (st.val a) (st.val b)), st.acc⟩) 2 := by
  by_cases hab : st.val a < st.val b
  · apply TblDo.iteT hab
    apply TblDo.insX (.copy a c) (by trivial)
    simp [TblIns.exact, min_eq_left hab.le]
  · apply TblDo.iteF hab
    apply TblDo.insX (.copy b c) (by trivial)
    simp [TblIns.exact, min_eq_right (Nat.le_of_not_gt hab)]

end IntegerMultBounds.MathlibTM2.Fast.TableVM
