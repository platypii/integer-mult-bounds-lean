module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg
public import IntegerMultBounds.NLogN.PhaseCellLatticeArgs

/-! Natural absolute difference on the table machine. The comparison selects
only a subtraction proved not to underflow. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

def naturalDistanceCode {n : ℕ} (x y dst : Fin n) : TblCode n :=
  .ite x y (.ins (.sub y x dst)) (.ins (.sub x y dst))

theorem naturalDistanceCode_do {n A V w a b : ℕ} (x y dst : Fin n) (st : TblSt n A)
    (hx : st.val x = a) (hy : st.val y = b) (ha : a < 2^V) (hb : b < 2^V) :
    TblDo A V w (naturalDistanceCode x y dst) st
      (fun st' => st' = ⟨Function.update st.val dst (naturalDistance a b),st.acc⟩) 2 := by
  by_cases hab : a < b
  · apply TblDo.iteT (by simpa [hx,hy] using hab)
    apply TblDo.insX (.sub y x dst)
      (by simp [TblIns.fits,hx,hy]; omega)
    simp [TblIns.exact,hx,hy,naturalDistance,Nat.sub_eq_zero_of_le hab.le]
  · apply TblDo.iteF (by simpa [hx,hy] using hab)
    apply TblDo.insX (.sub x y dst)
      (by simp [TblIns.fits,hx,hy]; omega)
    simp [TblIns.exact,hx,hy,naturalDistance,Nat.sub_eq_zero_of_le (by omega : b ≤ a)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
