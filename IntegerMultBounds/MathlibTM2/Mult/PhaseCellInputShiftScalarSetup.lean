module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellParameterArithmetic

/-! Generate reversible input-conversion dimensions from binary precision and width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblInputShiftDimensions : TblCode 25 :=
  tblBlock 25 [.sub 18 0 15,.zero 17,.inc 17,.sub 15 17 15] (.sub 20 15 16)

theorem tblInputShiftDimensions_do {A W e w q p : ℕ} (st : TblSt 25 A)
    (h0 : st.val 0 = p) (h18 : st.val 18 = q) (h20 : st.val 20 = w)
    (hp : p+1 ≤ q) (hq : q ≤ w) (hroom : w < 2^W) :
    TblDo A W e tblInputShiftDimensions st (fun z =>
      (∀ i : Fin 25, i ≠ 15 → i ≠ 16 → i ≠ 17 → z.val i = st.val i) ∧
      z.val 15 = q-p-1 ∧ z.val 16 = w-(q-p-1) ∧ z.val 17 = 1 ∧ z.acc = st.acc) 5 := by
  have hW : W ≠ 0 := by
    intro he
    rw [he] at hroom
    norm_num at hroom
    omega
  unfold tblInputShiftDimensions
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList,TblIns.fits,TblIns.exact,h0,h18,h20]
    omega
  · refine ⟨?_,?_,?_,?_,?_⟩
    · intro i h15 h16 h17
      simp [tblExactList,TblIns.exact,h15,h16,h17]
    all_goals simp [tblExactList,TblIns.exact,h0,h18,h20]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
