module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! Compute final rounding dimensions from ordinary binary scalars. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- Inputs: storage width, precision, output precision, shift, magnitude exponent.
Outputs: retained width, truncated bits, dropped high padding. -/
def tblRoundScalars : TblCode 8 :=
  tblBlock 8 [.add 2 4 5,.inc 5,.inc 5,.inc 5,.inc 5,.inc 5,
    .sub 1 2 6,.add 6 3 6,.sub 0 6 7] (.sub 7 5 7)

theorem tblRoundScalars_do {A W e w q p j E : ℕ} (st : TblSt 8 A)
    (h0 : st.val 0 = w) (h1 : st.val 1 = q) (h2 : st.val 2 = p)
    (h3 : st.val 3 = j) (h4 : st.val 4 = E)
    (hp : p ≤ q) (hsize : q-p+j+(p+E+5) ≤ w) (hroom : w < 2^W) :
    TblDo A W e tblRoundScalars st (fun z =>
      (∀ i : Fin 5, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
      z.val 5 = p+E+5 ∧ z.val 6 = q-p+j ∧ z.val 7 = w-(q-p+j)-(p+E+5) ∧
      z.acc = st.acc) 10 := by
  unfold tblRoundScalars
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList,TblIns.fits,TblIns.exact,h0,h1,h2,h3,h4]
    omega
  · refine ⟨?_,?_,?_,?_,?_⟩
    · intro i
      fin_cases i <;> simp [tblExactList,TblIns.exact]
    all_goals simp [tblExactList,TblIns.exact,h0,h1,h2,h3,h4]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
