module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! Emit a nonempty structural row of retained variables. The shared zero
coordinate selects real binary packets; variable values are unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblEmitVars {n : ℕ} (zero : Fin n) : Fin n → List (Fin n) → TblCode n
  | c,[] => .ins (.emit c zero)
  | c,r::rs => .seq (.ins (.emit c zero)) (tblEmitVars zero r rs)

theorem tblEmitVars_do {n A W w : ℕ} (zero c : Fin n) (rs : List (Fin n))
    (st : TblSt n A) (hz : st.val zero = 0) :
    TblDo A W w (tblEmitVars zero c rs) st (fun F => F.val = st.val ∧
      F.acc = ((c::rs).flatMap (fun r => tblPairs A w (st.val r) 0)).reverse++st.acc) (rs.length+1) := by
  induction rs generalizing c st with
  | nil =>
    exact TblDo.ins _ (by simp [TblIns.run,hz])
  | cons r rs ih =>
    let M : TblSt n A := ⟨st.val,(tblPairs A w (st.val c) 0).reverse++st.acc⟩
    have hfirst : TblDo A W w (.ins (.emit c zero)) st (fun F => F = M) 1 :=
      TblDo.ins _ (by simp [TblIns.run,hz,M])
    apply (hfirst.seq (K₂ := rs.length+1) ?_).mono (fun _ h => h) (by simp; omega)
    intro st₁ he
    subst st₁
    exact (ih r M hz).mono (fun F hF => by
      rcases hF with ⟨hv,ha⟩
      refine ⟨hv,?_⟩
      simpa only [M,List.flatMap_cons,List.reverse_append,List.append_assoc] using ha) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
