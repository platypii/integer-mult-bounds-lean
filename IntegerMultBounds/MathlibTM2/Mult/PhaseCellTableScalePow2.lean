module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! Reuse the certified power-of-two loop to scale a retained packet width.
Only the destination, power scratch and loop index change. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblScalePow2 {n : ℕ} (c e p i : Fin n) : TblCode n :=
  .seq (tblPow2 p e i) (.ins (.mul c p c))

theorem tblScalePow2_do {n A W w C E : ℕ} (c e p i : Fin n)
    (hcp : c ≠ p) (hci : c ≠ i) (hpe : p ≠ e) (hpi : p ≠ i) (hei : e ≠ i)
    (st : TblSt n A) (hc : st.val c = C) (he : st.val e = E)
    (hEW : E < W) (hfit : C*2^E < 2^W) :
    TblDo A W w (tblScalePow2 c e p i) st (fun st' =>
      st'.val c = C*2^E ∧ st'.val p = 2^E ∧ st'.val i = E ∧ st'.acc = st.acc ∧
      ∀ k, k ≠ c → k ≠ p → k ≠ i → st'.val k = st.val k) (4*E+6) := by
  have hp := tblPow2_do (W := W) (w := w) hpe hpi hei st (by rw [he]; exact hEW)
  unfold tblScalePow2
  apply (hp.seq (K₂ := 1) ?_).mono (fun _ h => h) (by rw [he])
  intro s ⟨hp,hi,hframe,hacc⟩
  have hC : s.val c = C := (hframe c hcp hci).trans hc
  have hP : s.val p = 2^E := by simpa only [he] using hp
  have hI : s.val i = E := hi.trans he
  apply TblDo.insX (.mul c p c)
  · simpa only [TblIns.fits,hC,hP] using hfit
  · refine ⟨?_,?_,?_,hacc,?_⟩
    · simp only [TblIns.exact,Function.update_self,hC,hP]
    · simpa only [TblIns.exact,Function.update_of_ne hcp.symm] using hP
    · simpa only [TblIns.exact,Function.update_of_ne hci.symm] using hI
    · intro k hkc hkp hki
      simpa only [TblIns.exact,Function.update_of_ne hkc] using hframe k hkp hki

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
