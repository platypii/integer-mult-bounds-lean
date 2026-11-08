module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! Select an original-coordinate row from the right-then-left residual bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def cyclicResidualIndex (s a b i : ℕ) : ℕ :=
  if i < a then i else if i < b then s+i else i

theorem cyclicResidualIndex_eq (s a b i : ℕ) :
    cyclicResidualIndex s a b i = if a ≤ i ∧ i < b then s+i else i := by
  unfold cyclicResidualIndex
  split_ifs <;> omega

theorem cyclicResidualIndex_lt {s a b i : ℕ} (hi : i < s) : cyclicResidualIndex s a b i < s+s := by
  unfold cyclicResidualIndex
  split_ifs <;> omega

def cyclicResidualIndexCode : TblCode 5 :=
  .ite 3 1 (.ins (.copy 3 4)) (.ite 3 2 (.ins (.add 0 3 4)) (.ins (.copy 3 4)))

theorem cyclicResidualIndexCode_do {A W w s a b i : ℕ} (st : TblSt 5 A)
    (hs : st.val 0 = s) (ha : st.val 1 = a) (hb : st.val 2 = b) (hi : st.val 3 = i)
    (his : i < s) (hwide : s+s ≤ 2^W) :
    TblDo A W w cyclicResidualIndexCode st
      (fun F => F = ⟨Function.update st.val 4 (cyclicResidualIndex s a b i),st.acc⟩) 3 := by
  by_cases hia : i < a
  · have hcopy : TblDo A W w cyclicResidualIndexCode st
        (fun F => F = ⟨Function.update st.val 4 (cyclicResidualIndex s a b i),st.acc⟩) 2 := by
      apply TblDo.iteT (by simpa only [hi,ha] using hia)
      apply TblDo.insX
      · simp [TblIns.fits]
      · simp [TblIns.exact,hi,cyclicResidualIndex,hia]
    exact hcopy.mono (fun _ h => h) (by decide)
  · apply TblDo.iteF (by simpa only [hi,ha] using hia)
    by_cases hib : i < b
    · apply TblDo.iteT (by simpa only [hi,hb] using hib)
      apply TblDo.insX
      · simp only [TblIns.fits,hs,hi]
        omega
      · simp [TblIns.exact,hs,hi,cyclicResidualIndex,hia,hib]
    · apply TblDo.iteF (by simpa only [hi,hb] using hib)
      apply TblDo.insX
      · simp [TblIns.fits]
      · simp [TblIns.exact,hi,cyclicResidualIndex,hia,hib]

/-- The selected address reads exactly the required physical residual row. -/
theorem getElem_cyclicResidualIndex {X : Type*} (right left : List X) (s a b i : ℕ)
    (hR : right.length = s) (hL : left.length = s) (hi : i < s) :
    (right++left)[cyclicResidualIndex s a b i]'(by
      rw [List.length_append,hR,hL]
      exact cyclicResidualIndex_lt hi) =
      if a ≤ i ∧ i < b then left[i]'(by omega) else right[i]'(by omega) := by
  simp only [cyclicResidualIndex_eq]
  split_ifs with hmem
  · rw [List.getElem_append_right (by omega)]
    simp only [hR,Nat.add_sub_cancel_left]
  · exact List.getElem_append_left (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
