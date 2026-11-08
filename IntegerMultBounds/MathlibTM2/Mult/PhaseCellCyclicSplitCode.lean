module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! Compute the two physical pieces of a cyclic window without restarting its phase. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def cyclicSplitMinimum : TblCode 7 :=
  .ite 2 3 (.ins (.copy 2 4)) (.ins (.copy 3 4))

def cyclicSplitCode : TblCode 7 :=
  .ins (.sub 0 1 3) ;; cyclicSplitMinimum ;; tblBlock 7 [.add 1 4 5] (.sub 2 4 6)

theorem cyclicSplitMinimum_do {A W w s a n : ℕ} (st : TblSt 7 A)
    (hn : st.val 2 = n) (hroom : st.val 3 = s-a) :
    TblDo A W w cyclicSplitMinimum st
      (fun F => F = ⟨Function.update st.val 4 (min n (s-a)),st.acc⟩) 2 := by
  by_cases h : n < s-a
  · apply TblDo.iteT (by simpa only [hn,hroom] using h)
    apply TblDo.insX
    · simp [TblIns.fits]
    · simp [TblIns.exact,hn,min_eq_left h.le]
  · apply TblDo.iteF (by simpa only [hn,hroom] using h)
    apply TblDo.insX
    · simp [TblIns.fits]
    · simp [TblIns.exact,hroom,min_eq_right (by omega : s-a ≤ n)]

theorem cyclicSplitCode_do {A W w s a n : ℕ} (st : TblSt 7 A)
    (hs : st.val 0 = s) (ha : st.val 1 = a) (hn : st.val 2 = n)
    (has : a ≤ s) (hns : n ≤ s) (hwide : s < 2^W) :
    TblDo A W w cyclicSplitCode st (fun F =>
      F.val 5 = a+min n (s-a) ∧ F.val 6 = n-min n (s-a) ∧
      F.val 3 = s-a ∧ F.val 4 = min n (s-a) ∧ F.acc = st.acc ∧
      ∀ i, i ∉ [(3 : Fin 7),4,5,6] → F.val i = st.val i) 5 := by
  let S₁ : TblSt 7 A := ⟨Function.update st.val 3 (s-a),st.acc⟩
  let S₂ : TblSt 7 A := ⟨Function.update S₁.val 4 (min n (s-a)),st.acc⟩
  have h₁ : TblDo A W w (.ins (.sub 0 1 3)) st (fun F => F = S₁) 1 := by
    apply TblDo.insX
    · simp only [TblIns.fits,hs,ha]
      omega
    · simp [TblIns.exact,S₁,hs,ha]
  have h₂ : TblDo A W w cyclicSplitMinimum S₁ (fun F => F = S₂) 2 :=
    cyclicSplitMinimum_do S₁ (by simpa [S₁] using hn) (by simp [S₁])
  have h₃ : TblDo A W w (tblBlock 7 [.add 1 4 5] (.sub 2 4 6)) S₂
      (fun F => F = ⟨Function.update (Function.update S₂.val 5 (a+min n (s-a)))
        6 (n-min n (s-a)),st.acc⟩) 2 := by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact,S₂,S₁,ha,hn]
      constructor <;> omega
    · simp [tblExactList,TblIns.exact,S₂,S₁,ha,hn]
  have hseq : TblDo A W w cyclicSplitCode st
      (fun F => F = ⟨Function.update (Function.update S₂.val 5 (a+min n (s-a)))
        6 (n-min n (s-a)),st.acc⟩) 5 := by
    exact h₁.seq (fun F hF => by subst F; exact h₂.seq (fun G hG => by subst G; exact h₃))
  exact hseq.mono (fun F hF => by
    subst F
    refine ⟨by simp,by simp,by simp [S₂,S₁],by simp [S₂],rfl,?_⟩
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    simp [S₂,S₁,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2]) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
