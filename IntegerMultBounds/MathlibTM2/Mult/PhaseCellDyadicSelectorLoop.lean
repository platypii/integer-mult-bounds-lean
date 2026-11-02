module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicSelectorProgress

/-! A fixed while loop implements arithmetic row selection. Structural fuel
proves termination and a uniform polynomial bound; it is absent from the code. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def dyadicSelectorLoopCode : TblCode 16 := .loop 2 5 dyadicSelectorStepCode

theorem dyadicSelectorLoopCode_do {A W w : ℕ} (B : ℕ) (hBW : B < W)
    (fuel a b C i : ℕ) (h : a+b ≤ fuel) (hB : a+b ≤ B) (st : TblSt 16 A)
    (ha : st.val 0 = a) (hb : st.val 1 = b) (hz : st.val 2 = 0)
    (hn : st.val 5 = dyadicStageCount fuel a b) (hi : st.val 8 = i)
    (hC : st.val 9 = C) (hone : st.val 14 = 1) (hfit : C*2^(a+b) < 2^W)
    (hindex : i < dyadicStageCount fuel a b) :
    let row := selectDyadicStage fuel a b C (dyadicStageCount fuel a b) i
    TblDo A W w dyadicSelectorLoopCode st (fun F =>
      F.val 11 = row.outerCount ∧ F.val 9 = row.blockWidth ∧ F.val 10 = row.fieldBits ∧ F.val 5 = 0 ∧
      F.acc = st.acc ∧ ∀ j, j ∉ dyadicSelectorWrites → F.val j = st.val j)
      (fuel*(4*B+19)+2) := by
  induction fuel generalizing a b C i st with
  | zero => simp [dyadicStageCount] at hindex
  | succ fuel ih =>
    obtain ⟨s,k,hstep,hpost,hk⟩ := dyadicSelectorStepCode_do (W := W) (w := w) st ha hb hz hn hi hC hone
      hindex (dyadicStageCount_le (fuel+1) a b h) (hB.trans_lt hBW) hfit
    rcases hpost with ⟨hvalues,hacc,hframe⟩
    have hsZero : s.val 2 = 0 := (hframe 2 (by decide)).trans hz
    have hsOne : s.val 14 = 1 := (hframe 14 (by decide)).trans hone
    have hprogress := dyadicSelectorTransition_spec (fuel+1) a b C i h hindex
    simp only [Nat.add_sub_cancel] at hprogress
    have hkB : k ≤ 4*B+17 := by omega
    cases hresult : dyadicSelectorTransition a b C (dyadicStageCount (fuel+1) a b) i with
    | found row =>
      rw [hresult] at hvalues hprogress
      rcases hvalues with ⟨hg,h11,h9,h10⟩
      have hexit : TblBig A W w dyadicSelectorLoopCode s s 2 :=
        TblBig.loopF (by rw [hsZero,hg]; omega)
      refine ⟨s,k+2+2,TblBig.loopT (by rw [hz,hn]; omega) hstep hexit,?_,?_⟩
      · simpa only [←hprogress] using ⟨h11,h9,h10,hg,hacc,hframe⟩
      · have hm := Nat.mul_le_mul_right (4*B+19) (show 1 ≤ fuel+1 by omega)
        simp only [Nat.one_mul] at hm
        omega
    | next a' b' C' n' i' =>
      rw [hresult] at hvalues hprogress
      rcases hvalues with ⟨ha',hb',hC',hn',hi'⟩
      rcases hprogress with ⟨hsmall,hsmallB,hvolume,hcount,hindex',hrow⟩
      have hfit' : C'*2^(a'+b') < 2^W := by rw [hvolume]; exact hfit
      obtain ⟨F,m,hrest,hF,hm⟩ := ih a' b' C' i' hsmall (hsmallB.trans hB) s
        ha' hb' hsZero (hn'.trans hcount) hi' hC' hsOne hfit' (by simpa only [hcount] using hindex')
      refine ⟨F,k+m+2,TblBig.loopT (by rw [hz,hn]; omega) hstep hrest,?_,?_⟩
      · rcases hF with ⟨h11,h9,h10,h5,haccF,hframeF⟩
        refine ⟨?_,?_,?_,h5,haccF.trans hacc,?_⟩
        · simpa only [hrow,hcount] using h11
        · simpa only [hrow,hcount] using h9
        · simpa only [hrow,hcount] using h10
        · intro j hj
          exact (hframeF j hj).trans (hframe j hj)
      · simp only [Nat.add_mul,Nat.one_mul]
        omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
