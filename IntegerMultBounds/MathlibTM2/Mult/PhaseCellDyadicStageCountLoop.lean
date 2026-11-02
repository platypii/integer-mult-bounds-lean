module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicStageCountCode

/-! A fixed Euclidean table loop computes the exact stage count. The proof
uses structural fuel only for termination, not in the physical program. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def dyadicCountLoopCode : TblCode 16 := .loop 2 5 dyadicCountStepCode

private theorem stageCount_zero_left (fuel b : ℕ) : dyadicStageCount fuel 0 b = 0 := by
  cases fuel <;> simp [dyadicStageCount]

private theorem stageCount_zero_right (fuel a : ℕ) : dyadicStageCount fuel a 0 = 0 := by
  cases fuel <;> simp [dyadicStageCount]

private theorem dyadicCountLoop_exit {A W w fuel a b c : ℕ} (st : TblSt 16 A)
    (hz : st.val 2 = 0) (hc : st.val 3 = c) (hguard : st.val 5 = min a b)
    (hstop : a = 0 ∨ b = 0) :
    TblDo A W w dyadicCountLoopCode st (fun st' =>
      st'.val 3 = c+dyadicStageCount fuel a b ∧ st'.val 5 = 0 ∧ st'.val 2 = 0 ∧ st'.acc = st.acc ∧
      ∀ k, k ∉ [(0 : Fin 16),1,3,4,5] → st'.val k = st.val k) (9*dyadicStageCount fuel a b+2) := by
  have hg : st.val 5 = 0 := by
    rcases hstop with ha | hb
    · simp [hguard,ha]
    · simp [hguard,hb]
  have hn : dyadicStageCount fuel a b = 0 := by
    rcases hstop with ha | hb
    · rw [ha,stageCount_zero_left]
    · rw [hb,stageCount_zero_right]
  exact ⟨st,2,TblBig.loopF (by rw [hz,hg]; omega),by simp [hc,hg,hz,hn],by simp [hn]⟩

theorem dyadicCountLoopCode_do {A W w : ℕ} (fuel a b c : ℕ) (h : a+b ≤ fuel) (st : TblSt 16 A)
    (ha : st.val 0 = a) (hb : st.val 1 = b) (hz : st.val 2 = 0) (hc : st.val 3 = c)
    (hguard : st.val 5 = min a b) (hwide : c+a+b < 2^W) :
    TblDo A W w dyadicCountLoopCode st (fun st' =>
      st'.val 3 = c+dyadicStageCount fuel a b ∧ st'.val 5 = 0 ∧ st'.val 2 = 0 ∧ st'.acc = st.acc ∧
      ∀ k, k ∉ [(0 : Fin 16),1,3,4,5] → st'.val k = st.val k) (9*dyadicStageCount fuel a b+2) := by
  induction fuel generalizing a b c st with
  | zero =>
    exact dyadicCountLoop_exit st hz hc hguard (Or.inl (by omega))
  | succ fuel ih =>
    by_cases ha0 : a = 0
    · exact dyadicCountLoop_exit st hz hc hguard (Or.inl ha0)
    by_cases hb0 : b = 0
    · exact dyadicCountLoop_exit st hz hc hguard (Or.inr hb0)
    let a' := if a < b then b-a else a-b
    let b' := if a < b then a else b
    have hsmall : a'+b' ≤ fuel := by dsimp only [a',b']; split_ifs <;> omega
    have hwide' : c+1+a'+b' < 2^W := by dsimp only [a',b']; split_ifs <;> omega
    have hcount : dyadicStageCount (fuel+1) a b = 1+dyadicStageCount fuel a' b' := by
      by_cases hab : a < b
      · simp [dyadicStageCount,a',b',ha0,hb0,hab,not_le.mpr hab]
      · simp [dyadicStageCount,a',b',ha0,hb0,hab,Nat.le_of_not_gt hab]
    obtain ⟨st₁,k₁,hstep,he,hk₁⟩ := dyadicCountStepCode_do (W := W) (w := w) st ha hb hc
      (by omega) (by omega) hwide
    subst st₁
    have hv0 : (dyadicCountNext a b c st).val 0 = a' := by
      by_cases hab : a < b <;> simp [dyadicCountNext,a',hab]
    have hv1 : (dyadicCountNext a b c st).val 1 = b' := by
      by_cases hab : a < b <;> simp [dyadicCountNext,b',hab,hb]
    have hv2 : (dyadicCountNext a b c st).val 2 = 0 := by
      by_cases hab : a < b <;> simp [dyadicCountNext,hab,hz]
    have hv3 : (dyadicCountNext a b c st).val 3 = c+1 := by simp [dyadicCountNext]
    have hv5 : (dyadicCountNext a b c st).val 5 = min a' b' := by simp [dyadicCountNext,a',b']
    obtain ⟨F,k₂,hrest,hF,hk₂⟩ := ih a' b' (c+1) hsmall (dyadicCountNext a b c st)
      hv0 hv1 hv2 hv3 hv5 hwide'
    refine ⟨F,k₁+k₂+2,TblBig.loopT (by rw [hz,hguard]; omega) hstep hrest,?_,?_⟩
    · rcases hF with ⟨hresult,hzeroGuard,hzero,hacc,hframe⟩
      refine ⟨?_,hzeroGuard,hzero,hacc,?_⟩
      · rw [hcount]; omega
      · intro k hk
        exact (hframe k hk).trans (dyadicCountNext_off st k hk)
    · rw [hcount]
      omega

/-- Retained exponents occupy 6 and 7. All Euclidean control variables are
initialized by this fixed program; no supplied counter or guard is needed. -/
def generatedDyadicCountCode : TblCode 16 :=
  .seq (tblBlock 16 [.copy 6 0,.copy 7 1,.zero 2] (.zero 3))
    (.seq (tblNatMin 0 1 5) dyadicCountLoopCode)

theorem generatedDyadicCountCode_do {A W w a b : ℕ} (st : TblSt 16 A)
    (ha : st.val 6 = a) (hb : st.val 7 = b) (hwide : a+b < 2^W) :
    TblDo A W w generatedDyadicCountCode st (fun st' =>
      st'.val 3 = dyadicStageCount (a+b) a b ∧ st'.val 5 = 0 ∧ st'.val 2 = 0 ∧ st'.acc = st.acc ∧
      ∀ k, k ∉ [(0 : Fin 16),1,2,3,4,5] → st'.val k = st.val k)
      (9*dyadicStageCount (a+b) a b+8) := by
  let M : TblSt 16 A := ⟨Function.update (Function.update (Function.update (Function.update
    st.val 0 a) 1 b) 2 0) 3 0,st.acc⟩
  have hinit : TblDo A W w (tblBlock 16 [.copy 6 0,.copy 7 1,.zero 2] (.zero 3)) st
      (fun st' => st' = M) 4 := by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits]
    · simp [tblExactList,TblIns.exact,M,ha,hb]
  unfold generatedDyadicCountCode
  apply (hinit.seq (K₂ := 2+(9*dyadicStageCount (a+b) a b+2)) ?_).mono
    (fun _ h => h) (by omega)
  intro st₁ he
  subst st₁
  apply (tblNatMin_do (W := W) (w := w) 0 1 5 M).seq
  intro st₂ he
  subst st₂
  let N : TblSt 16 A := ⟨Function.update M.val 5 (min a b),M.acc⟩
  have hloop := dyadicCountLoopCode_do (W := W) (w := w) (a+b) a b 0 (by omega) N
    (by simp [N,M]) (by simp [N,M]) (by simp [N,M]) (by simp [N,M])
    (by simp [N]) (by simpa using hwide)
  have heq : ({val := Function.update M.val 5 (min (M.val 0) (M.val 1)), acc := M.acc} : TblSt 16 A) = N := by
    simp [N,M]
  rw [heq]
  exact hloop.mono (fun F hF => by
    rcases hF with ⟨hc,hg,hz,hacc,hframe⟩
    refine ⟨by simpa using hc,hg,hz,hacc,?_⟩
    intro k hk
    have hk' : k ∉ [(0 : Fin 16),1,3,4,5] := by
      intro hm
      apply hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm ⊢
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp
    rw [hframe k hk']
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
    simp [N,M,hk]) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
