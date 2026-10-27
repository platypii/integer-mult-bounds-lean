module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloPhaseBit

/-! Execute the halo interior membership bit from original numeric geometry. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloInteriorMaskPrefix : TblCode 16 :=
  tblBlock 16 [.add 4 2 13, .sub 5 2 14] (.zero 15)

def haloInteriorMaskCore : TblCode 16 := haloInteriorMaskPrefix ;;
  .ite 3 13 (.ins (.zero 15)) (.ite 3 14 haloPhaseBitCode (.ins (.zero 15)))

theorem haloInteriorMaskCore_do {A V w s t band a b k : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hbandB : band ≤ b)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w haloInteriorMaskCore st (fun st' =>
      st'.val 15 = (if haloInteriorAt s t band a b k then 1 else 0) ∧
      st'.acc = st.acc ∧ ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 19 := by
  have h2t : 2*t+2 < 2^V := by nlinarith only [hwide]
  have hcap : 2*t*t+t < 2^V := by nlinarith only [hwide]
  have hsV : 2*s < 2^V := by omega
  let S₀ : TblSt 16 A := ⟨Function.update (Function.update (Function.update st.val 13 (a+band))
    14 (b-band)) 15 0,st.acc⟩
  let Post := fun st' : TblSt 16 A =>
    st'.val 15 = (if haloInteriorAt s t band a b k then 1 else 0) ∧
      st'.acc = st.acc ∧ ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r
  have hlow (r : Fin 16) (hr : r.val < 6) : S₀.val r = st.val r := by
    have hr13 : r ≠ 13 := by intro he; subst r; norm_num at hr
    have hr14 : r ≠ 14 := by intro he; subst r; norm_num at hr
    have hr15 : r ≠ 15 := by intro he; subst r; norm_num at hr
    simp [S₀,hr13,hr14,hr15]
  have hp : TblDo A V w haloInteriorMaskPrefix st (fun st' => st' = S₀) 3 := by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact,ha,hb,hband]
      omega
    · simp [tblExactList,TblIns.exact,ha,hb,hband,S₀]
  have hzero (hflag : haloInteriorAt s t band a b k = false) :
      TblDo A V w (.ins (.zero 15)) S₀ Post 1 := by
    apply TblDo.insX (.zero 15) (by simp [TblIns.fits])
    refine ⟨by simp [TblIns.exact,hflag],rfl,?_⟩
    intro r hr
    have hr15 : r ≠ 15 := by intro he; subst r; norm_num at hr
    simpa [TblIns.exact,hr15] using hlow r hr
  unfold haloInteriorMaskCore
  refine hp.seq (K₂ := 16) (fun s₁ h₁ => ?_)
  subst s₁
  by_cases hstart : k < a+band
  · exact (TblDo.iteT (by simpa [S₀,hk] using hstart)
      (hzero (by simp [haloInteriorAt,show ¬a+band ≤ k by omega]))).mono (fun _ h => h) (by omega)
  · apply TblDo.iteF (by simpa [S₀,hk] using hstart)
    by_cases hstop : k < b-band
    · apply TblDo.iteT (by simpa [S₀,hk] using hstop)
      have hkband : band ≤ k := by omega
      have hks : k+band < s := by omega
      have hprod : 2*(t-s)*(k+band) ≤ 2*t*t :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.sub_le t s)) (by omega)
      have hright : 2*(t-s)*(k+band)+s < 2^V :=
        (Nat.add_le_add hprod hst.le).trans_lt hcap
      have hleft : 2*(t-s)*(k-band)+s < 2^V :=
        (Nat.add_le_add_right (Nat.mul_le_mul_left (2*(t-s)) (show k-band ≤ k+band by omega)) s).trans_lt hright
      have hbit := haloPhaseBitCode_do (w := w) S₀
        (by simpa [S₀] using hs) (by simpa [S₀] using ht)
        (by simpa [S₀] using hband) (by simpa [S₀] using hk) (by simp [S₀])
        hs0 hst.le hkband hsV (by omega) (by omega) hleft hright
      exact hbit.mono (fun s₂ h₂ => by
        refine ⟨?_,h₂.2.1,?_⟩
        · simpa [haloInteriorAt,show a+band ≤ k by omega,hstop] using h₂.1
        · intro r hr; exact (h₂.2.2 r hr).trans (hlow r hr)) le_rfl
    · exact (TblDo.iteF (by simpa [S₀,hk] using hstop)
        (hzero (by simp [haloInteriorAt,hstop]))).mono (fun _ h => h) (by omega)

def haloInteriorMaskCode : TblCode 16 :=
  .ite 5 2 (.ins (.zero 15)) haloInteriorMaskCore

theorem haloInteriorMaskCode_do {A V w s t band a b k : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w haloInteriorMaskCode st (fun st' =>
      st'.val 15 = (if haloInteriorAt s t band a b k then 1 else 0) ∧
      st'.acc = st.acc ∧ ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 20 := by
  unfold haloInteriorMaskCode
  by_cases hbb : b < band
  · have hflag : haloInteriorAt s t band a b k = false := by
      simp [haloInteriorAt,Nat.sub_eq_zero_of_le hbb.le]
    have hz : TblDo A V w (.ins (.zero 15)) st (fun st' =>
        st'.val 15 = (if haloInteriorAt s t band a b k then 1 else 0) ∧
        st'.acc = st.acc ∧ ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 1 := by
      apply TblDo.insX (.zero 15) (by simp [TblIns.fits])
      refine ⟨by simp [TblIns.exact,hflag],rfl,?_⟩
      intro r hr
      have hr15 : r ≠ 15 := by intro he; subst r; norm_num at hr
      simp [TblIns.exact,hr15]
    exact (TblDo.iteT (by simpa [hb,hband] using hbb) hz).mono (fun _ h => h) (by omega)
  · apply TblDo.iteF (by simpa [hb,hband] using hbb)
    exact haloInteriorMaskCore_do st hs ht hband hk ha hb hs0 hst haS hbS (by omega) hwide

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
