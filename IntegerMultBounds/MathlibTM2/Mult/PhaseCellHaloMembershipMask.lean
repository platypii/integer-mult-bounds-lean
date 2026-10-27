module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloInteriorMask

/-! Both sides of the halo partition use the same executed interior test. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def invertHaloMaskCode : TblCode 16 := tblBlock 16 [.zero 6, .inc 6] (.sub 6 15 15)

theorem invertHaloMaskCode_do {A V w : ℕ} (flag : Bool) (st : TblSt 16 A)
    (hflag : st.val 15 = if flag then 1 else 0) (hV : 1 < 2^V) :
    TblDo A V w invertHaloMaskCode st (fun st' =>
      st'.val 15 = (if !flag then 1 else 0) ∧ st'.acc = st.acc ∧
      ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 3 := by
  apply TblDo.block
  · cases flag <;> simp [tblFitsList,TblIns.fits,TblIns.exact,hflag,hV]
  · simp only [List.cons_append,List.nil_append,tblExactList,TblIns.exact]
    cases flag <;> simp [hflag]
    all_goals
      intro r hr
      have hr6 : r ≠ 6 := by intro he; subst r; norm_num at hr
      have hr15 : r ≠ 15 := by intro he; subst r; norm_num at hr
      simp [hr6,hr15]

def haloMembershipMaskCode (boundary : Bool) : TblCode 16 :=
  if boundary then haloInteriorMaskCode ;;
    .ite 3 4 (.ins (.zero 15)) (.ite 3 5 invertHaloMaskCode (.ins (.zero 15)))
  else haloInteriorMaskCode

theorem haloMembershipMaskCode_do {A V w s t band a b k : ℕ} (boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w (haloMembershipMaskCode boundary) st (fun st' =>
      st'.val 15 = (if haloMaskAt boundary s t band a b k then 1 else 0) ∧
      st'.acc = st.acc ∧ ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 25 := by
  have hcore := haloInteriorMaskCode_do (w := w) st hs ht hband hk ha hb hs0 hst haS hbS hwide
  cases boundary
  · exact hcore.mono (fun _ h => h) (by omega)
  · unfold haloMembershipMaskCode
    simp only [Bool.true_eq_false,ite_true]
    refine hcore.seq (K₂ := 5) (fun s₁ h₁ => ?_)
    have hlow (r : Fin 16) (hr : r.val < 6) := h₁.2.2 r hr
    have hzero (hflag : haloMaskAt true s t band a b k = false) :
        TblDo A V w (.ins (.zero 15)) s₁ (fun st' =>
          st'.val 15 = (if haloMaskAt true s t band a b k then 1 else 0) ∧
          st'.acc = st.acc ∧ ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 1 := by
      apply TblDo.insX (.zero 15) (by simp [TblIns.fits])
      refine ⟨by simp [TblIns.exact,hflag],h₁.2.1,?_⟩
      intro r hr
      have hr15 : r ≠ 15 := by intro he; subst r; norm_num at hr
      simpa [TblIns.exact,hr15] using hlow r hr
    by_cases hka : k < a
    · exact (TblDo.iteT (by simpa [hlow 3 (by decide),hlow 4 (by decide),hk,ha] using hka)
        (hzero (by simp [haloMaskAt,show ¬a ≤ k by omega]))).mono (fun _ h => h) (by omega)
    · apply TblDo.iteF (by simpa [hlow 3 (by decide),hlow 4 (by decide),hk,ha] using hka)
      by_cases hkb : k < b
      · apply TblDo.iteT (by simpa [hlow 3 (by decide),hlow 5 (by decide),hk,hb] using hkb)
        have hone : 1 < 2^V := by nlinarith only [hwide]
        exact (invertHaloMaskCode_do (haloInteriorAt s t band a b k) s₁ h₁.1 hone).mono
          (fun s₂ h₂ => by
            refine ⟨?_,h₂.2.1.trans h₁.2.1,?_⟩
            · simpa [haloMaskAt,show a ≤ k by omega,hkb] using h₂.1
            · intro r hr; exact (h₂.2.2 r hr).trans (hlow r hr)) le_rfl
      · exact (TblDo.iteF (by simpa [hlow 3 (by decide),hlow 5 (by decide),hk,hb] using hkb)
          (hzero (by simp [haloMaskAt,hkb]))).mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
