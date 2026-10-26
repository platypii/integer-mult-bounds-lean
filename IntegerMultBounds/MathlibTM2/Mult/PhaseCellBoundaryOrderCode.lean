module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloMembershipMask
public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! Enumerate the actual halo boundary in ambient coordinate order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def boundaryOrderRow : TblCode 16 :=
  haloMembershipMaskCode true ;; .ins (.zero 6) ;;
    .ite 6 15 (.ins (.emit 3 6)) (.ins (.zero 6))

def boundaryOrderSymbols (A w s t band a b : ℕ) : List (Fin (A+4)) :=
  (List.range s).flatMap (fun k =>
    if haloMaskAt true s t band a b k then tblPairs A w k 0 else [])

theorem boundaryOrderRow_do {A V w s t band a b k : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w boundaryOrderRow st (fun st' =>
      st'.acc = (if haloMaskAt true s t band a b k then tblPairs A w k 0 else []).reverse ++ st.acc ∧
      ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 28 := by
  have hm := haloMembershipMaskCode_do (A := A) (V := V) (w := w) true st
    hs ht hband hk ha hb hs0 hst haS hbS hbandS hwide
  unfold boundaryOrderRow
  apply hm.seq (K₂ := 3)
  intro st₁ ⟨hflag,hacc,hframe⟩
  have hz : TblDo A V w (.ins (.zero 6)) st₁ (fun st₂ =>
      st₂.val 6 = 0 ∧ st₂.val 15 = st₁.val 15 ∧ st₂.acc = st₁.acc ∧
      ∀ r : Fin 16, r.val < 6 → st₂.val r = st₁.val r) 1 := by
    apply TblDo.ins
    refine ⟨by simp [TblIns.run],by simp [TblIns.run],rfl,?_⟩
    intro r hr
    have hne : r ≠ 6 := by intro he; subst r; norm_num at hr
    simp [TblIns.run,hne]
  apply hz.seq (K₂ := 2)
  intro st₂ ⟨hzero,h15,hacc₂,hframe₂⟩
  have hlow (r : Fin 16) (hr : r.val < 6) := (hframe₂ r hr).trans (hframe r hr)
  by_cases hB : haloMaskAt true s t band a b k = true
  · apply TblDo.iteT (by simp [hzero,h15,hflag,hB])
    apply TblDo.ins
    refine ⟨?_,hlow⟩
    simp [TblIns.run,hB,hlow 3 (by decide),hk,hzero,hacc₂,hacc]
  · apply TblDo.iteF (by simp [hzero,h15,hflag,hB])
    apply TblDo.ins
    refine ⟨by simp [TblIns.run,hB,hacc₂,hacc],?_⟩
    intro r hr
    have hne : r ≠ 6 := by intro he; subst r; norm_num at hr
    simpa [TblIns.run,hne] using hlow r hr

def boundaryOrderCode : TblCode 16 := tblFor 3 0 boundaryOrderRow

theorem boundaryOrderCode_do {A V w s t band a b : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w boundaryOrderCode st (fun st' =>
      st'.acc = ((List.range s).flatMap (fun k =>
        if haloMaskAt true s t band a b k then tblPairs A w k 0 else [])).reverse ++ st.acc)
      (31*s+3) := by
  let F := fun k => if haloMaskAt true s t band a b k then tblPairs A w k 0 else []
  let Inv := fun j (st' : TblSt 16 A) =>
    (∀ r : Fin 16, r.val < 6 → r ≠ 3 → st'.val r = st.val r) ∧
    st'.acc = ((List.range j).flatMap F).reverse ++ st.acc
  have hsV : s < 2^V := by nlinarith [hst, Nat.zero_le (t*t)]
  have hc : TblDo A V w boundaryOrderCode st (fun st' =>
      st'.acc = ((List.range s).flatMap F).reverse ++ st.acc) (1+(s*(28+1+2)+2)) := by
    apply TblDo.for s 28 hs hsV (by decide) Inv
    · constructor
      · intro r hr h3
        simp [h3]
      · simp
    · intro k hk st₁ ⟨hf,hacc⟩ hindex hcount
      have hrow := boundaryOrderRow_do (A := A) (V := V) (w := w) st₁
        ((hf 0 (by decide) (by decide)).trans hs)
        ((hf 1 (by decide) (by decide)).trans ht)
        ((hf 2 (by decide) (by decide)).trans hband) hindex
        ((hf 4 (by decide) (by decide)).trans ha)
        ((hf 5 (by decide) (by decide)).trans hb)
        hs0 hst haS hbS hbandS hwide
      exact hrow.mono (fun st₂ ⟨hrowacc,hframe⟩ =>
        ⟨(hframe 3 (by decide)).trans hindex,(hframe 0 (by decide)).trans hcount,by
          constructor
          · intro r hr h3
            simpa [h3] using (hframe r hr).trans (hf r hr h3)
          · rw [hrowacc,hacc,List.range_succ]
            simp [F,List.reverse_append,List.append_assoc]⟩) le_rfl
    · intro st' hI _ _
      exact hI.2
  exact hc.mono (fun st' hh => hh) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
